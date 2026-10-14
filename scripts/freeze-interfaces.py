#!/usr/bin/env python3
"""Freeze captured Lean interfaces and the exact pending proof obligations.

Run this script with --prepare, then run the matching .lake/Capture{Module}.lean files and scripts/CaptureTrust.lean
with the pinned `lake env lean` first. This intentionally updates reviewed lock
files; normal `lake build` validates them and never accepts a new hole silently.
"""
import json,re
from collections import Counter
from pathlib import Path

def commands(path):
    text=Path(path).read_text()
    # Preserve line positions while removing nested Lean comments.
    out=[];depth=0;i=0
    while i<len(text):
        if text[i:i+2]=='/-': depth+=1;out.extend('  ');i+=2
        elif depth and text[i:i+2]=='-/': depth-=1;out.extend('  ');i+=2
        elif depth: out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif text[i:i+2]=='--':
            j=text.find('\n',i)
            if j<0:j=len(text)
            out.extend(' '*(j-i));i=j
        else:out.append(text[i]);i+=1
    scope='';stack=[];decls={};count=0
    for line,t in enumerate(''.join(out).splitlines(),1):
        t=t.strip()
        n=re.match(r'namespace\s+([\w.]+)',t)
        if n:
            stack.append(scope);v=n[1];scope=v if v.startswith('KIP126.') else '.'.join(x for x in (scope,v) if x);continue
        if re.search(r'\b(?:noncomputable\s+)?section(?:\s+\w+)?\s*$',t):stack.append(scope);continue
        if re.match(r'end(?:\s+[\w.]+)?\s*$',t):
            if stack:scope=stack.pop()
            continue
        m=re.search(r'\bpublic\s+(?:noncomputable\s+)?(def|abbrev|theorem|lemma|structure|inductive|class|instance)\b\s*([^\s(:{\[]*)',t)
        if not m:continue
        count+=1
        if not m[2]:continue
        name='.'.join(x for x in (scope,m[2]) if x)
        decls[name]={'source_kind':m[1],'line':line}
    return decls,count

def freeze(stem,module):
    data=json.load(open(f'.lake/{stem}-capture.json'))
    trust={d['name']: d for d in json.load(open('.lake/trust-capture.json'))}
    sourceinfo={};totalcommands=0
    for source in sorted(set(d['module'].replace('.','/')+'.lean' for d in data)):
        records,n=commands(source); sourceinfo[source]=records;totalcommands+=n
    ledgerpath=Path(stem+'-contracts.json')
    ledger=json.loads(ledgerpath.read_text()) if ledgerpath.exists() else {}
    capabilities=ledger.get('capabilities',[])
    reverse={}
    for row in data:
        for dep in row['type_dependencies']:
            reverse.setdefault(dep,[]).append(row['name'])
    named=[];generated=[]
    for row in sorted(data,key=lambda x:x['name']):
        source=row['module'].replace('.','/')+'.lean'; matches=sourceinfo[source]
        info=matches.get(row['name'])
        if info is None:
            suffix=[(n,d) for n,d in matches.items() if row['name'].endswith('.'+n.split('.')[-1])]
            # Only accept unique exact-name matches; namespaces must remain authoritative.
        node=trust[row['name']]
        row['axioms']=sorted(node['axioms'])
        row['proof_status']='pending-direct' if node['direct_sorry'] else ('provided-with-pending-dependencies' if 'sorryAx' in node['axioms'] else 'provided')
        row['directly_callable']=row['name'].startswith('KIP126.'+module+'.Standard.')
        row['source']=source
        row.pop('column',None)
        row.pop('line',None)
        row['type_consumers']=sorted(reverse.get(row['name'],[]))
        roles=[]
        for c in capabilities:
            impl=c.get('implementation',[])
            if any(e.get('path')==source and (row['name'].endswith('.'+e.get('declaration','')) or row['name']==e.get('declaration','')) for e in impl):roles.append(c['id'])
        if not roles:
            roles=[c['id'] for c in capabilities if any(e.get('path')==source for e in c.get('implementation',[]))]
        row['capability_evidence']=roles
        if info:
            row.update(info)
            k=info['source_kind']
            row['category']='operation-theorem' if k in ('theorem','lemma') else ('mathematical-definition' if k in ('def','abbrev') else 'type-support')
            row['responsibility']='derived-theorem' if k in ('theorem','lemma') else ('input-signature' if k in ('structure','class') else 'defined-operation-or-predicate')
            if node['direct_sorry']:
                row['responsibility']='pending-upstream-proof' if k in ('theorem','lemma') else 'pending-upstream-construction'
            elif row['directly_callable']:
                row['responsibility']='proved-operation' if k in ('theorem','lemma') else 'fixed-mathematical-object-or-operation'
            named.append(row)
        else:
            row['category']='generated-declaration'
            row['responsibility']='field-constructor-recursion-instance-or-generated-proof-support'
            generated.append(row)
    result={
      'schema_version':3,'module':module,'entry_module':'KIP126.Def.'+module,
      'source_commit':'bbac1fc05843bdf2d56057e6114a38839e939378',
      'capability_ledger':stem+'-contracts.json','source_manifest':stem+'-sources.json',
      'type_fingerprint_algorithm':'Lean hash (toString ConstantInfo.type), checked with universe parameter names',
      'type_rendering':'Elaborated full type, universe parameters shown; inferred arguments use Lean implicit notation. Fingerprint locks the exact kernel expression, including elaborated proof terms.',
      'classification':'Explicit named public source commands are separated from generated fields, constructors, recursors, instances and generated proof helpers. Generated declarations are not independent mathematical promises.',
      'public_source_commands':totalcommands,
      'named_public_declarations':len(named),'generated_declaration_count':len(generated),
      'declarations':named,'generated_declarations':generated,
      'proof_obligation_registry':'proof-obligations.json',
      'proof_status_meaning':'provided-with-pending-dependencies means this declaration has a body/proof but uses upstream declarations whose proofs or constructions remain pending. It does not assert that the theorem is sorry-free.',
      'exports':sorted(r['name'] for r in data)}
    Path(stem+'-api.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(module,len(named),'named',len(generated),'generated',totalcommands,'source commands')


def freeze_trust():
    data=json.load(open('.lake/trust-capture.json'))
    obligations=[]
    for row in sorted(data,key=lambda r:r['name']):
        if row['is_axiom'] or row['synthetic_sorry']:
            raise ValueError('Cannot freeze project axiom or synthetic sorry: '+row['name'])
        if set(row['axioms'])-{'propext','Classical.choice','Quot.sound','sorryAx'}:
            raise ValueError('Unexpected trust dependency: '+row['name'])
        if not row['direct_sorry']:continue
        if '.Standard' not in row['module']:
            raise ValueError('Only individual fixed upstream obligations are authorized: '+row['name'])
        source=row['module'].replace('.','/')+'.lean'
        parsed,_=commands(source)
        info=parsed.get(row['name'],{})
        kind=info.get('source_kind','generated')
        obligations.append({k:row[k] for k in ['name','module','full_type','type_fingerprint','body_fingerprint']} | {
            'source':source,'line':info.get('line'), 'kind':kind,
            'status':'pending-proof' if kind in ('theorem','lemma') else 'pending-construction',
            'reason':'Fixed upstream mathematical fact or object; proof/construction deferred by the user. This obligation is not a downstream theorem premise.',
            'synthetic_sorry':False})
    result={
        'schema_version':1,
        'policy':'No project axiom declarations. Only these exact individual direct sorry declarations are allowed. Synthetic sorry, unregistered holes, and changed hole types/bodies fail the default build. Consumer tests contain no local sorry. SpectralSequence remains sorry-free.',
        'authorization':'User requested fixed upstream objects/callable theorems with temporarily unfinished proofs, removing Challenge and downstream result packages.',
        'meaning':'Counts include unconstructed mathematical objects as well as unproved theorems. A compiled consumer may depend transitively on these obligations; this registry does not certify their proofs.',
        'summary':{'total':len(obligations),'by_module':dict(Counter(r['module'].split('.')[2] for r in obligations)),
                   'by_kind':dict(Counter(r['status'] for r in obligations))},
        'obligations':obligations}
    Path('proof-obligations.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print('Registered individual obligations:',result['summary'])

def prepare():
    # Capture uses only ordinary public imports. Trust capture separately sees
    # private implementation declarations, including internal generic helpers.
    template = 'module\npublic import KIP126.Def.AdamsSynthetic\nimport Lean\nopen Lean Elab Command\nset_option maxHeartbeats 0\nset_option maxRecDepth 8192\nset_option pp.universes true\nset_option pp.explicit false\nset_option pp.proofs true\nset_option pp.deepTerms true\nrun_cmd do\n  let env ← getEnv\n  let exported := env.setExporting true\n  let mut rows : Array Json := #[]\n  for (name, info) in env.constants.toList do\n    let some idx := env.getModuleIdxFor? name | continue\n    let mod := env.header.moduleNames[idx.toNat]!\n    unless (`KIP126.Def.AdamsSynthetic).isPrefixOf mod do continue\n    unless (exported.find? name).isSome do continue\n    if isPrivateName name then continue\n    let ranges ← findDeclarationRanges? name\n    let kind := match info with\n      | .thmInfo _ => "theorem"\n      | .defnInfo _ => "definition"\n      | .inductInfo _ => "inductive"\n      | .ctorInfo _ => "constructor"\n      | _ => "generated"\n    let ty ← liftTermElabM <| Meta.ppExpr info.type\n    let axioms ← collectAxioms name\n    rows := rows.push <| Json.mkObj [\n      ("axioms", toJson (axioms.map Name.toString)),\n      ("name", toJson name.toString), ("module", toJson mod.toString),\n      ("kind", toJson kind), ("full_type", toJson ty.pretty),\n      ("line", toJson (ranges.map (·.selectionRange.pos.line))),\n      ("column", toJson (ranges.map (·.selectionRange.pos.column))),\n      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),\n      ("universes", toJson (info.levelParams.map Name.toString)),\n      ("type_fingerprint", toJson (toString (hash (toString info.type))))]\n  liftIO <| IO.FS.writeFile ".lake/adams-synthetic-capture.json" (Json.arr rows).compress\n  logInfo m!"Captured {rows.size} exported project declarations"\n'
    Path('.lake').mkdir(exist_ok=True)
    for stem,module in [('spectral-sequence','SpectralSequence'),('adams-synthetic','AdamsSynthetic'),('literature','Literature'),('computation','Computation')]:
        Path('.lake/Capture'+module+'.lean').write_text(template.replace('AdamsSynthetic',module).replace('adams-synthetic',stem))
    path=Path('scripts/CaptureTrust.lean')
    body=path.read_text(); body=body[body.index('import Lean'):]
    sources=sorted(p for p in Path('KIP126/Def').rglob('*.lean') if p.name!='InternalAudit.lean')
    path.write_text('module\n'+''.join('import all '+str(p.with_suffix('')).replace('/','.')+'\n' for p in sources)+body)
    print('Prepared .lake/Capture{Module}.lean and scripts/CaptureTrust.lean; run them with lake env lean before freezing.')

if __name__=='__main__':
    import sys
    if sys.argv[1:] == ['--prepare']:
        prepare()
        sys.exit(0)
    freeze_trust()
    for stem,module in [('spectral-sequence','SpectralSequence'),('adams-synthetic','AdamsSynthetic'),('literature','Literature'),('computation','Computation')]:
        if not sys.argv[1:] or stem in sys.argv[1:]:freeze(stem,module)
