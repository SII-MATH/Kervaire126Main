#!/usr/bin/env python3
"""Write minimal interface and permitted-hole baselines from compiled captures.

Mathematical prose and citations live in Blueprint/hgraph. This explicit lock
update command never grants permission to change a public interface or introduce
new obligations. Existing hole types/bodies must match the reviewed baseline;
completed holes may be removed. Normal builds only validate these baselines.
Run --prepare and the resulting Lean captures before explicitly updating locks.
"""
import json
import re
from collections import Counter
from pathlib import Path

METADATA_DIR = Path('metadata')
MODULES = [
    ('spectral-sequence', 'SpectralSequence', 'KIP126.SpectralSequence'),
    ('adams-synthetic', 'AdamsSynthetic', 'KIP126.AdamsSynthetic'),
    ('literature', 'Literature', 'KIP126.Literature'),
    ('e2-computation', 'E2Computation', 'KIP126.E2Computation'),
    ('proof-tools', 'ProofTools', 'KIP126.ProofTools'),
    ('adams-calculations', 'AdamsCalculations', 'KIP126.AdamsCalculations'),
    ('main', 'Main', 'KIP126.Main'),
    ('computation', 'Computation', 'KIP126.Computation'),
]
API_FIELDS = ('name', 'type_fingerprint', 'universes', 'axioms')
HOLE_FIELDS = ('name', 'module', 'type_fingerprint', 'body_fingerprint', 'status')
ROUTE_KEY = 'main_zero_layer_rewire_2026_10_16'
ROUTE_FIELDS = ('public_main_roots', 'proofTools_boundary_declarations')


def module_owner(name):
    for _, owner, entry in MODULES:
        if name == entry or name.startswith(entry + '.'):
            return owner
    raise ValueError('Project declaration has no responsibility owner: ' + name)


def minimal_api(data):
    result = {k: data[k] for k in ('module', 'entry_module')}
    result['schema_version'] = 4
    names = []
    for category in ('declarations', 'generated_declarations'):
        result[category] = [{k: row[k] for k in API_FIELDS} for row in data[category]]
        names.extend(row['name'] for row in result[category])
    if len(set(names)) != len(names) or sorted(names) != sorted(data['exports']):
        raise ValueError('Public export partition is not exact and unique')
    result['exports'] = data['exports']
    return result


def minimal_obligations(data):
    rows = [{k: row[k] for k in HOLE_FIELDS} for row in data['obligations']]
    if len({r['name'] for r in rows}) != len(rows):
        raise ValueError('Duplicate permitted hole')
    for row in rows:
        module_owner(row['module'])
        if row['status'] not in ('pending-proof', 'pending-construction'):
            raise ValueError('Unknown obligation kind: ' + row['name'])
    return {
        'schema_version': 2,
        'summary': {'total': len(rows),
                    'by_module': dict(Counter(module_owner(r['module']) for r in rows)),
                    'by_kind': dict(Counter(r['status'] for r in rows))},
        'obligations': rows,
        ROUTE_KEY: {k: data[ROUTE_KEY][k] for k in ROUTE_FIELDS},
    }


def write_baseline(path, data):
    """One declaration per line; never duplicate rendered types or dependency graphs."""
    fields = []
    for key, value in data.items():
        if key in ('declarations', 'generated_declarations', 'exports', 'obligations'):
            encoded = '[\n' + ',\n'.join('    ' + json.dumps(row, ensure_ascii=False)
                                        for row in value) + '\n  ]'
        else:
            encoded = json.dumps(value, ensure_ascii=False, indent=2).replace('\n', '\n  ')
        fields.append('  ' + json.dumps(key) + ': ' + encoded)
    Path(path).write_text('{\n' + ',\n'.join(fields) + '\n}\n')


def reviewed_obligations(data, previous):
    """Accept actual completion; refuse new holes or changed registered objects."""
    old = {r['name']: r for r in previous['obligations']}
    actual = {r['name']: r for r in data}
    if len(actual) != len(data):
        raise ValueError('Duplicate compiled declaration')
    if old.keys() - actual.keys():
        raise ValueError('Registered declaration disappeared: ' + str(old.keys() - actual.keys()))
    rows = []
    for row in data:
        if row['is_axiom'] or row['synthetic_sorry']:
            raise ValueError('Project axiom or synthetic sorry: ' + row['name'])
        if set(row['axioms']) - {'propext', 'Classical.choice', 'Quot.sound', 'sorryAx'}:
            raise ValueError('Unexpected trust dependency: ' + row['name'])
        prior = old.get(row['name'])
        if prior is not None:
            # Finishing a proof permits a new body, never a weaker statement
            # or a change of the mathematical object's owning module.
            for field in ('module', 'type_fingerprint'):
                if row[field] != prior[field]:
                    raise ValueError('Registered obligation changed: ' + row['name'] + ' (' + field + ')')
        if not row['direct_sorry']:
            continue
        if prior is None:
            raise ValueError('New obligation requires explicit review: ' + row['name'])
        if row['body_fingerprint'] != prior['body_fingerprint']:
            raise ValueError('Registered obligation changed: ' + row['name'] + ' (body_fingerprint)')
        rows.append(prior)
    return minimal_obligations({**previous, 'obligations': sorted(rows, key=lambda r: r['name'])})


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
        m=re.search(r'\bpublic\s+(?:noncomputable\s+)?(def|abbrev|theorem|lemma|structure|inductive|class|instance|alias)\b\s*([^\s(:{\[]*)',t)
        if not m:continue
        count+=1
        if not m[2]:continue
        name='.'.join(x for x in (scope,m[2]) if x)
        decls[name]={'source_kind':m[1],'line':line}
    return decls,count

def freeze(stem, module, entry_module):
    data = json.loads(Path(f'.lake/{stem}-capture.json').read_text())
    trust = {r['name']: r for r in json.loads(Path('.lake/trust-capture.json').read_text())}
    sourceinfo = {source: commands(source)[0]
                  for source in {r['module'].replace('.', '/') + '.lean' for r in data}}
    named, generated = [], []
    for row in sorted(data, key=lambda r: r['name']):
        source = row['module'].replace('.', '/') + '.lean'
        item = {k: row[k] for k in ('name', 'type_fingerprint', 'universes')}
        item['axioms'] = sorted(trust[row['name']]['axioms'])
        (named if row['name'] in sourceinfo[source] else generated).append(item)
    result = minimal_api({'module': module, 'entry_module': entry_module,
                          'declarations': named, 'generated_declarations': generated,
                          'exports': sorted(r['name'] for r in data)})
    write_baseline(METADATA_DIR / (stem + '-api.json'), result)
    print(module, len(named), 'named', len(generated), 'generated')


def freeze_trust():
    previous = json.loads((METADATA_DIR / 'proof-obligations.json').read_text())
    data = json.loads(Path('.lake/trust-capture.json').read_text())
    result = reviewed_obligations(data, previous)
    write_baseline(METADATA_DIR / 'proof-obligations.json', result)
    print('Permitted obligations:', result['summary'])


def prepare():
    # Capture uses only ordinary public imports. Trust capture separately sees
    # private implementation declarations, including internal generic helpers.
    template = 'module\npublic import KIP126.AdamsSynthetic\nimport Lean\nopen Lean Elab Command\nset_option maxHeartbeats 0\nset_option maxRecDepth 8192\nset_option pp.universes true\nset_option pp.explicit false\nset_option pp.proofs true\nset_option pp.deepTerms true\nrun_cmd do\n  let env ← getEnv\n  let exported := env.setExporting true\n  let mut rows : Array Json := #[]\n  for (name, info) in env.constants.toList do\n    let some idx := env.getModuleIdxFor? name | continue\n    let mod := env.header.moduleNames[idx.toNat]!\n    unless (`KIP126.AdamsSynthetic).isPrefixOf mod do continue\n    unless (exported.find? name).isSome do continue\n    if isPrivateName name then continue\n    let ranges ← findDeclarationRanges? name\n    let kind := match info with\n      | .thmInfo _ => "theorem"\n      | .defnInfo _ => "definition"\n      | .inductInfo _ => "inductive"\n      | .ctorInfo _ => "constructor"\n      | _ => "generated"\n    let ty ← liftTermElabM <| Meta.ppExpr info.type\n    let axioms ← collectAxioms name\n    rows := rows.push <| Json.mkObj [\n      ("axioms", toJson (axioms.map Name.toString)),\n      ("name", toJson name.toString), ("module", toJson mod.toString),\n      ("kind", toJson kind), ("full_type", toJson ty.pretty),\n      ("line", toJson (ranges.map (·.selectionRange.pos.line))),\n      ("column", toJson (ranges.map (·.selectionRange.pos.column))),\n      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),\n      ("universes", toJson (info.levelParams.map Name.toString)),\n      ("type_fingerprint", toJson (toString (hash (toString info.type))))]\n  liftIO <| IO.FS.writeFile ".lake/adams-synthetic-capture.json" (Json.arr rows).compress\n  logInfo m!"Captured {rows.size} exported project declarations"\n'
    Path('.lake').mkdir(exist_ok=True)
    for stem,module,entry in MODULES:
        capture = template.replace('KIP126.AdamsSynthetic', entry).replace('adams-synthetic', stem)
        if module == 'Computation':
            # The historical facade owns no definitions. Preserve its exact
            # original lock by capturing both actual defining-module owners.
            capture = capture.replace(
                'unless (`KIP126.Computation).isPrefixOf mod do continue',
                'unless (`KIP126.Computation).isPrefixOf mod || '
                '(`KIP126.E2Computation).isPrefixOf mod || '
                '(`KIP126.AdamsCalculations).isPrefixOf mod do continue')
        Path('.lake/Capture' + module + '.lean').write_text(capture)
    path=Path('scripts/CaptureTrust.lean')
    body=path.read_text(); body=body[body.index('import Lean'):]
    if '"source_name"' not in body:
        body=body.replace('("declaration_kind", toJson kind),', '("source_name", toJson ((privateToUserName? name).getD name).toString),\n      ("declaration_kind", toJson kind),')
    sources=sorted(p for p in Path('KIP126').rglob('*.lean') if p.name!='InternalAudit.lean')
    path.write_text('module\n'+''.join('import all '+str(p.with_suffix('')).replace('/','.')+'\n' for p in sources)+body)
    print('Prepared .lake/Capture{Module}.lean and scripts/CaptureTrust.lean; run them with lake env lean before freezing.')

if __name__ == '__main__':
    import sys
    if sys.argv[1:] == ['--prepare']:
        prepare()
        sys.exit(0)
    freeze_trust()
    for stem, module, entry in MODULES:
        if not sys.argv[1:] or stem in sys.argv[1:]:
            freeze(stem, module, entry)
