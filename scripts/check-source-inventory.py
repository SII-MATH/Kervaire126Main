#!/usr/bin/env python3
"""Ensure no project source or consumer can bypass the default trust audits."""
from pathlib import Path
import re
root=Path(__file__).resolve().parent.parent
errors=[]
modules=['SpectralSequence','AdamsSynthetic','Literature','Computation']
expected_project={root/'KIP126.lean'}
for module in modules:
    directory=root/'KIP126/Def'/module
    sources=set(directory.rglob('*.lean'))|{root/('KIP126/Def/'+module+'.lean')}
    expected_project|=sources
    audit=directory/'InternalAudit.lean'
    expected={str(p.relative_to(root).with_suffix('')).replace('/','.') for p in sources-{audit}}
    imported=set(re.findall(r'^import all (KIP126\.[\w.]+)$',audit.read_text(),re.M))
    if expected != imported:
        errors.append(f'{module} audit source mismatch: missing {sorted(expected-imported)}, stale {sorted(imported-expected)}')
actual_project=set((root/'KIP126').rglob('*.lean'))|{root/'KIP126.lean'}
if actual_project != expected_project:
    errors.append('Project modules lack an audit owner: '+str(sorted(str(p.relative_to(root)) for p in actual_project-expected_project)))
tests=set((root/'Tests').rglob('*.lean'))-{root/'Tests/Trust.lean'}
expected={str(p.relative_to(root).with_suffix('')).replace('/','.') for p in tests}
actual=set(re.findall(r'^import all (Tests\.[\w.]+)$',(root/'Tests/Trust.lean').read_text(),re.M))
if actual!=expected:errors.append(f'Consumer audit source mismatch: missing {sorted(expected-actual)}, stale {sorted(actual-expected)}')

# Lean `example` proofs need not survive as environment declarations. Audit their
# source too, after removing nested comments and string literals. Quoted names
# such as `sorryAx in the trust checker are data, not proof terms.
def code_only(text):
    out=[];i=0;depth=0
    while i<len(text):
        if text[i:i+2]=='/-':depth+=1;i+=2
        elif depth and text[i:i+2]=='-/':depth-=1;i+=2
        elif depth:i+=1
        elif text[i:i+2]=='--':
            j=text.find('\n',i);i=len(text) if j<0 else j
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\':i+=2
                elif text[i]=='"':i+=1;break
                else:i+=1
            out.append(' ')
        else:out.append(text[i]);i+=1
    return ''.join(out)
for path in tests|{root/'Tests/Trust.lean'}:
    if re.search(r'(?<![\w`])(?:sorry|sorryAx|axiom)\b',code_only(path.read_text())):
        errors.append('Consumer source contains a local sorry/axiom: '+str(path.relative_to(root)))

if errors:raise SystemExit('\n'.join(errors))
print(f'Source inventory: {len(actual_project)} project files and {len(tests)+1} consumer/audit files covered.')
