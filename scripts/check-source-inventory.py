#!/usr/bin/env python3
"""Cover every source with an audit and enforce the mathematical module DAG."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parent.parent
errors = []
entries = {
    'SpectralSequence': 'KIP126.Def.SpectralSequence',
    'AdamsSynthetic': 'KIP126.Def.AdamsSynthetic',
    'Literature': 'KIP126.Def.Literature',
    'Computation': 'KIP126.Def.Computation',
    'ProofTools': 'KIP126.Def.ProofTools',
    'Main': 'KIP126.Main',
}
allowed_dependencies = {
    'SpectralSequence': {'SpectralSequence'},
    'AdamsSynthetic': {'SpectralSequence', 'AdamsSynthetic'},
    'Literature': {'SpectralSequence', 'AdamsSynthetic', 'Literature'},
    'Computation': {'SpectralSequence', 'AdamsSynthetic', 'Literature', 'Computation'},
    'ProofTools': {'SpectralSequence', 'AdamsSynthetic', 'Literature', 'Computation', 'ProofTools'},
    'Main': set(entries),
}


def lean_name(path):
    return str(path.relative_to(root).with_suffix('')).replace('/', '.')


def owner(name):
    for module, entry in entries.items():
        if name == entry or name.startswith(entry + '.'):
            return module
    return None


# Lean `example` proofs need not survive as environment declarations. Audit their
# source too. Preserve newlines while removing nested comments and string literals.
# Quoted names such as `sorryAx in trust checks are data, not proof terms.
def code_only(text):
    out = []
    i = depth = 0
    while i < len(text):
        if text[i:i + 2] == '/-':
            depth += 1
            out.append('  ')
            i += 2
        elif depth and text[i:i + 2] == '-/':
            depth -= 1
            out.append('  ')
            i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' ')
            i += 1
        elif text[i:i + 2] == '--':
            j = text.find('\n', i)
            j = len(text) if j < 0 else j
            out.append(' ' * (j - i))
            i = j
        elif text[i] == '"':
            out.append(' ')
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    out.append('  ')
                    i += 2
                elif text[i] == '"':
                    out.append(' ')
                    i += 1
                    break
                else:
                    out.append('\n' if text[i] == '\n' else ' ')
                    i += 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def imports(path):
    result = []
    for match in re.finditer(
            r'^\s*(?:(?:public|private|meta)\s+)*import\s+(all\s+)?([^\n]+)',
            code_only(path.read_text()), re.M):
        for name in match[2].split():
            result.append((bool(match[1]), name))
    return result


# Keep the individually reviewed mathematical names from the upstream cleanup.
# Local coordinate variables (for example c3) are unrelated to declarations.
naming_path = root / 'mathematical-naming-restoration.json'
if naming_path.exists():
    naming = json.loads(naming_path.read_text())
    retired_names = set(naming['identifier_renames']) - {'PropositionSevenEight'}
    for path in (root / 'KIP126/Main').rglob('*.lean'):
        declared = re.findall(
            r'\b(?:def|abbrev|theorem|lemma|structure|class|inductive)\s+([\w\']+)',
            code_only(path.read_text()))
        for name in sorted(retired_names.intersection(declared)):
            errors.append(f'Retired numbered declaration restored: {path.relative_to(root)}: {name}')

expected_project = {root / 'KIP126.lean'}
for module, entry in entries.items():
    directory = root / entry.replace('.', '/')
    facade = directory.with_suffix('.lean')
    sources = set(directory.rglob('*.lean')) | {facade}
    expected_project |= sources
    if not facade.is_file():
        errors.append(f'{module} public entry is missing: {facade.relative_to(root)}')
    audit = directory / 'InternalAudit.lean'
    expected = {lean_name(p) for p in sources - {audit}}
    if not audit.is_file():
        errors.append(f'{module} InternalAudit is missing')
        continue
    imported = {name for all_, name in imports(audit) if all_ and name.startswith('KIP126.')}
    if expected != imported:
        errors.append(f'{module} audit source mismatch: missing {sorted(expected - imported)}, '
                      f'stale {sorted(imported - expected)}')

actual_project = set((root / 'KIP126').rglob('*.lean')) | {root / 'KIP126.lean'}
if actual_project - expected_project:
    errors.append('Project modules lack an audit owner: ' + str(sorted(
        str(p.relative_to(root)) for p in actual_project - expected_project)))

for path in actual_project:
    source_owner = owner(lean_name(path))
    for all_, imported in imports(path):
        imported_owner = owner(imported)
        if imported == 'KIPBase' or imported.startswith(('KIPBase.', 'Interface.', 'LinProgram.')):
            errors.append(f'Legacy dependency forbidden: {path.relative_to(root)} imports {imported}')
        if imported == 'KIP126' or imported.startswith('KIP126.'):
            if imported_owner is None:
                errors.append(f'Unowned/root project dependency: {path.relative_to(root)} imports {imported}')
            elif source_owner and imported_owner not in allowed_dependencies[source_owner]:
                errors.append(f'{source_owner} crossed its dependency boundary: '
                              f'{path.relative_to(root)} imports {imported}')
            if all_ and (source_owner is None or imported_owner != source_owner):
                errors.append(f'Cross-module import all forbidden: {path.relative_to(root)} imports {imported}')
        if imported.startswith(('Tests.', 'Checks.')) and path.name != 'InternalAudit.lean':
            errors.append(f'Mathematics imports audit/test code: {path.relative_to(root)} imports {imported}')

tests = set((root / 'Tests').rglob('*.lean')) - {root / 'Tests/Trust.lean'}
expected = {lean_name(p) for p in tests}
actual = {name for all_, name in imports(root / 'Tests/Trust.lean') if all_ and name.startswith('Tests.')}
if actual != expected:
    errors.append(f'Consumer audit source mismatch: missing {sorted(expected - actual)}, '
                  f'stale {sorted(actual - expected)}')
for path in tests | {root / 'Tests/Trust.lean'}:
    if re.search(r'(?<![\w`])(?:sorry|sorryAx|axiom)\b', code_only(path.read_text())):
        errors.append('Consumer source contains a local sorry/axiom: ' + str(path.relative_to(root)))

# The completed ProofTools port retains precisely the four original local
# subgoals; proof-port work may not be disguised as an additional paper gap.
tool_holes = {}
for path in (root / 'KIP126/Def/ProofTools').rglob('*.lean'):
    count = len(re.findall(r'(?<![\w`])sorry\b', code_only(path.read_text())))
    if count:
        tool_holes[str(path.relative_to(root))] = count
if tool_holes != {
        'KIP126/Def/ProofTools/GeneralizedLeibniz.lean': 2,
        'KIP126/Def/ProofTools/GeneralizedMahowald.lean': 2}:
    errors.append('ProofTools original four-gap budget changed: ' + str(tool_holes))

# Every Main declaration, including the completed choice-transport results,
# must have an actual proof body. Upstream obligations keep their own owners.
main_holes = {}
for path in (root / 'KIP126/Main').rglob('*.lean'):
    count = len(re.findall(r'(?<![\w`])sorry\b', code_only(path.read_text())))
    if count:
        main_holes[str(path.relative_to(root))] = count
if main_holes:
    errors.append('Main proof placeholders forbidden: ' + str(main_holes))

if errors:
    raise SystemExit('\n'.join(errors))
print(f'Source inventory: {len(actual_project)} project files and {len(tests) + 1} consumer/audit '
      'files covered; module dependency and private-import boundaries verified.')
