#!/usr/bin/env python3
"""Read-only source audit; write evidence only beside this script. Never invokes Lean/Lake."""
from pathlib import Path
import hashlib
import json
import subprocess

ROOT = Path('/tmp/kip-adams-synthetic-20261016T1625')
OUT = Path(__file__).resolve().parent
BASE = 'bef90640c4594af4db32c86837f9d95340d1e171'
OLD = 'a484b981fad612eabe2bc7a01b54e049e9a01ce4'
RUN = 'metadata/proof-sessions/runs/AdamsSynthetic/20261016T1625'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def git_show(commit, path):
    return subprocess.check_output(['git', 'show', f'{commit}:{path}'], cwd=ROOT)

def write_json(name, obj):
    (OUT / name).write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n')

def records(x, names):
    if isinstance(x, dict):
        if x.get('name') in names:
            yield x
        else:
            for y in x.values():
                yield from records(y, names)
    elif isinstance(x, list):
        for y in x:
            yield from records(y, names)

names = {
    'KIP126.AdamsSynthetic.Standard.synthetic_homotopy_separated',
    'KIP126.AdamsSynthetic.Standard.classical_sphere_separated',
    'KIP126.AdamsSynthetic.HomotopySeparated',
    'KIP126.AdamsSynthetic.Standard.sourceRecognition',
    'KIP126.AdamsSynthetic.Standard.syntheticTower',
    'KIP126.AdamsSynthetic.Standard.nu',
    'KIP126.AdamsSynthetic.Standard.recovery',
    'KIP126.AdamsSynthetic.Standard.coefficients',
    'KIP126.Synthetic.Context.NuFunctorData.suspensionIso',
    'KIP126.Synthetic.SpectralSequence.SyntheticAdamsFamily.nuSphereIso',
}
decls = {}
for p in ['metadata/adams-synthetic-api.json', f'{RUN}/obligations-baseline.json']:
    decls[p] = list(records(json.loads((ROOT / p).read_text()), names))
write_json('exact-declarations.json', decls)

current_ranges = {
    'KIP126/AdamsSynthetic/Standard/Separation.lean': [(1, 25)],
    'KIP126/AdamsSynthetic/Standard/ClassicalSupport.lean': [(67, 109)],
    'KIP126/AdamsSynthetic/Context.lean': [(27, 48), (87, 98), (194, 208), (228, 242)],
    'KIP126/AdamsSynthetic/Configuration.lean': [(33, 58)],
    'KIP126/AdamsSynthetic/Recovery.lean': [(84, 96), (118, 124), (147, 160)],
    'KIP126/AdamsSynthetic/Detection.lean': [(103, 112), (183, 191)],
    'KIP126/AdamsSynthetic/Tower.lean': [(26, 44), (46, 54), (240, 250)],
    'KIP126/AdamsSynthetic/System.lean': [(23, 28), (110, 119)],
    'KIP126/AdamsSynthetic/Standard/Background.lean': [(22, 52), (75, 87), (126, 140)],
    'KIP126/AdamsSynthetic/Standard/Source.lean': [(24, 36), (184, 215)],
    'KIP126/AdamsSynthetic/Internal/Source/Recognition.lean': [(24, 50), (59, 93)],
    'KIP126/AdamsSynthetic/Internal/Source/Prespectrum.lean': [(17, 28)],
    'KIP126/AdamsSynthetic/Internal/Source/Sphere.lean': [(107, 127)],
    'KIP126/AdamsSynthetic/Families.lean': [(90, 95)],
    'KIP126/AdamsSynthetic/Standard/Filtration.lean': [(35, 57)],
}
snap = []
hashes = {}
baseline_map = json.loads((ROOT / f'{RUN}/baseline.json').read_text())['file_sha256']
for p, ranges in current_ranges.items():
    b = (ROOT / p).read_bytes()
    h = sha(b)
    hashes[p] = {'current_sha256': h, 'baseline_sha256': baseline_map.get(p),
                 'matches_session_baseline': h == baseline_map.get(p)}
    lines = b.decode().splitlines()
    snap += [f'\n### {p}\nSHA256={h}']
    for lo, hi in ranges:
        snap += [f'{i+1}: {lines[i]}' for i in range(lo-1, min(hi, len(lines)))]
for p in ['AGENTS.md', 'README.md', 'metadata/adams-synthetic-api.json',
          'metadata/adams-synthetic-contracts.json', 'metadata/adams-synthetic-sources.json',
          'metadata/proof-obligations.json', f'{RUN}/obligations-baseline.json']:
    hashes[p] = {'current_sha256': sha((ROOT / p).read_bytes())}
write_json('input-sha256.json', hashes)
(OUT / 'source-excerpts.txt').write_text('\n'.join(snap) + '\n')
baseline_snap = [f'Session baseline source: {BASE}']
for p in ['KIP126/AdamsSynthetic/Standard/Separation.lean',
          'KIP126/AdamsSynthetic/Standard/ClassicalSupport.lean']:
    b = git_show(BASE, p)
    baseline_snap += [f'\n### {BASE}:{p}\nSHA256={sha(b)}', b.decode()]
(OUT / 'baseline-separation-source.txt').write_text('\n'.join(baseline_snap) + '\n')

old_ranges = {
    'KIP126/Def/AdamsSynthetic/Comparison/Coherent/Data.lean': [(18, 34)],
    'KIP126/Def/AdamsSynthetic/Comparison/Predicates.lean': [(82, 88)],
    'KIP126/Def/StableHomotopy/Spectra/Comparison.lean': [(23, 36)],
    'KIP126/Def/StableHomotopy/Spectra/Completion.lean': [(196, 213)],
    'KIP126/Def/ClassicalAdams/Context/Data.lean': [(284, 297)],
    'KIP126/Main/AdamsSynthetic/SphereConvergence.lean': [(44, 50), (3716, 3745)],
}
old_snap = [f'Read-only Git object source: {OLD}']
for p, ranges in old_ranges.items():
    b = git_show(OLD, p)
    lines = b.decode().splitlines()
    old_snap += [f'\n### {OLD}:{p}\nSHA256={sha(b)}']
    for lo, hi in ranges:
        old_snap += [f'{i+1}: {lines[i]}' for i in range(lo-1, min(hi, len(lines)))]
(OUT / 'a48-source-excerpts.txt').write_text('\n'.join(old_snap) + '\n')

callers = subprocess.run(['rg', '-n', 'synthetic_homotopy_separated|classical_sphere_separated', 'KIP126', 'Tests'],
                         cwd=ROOT, text=True, capture_output=True, check=True).stdout
(OUT / 'downstream-callers.txt').write_text(callers)

# This verifies only the scalar arithmetic used in the mathematical argument.
scalar_check = [((4 ** n) * 8) % 24 for n in range(17)]
result = {
    'worktree': str(ROOT), 'baseline_commit': BASE, 'migration_source': OLD,
    'git_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'session_baseline_hashes_all_match': all(v['matches_session_baseline'] for v in hashes.values()
                                            if 'matches_session_baseline' in v),
    'independent_reporter': '/root/separation_reporter',
    'independent_source_read_and_mathematical_derivation': True,
    'scalar_arithmetic_check_in_ZMod24': scalar_check,
    'scalar_arithmetic_check_passed': all(v == 8 for v in scalar_check),
    'lean_or_lake_executed': False,
    'formal_counterexample_proved': False,
    'evidence_level': 'complete mathematical argument for the intended actual ordinary/HF2 synthetic interpretation; conditional at pending Lean construction/recognition boundary',
    'limitations': [
        'The actual fixed categories, coefficients, nu, recovery, tower and source recognition remain pending.',
        'No project theorem computing actual ordinary pi_3 sphere was used as a checked Lean input.',
        'ModTwoCoefficients alone does not assert the endomorphism 2 id_HF2 vanishes.',
        'StableHomotopyCategory alone does not assert tensor additivity.',
        'Finite scalar arithmetic is not proof of a topological or formal counterexample.',
    ],
}
write_json('reproduction-result.json', result)
print(json.dumps(result, ensure_ascii=False, indent=2))
