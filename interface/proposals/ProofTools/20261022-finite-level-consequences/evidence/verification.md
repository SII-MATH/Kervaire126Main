# Verification on 2026-10-22

The checks below ran in the existing working tree at base commit
`fa6c729fe2f1b251ef6ead8838a0fbbb0975f8aa`. They include the prior authorized
uncommitted work. No commit, push, upstream interface change, or dependency-lock
change was performed for these two consequences.

## Lean

- `lake build KIP126.ProofTools.FiniteLifting.LevelClassicalLift KIP126.ProofTools.FiniteLifting.CutoffDifferential`: exit 0, 3336 jobs.
- `lake build`: exit 0, 3721 jobs.
- `KIP126.ProofTools.InternalAudit`: 6064 declarations, one previously registered pending responsibility, no project axioms. The two new complete private theorems are explicit roots of its recursive no-local-proof-gap check.
- `lake env lean /tmp/FiniteLevelTheoremAudit.lean`: exit 0. The saved probe imports all five relevant module audits, prints the complete elaborated types, and traverses actual project proof dependencies.
- `lake env lean interface/proposals/ProofTools/20261022-finite-level-consequences/evidence/FiniteLevelConsequences.lean`: exit 0, no diagnostics. This is a candidate file only; the public module entry point and interface lock do not export these declarations yet.

The cutoff theorem has 861 ProofTools dependencies with no local gap and 52
existing upstream responsibilities (35 AdamsSynthetic, 2 E2Computation,
15 Literature). The realization theorem has 322 ProofTools dependencies with
no local gap and 46 existing upstream responsibilities (35 AdamsSynthetic,
11 Literature). All 52 distinct upstream responsibilities are present in
`interface/baselines/proof-obligations.json`; none is new. Both transitive
axiom sets include `sorryAx` from those upstream responsibilities, alongside
`propext`, `Classical.choice`, and `Quot.sound`.

Exact types and dependency lists are in
[finite-level-theorem-audit.json](finite-level-theorem-audit.json), with the
actual output in [finite-level-theorem-audit.log](finite-level-theorem-audit.log)
and the reproducible probe in [FiniteLevelTheoremAudit.lean](FiniteLevelTheoremAudit.lean).

## Repository And Blueprint

- `python3 scripts/check-source-inventory.py`: exit 0; 622 project files and 35 consumer/audit files covered.
- `.lake/blueprint-env/bin/python -m unittest discover -s Tests -p 'test_blueprint*.py'`: exit 0; 49 tests in 244.880 seconds.
- `git diff --check`: exit 0.

## Source Fingerprints

| File | SHA-256 |
| --- | --- |
| `KIP126/ProofTools/FiniteLifting/CutoffDifferential.lean` | `8d3dc5b12f76d58894c79f91fd13f0182d5b5c3905c89bd6a0a3d229cb23e338` |
| `KIP126/ProofTools/FiniteLifting/LevelSourceLift.lean` | `a087d450d23b760aa726dc07d79e4dca1499c4358a474635651d33561a36fd0c` |
| `KIP126/ProofTools/FiniteLifting/LevelClassicalLift.lean` | `9eff31c96c2d0ea4362b19beb32c15efd62daa7e1fa27d225f053fb7524bca54` |
| `evidence/FiniteLevelConsequences.lean` | `6eafd5db4ac3cfa415c906217a5bbb6bf8aa94407b845746eb620e2d4cdc7394` |

Before commit, the candidate's extra trailing blank line was removed. Its
original reviewed hash was `79ccd321cb1e2fe3a05788500081e6eaa49833256e23a5bc5e2b5f4b92ad5c62`;
it now matches the public module byte for byte.

The pre-existing meeting edit and dependency lock retain their start-of-turn
fingerprints:

- `meeting/2026-10-13.yaml`: `cc22e499b9d16edcfc6a95219f3a5cb378a9d86ffb007213d7019b1cddace3fc`.
- `lake-manifest.json`: `dff78efd5fbb68ae0f12683a80fdf373952838fc7fd31e1ff4ef100731202ceb`.

## Post-Approval Implementation

After the user's approval on 2026-10-22, the two reviewed wrappers were added
to `KIP126/ProofTools/FiniteLevelConsequences.lean`, exported through the
ordinary `KIP126.ProofTools` entry point, and bound to the complete Blueprint
conclusions `sem:ProofTools:ss-adams-soundness` (5.53) and
`sem:ProofTools:ss-classical-soundness` (5.56).

- `lake build KIP126.ProofTools`: exit 0, 3430 jobs.
- Public interface capture: 354 exports; complete trust capture: 25424 project declarations.
- Exact ProofTools interface-lock comparison: the two approved theorems and three Lean-generated proof constants were added. No existing row, type, universe parameter, axiom set, or export was removed or changed.
- `lake build`: exit 0, 3722 jobs. Public consumption, interface locks, architecture, and trust audits all passed.
- ProofTools internal audit: 6072 declarations, the one previously registered responsibility, and no project axioms. Both new public theorems and their complete private proofs are checked recursively for the absence of ProofTools-local proof gaps.
- Ordinary-import consumer checks expose the two public theorems and reject access to the three private implementation helpers.
- `python3 scripts/check-source-inventory.py`: exit 0; 623 project files and 35 consumer/audit files covered.
- `.lake/blueprint-env/bin/python -m unittest discover -s Tests -p 'test_blueprint*.py'`: exit 0; 49 tests in 238.674 seconds.
- `.lake/blueprint-env/bin/python scripts/interface-proposals.py validate`: exit 0; 29 reports.
- `git diff --check`: exit 0.

The transitive upstream responsibilities described above remain in place.
No new axiom, obligation, upstream interface change, or dependency-lock change
was introduced. The obligation baseline, meeting edit, and dependency lock
retain their start-of-turn fingerprints.

| File | SHA-256 after implementation |
| --- | --- |
| `KIP126/ProofTools/FiniteLevelConsequences.lean` | `6eafd5db4ac3cfa415c906217a5bbb6bf8aa94407b845746eb620e2d4cdc7394` |
| `interface/baselines/proof-tools-api.json` | `3f3954ebcef1eba9924f591b19124edd863bcb53a6224d44eb652aa992c91d00` |
| `interface/baselines/proof-obligations.json` | `895e790f0c0944b63f780fa38647ea332ac5b989f0718fe90726d0181f58ff38` |
