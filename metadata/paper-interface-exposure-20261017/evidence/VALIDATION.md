# Crossing worker delivery

Baseline commit: `93fbf1215b16c9630198370c6ce3cbcff9eb4912`.

Completed: AimPaper Proposition 4.16, `prop:cross-dr-En`, in the full range
`2 <= page <= r`, where the paper's `n` is `page-1`.

New public declarations in `KIP126.ProofTools.Paper`:

* `DeltaHasCrossing`: an essential higher-source extension in the actual
  absolute-boundary ESS, with the original stem and weight fixed.
* `classical_crossing_iff_delta_crossing`: the complete two-way equivalence
  with the existing classical `HasCrossingOn` predicate.

All auxiliary statements remain private. The new reverse implication uses
actual quotient representatives and the proved absolute-boundary division
filtration equivalence. It does not assume the desired equivalence or use
either pending generalized Leibniz/Mahowald theorem.

Source SHA-256 of `../Crossing.lean`:
`edd7f76b80d66bef5075d00b964da8a9ec8924a630e89f259d38135f1ca0891d`.

Actual checks:

1. `lake env lean KIP126/ProofTools/Paper/Crossing.lean`: exit 0, no warnings.
2. Compiled that source to an isolated `/tmp/kip126-crossing-public-check/`
   output, without writing the shared project build cache.
3. An ordinary `import KIP126.ProofTools.Paper.Crossing` consumed the full
   theorem type and applied it at arbitrary valid parameters: exit 0.
4. That ordinary consumer checked an auxiliary declaration is unavailable.
5. A separate audit imported private implementation bodies, recursively
   visited 1,962 dependency constants, and found no ProofTools direct hole,
   synthetic sorry, or missing dependency. It identified 47 still-pending
   upstream declarations (34 AdamsSynthetic and 13 Literature), all already
   registered in `metadata/proof-obligations.json`; the exact list is in
   `transitive-upstream-obligations.json`.
6. `#print axioms` reported only `propext`, `Classical.choice`, `Quot.sound`,
   and inherited `sorryAx`. Thus the local proof is complete relative to the
   existing upstream interfaces; the inherited constructions and results are
   not claimed proved here.

The coordinated root task owns source-inventory registration, entry-point
exports, exact public API capture, tests, and the final `lake build`.

Uncompleted: Proposition 5.10. Its precise unresolved source/image division
step and the limitations of the abstract evidence are recorded in
`PROPOSITION-5-10-GAP.md`. No partial public result is substituted for it.
