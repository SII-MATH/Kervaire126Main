# Proposition 5.10: unresolved simultaneous division step

Baseline: `93fbf1215b16c9630198370c6ce3cbcff9eb4912`.
Source: `AimPaper/main.tex`, Proposition `prop:cross-f-Er`, lines 1515–1548.
This note records a proof gap in the available derivation. It is not a
counterexample for the fixed synthetic category or the actual normalized map.

The paper's proof passes from a strict extension for `fhat_(r-1)` whose source
is a lambda multiple to a strict extension for `fhat_(r-1-a)`. The required
step must synchronize both the source and its image: a lift of the original
source through lambda must be chosen whose image has the specified target
filtration. Existence of an arbitrary source lift does not assert this.

The registered code currently provides these relevant tools:

* `normalized_finite_source_division` in
  `GeneralizedLeibniz/CrossingFinite.lean:24` supplies a source lift.
* `model.quotients.natural(...).lambda_naturality` makes the square commute.
* `CrossingLabels.lambda_finite_label_nonzero` identifies survival after
  lambda with the paper's enlarged boundary exclusion.
* `short_finite_noCrossing_tower` in
  `GeneralizedMahowald/ShortSource.lean:536` proves one direction for
  `n <= e(f)+1`. In that range the divided target is already at its bottom
  possible filtration. The general target need not be at the bottom.

Here is an elementary filtered-group model showing that source lifting,
commutativity, and even strictness of both vertical maps do not by themselves
imply the synchronization step. All groups are over the integers.

Let `A' = A = Z`, with filtration equal to the whole group in degrees at most
1 and zero in degrees at least 2. Let `B' = Z × Z`, with filtration whole
in degrees at most 1, `{0} × Z` in degree 2, and zero in degrees at least 3.
Let `B = Z`, with filtration whole in degrees at most 2 and zero in degrees
at least 3. Define

```
lambda_A(a) = a,       lambda_B(b,c) = c,
f'(a) = (a,a),         f(a) = a.
```

The square commutes, all four maps preserve filtration, both lambda maps
are strict, and every source lifts. Nevertheless `f(1)` lies in filtration
2 and not 3, while the only lift of its source `1` has image `(1,1)`, which
does not lie in filtration 2. The smaller square's leading target in
filtration 1 is killed on the associated graded by `lambda_B`.

This also explains why the already proved short-length argument does not
generalize merely by replacing `1` with `a` and increasing the target length.
A genuine proof for the actual objects must supply further structure forcing
the compatible source correction; for example it would be enough to realize
the relevant target-kernel corrections as images of source-kernel corrections.
No such statement is assumed here, no interface is changed, and no public
substitute for the full Proposition 5.10 has been added.

By contrast, Proposition 4.16 has been completed in `KIP126/ProofTools/Paper/Crossing.lean`.
The absolute boundary has its own proved division/filtration equivalence,
`divided_boundary_filtration_iff`, which avoids this unresolved generic square
step.

Reference source hashes at task start:

* `GeneralizedLeibniz/CrossingDelta.lean`:
  `63d16bde2f9c2dfc781ace7d29c5bf204e6c130df5806ab01d157c2e7cb71090`.
* `GeneralizedMahowald/ShortSource.lean`:
  `a7723065f3d074ca46992e331eb69a5ef76d4921a8129bc9037536ed7d15941f`.

This evidence was independently reproduced by the session's counteraudit
worker. It remains abstract filtered-group evidence, without an identification
of these groups and maps with the fixed synthetic objects.
