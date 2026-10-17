# Independent audit of λ injectivity and θ realization-kernel descent

Verdict: no mathematical interface mismatch or new Main proof gap found in the audited local derivations. This is a proof review relative to the existing registered upstream interfaces, not a claim that their pending constructions are completed.

Read-only production review; no production file or shared Lake output was written by this audit.

Audited snapshots:

- `KIP126/Main/Internal/Choice/LambdaInjectivity.lean`: SHA-256 `b81366348b59acc32aa35f203a231d522c13819421bcd74d59a8b7c3fd5b7813`.
- `/tmp/kip-theta-realization-full.lean` and production `KIP126/Main/Internal/Theta/RealizationKernel.lean`: identical at review end, SHA-256 `c1e39f6940fba0be3fc370214bdc40a6ab1b97f7deb15a9fd2429f1d5eebba17`.

## Actual cofiber kernel, degrees, and common representatives

`nu_lambda_injective_from_source` uses the actual λ cofiber triangle on `νX`. Its kernel source is in `BiHom (m+1) (wt-1) (CλνX)`, so the exact classical first-quotient bidegree is `(wt-m-2, wt-1)`. The given `NoOutgoingAt` condition includes every differential on every page from 2 onward at that exact source. `isPermanentCycle_of_reachesPage` starts with the same E₂ element and produces one common Z∞ representative; it does not infer nonzero survival or require the class not to be a boundary. `selected_permanent_lift` is applied to precisely that same label.

The `nuZero` shift is removed with the actual shift-zero isomorphism and functorial quotient maps, not by replacing the target. Each actual Cλ class is lifted through the actual inclusion. Cofiber exactness then makes its connecting map zero. The final inference uses faithfulness of the shift functor and legitimate cancellation of sphere isomorphisms. No associated-graded injectivity is promoted to homotopy injectivity on an untruncated object.

## Actual cofiber δ versus the tower δ

The tower triangle δ is not assumed equal to the chosen cofiber boundary. `lambda_first_quotient_delta_evaluation` constructs a TR3 comparison from the actual λ^i cofiber triangle to the actual `LambdaRhoDeltaTriangle`. TR3 gives an endomorphism `c` on the quotient and the correct δ square. Its restriction along the actual inclusion equals the identity restriction by `lambda_quotient` and `rho_quotient`.

The proof then establishes `a ≫ c = a` for every actual bigraded sphere class `a`. The difference from identity factors through the actual cofiber boundary by triangle exactness. `lambda_boundary_no_return` kills this correction after a sphere test: the source `Σ^(1,-q)νX` in bidegree `(m,w)` has filtration at least `L = w-m+1+q`, while `Cλ^qνX` has no associated graded in that range. The source E∞ vanishing is used only over the finite interval needed to reach `L`; if `L≤0`, stage-zero filtration and antitonicity suffice. The final zero conclusion is on the actual finite quotient.

This argument justifies the required equality on the tested homotopy element; it never claims the TR3 comparison is categorically the identity or silently chooses a canonical δ. The `nuZero` version is transported using the actual quotient tower naturality and shift-zero isomorphism.

## Finite separation boundary

`lambda_shifted_finite_high_filtration_zero` transports actual filtration levels through `essShift` and its `FilteredPieceIso`, then applies `finite_high_filtration_zero` to the unshifted, actual `XModLambdaN (νX) q`. The latter uses the revised `synthetic_homotopy_separated (.nu X) q` on exactly that quotient, together with the existing finite E∞ window. No universal untruncated separation, classical-sphere zero separation, or change to a completion object is used.

For the θ kernel, projecting an F9 class `a : π_(62,w)(Σ^(0,-1)νS)` lands in `Σ^(0,-1)CλνS`. The unshifted weight is `w+1`. The finite-window inequality is exactly `1 ≤ 62+9-(w+1)`, valid for `w≤69`. Thus the actual projected class is zero; the proof does not select an arbitrary cofiber lift and assume it has F9.

## Bockstein d₂ and θ descent

For `s=w-63,t=w`, actual λ-kernel exactness constructs `b'` in the first quotient with actual boundary the suspension of `a`. The finite-projection zero above makes its further actual cofiber projection zero. The audited TR3 comparison transports that to the specified tower δ on the same element `b₀` after the shift-zero change.

The first-quotient isomorphism chooses `x` with `firstLabel x=b₀`. `bhs_bockstein` is specialized to q=1. Its existential representative is forced equal to `b₀` by the exact `rho_id` law; hence the computed zero Bockstein is genuinely the d₂ of this same `x`, not of an unrelated representative. The HasDifferential page-two equality is cancelled through its actual grading transport to obtain `d₂ x=0`.

The source is `(w-63,w)`, stem 63 with filtration `w-63≤6`. `actual_stem63_no_late` supplies all outgoing maps for every r≥3, and the separate d₂ computation gives reachability to page 3. `route_permanent_of_d2_and_no_late` therefore constructs a common permanent representative. Its actual selected lift kills the original cofiber boundary, hence the original λ-kernel element.

Finally `selected_realization_kernel` supplies a finite λ-torsion exponent. The descent constructs each intermediate element explicitly from a shifted copy of the original relative-weight-71 class, giving F9 via `shifted_weight71_filtration9`, and postcomposes with the actual restriction source map. For n≥1, its weight `71-(n+1)≤69` meets the just-proved kernel bound. This decreases the annihilating exponent to 1. The k=0 and k=1 base cases are handled separately. There is no assertion that finite separation alone kills an arbitrary infinitely filtered untruncated λ-torsion element.

## Actual checks and dependency evidence

Independent full candidate plus dependency audit compiled exit 0 using:

`/root/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lake env bash -c 'export LEAN_PATH="/tmp/kip-main-lambda-olean:$LEAN_PATH"; exec lean --root=/tmp /tmp/kip-main-lambda-independent-audit.lean -o /tmp/kip-main-lambda-independent-audit.olean'`

Outputs only in `/tmp`. The overlay contains the worker's independently emitted current LambdaInjectivity olean, with shared upstream cache read through symlinks. This audit explicitly imports all cited upper proof modules to avoid mistaking hidden opaque proof values for dependency-free results.

Evidence:

- `/tmp/kip-main-lambda-independent-audit.lean`: exact independently compiled candidate plus dependency walker.
- `/tmp/kip-main-lambda-independent-audit.log`: exit-0 log, one existing stylistic unnecessarySeqFocus warning, and capture completion.
- `/tmp/kip-main-lambda-independent-deps.json`: actual reachable project constants and direct pending project declarations for three reviewed roots.

The dependency walker found:

| Root | Reachable project constants | Reachable direct pending project declarations | Direct pending Main declarations |
| --- | ---: | ---: | ---: |
| `nu_lambda_injective_from_source` | 322 | 25 | 0 |
| `lambda_first_quotient_delta_evaluation` | 376 | 29 | 0 |
| `lambda_kills_realization_kernel_62_71` | 687 | 44 | 0 |

The first root does not depend on synthetic separation. The δ comparison and final θ result depend on the revised finite-quotient synthetic separation. The final result also reaches the existing pending `eInfinity_finite`, `eInfinity_nu`, `bhs_bockstein`, `selected_permanent_lift`, `selected_realization_kernel`, and sphere vanishing comparisons, plus fixed model / shift / computation constructions. No reached `classical_sphere_separated` or `selected_filtration_lambda` was found. These existing upstream responsibilities are retained, not discharged or moved into Main.

The reviewed direction is Main local cofiber constructions → ProofTools finite-window facts → AdamsSynthetic/Literature interfaces. The actual cofiber/TR3 proof does not consume the θ target or a theorem downstream of it. Source inspection and the compiled root closures revealed no new local pending responsibility or target cycle. Full repository build and frozen-interface/trust inventory checks remain the coordinator's separate verification task.
