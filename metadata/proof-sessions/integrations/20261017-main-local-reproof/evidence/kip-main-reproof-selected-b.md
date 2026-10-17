# Main selected-b reproof

Read repository AGENTS.md and supplied protocol. Production write scope is exactly:

- `KIP126/Main/Internal/Theta/OrderTwo.lean`
- `KIP126/Main/Internal/Theta/TodaExistence.lean`
- `KIP126/Main/SectionSeven/ThetaToda.lean`

No other production files, metadata, locks, tests, or shared build artifacts changed by this worker. Other workers' prior changes in these three files (notably the explicit private theta order-two argument) are retained.

Baseline and result hashes: `/tmp/kip-main-reproof-selected-b-hashes.json`.
Patch against task-start files: `/tmp/kip-main-reproof-selected-b.patch`.

## Actual construction

The false assertion that every integral `b : BiHom 62 70 S_0_0` has order two is removed. Its replacement only proves order two under an explicit private hypothesis that the realization of b is 2-primary. This is then genuinely constructed for a chosen lift, with no new public assumptions or direct obligations:

1. `model.sphereAlgebra.scalar p` is a `ZMod 2` module structure on actual classical E2. Therefore all actual E2 classes double to zero. Surjectivity of the infinite-cycle quotient and `SSData.infinity_projection_eq_of_page_projection_eq` give the same fact on actual E-infinity.
2. Through actual classical convergence, doubling any element in F_s moves it to F_(s+1). Iterating 34 times places `2^34 • α` in F_34 for every ordinary integral α in stem 62.
3. For s >= 34, the sourced sphere vanishing line gives E2(s,62+s)=0 because 62 < 2s-3. Infinite-page vanishing implies F_s = F_(s+1) on stem 62. Thus `2^34 • α` lies in every nonnegative Adams filtration level.
4. The corrected ordinary-sphere separation theorem gives a positive odd n annihilating `2^34 • α`. Commuting natural multiples gives `2^34 • (n • α) = 0`, so `n • α` is 2-primary. No finiteness assertion about the integral 62-stem is needed.
5. Begin with the existing actual permanent first-quotient lift b0 of atom.b. Choose the above odd n for `α = realizeSphere b0` and set `b = n • b0`. The first quotient is a ZMod 2 module, so odd n preserves its label exactly; realization is additive, so its realization is the constructed 2-primary class.
6. Apply the corrected `stem62_exponent_two` to this actual realization, obtaining R(2b)=0. The existing λh0=2 calculation and realization of λ being invertible give R(h0 b)=0 in bidegree (62,71). The independently repaired weight-71 realization-kernel lemma then gives λ(h0 b)=2b=0. This is the existing kernel argument specialized to an actual valid primary representative, with no circular dependence on the present b theorem.
7. `SectionSeven.synthetic_theta_b_toda` now uses this selected order-two lift before applying the genuine untruncated Toda bracket-existence construction. Nonzero detection still comes from the same first-quotient label and its existing nonzero proof.

The new existential helper is stronger than needed but valid: any *liftable* first-quotient class in this bidegree has an order-two representative after an odd adjustment. It does not assert every lift is order two.

## Shuffle repair and finite quotient scope

`tripleToda_right_order_two` directly derives b+b=0 from the actual Toda relation via `Toda.composable`. This supplies the shuffle's b order-two premise without using any arbitrary-b exponent assertion.

By coordinator instruction, both private theta shuffle wrappers return exactly

```lean
quotientClass 9 (lambdaMultiply 2 (sphereProduct syntheticH0 z)) =
  quotientClass 9 (lambdaMultiply 3 (sphereProduct eta (sphereProduct theta b)))
```

Their application to `theta_b_shuffle_from_low_degrees` drops only the obsolete untruncated eta-uniqueness parameter; its remaining arguments match the new finite-quotient worker signature. Main public declarations and specified objects are unchanged. Coordinator must integrate the matching `WeakRepresentative`/`NuTarget` consumer changes; this worker did not modify those owned files.

## Actual validation

All commands used the pinned toolchain through escalated `lake env lean`, writing logs and optional outputs only under `/tmp`.

- `/tmp/KipBSelectedArithmetic.lean`: **exit 0**. This contains the complete actual classical E-infinity, doubling-filtration, vanishing-tail, and odd-multiple-primary construction with ordinary public imports. It has no kernel parameter.
- `/tmp/KipBSelectedLocalTypecheck.lean`: **exit 0**. This contains the entire new OrderTwo mathematics, including first-quotient label preservation, primary realization transport, and the final λh0 argument. For isolation while another worker rebuilds the imported kernel module, the existing weight-71 kernel lemma is made one explicit local section parameter. This checks the local composition only and does **not** discharge that kernel lemma. No such parameter is added in production.
- `/tmp/KipTodaRightOrderTwo.lean`: **exit 0**. This independently checks actual bracket existence and the new `Toda.composable` right-order-two theorem, with ordinary public imports and no additional assumptions beyond each stated theorem's existing premises.
- Full production `OrderTwo.lean` compile attempted before these probes: **exit 1 at import**, because the concurrently changing `Choice/LambdaInjectivity.olean` had not yet been built. Log `/tmp/kip-main-selected-b-order-two.log`. This did not enter target typechecking and is not a mathematical failure.
- No new `sorry`, `axiom`, `False.elim`, or public declarations appear in the three source files.
- Full production chain compile and matching private consumer checks remain for coordinator after the downstream kernel and finite shuffle workers deliver their imports.

Logs: `/tmp/kip-b-arithmetic.log`, `/tmp/kip-b-local.log`, `/tmp/kip-toda-right-order-two.log`.

## Dependencies and responsibility

Retained sourced upstream dependencies include actual fixed classical/synthetic systems and convergence, `sphereAlgebra`, `sphereVanishing`, corrected `finite_map_separation` through `classical_sphere_separated`, corrected `stem62_exponent_two`, realization coordinates/additivity and λ comparison, `toda_lambda_h0`, the independent actual weight-71 realization-kernel construction, and existing permanent-lift/detection/computation interfaces. Their direct pending responsibilities remain upstream. This worker has not proved any fixed-model source recognition or removed those upstream holes.

The weight-71 kernel worker explicitly confirmed it preserves that helper's full type and reconstructs its proof via actual λ cofiber, finite quotient comparison, BHS Bockstein, and selected permanent lift, without using b order two or Toda existence. This dependency must be checked in the completed production build and trust audit; the local parameter probe alone is not that audit.

## Follow-up read-only audit of the actual repaired kernel sources

Read the complete production `Choice/LambdaInjectivity.lean` and `Theta/RealizationKernel.lean` after the kernel worker delivered its reconstruction. The unchanged callable `lambda_kills_realization_kernel_62_71` now has an actual proof chain:

- finite shifted first-quotient vanishing sends the F9 class to zero in the shifted finite quotient;
- the actual λ-cofiber supplies a preimage;
- the TR3 comparison with the specified LambdaRhoDeltaTriangle, corrected by the finite no-return argument, identifies its actual connecting map on sphere maps;
- the BHS Bockstein comparison yields d2=0 for its exact first-quotient label;
- the computation-derived no-late-differentials theorem in stem 63 and filtration <=6 makes this label permanent;
- the registered selected permanent lift kills the actual cofiber boundary;
- λ-power descent uses this actual kernel statement and the registered realization-kernel comparison.

There is no call to selected b order two, b Toda existence, or either theta shuffle in these upstream proofs. `RealizationKernel` imports `NoCrossing` and `Choice/LambdaInjectivity`; those routes do not import or call `Theta/OrderTwo`. The underlying source/lift interfaces are Literature/ProofTools upstream and cannot import Main. No target cycle or False elimination was found.

The chosen b is genuinely an existential witness in `synthetic_theta_b_toda`; no public fixed synthetic b object is replaced. The named `atom .b` is its fixed E2 label and remains literally unchanged. The construction gives equality of the full first-quotient label, then the existing sphere nonzero detection theorem supplies actual detection. The untruncated Toda bracket uses the actual constructed hb2 before any finite-quotient passage.

Coordinator is now running the shared production build of RealizationKernel, the three owned files, and the downstream consumers; at its request this worker did not start a redundant build.

Source snapshots reviewed:
- `KIP126/Main/Internal/Choice/LambdaInjectivity.lean`: SHA-256 `b81366348b59acc32aa35f203a231d522c13819421bcd74d59a8b7c3fd5b7813`.
- `KIP126/Main/Internal/Theta/RealizationKernel.lean`: SHA-256 `c1e39f6940fba0be3fc370214bdc40a6ab1b97f7deb15a9fd2429f1d5eebba17`.
