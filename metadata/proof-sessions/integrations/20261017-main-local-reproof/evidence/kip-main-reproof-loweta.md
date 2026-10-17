# LowEta actual finite-quotient reproof

Assigned baseline: HEAD `2c703812db7edb830b995c53e9fe648747a66429` plus authorized worktree changes.
Baseline LowEta SHA-256: `ca9b43c619e80122da0f695e9e8f0c4baf3033c3718e5fd8266c1cd8ed4540c6`.
Protocol read: `/root/.agents/skills/kip-upstream-session/references/protocol.md`.
Exclusive production write: `KIP126/Main/Internal/LowEta.lean` only.

## Implemented true local results

1. `sphere_one_three_infinite_filtration (z : BiHom 1 3 S) : ∀ j : ℕ, FiltrationAtLeast model.syntheticTower j z`.
   The original E∞ calculation is valid and is now exported only as a private, intermediate all-filtration conclusion, without any use of universal untruncated separation.
2. `sphere_one_three_finite_quotient_zero (z : BiHom 1 3 S) (n : ℕ) : quotientClass n z = 0`.
   Maps actual all-filtration class along the actual cofiber inclusion using `model.convergentMap` / `map_preserves_filtration`, then uses the newly restricted `synthetic_homotopy_separated .sphere n` on exactly `XModLambdaN S n`.
3. `eta_finite_quotient_eq_of_first_quotient_eq (n : ℕ) (x y : BiHom 1 2 S) (h : quotientClass 1 x = quotientClass 1 y) : quotientClass n x = quotientClass n y`.
   Actual cofiber exactness (`AlphaOne.lambda_one_division_of_quotient_zero`, whose proof is only division through the λ cofiber followed by shift full faithfulness) gives `x-y = λb` for `b : BiHom 1 3 S`. Result 2 kills `b` in each finite quotient; λ multiplication is source precomposition, so this kills the actual difference in the same quotient.
4. `eta_source_iso_fixed_in_finite_quotient (n : ℕ) (eta : BiHom 1 2 S) (a : Smn 1 2 ≅ Smn 1 2) : quotientClass n (a.hom ≫ eta) = quotientClass n eta`.
   The first quotient is identified with the actual `(1,2)` E₂ group; the existing archive identifies that group with `Fin 1 →₀ ZMod 2`. An invertible source map preserves whether the quotient class vanishes, hence fixes its value. Result 3 transports this equality to every finite λ quotient. No nonzero hypothesis on eta is needed.

Existing private `low_eta_page_zero` and `low_eta_page_unique` retained unchanged.

## Removed private statements and mathematical limit

By root's explicit follow-up authorization, removed `sphere_one_three_zero`, `eta_first_quotient_injective`, and `eta_unique_from_low_degrees`. Their former derivation used universal untruncated separation, which the user approved replacing. No public Main interface, premise, source object, or declaration export was changed.

A proof of the former untruncated statements would need genuine ordinary low-degree input / comparison, such as π₁ ordinary sphere having no odd torsion, together with an applicable realization comparison. Those were not found as current public interfaces. All finite quotient images vanishing does not by itself prove the untruncated element zero; no completion object substitution was made.

Root and compose_interface were notified of all new names and complete types before consumer adaptation. Existing private consumers in AnyYError and Theta/TodaExistence are being adapted by their assigned writers. The actual use of uniqueness there is to erase source automorphisms in η actions; finite quotient action can use `quotientAlgebra_sphere_action` and result 4.

## Dependencies and checks

No new `sorry`, axiom, or tracked obligation introduced. Finite synthetic separation remains its existing upstream direct pending proof and is truthfully retained as a transitive dependency, together with existing fixed model, convergence, E∞ comparison, and archive/source identifications. This is an actual local derivation at these existing boundaries, not a claim that those upstream constructions are completed.

Successful actual checks:

- Fixed-toolchain `/root/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lake env lean --root=/tmp /tmp/LowEtaFiniteProbe.lean -o /tmp/LowEtaFiniteProbe.olean` completed exit 0 after the complete four-helper candidate.
- Fixed-toolchain `/root/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lake env lean KIP126/Main/Internal/LowEta.lean -o /tmp/LowEtaVerified.olean` completed exit 0 on the same production proofs. Later edits were explanatory comments only.
- `git diff --check -- KIP126/Main/Internal/LowEta.lean` passed.
- Source search finds only the restricted finite-quotient call to `synthetic_homotopy_separated` and no `sorry`/axiom in LowEta.

These commands used require_escalated because sandboxed Lake could not detect its installation. All Lean outputs were in `/tmp`; no Lake target build or shared output was written by this worker.

Current LowEta SHA-256: `bc959ea8d8f0ed1dd7aa36f96e5473a4264a1c6b612042d0045e8462a721b2e8`.

## Final additional consumer helper

At compose_interface's request, added the normal same-module import `KIP126.Literature.Standard.QuotientAlgebra` and proved:

```lean
eta_action_source_iso_fixed_in_finite_quotient
    (n : ℕ) (hn : 0 < n) (eta : BiHom 1 2 (S_0_0 : SyntheticSpectrum))
    {k l : ℤ} (x : BiHom k l (XModLambdaN (S_0_0 : SyntheticSpectrum) n))
    (a : Smn (Syn := SyntheticSpectrum) (1+k) (2+l) ≅ Smn (1+k) (2+l)) :
    a.hom ≫ sphereAction eta x = sphereAction eta x
```

The proof lowers `a` through the actual fully faithful bigraded shift; the resulting source automorphism fixes the finite quotient of eta by result 4. `quotientAlgebra_sphere_action` identifies the actual action with multiplication in that same quotient algebra, which makes the finite-quotient equality usable. No eta nonzero, realization injectivity, ordinary π₁, or untruncated separation assumption is used. The quotient-algebra comparison remains its already registered upstream pending dependency.

Final compilation (exit 0): fixed `lake env lean KIP126/Main/Internal/LowEta.lean -o /tmp/kip-shuffle-overlay/KIP126/Main/Internal/LowEta.olean`. This path was sent to compose_interface for isolated consumer verification. Final `git diff --check` passed.

Final LowEta SHA-256 superseding earlier value: `4944aaa62da6b331cc6af4655e8b4105ca5a9dee5610184500eaa181608b6bb4`.
