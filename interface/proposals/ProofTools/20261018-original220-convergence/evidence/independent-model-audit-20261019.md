# Independent mathematical audit of the proposed 2.20 countermodel

Reviewer: `/root/convergence_reporter`; date: 2026-10-19. The reviewer did not discover or implement the candidate. This is a mathematical/source audit, not a Lean construction of `D : Model C Syn`. No production theorem, `sorry`, `False`, GL, MH, or Main contradiction is used as evidence.

## 1. Scope and objects

Use ordinary 2-local spectra `C=Sp_(2)`. Start with **non-hypercomplete** HF₂-synthetic spectra, and take its full subcategory of objects on which every odd integer acts invertibly. This is a stable smashing localization, with its localized tensor unit, not the unrelocalized unit of the larger category. The synthetic analogue preserves filtered colimits, so localization of `νS` at odd maps is `ν(S_(2))`. This is the unit of the restricted category. `ν(HF₂)` is already odd-local. Shifts, finite cofibers, and λ-localization preserve this subcategory. Pstrągowski's equivalence between all λ-invertible synthetic spectra and ordinary spectra restricts to this equivalence with **2-local** spectra. Using the full synthetic category and claiming its λ-invertibles are precisely 2-local spectra would be incorrect.

Set `M=H(Z_(2)) ⊕ H(Q[t])`, pointed through the first summand. `AuxiliaryData` requires maps of the indicated types, not source recognitions of η, ν, or tmf; set its two Hopf-labelled maps to zero. Its actual ν cofiber is `S_(2) ∨ Σ⁴S_(2)`. Every selected classical object is a finite sum/shift of `S_(2)`, `H(Z_(2))`, `H(Q[t])`. Its mod-2 homology is bounded below and finite in each degree. Its integral/rational homotopy need not be finitely generated. Thus this is admissible for the typed `AuxiliaryData`, but is deliberately **not** the intended named Standard auxiliary object.

No claim identifies this model with `Standard.model`, the fixed source realization, or AimPaper's complete category.

## 2. Complete field audit against System.lean

The following table covers every field of `ModelData` and the four additional fields of `Model`; the instance fields are covered first. “Mathematical” means supplied by the indicated actual categories/constructions and source results, not instantiated in Lean here.

| Field(s) | Independent check / construction | Status |
| --- | --- | --- |
| `StableHomotopyCategory`, `SyntheticCategory` | Stable homotopy categories of the stated stable enhancements, actual suspension/tensor/zero and distinguished triangles; coherent invertible bigraded spheres and actual λ. Odd localization uses its localized unit. | Mathematical, not Lean implemented. |
| Both `HasFunctorialCofiber` | Actual enhanced cofibers and induced triangle maps. The Lean record requests a triangle map for each commuting square and its two equations; it does not request an impossible strictly functorial cone construction in an arbitrary triangulated category. | Mathematical. |
| `coefficients` | HF₂ with actual π₀=F₂ and all other π zero, and coefficient unit specified by 1. | Mathematical. |
| `classical`, `family` | Actual functorial coefficient-unit Adams exact couples. All their selected objects/maps are actual objects/maps; no arbitrary relabelling of E∞ or filtration. | Mathematical. |
| `classicalTower`, `syntheticTower` | Actual iterated coefficient-unit fiber towers, stage 0 the object, layer `H⊗stage`, layer inclusion the same coefficient unit. Coherent layer and map choices come from the stable enhancement. | Mathematical; respects `layer_unit`. |
| `classicalSuspension` | Exactness of coefficient tensor identifies towers and layers after suspension, with the actual triangulated connecting sign as required by `Suspension.lean`. | Mathematical. |
| `nu` | Pstrągowski's ν restricted to `Sp_(2)`; additive, preserves finite sums/zero, sends localized sphere to localized synthetic unit, and `νΣ ≃ Σ^(1,1)ν`. | Mathematical. |
| `nuExactTriangle` | Pst Lemma 4.23, source label `fibre_sequences_that_are_short_exaft_sequences_on_homology_preserved_by_synthetic_analogue_construction`: requires **full** homology SES, including endpoint conditions. | Source checked. |
| `recovery` | Actual λ-localization, full λ-invertible subcategory, and its restricted equivalence with `Sp_(2)`; ν followed by localization recovers its given input. | Source checked; restriction argument above essential. |
| `exactness` | Stable localization is exact; invertible bigraded tensor shifts are additive/exact and commute with ordinary shifts. ν itself is not assumed exact on every triangle. | Mathematical. |
| `auxiliary` | Exactly the M and maps in §1, checked against each typed field of `Configuration.lean`. | Explicit. |
| `sphereAlgebra`, `standardClasses` | Actual classical mod-2 sphere Ext product/unit and its usual hᵢ. Typed fields do not impose additional nonvanishing, nor identify this model with `Standard`. | Mathematical. |
| `comparison` | BHS `thm:synth-ASS` in `SynRevAdams.tex:83–114`, with natural actual tower maps, gives classical E₂ times polynomial λ, including the map and λ equations. The theorem begins with arbitrary X; completeness is introduced separately later. | Source checked. |
| `quotients` | Actual finite cofibers of λⁿ, quotient functors and the ordinary finite Bockstein/octrahedral triangles. Same λ and same shifts, with n=0 cofiber zero. | Mathematical. |
| `normalizedMap` | Exponent is only 0 or 1. Exponent 0 uses νf. If target-stage-1 factorization exists, HF₂⊗f=0. The image of νf in `Cλ⊗νY` is zero: the source/target 0th truncations are the actual homology comodules, and maps between heart objects are their comodule maps. Exactness of mapping into the λ triangle gives the required lift. Moving its weight shift from target to source gives exactly the field's displayed equation. | Independently checked; also BHS `lemm:adams-fil1`. No uniqueness claim needed. |
| `classicalConvergence` | Actual canonical E∞→gr for the selected incomplete objects, transferred with the image-divisibility condition in §3. Rational summands have constant full filtration and zero gr. | Mathematical construction in §3. |
| `convergence` | Same construction for ν of selected classical objects and the synthetic sphere; all shifts reindex. Every object containing a positive λ quotient is covered inductively by §4. Includes every recursive `SyntheticObject` constructor. | Mathematical construction; not a Lean record. |
| `firstQuotient` | Pst `lemma:maps_from_synthetic_analogue_to_synthetic_analogue_tensor_ctau_compute_ext_groups_in_comodules`, around line 2612, with the preceding homology-comodule discussion around line 2594; equivalently BHS `lemm:ctauE2`. Exact source shift gives `(t-s,t+a)` as required. | Source checked; completeness not needed. |
| `comparisonCompatible.convergence_natural` | Canonical stage-lift, cofiber, projection diagrams give natural associated-grade maps for every actual map between selected synthetic objects. This does not require such maps to respect a chosen decomposition. `Standard/Background.lean` also contains a generic definition-level derivation of this field from canonical identifications; its statement agrees with this argument. | Mathematical; no use of Standard's unfinished constructors. |
| `comparisonCompatible.first_quotient` | Quotient ASS is concentrated on its first-quotient diagonal and detects the very Ext element under the actual inclusion. This is the collapse and actual inclusion calculation, not a freely chosen isomorphism; see BHS `Proof of thm:synthetic-Adams(2)–(4)`, first paragraphs. Incomplete→complete transfer changes neither Cλ nor the canonical lift's grade. | Source / representative checked. |
| `sphereDetectionCompatible` | Same first-quotient calculation on the actual localized unit. Sphere λ action is the actual tower operation; complete-sphere formulas transfer along the actual maps and agree on associated grades. | Mathematical. |
| `multiplicationCompatible` | Actual multiplicative coefficient towers and canonical associated grades identify the same E₂ product and actual sphere composition, including zero leading terms. No h₆² permanence theorem enters. | Mathematical. |
| `sphereProductCommutative` | Twist on any pair of bigraded spheres is a scalar in π₀₀νS_(2)=Z_(2). Realization is injective on this group and sends the twist to the ordinary sphere sign `(-1)^(mk)`. Thus there is no additional weight sign in the required equation. The integer exponent's `natAbs` does not change its parity. | Independently checked sign, not merely asserted symmetry. |

## 3. Correct completion-transfer argument

An arbitrary mod-2 equivalence with rational cofiber does **not** give an isomorphism of Adams associated grades. For example let `A=fiber(HZ_(2)→HQ)`, `B=HZ_(2)`, `R=HQ`. The map is a mod-2 equivalence, but its π₀-source is zero and π₀B has nonzero grade 0. Here the image in π₀R is `Z_(2)`, which is not 2-divisible. This example is a warning about the transfer lemma only; it is not the proposed full `Model`.

Here is the corrected lemma, reproved independently. Suppose `A→B→R` is a triangle, `H⊗R=0`, coefficient multiplication by 2 is zero, and for **every degree under consideration**

`I_m = im(π_m B → π_m R)` satisfies `2^s I_m = I_m` for every natural s.

Apply the coefficient-fiber functor s times. Each stage triangle has the same R, and stage projection induces identity on R. Since `2·id` factors through the first coefficient fiber, `2^s π_m B ⊆ F^sπ_m B`. Therefore the image of every stage in π_mR equals I_m. To lift a grade-s class of B to A, subtract a stage-(s+1) element with the same R-image, then lift at stage s. For injectivity, lift a stage-(s+1) B-element whose base projection is the image of the A-element; its R-image is zero and hence it lifts at stage s+1 in A. The remaining difference is in the connecting-image kernel of `π_mA→π_mB`; this kernel lies in every F^sA, by the stage triangles. This proves `gr^sπ_mA≅gr^sπ_mB` using actual lifts, and the canonical layer/projection equation is preserved. Divisibility of R alone would not suffice: it is I_m that must satisfy this condition.

For `A=S_(2)` or `HZ_(2)` and `B=S_2^∧` or `HZ₂`, respectively, the actual completion cofiber is `H(V)` with `V=Z₂/Z_(2)`. Completion is an isomorphism on the positive stems of the 2-local sphere (finite 2-primary groups), and both spectra are zero on negative stems. Multiplication by 2 on V is injective (if 2z is 2-local rational, so is z) and surjective. Thus V is rational in the 2-local category.

The completion triangle is a full mod-2 homology SES, so ν preserves it by the exactness lemma already checked. `CλνHV=0`, hence `νHV` is λ-invertible. Its π_(m,w) is V in stem m=0 and zero otherwise, with λ invertible. Its coefficient tensor is zero: 2 is invertible on the first factor and zero on νHF₂. Therefore its Adams tower is constant with full filtration, and its pages and associated grades are zero.

For complete B, BHS strong convergence and the actual h₀ tower give

`π_(0,w)νB = 2^max(w,0) Z₂`,
`F^sπ_(0,w)νB = 2^max(s,w,0) Z₂`,
`π_(-1,w)νB = 0`.

These formulas use no differential on stem 0 or -1: the classical stem-0 groups are generated by h₀ powers and negative stems vanish. The map to V is actual reduction after realization, since λ is injective on these stem-zero groups. Every `2^N Z₂→V` is onto: subtract the first N binary digits of an element of Z₂; this subtracts an integer lying in Z_(2). Hence the triangle LES gives **at every weight**, including the adjacent stem,

`π_(0,w)νA = 2^max(w,0) Z_(2)`, `π_(-1,w)νA=0`.

In all other stems the completion map is an isomorphism. The required image I_(m,w) is therefore V at m=0 and zero otherwise; it is uniquely 2-divisible in **each** degree. The corrected transfer lemma applies to every fixed weight and the actual same coefficient tower. It gives the canonical weak grade identifications and

`F^sπ_(0,w)νA = 2^max(s,w,0) Z_(2)`.

Classically the same proof gives `F^sπ₀A=2^max(s,0)Z_(2)`. Finite sums and the rational summand preserve the canonical equations. Integer classical shifts and arbitrary bigraded synthetic shifts reindex these equations, including weights ≤0 and filtration indices ≤0. There is no assertion that these incomplete filtrations are complete.

## 4. All finite nested quotients, and the actual ML hypotheses

The object closure is recursively finite; it does not include infinite cofibers, infinite towers as objects, or arbitrary infinite sums of its generators.

A positive λ quotient of νA is equivalent to the same quotient of νB because its rational completion cofiber is λ-invertible. Its rational summand similarly disappears. A zero-th quotient is zero. Thus after the first positive quotient, any further shifts and λ quotients are finite iterated cofibers of the complete-base objects and their shifts. Since νB is νHF₂-nilpotent complete (BHS `lemm:easy-e-compton`), and the complete subcategory is stable, all such finite iterates are νHF₂-nilpotent complete.

Completeness alone is not used as strong convergence. The following finite-input check supplies ML. Let `I=fiber(1→νHF₂)`; the actual canonical stage on W is `I^⊗s⊗W`, so stage construction and the layer `νHF₂⊗I^⊗s⊗W` commute with every finite cofiber and bigraded shift used here. On the unquotiented complete bases the stage description in BHS `SynRevAdams.tex:37–61` identifies these layer groups with classical coefficient-homology groups and polynomial λ copies. For each fixed stage/tridegree these groups are finite: the complete sphere and HZ₂ have bounded-below mod-2 homology finite in each degree; classical coefficient-fiber stages retain these properties inductively by the homology LES. At a fixed internal degree, convolution with the dual Steenrod algebra is a finite sum of finite groups. At a fixed weight a polynomial λ copy contributes at most one exponent.

The layer homotopy LES for each further finite quotient has only finitely many such terms in each specified tridegree. By induction every resulting E₁, hence E₂, group is finite. At fixed nonnegative Adams filtration s there are no incoming differentials once r>s; E_r then forms a descending chain of subgroups of a finite group, hence stabilizes. Negative s pages are zero. Consequently the actual page tower is ML and its `lim¹_r` vanishes in each tridegree. The analogous Boardman condition stated in BHS `thm:strong-conv` now applies to the already nilpotent-complete synthetic objects. This supplies canonical convergence for **every** finite nested quotient and all shifts. This argument does not infer a global uniform collapse page, nor finite-dimensionality from completeness alone.

## 5. Classical contradiction, with all local theorem premises

Choose `X=.sphere`, `Y=Z=.detector`, `f=0`, and the map of Eilenberg–Mac Lane spectra induced by

`g(z,p(t))=(0,z+t p(t))`.

It is an actual HZ-linear map. Constant coefficient zero implies z=0; then `t p=0` implies p=0. Thus g is injective in π₀. In other stems all homotopy groups of M vanish. Hence the theorem's exact `hexact` holds for every integer d: `a≫g=0 ↔ a=0 ↔ ∃b, b≫f=a`. No triangle or short exactness premise has been silently added.

At d=s=0, `F^nπ₀M=2^nZ_(2)⊕Q[t]` for n≥0. Therefore `gr⁰π₀M=F₂`. Let y be the inverse canonical E∞ image of `(1,0)` in this grade, and let a=(1,0). Then y≠0, and `a≫g=(0,1)` is in **every** filtration subgroup. The same a, not a sequence of differing representatives, witnesses `ClassicalExtension ... g ... 0 n y 0` for each n by the definition-level zero-grade criterion. Hence the exact `ClassicalPermanent` premise holds.

If the original conclusion held, its f-extension representative would be `b≫0=0`, which represents only the zero grade. Canonical convergence is a grade isomorphism, so this would force y=0. Contradiction. Allowing arbitrary a≤s and zero source labels does not repair this contradiction.

## 6. Evidence limits

The classical spectra construction, the corrected transfer lemma, the all-fields comparison with the actual source statements, and the finite nested-quotient ML argument have been checked mathematically here. No Lean term instantiates all of `Model`; no kernel-checked `¬∀D,...` or `¬... Standard.model` is delivered. The source-level coherence arguments and standard completion/Adams theory are mathematical inputs, not newly proved Lean lemmas. The exact finite rational computation in `local-checks-20261019.txt` checks only the displayed elementary witnesses and polynomial injectivity; it cannot certify these spectral-category constructions.

The result is a strengthened **spectra-level mathematical countermodel candidate with a complete field audit**, and an independently confirmed obstruction to proving the generic statement from weak associated-grade convergence by the proposed method. If policy requires a fully Lean-realized countermodel before declaring the generic public theorem false, that threshold has not been met. The report must not present it as a Lean refutation, a counterexample to Standard, or an error in AimPaper under its global 2-completeness hypotheses.
