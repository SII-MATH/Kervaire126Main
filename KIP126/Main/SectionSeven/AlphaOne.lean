module

public import KIP126.Main.Computation.LinCoordinates.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Computation.Hypotheses
public import Batteries.Data.String.Lemmas
public import KIP126.Def.ClassicalAdams.TowerNaturality.Proofs
public import Mathlib.CategoryTheory.Triangulated.Functor
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Def.Synthetic.Context.LambdaPowers.Proofs
public import KIP126.Main.AdamsSynthetic
public import KIP126.Main.Computation.Lambda
public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.Synthetic.Context.Coherence.Proofs
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Proofs
public import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
public import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Proofs
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Order.Proofs
public import KIP126.Def.Algebra.NestedQuotient.Proofs
public import KIP126.Def.Synthetic.Detection.Proofs
public import KIP126.Def.SpectralSequence.Permanence.Proofs
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
import all KIP126.Main.SectionSeven.AlphaOne.LowFiltration
import all KIP126.Main.SectionSeven.AlphaOne.FiltrationTen
import all KIP126.Main.SectionSeven.AlphaOne.Exhaustion
import all KIP126.Main.SectionSeven.AlphaOne.ThetaSquareDetection
import all KIP126.Main.SectionSeven.AlphaOne.Filtration
import all KIP126.Main.SectionSeven.AlphaOne.HighFiltrationPermanence
import all KIP126.Main.SectionSeven.AlphaOne.Existence

@[expose] public section


/-! Filtration and representative calculations for Proposition 7.8 and
Lemma 7.14 (`lem:x_123_9`). The complete bases, products and differential
calculations refer to the same standard sphere as the literature hypotheses.
These lemmas derive the required homotopy relations from those inputs. -/
namespace KIP126.Main.SectionSeven

open private stem124_af10_exhaustion stem124_af13_exhaustion from KIP126.Main.SectionSeven.AlphaOne.Exhaustion
open private alpha_exists_from_finite_frames from KIP126.Main.SectionSeven.AlphaOne.Existence
open private alpha_h0_filtration_from_finite_window from KIP126.Main.SectionSeven.AlphaOne.Filtration
open private stem124_weight128_filtration_ten from KIP126.Main.SectionSeven.AlphaOne.FiltrationTen
open private stem124_finite_pages from KIP126.Main.SectionSeven.AlphaOne.LowFiltration
open private stem124_filtration_fourteen_fifteen_permanent_cycles from KIP126.Main.SectionSeven.AlphaOne.HighFiltrationPermanence
open private finite_last_nonzero theta_three_cases_from_frames from KIP126.Main.SectionSeven.AlphaOne.ThetaSquareDetection
open KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic KIP126.Main.AdamsSynthetic
noncomputable section

-- This local attribute also governed the public tail before the split.
attribute [local irreducible] KIP126.LinE2.homogeneousPart

local notation "D" => adamsComparison
local notation "M" => standardMilnorCooperations
local notation "L" => sphereClasses
local notation "I" => computationTheorems
local notation "η" => etaClass
local notation "h₀" => literatureTheorems.toda.h0

abbrev eV := (I).interpretation.sphere 9 132 KIP126.Computation.Near126.V
abbrev eCorrection := (I).interpretation.sphere 13 137 KIP126.Computation.Near126.correction

open KIP126.LinE2 KIP126.Computation.Near126 in
/-- The Q9 d3 actually used to eliminate the other AF13 error direction.
The weight131 target is nonzero on E3, not just an E2 label with exponent8. -/
theorem ninth_quotient_error_d3 :
    FiniteNonzeroDifferential D 9 3 13 137 16 139 6 8
      ((I).interpretation.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12)))
      ((I).interpretation.sphere 16 139 (mulAt dataH1 (atom .x_122_15_2))) := by
  exact finite_last_nonzero literatureTheorems.synthetic 9 3 6 (by decide) (by decide)
    13 137 _ _
    (KIP126.Computation.SphereAndCofiber.d3_h4_x_109_12 computation)

open KIP126.LinE2 KIP126.Computation.Near126 in
/-- Q11, weight130: both common E7 representatives and target nonzero
are required. BHS lifting of the classical equation alone is insufficient. -/
theorem eleventh_quotient_candidate_d7 :
    FiniteNonzeroDifferential D 11 7 11 134 18 140 4 10
      ((I).interpretation.sphere 11 134 d7Source)
      ((I).interpretation.sphere 18 140 (mulAt dataH1 (atom .x_121_17))) := by
  exact finite_last_nonzero literatureTheorems.synthetic 11 7 4 (by decide) (by decide)
    11 134 _ _
    (KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing).d7_source

open KIP126.LinE2 KIP126.Computation.Near126 in
/-- The other Q11 weight130 candidate supports a nonzero E3 differential.
Its target has the same degree as the d7 target but a different E2 label. -/
theorem eleventh_quotient_candidate_d3 :
    FiniteNonzeroDifferential D 11 3 15 138 18 140 8 10
      ((I).interpretation.sphere 15 138 (mulAt h0Sq (atom .x_123_13_2)))
      ((I).interpretation.sphere 18 140 (mulAt h0Sq (atom .x_122_16))) := by
  exact finite_last_nonzero literatureTheorems.synthetic 11 3 8 (by decide) (by decide)
    15 138 _ _
    (KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing).d3_h0Sq_x_123_13_2

set_option backward.isDefEq.respectTransparency false in
private theorem sphere_quotient_page_zero (q : ℕ) (hq : 0 < q)
    (r s t w : ℤ) (hr : 2 ≤ r) (hwindow : t < w ∨ (q : ℤ) ≤ t - w) :
    Subsingleton (((D).family.quotient (S_0_0 : KIP126.Def.standardSyntheticContext.Syn) q).Page
      r (s,t,w)) := by
  classical
  let Q := (D).quotientFunctoriality.functor q

  let e := (D).family.functor.mapIso (Q.mapIso (D).nu.unitIso)

  have hz := literatureTheorems.synthetic.finite_quotient_page_vanishing
    .sphere q hq r s t w hr hwindow

  let i := e.inv.pageMap r (s,t,w)

  let j := e.hom.pageMap r (s,t,w)

  have hij : i ≫ j = 𝟙 _ := by
    classical
    dsimp only [i, j]
    rw [← SpectralSequenceMorphism.pageMap_comp, e.inv_hom_id,
      SpectralSequenceMorphism.pageMap_id]

  have hi : Function.Injective i := by
    classical
    intro x y hxy
    have hh := congrArg j hxy
    simpa only [← CategoryTheory.comp_apply, hij, ModuleCat.id_apply] using hh

  have hsource : Subsingleton ((KIP126.SpectralSequence.Page
      ((D).family.functor.obj (XModLambdaN ((D).nu.functor.obj SphereSpectrum) q))
      r (s,t,w)) : ModuleCat ℤ) := by
    classical
    simpa only [KIP126.SpectralSequence.Page, (D).family.firstPage,
      SyntheticAdamsFamily.nuQuotient, SyntheticAdamsFamily.quotient,
      SyntheticAdamsFamily.obj, SyntheticAdamsSS.Page, ClassicalObject.obj] using hz

  have hz' : Subsingleton ((KIP126.SpectralSequence.Page
      ((D).family.functor.obj (XModLambdaN (S_0_0 : KIP126.Def.standardSyntheticContext.Syn) q))
      r (s,t,w)) : ModuleCat ℤ) := ⟨fun x y => hi (hsource.elim _ _)⟩

  simpa only [KIP126.SpectralSequence.Page, (D).family.firstPage,
      SyntheticAdamsFamily.nuQuotient, SyntheticAdamsFamily.quotient,
      SyntheticAdamsFamily.obj, SyntheticAdamsSS.Page, ClassicalObject.obj] using hz'

/-- In Q9 both preceding targets have exponent10, so this WHOLE component
vanishes on every finite page. Transport of the BHS nu(S) statement uses
the same unit isomorphism and actual quotient functor. -/
theorem ninth_quotient_candidate_target_zero (r : ℤ) (hr : 2 ≤ r) :
    Subsingleton (((D).family.quotient (S_0_0 : KIP126.Def.standardSyntheticContext.Syn) 9).Page
      r (18,140,130)) := by
  exact sphere_quotient_page_zero 9 (by decide) r 18 140 130 hr
    (Or.inr (by norm_num))

/-- The actual rho page map kills these Q11 targets in Q9. This records
the map used in Lemma x1239, rather than only comparing two dimensions. -/
theorem rho_to_ninth_kills_candidate_target (r : ℤ) (hr : 2 ≤ r)
    (y : ((D).family.quotient (S_0_0 : KIP126.Def.standardSyntheticContext.Syn) 11).Page
      r (18,140,130)) :
    familyPageMap (D).family ((D).quotientTower S_0_0 |>.rho 9 11 (by decide))
      r (18,140,130) y = 0 := by
  exact (ninth_quotient_candidate_target_zero r hr).elim _ _

/-- `prop:possible_h_6_sq`: complete stem124 staircase reconstruction,
including the negative-filtration half-plane, before passing to homotopy.
This is E-infinity vanishing, not a false E2 vanishing assertion. -/
theorem classical_stem124_einfty_below_ten (s : ℤ) (hs : s < 10) :
    Subsingleton ((adamsTowerInternalSpectralSequence standardFoundation.hf2.unit
      SphereSpectrum).ssData (s,s+124)).eInfty := by
  set_option backward.isDefEq.respectTransparency false in
  set_option maxRecDepth 10000 in
    let E := adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum
    have collapse (r : ℤ) (hp : Subsingleton (E.Page r (s,s+124))) :
        Subsingleton ((E.ssData (s,s+124)).eInfty) := by
      let A := E.ssData (s,s+124)
      haveI : Epi (A.pageπ ⊤) := inferInstanceAs (Epi (CategoryTheory.Limits.cokernel.π _))
      refine ⟨fun x y => ?_⟩
      obtain ⟨x,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance x
      obtain ⟨y,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance y
      exact A.infinity_projection_eq_of_page_projection_eq ↑(r-E.r₀).toNat x y (hp.elim _ _)
    by_cases hneg : s < 0
    · exact collapse 2 (adamsTowerInternal_page_subsingleton_of_negative
        standardFoundation.hf2.unit SphereSpectrum 2 s (s+124) hneg)
    have hs0 : 0 ≤ s := by omega
    by_cases hsmall : s ≤ 5
    · have hd : (⟨.sphere,s.toNat,(s+124).toNat,[]⟩ : KIP126.Computation.SphereAndCofiber.Raw.Degree) ∈ KIP126.Computation.SphereAndCofiber.Raw.degrees := by
        interval_cases s <;> simp [KIP126.Computation.SphereAndCofiber.Raw.degrees]
      obtain ⟨e,_⟩ := computationTheorems.basis _ hd
      change KIP126.Computation.SphereAndCofiber.Page adamsComparison .sphere s.toNat (s+124).toNat ≃ₗ[ℤ] (Fin 0 →₀ KIP126.Algebra.F2) at e
      have he : Subsingleton (KIP126.Computation.SphereAndCofiber.Page adamsComparison .sphere s.toNat (s+124).toNat) := e.injective.subsingleton
      apply collapse 2
      simpa only [KIP126.Computation.SphereAndCofiber.Page,KIP126.Computation.SphereAndCofiber.sequence,KIP126.Computation.SphereAndCofiber.object,E,standardFoundation,
      KIP126.AdamsSynthetic.Standard.classicalContext, KIP126.HF2AdamsContext.foundation, KIP126.Foundation.Mod2StableHomotopyContext.toStandard,Int.toNat_of_nonneg hs0,
        Int.toNat_of_nonneg (by omega : 0 ≤ s+124)] using he
    have hfinite := stem124_finite_pages computationTheorems
    change Subsingleton (E.Page 6 (6,130)) ∧ Subsingleton (E.Page 6 (7,131)) ∧
      Subsingleton (E.Page 3 (8,132)) ∧ Subsingleton (E.Page 4 (9,133)) at hfinite
    interval_cases s
    · exact collapse 6 hfinite.1
    · exact collapse 6 hfinite.2.1
    · exact collapse 3 hfinite.2.2.1
    · exact collapse 4 hfinite.2.2.2

/-- Full AF10 exhaustion in `prop:possible_h_6_sq`: incoming d2/d4,
the remaining outgoing d5, and U's nonzero permanence are all needed. -/
theorem classical_stem124_af10_generated :
    ClassicalInfinityGenerated 10 134 ((L).U M) := by
  have h := stem124_af10_exhaustion computationTheorems sphereVanishing
  rw [(KIP126.Computation.SphereAndCofiber.distinguished_expression_comparisons computationTheorems).2.1] at h
  exact h

/-- Full AF13 exhaustion. The E2 group has four basis vectors; only the
permanent correction remains at infinity. Finite Reaches1000 uses V's
independent tail before it may supply the infinite representative. -/
theorem classical_stem124_af13_generated :
    ClassicalInfinityGenerated 13 137 eCorrection := by
  exact stem124_af13_exhaustion computationTheorems
    (KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing)

-- Retain the named hypotheses in the statement of this theorem.
set_option linter.unusedVariables false in
/-- The filtration bound in Proposition 7.8 combines classical vanishing
with BHS boundary stabilization at weight128. The remaining incoming sources
vanish, excluding synthetic lambda-torsion in these lower filtrations. -/
theorem theta5_square_filtration_ten
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn))
    (htheta : ThetaChoice M (D).toAdamsComparisonData theta) :
    FiltrationAtLeast (nuCoefficientUnit standardFoundation.hf2.unit (D).nu) 10
      (sphereProduct theta theta) := by
  exact stem124_weight128_filtration_ten literatureTheorems.synthetic I
    classical_stem124_einfty_below_ten (sphereProduct theta theta)

/-- The three exhaustive branches in Proposition 7.8, retaining a real
lambda preimage in the third branch and nonzero leading detection in the
first two. This does not assume which branch actually occurs. -/
theorem theta5_square_three_cases
    (theta : BiHom 62 64 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn))
    (htheta : ThetaChoice M (D).toAdamsComparisonData theta) :
    Theta5SquareNonzeroDetectionAt M (D).toAdamsComparisonData L theta ∨
      SphereDetected D 13 137 9 eCorrection (sphereProduct theta theta) ∨
      ∃ a : BiHom 124 138 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn),
        lambdaMultiply 10 a = sphereProduct theta theta := by
  have h := theta_three_cases_from_frames computationTheorems literatureTheorems.synthetic
    ((L).U M) eCorrection classical_stem124_af10_generated classical_stem124_af13_generated
    (KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing).e5_stem124_af11
    (KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing).e4_stem124_af12
    (sphereProduct theta theta) (theta5_square_filtration_ten theta htheta)
  exact h

/-- At weight130 and stem123 the BHS finite-quotient window for Q9 is
7<=s<=15. Every graded piece at s>=16 vanishes. Actual separatedness
then kills the filtration, without asserting lambda^9 acts as zero on Q9. -/
theorem ninth_quotient_stem123_weight130_filtration16_zero
    (a : BiHom 123 130 (XModLambdaN (S_0_0 : KIP126.Def.standardSyntheticContext.Syn) 9))
    (ha : FiltrationAtLeast (nuCoefficientUnit standardFoundation.hf2.unit (D).nu) 16 a) :
    a = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    apply ((D).quotientConvergence 9 (by decide)).eq_zero_of_eInfty_isZero_ge
      16 123 130 ((D).homotopySeparated (.quotient 9 .sphere) 123 130) ?_ a ha
    intro j hj
    let E := (((D).family.quotient (S_0_0 : KIP126.Def.standardSyntheticContext.Syn) 9).sequence.ssData
      (j, 123+j, 130))
    have hzero : Subsingleton (E.page 0) :=
      sphere_quotient_page_zero 9 (by decide) 2 j (123+j) 130 (by decide)
        (Or.inr (by omega))
    apply ModuleCat.isZero_iff_subsingleton.mpr
    refine ⟨fun x y => ?_⟩
    haveI : Epi (E.pageπ ⊤) := inferInstanceAs
      (Epi (CategoryTheory.Limits.cokernel.π _))
    obtain ⟨x', rfl⟩ := (ModuleCat.epi_iff_surjective (E.pageπ ⊤)).mp inferInstance x
    obtain ⟨y', rfl⟩ := (ModuleCat.epi_iff_surjective (E.pageπ ⊤)).mp inferInstance y
    exact E.infinity_projection_eq_of_page_projection_eq 0 x' y' (hzero.elim _ _)

/-- The calculation is performed in Q11: its two weight130 candidates
support the nonzero d7(lambda^4 d7Source) and d3(lambda^8 h0^2 x123,13,2).
Those targets disappear in Q9, so doing the calculation there first would
lose the needed exclusion. All representatives with this detector qualify. -/
theorem alpha_one_h0_filtration_seventeen
    (a : BiHom 123 132 (XModLambdaN (S_0_0 : KIP126.Def.standardSyntheticContext.Syn) 11))
    (ha : FiniteDetected D 11 (by decide) 9 132 0 eV a) :
    FiltrationAtLeast (nuCoefficientUnit standardFoundation.hf2.unit (D).nu) 17
      (lambdaMultiply 3 (sphereAction h₀ a)) := by
  exact alpha_h0_filtration_from_finite_window computationTheorems literatureTheorems.synthetic
    literature.sources.sourceComparisons.algebra literature.sources.sourceComparisons.algebraDetectionCompatibility h₀ eV a ha

/-- Lemma 7.14 (`lem:x_123_9`): an α₁ representative in S⁰,⁰/λ¹¹ whose
image in S⁰,⁰/λ⁹ has the required η- and h₀-relations. The proof includes
the nonzero quotient d₃ on λ⁶h₄x₁₀₉,₁₂, the error-filtration calculation
and preservation of filtration under the quotient map. -/
theorem lemma_7_14_alpha_one_exists :
    ∃ a11 : BiHom 123 132 (XModLambdaN (S_0_0 : KIP126.Def.standardSyntheticContext.Syn) 11),
      AlphaOneProperties D η h₀ ((L).U M) eV a11 := by
  obtain ⟨hp14,hp15⟩ := stem124_filtration_fourteen_fifteen_permanent_cycles computation sphereVanishing
  have h := alpha_exists_from_finite_frames computationTheorems literatureTheorems.synthetic
    (KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing)
    literature.sources.sourceComparisons.algebra literature.sources.sourceComparisons.algebraDetectionCompatibility
    etaClass literatureTheorems.classical.hopf.1 literatureTheorems.toda.h0
    alpha_one_h0_filtration_seventeen
    ninth_quotient_stem123_weight130_filtration16_zero hp14 hp15
  rw [(KIP126.Computation.SphereAndCofiber.distinguished_expression_comparisons computationTheorems).2.1] at h
  exact h

end
end KIP126.Main.SectionSeven
