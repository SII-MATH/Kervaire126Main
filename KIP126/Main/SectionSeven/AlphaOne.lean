module

public import KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Computation.Hypotheses
public import Batteries.Data.String.Lemmas
public import KIP126.Def.ClassicalAdams.TowerNaturality.Proofs
public import Mathlib.CategoryTheory.Triangulated.Functor
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Def.Synthetic.Context.LambdaPowers.Proofs
public import KIP126.Main.AdamsSynthetic
public import KIP126.Main.SectionSeven.Lambda
import all KIP126.Main.SectionSeven.Lambda
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
import all KIP126.Main.SectionSeven.AlphaOne.Exhaustion
import all KIP126.Main.SectionSeven.AlphaOne.Filtration
import all KIP126.Main.SectionSeven.AlphaOne.HighFiltrationPermanence
import all KIP126.Main.SectionSeven.AlphaOne.Existence

@[expose] public section

/-! Filtration and representative calculations for Proposition 7.8 and
Lemma 7.14 (`lem:x_123_9`). The complete bases, products and differential
calculations refer to the same standard sphere as the literature hypotheses.
These lemmas derive the required homotopy relations from those inputs. -/
namespace KIP126.Main.SectionSeven

open private stem124_af13_exhaustion from KIP126.Main.SectionSeven.AlphaOne.Exhaustion
open private alpha_exists_from_finite_frames from KIP126.Main.SectionSeven.AlphaOne.Existence
open private alpha_h0_filtration_from_finite_window from KIP126.Main.SectionSeven.AlphaOne.Filtration

open private stem124_filtration_fourteen_fifteen_permanent_cycles from KIP126.Main.SectionSeven.AlphaOne.HighFiltrationPermanence

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

/-- Full AF13 exhaustion. The E2 group has four basis vectors; only the
permanent correction remains at infinity. Finite Reaches1000 uses V's
independent tail before it may supply the infinite representative. -/
theorem classical_stem124_af13_generated :
    ClassicalInfinityGenerated 13 137 eCorrection := by
  exact stem124_af13_exhaustion computationTheorems
    (KIP126.Computation.SphereAndCofiber.sphere_facts computation sphereVanishing)

-- Retain the named hypotheses in the statement of this theorem.

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
