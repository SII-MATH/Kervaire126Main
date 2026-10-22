module

import KIP126.AdamsSynthetic.Standard.Filtration

/-! Actual HF₂ homology short exactness of the rotated selected cofiber
triangle. Positive normalization is converted to zero on the same HF₂
homology through the registered filtration comparison. These lemmas retain
the actual arrows Y → Z → ΣX; they do not construct comodules or identify
the separate Ext connecting homomorphism. -/

@[expose] section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace KIP126.ProofTools.Internal.ExtBoundaryComparison.HomologySES

private theorem shifted_zero_on_spheres
    {A B : KIP126.AdamsSynthetic.Standard.Spectrum} (f : A ⟶ B)
    (hf : ∀ (n : ℤ) (a : HomotopyGroup n A), a ≫ f = 0)
    (n : ℤ)
    (x : HomotopyGroup n ((shiftFunctor KIP126.AdamsSynthetic.Standard.Spectrum (1 : ℤ)).obj A)) :
    x ≫ (shiftFunctor KIP126.AdamsSynthetic.Standard.Spectrum (1 : ℤ)).map f = 0 := by
  let F := shiftFunctor KIP126.AdamsSynthetic.Standard.Spectrum (1 : ℤ)
  let e := (shiftFunctorAdd' KIP126.AdamsSynthetic.Standard.Spectrum
    (n - 1) 1 n (by omega)).app SphereSpectrum
  let a : HomotopyGroup (n - 1) A := F.preimage (e.inv ≫ x)
  have ha : F.map a = e.inv ≫ x := F.map_preimage _
  apply (cancel_epi e.inv).mp
  rw [comp_zero]
  calc
    e.inv ≫ (x ≫ F.map f) = F.map a ≫ F.map f := by rw [ha, Category.assoc]
    _ = F.map (a ≫ f) := (F.map_comp a f).symm
    _ = 0 := by rw [hf (n - 1) a, Functor.map_zero]

open KIP126.AdamsSynthetic.Standard

private def homologyTriangle (T : HoCofiberSequence (C := Spectrum)) : Triangle Spectrum :=
  Triangle.mk (coefficients.object ◁ T.f) (coefficients.object ◁ T.g)
    (coefficients.object ◁ T.h ≫ (homologyShift T.X).hom)

private theorem homologyTriangle_distinguished
    (T : HoCofiberSequence (C := Spectrum)) :
    homologyTriangle T ∈ distTriang Spectrum := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  letI := closedBackground.tensorExact coefficients.object
  let F := tensorRight coefficients.object
  refine isomorphic_distinguished _ (F.map_distinguished _ T.distinguished) _ ?_
  refine Triangle.isoMk _ _ (β_ coefficients.object T.X)
    (β_ coefficients.object T.Y) (β_ coefficients.object T.Z) ?_ ?_ ?_
  · exact BraidedCategory.braiding_naturality_right _ T.f
  · exact BraidedCategory.braiding_naturality_right _ T.g
  · change (coefficients.object ◁ T.h ≫
        ((β_ coefficients.object (T.X⟦(1 : ℤ)⟧)).hom ≫
          ((tensorRight coefficients.object).commShiftIso (1 : ℤ)).hom.app T.X ≫
          (shiftFunctor Spectrum (1 : ℤ)).map (β_ coefficients.object T.X).inv)) ≫
        (shiftFunctor Spectrum (1 : ℤ)).map (β_ coefficients.object T.X).hom =
      (β_ coefficients.object T.Z).hom ≫
        (T.h ▷ coefficients.object ≫
          ((tensorRight coefficients.object).commShiftIso (1 : ℤ)).hom.app T.X)
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      BraidedCategory.braiding_naturality_right_assoc]
    rw [(shiftFunctor Spectrum (1 : ℤ)).map_id ((tensorRight coefficients.object).obj T.X)]
    exact congrArg (fun k => (β_ coefficients.object T.Z).hom ≫
      T.h ▷ coefficients.object ≫ k)
      (Category.comp_id (((tensorRight coefficients.object).commShiftIso (1 : ℤ)).hom.app T.X))

private theorem rotated_homology_short_exact_of_zero
    (T : HoCofiberSequence (C := Spectrum))
    (hf : ZeroOnModTwoHomology coefficients T.f) :
    HomologyShortExact coefficients (Triangle.mk T.f T.g T.h).rotate := by
  let U := homologyTriangle T
  have hU : U ∈ distTriang Spectrum := homologyTriangle_distinguished T
  have hzero : ∀ (n : ℤ) (x : HomotopyGroup n U.obj₁), x ≫ U.mor₁ = 0 := hf
  intro n
  constructor
  · intro a b hab
    change a ≫ U.mor₂ = b ≫ U.mor₂ at hab
    have hz : (a - b) ≫ U.mor₂ = 0 := by
      rw [Preadditive.sub_comp, hab, sub_self]
    obtain ⟨u, hu⟩ := U.coyoneda_exact₂ hU (a - b) hz
    apply sub_eq_zero.mp
    rw [hu, hzero n u]
  constructor
  · intro z
    change z ≫ (coefficients.object ◁ T.h) = 0 ↔
      ∃ y, y ≫ (coefficients.object ◁ T.g) = z
    constructor
    · intro hz
      have hz' : z ≫ U.mor₃ = 0 := by
        change z ≫ (coefficients.object ◁ T.h ≫ (homologyShift T.X).hom) = 0
        rw [← Category.assoc, hz, zero_comp]
      obtain ⟨y, hy⟩ := U.coyoneda_exact₃ hU z hz'
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, rfl⟩
      apply (cancel_mono (homologyShift T.X).hom).mp
      rw [Category.assoc]
      change (y ≫ U.mor₂) ≫ U.mor₃ = 0 ≫ (homologyShift T.X).hom
      rw [Category.assoc, comp_distTriang_mor_zero₂₃ U hU, comp_zero, zero_comp]
  · intro x
    let x' : HomotopyGroup n U.rotate.obj₃ := x ≫ (homologyShift T.X).hom
    have hx : x' ≫ U.rotate.mor₃ = 0 := by
      change x' ≫ (-((shiftFunctor Spectrum (1 : ℤ)).map U.mor₁)) = 0
      rw [Preadditive.comp_neg, shifted_zero_on_spheres U.mor₁ hzero n x', neg_zero]
    obtain ⟨z, hz⟩ := U.rotate.coyoneda_exact₃ (rot_of_distTriang U hU) x' hx
    refine ⟨z, ?_⟩
    apply (cancel_mono (homologyShift T.X).hom).mp
    change (z ≫ (coefficients.object ◁ T.h)) ≫ (homologyShift T.X).hom =
      x ≫ (homologyShift T.X).hom
    rw [Category.assoc]
    exact hz.symm

open KIP126.Kervaire.Route

private theorem factorization_one_homology_zero
    {X Y : Spectrum} {f : X ⟶ Y}
    (h : AdamsMapFactorization coefficients 1 f) :
    ZeroOnModTwoHomology coefficients f := by
  cases h with
  | single f hz => exact hz
  | prepend f g hz rest => cases rest

/-- The same actual first arrow has zero HF₂ homology map when its
normalization exponent is one. -/
private theorem positive_normalized_homology_zero
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1) :
    ZeroOnModTwoHomology model.coefficients T.f := by
  have hfil : MapFiltrationAtLeast model.classicalTower T.f 1 := by
    classical
    by_contra h
    simp only [normalizedExponent, if_neg h] at hf
    omega
  have hfac : FactorizationFiltration model.coefficients T.f 1 :=
    (factorization_filtration_iff T.f 1).mpr hfil
  exact factorization_one_homology_zero (hfac 1 (by omega) (by omega))

/-- The actual same rotated cofiber triangle has an HF₂ homology SES in
every integer degree when its first map has positive normalization. -/
private theorem positive_normalized_rotated_homology_short_exact
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1) :
    HomologyShortExact model.coefficients (Triangle.mk T.f T.g T.h).rotate := by
  let C : HoCofiberSequence (C := Spectrum) :=
    ⟨T.X.obj model.auxiliary, T.Y.obj model.auxiliary, T.Z.obj model.auxiliary,
      T.f, T.g, T.h, T.distinguished⟩
  exact rotated_homology_short_exact_of_zero C (positive_normalized_homology_zero T hf)

end KIP126.ProofTools.Internal.ExtBoundaryComparison.HomologySES
