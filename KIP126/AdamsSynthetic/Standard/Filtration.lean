module

public import KIP126.AdamsSynthetic.Standard.Background
public import KIP126.AdamsSynthetic.HomologyExactness
public import KIP126.AdamsSynthetic.MappingDetection

/-! Direct filtration and homology theorems for the fixed HF₂ Adams tower.
Finiteness, rational acyclicity, two-locality and non-odd-torsion are retained
as mathematical hypotheses. The old separate proof-package parameters disappear. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The closed symmetric tensor structure of the fixed category of spectra. -/
public def closedBackground : ClosedSymmetricTensorTriangulated Spectrum := by sorry

public theorem sphere_twist (r s : ℤ) :
    letI := closedBackground.symmetric
    (β_ (Sphere r : Spectrum) (Sphere s)).hom ≫ (closedBackground.smashSpheres s r).hom ≫
      eqToHom (congrArg (Sphere (C := Spectrum)) (add_comm s r)) =
      if Even (r * s) then (closedBackground.smashSpheres r s).hom
      else -(closedBackground.smashSpheres r s).hom := by sorry

/-- The target tower and the HF₂-zero factorization definition agree. -/
public theorem factorization_filtration_iff {X Y : Spectrum} (f : X ⟶ Y) (s : ℤ) :
    FactorizationFiltration coefficients f s ↔ MapAdamsFiltration classicalTower f s := by sorry

/-- This remains an unfinished foundational proof, now owned by its upstream module. -/
public theorem finite_map_separation {X Y : Spectrum}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y)
    (hf : ∀ s : ℤ, MapAdamsFiltration classicalTower f s) : IsOddTorsionMap f := by sorry

public theorem separated_factorization {X Y : Spectrum}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y)
    (hf : ∀ s : ℤ, FactorizationFiltration coefficients f s) : IsOddTorsionMap f :=
  KIP126.AdamsSynthetic.separated_factorization classicalTower factorization_filtration_iff
    finite_map_separation hX hY f hf

public theorem finite_filtration_of_not_odd {X Y : Spectrum}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y)
    (hf : ¬ IsOddTorsionMap f) : ∃ s : ℤ, ExactMapAdamsFiltration classicalTower f s :=
  KIP126.AdamsSynthetic.finite_filtration_of_not_odd classicalTower
    finite_map_separation hX hY f hf

public theorem adams_filtration_bounded (X : Spectrum) (hX : IsFiniteSpectrum X)
    (hr : RationallyAcyclic X) (hl : HomotopyTwoLocal X) (i : ℤ) :
    ∃ N : ℤ, ∀ s : ℤ, N < s → (classicalTower.tower X).filtrationSubmodule s i = ⊥ := by sorry

public theorem filtration_excludes_nonzero (X : Spectrum) (hX : IsFiniteSpectrum X)
    (hr : RationallyAcyclic X) (hl : HomotopyTwoLocal X) (i : ℤ) :
    ∃ N : ℤ, ∀ s : ℤ, N < s → ∀ x : HomotopyGroup i X,
      x ≠ 0 → x ∉ (classicalTower.tower X).filtrationSubmodule s i :=
  filtration_excludes_nonzero_of_bounded adams_filtration_bounded X hX hr hl i

public def homologyShift (X : Spectrum) :
    coefficients.object ⊗ X⟦(1 : ℤ)⟧ ≅ (coefficients.object ⊗ X)⟦(1 : ℤ)⟧ := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  exact (β_ coefficients.object (X⟦(1 : ℤ)⟧)) ≪≫
    ((tensorRight coefficients.object).commShiftIso (1 : ℤ)).app X ≪≫
    (shiftFunctor Spectrum (1 : ℤ)).mapIso (β_ coefficients.object X).symm

private theorem desuspend_injective (X : Spectrum) (i : ℤ) :
    Function.Injective (AbstractAdamsTower.desuspend X i) := by
  let e := (shiftFunctorAdd' Spectrum i (-1) (i - 1) (by omega)).app SphereSpectrum
  let d := (shiftFunctorCompIsoId Spectrum 1 (-1) (by omega)).app X
  intro a b h
  change e.hom ≫ (shiftFunctor Spectrum (-1 : ℤ)).map a ≫ d.hom =
    e.hom ≫ (shiftFunctor Spectrum (-1 : ℤ)).map b ≫ d.hom at h
  apply (shiftFunctor Spectrum (-1 : ℤ)).map_injective
  apply (cancel_epi e.hom).mp
  apply (cancel_mono d.hom).mp
  simpa only [Category.assoc] using h

private theorem homology_triangle_distinguished (T : HoCofiberSequence (C := Spectrum)) :
    Pretriangulated.Triangle.mk (coefficients.object ◁ T.f) (coefficients.object ◁ T.g)
      (coefficients.object ◁ T.h ≫ (homologyShift T.X).hom) ∈ distTriang Spectrum := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  letI := closedBackground.tensorExact coefficients.object
  let F := tensorRight coefficients.object
  refine Pretriangulated.isomorphic_distinguished _
    (F.map_distinguished _ T.distinguished) _ ?_
  refine Pretriangulated.Triangle.isoMk _ _ (β_ coefficients.object T.X)
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

public theorem homology_exact (T : HoCofiberSequence (C := Spectrum)) (i : ℤ) :
    Function.Exact (modTwoHomologyMap coefficients T.g i)
      (modTwoConnecting coefficients homologyShift T i) := by
  let U := Pretriangulated.Triangle.mk (coefficients.object ◁ T.f)
    (coefficients.object ◁ T.g) (coefficients.object ◁ T.h ≫ (homologyShift T.X).hom)
  have hU : U ∈ distTriang Spectrum := homology_triangle_distinguished T
  intro z
  change AbstractAdamsTower.desuspend (coefficients.object ⊗ T.X) i
    (z ≫ U.mor₃) = 0 ↔ ∃ y, y ≫ U.mor₂ = z
  have hzero : AbstractAdamsTower.desuspend (coefficients.object ⊗ T.X) i
      (z ≫ U.mor₃) = 0 ↔ z ≫ U.mor₃ = 0 := by
    constructor
    · intro hz
      apply desuspend_injective (coefficients.object ⊗ T.X) i
      simpa only [map_zero] using hz
    · intro hz
      rw [hz, map_zero]
  rw [hzero]
  constructor
  · intro hz
    obtain ⟨y, hy⟩ := Pretriangulated.Triangle.coyoneda_exact₃ U hU z hz
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    rw [Category.assoc, Pretriangulated.comp_distTriang_mor_zero₂₃ U hU, comp_zero]

private def homologyExactness : ModTwoHomologyExactness coefficients :=
  ⟨homologyShift, homology_exact⟩

public theorem cofiber_homology_card_bound (T : HoCofiberSequence (C := Spectrum))
    (i : ℤ) (nX nY : ℕ)
    (hX : ∀ S : Finset (ModTwoHomology coefficients (i-1) T.X), S.card ≤ nX)
    (hY : ∀ S : Finset (ModTwoHomology coefficients i T.Y), S.card ≤ nY)
    (S : Finset (ModTwoHomology coefficients i T.Z)) : S.card ≤ nX*nY :=
  homologyExactness.cofiber_card_bound T i nX nY hX hY S

/-- Convergence is asserted only for the actual internal hom of finite spectra. -/
public def mappingConvergence (X Y : Spectrum)
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) :
    ClassicalTowerConvergence classicalTower (mappingSpectrum closedBackground X Y) := by sorry

public def mappingSystem :
    MappingSpectrumSystem closedBackground classicalTower (IsFiniteSpectrum (C := Spectrum)) :=
  ⟨mappingConvergence⟩

public theorem mapping_filtration_iff {X Y : Spectrum}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y) (s : ℤ) :
    MapAdamsFiltration classicalTower f s ↔
      (mappingHomotopyZeroEquiv closedBackground X Y).symm f ∈
        (classicalTower.tower (mappingSpectrum closedBackground X Y)).filtrationSubmodule s 0 := by
  sorry

public theorem mapping_detects_exact {X Y : Spectrum}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y)
    (s : ℤ) (hs : ExactMapAdamsFiltration classicalTower f s) :
    Nonempty (NonzeroClassicalDetection (mappingConvergence X Y hX hY) (s,s)
      (mappingClass closedBackground f s)) :=
  nonzeroClassicalDetection_of_exact_map (S := mappingSystem) mapping_filtration_iff hX hY f s hs

public theorem mapping_detect_non_odd {X Y : Spectrum}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y)
    (hf : ¬ IsOddTorsionMap f) :
    ∃ s : ℤ, ExactMapAdamsFiltration classicalTower f s ∧
      Nonempty (NonzeroClassicalDetection (mappingConvergence X Y hX hY) (s,s)
        (mappingClass closedBackground f s)) :=
  nonzeroClassicalDetection_of_not_odd_map (S := mappingSystem)
    mapping_filtration_iff finite_map_separation hX hY f hf

end
end KIP126.AdamsSynthetic.Standard
