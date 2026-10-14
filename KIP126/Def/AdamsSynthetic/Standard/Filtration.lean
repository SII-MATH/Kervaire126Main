module

public import KIP126.Def.AdamsSynthetic.Standard.Background
public import KIP126.Def.AdamsSynthetic.HomologyExactness
public import KIP126.Def.AdamsSynthetic.MappingDetection

/-! Direct filtration and homology theorems for the fixed HF₂ Adams tower.
Finiteness, rational acyclicity, two-locality and non-odd-torsion are retained
as mathematical hypotheses. The old separate proof-package parameters disappear. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams
noncomputable section

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

private theorem factorizationComparison : FactorizationFiltrationComparison classicalTower :=
  ⟨factorization_filtration_iff⟩

/-- This remains an unfinished foundational proof, now owned by its upstream module. -/
public theorem finite_map_separation {X Y : Spectrum}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y)
    (hf : ∀ s : ℤ, MapAdamsFiltration classicalTower f s) : IsOddTorsionMap f := by sorry

public theorem separated_factorization {X Y : Spectrum}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y)
    (hf : ∀ s : ℤ, FactorizationFiltration coefficients f s) : IsOddTorsionMap f :=
  KIP126.AdamsSynthetic.separated_factorization classicalTower factorizationComparison
    finite_map_separation hX hY f hf

public theorem finite_filtration_of_not_odd {X Y : Spectrum}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y)
    (hf : ¬ IsOddTorsionMap f) : ∃ s : ℤ, ExactMapAdamsFiltration classicalTower f s :=
  KIP126.AdamsSynthetic.finite_filtration_of_not_odd classicalTower
    finite_map_separation hX hY f hf

public theorem adams_filtration_bounded (X : Spectrum) (hX : IsFiniteSpectrum X)
    (hr : RationallyAcyclic X) (hl : HomotopyTwoLocal X) (i : ℤ) :
    ∃ N : ℤ, ∀ s : ℤ, N < s → (classicalTower.tower X).filtrationSubmodule s i = ⊥ := by sorry

private theorem boundedness : AdamsBoundednessInput classicalTower := ⟨adams_filtration_bounded⟩

public theorem filtration_excludes_nonzero (X : Spectrum) (hX : IsFiniteSpectrum X)
    (hr : RationallyAcyclic X) (hl : HomotopyTwoLocal X) (i : ℤ) :
    ∃ N : ℤ, ∀ s : ℤ, N < s → ∀ x : HomotopyGroup i X,
      x ≠ 0 → x ∉ (classicalTower.tower X).filtrationSubmodule s i :=
  boundedness.excludes_nonzero X hX hr hl i

public def homologyShift (X : Spectrum) :
    coefficients.object ⊗ X⟦(1 : ℤ)⟧ ≅ (coefficients.object ⊗ X)⟦(1 : ℤ)⟧ := by sorry

public theorem homology_exact (T : HoCofiberSequence (C := Spectrum)) (i : ℤ) :
    Function.Exact (modTwoHomologyMap coefficients T.g i)
      (modTwoConnecting coefficients homologyShift T i) := by sorry

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

private theorem mappingDetection : MappingDetectionInput closedBackground classicalTower mappingSystem :=
  ⟨factorizationComparison, ⟨mapping_filtration_iff⟩⟩

public theorem mapping_detects_exact {X Y : Spectrum}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y)
    (s : ℤ) (hs : ExactMapAdamsFiltration classicalTower f s) :
    Nonempty (NonzeroClassicalDetection (mappingConvergence X Y hX hY) (s,s)
      (mappingClass closedBackground f s)) :=
  mappingDetection.detects_exact hX hY f s hs

public theorem mapping_detect_non_odd {X Y : Spectrum}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y)
    (hf : ¬ IsOddTorsionMap f) :
    ∃ s : ℤ, ExactMapAdamsFiltration classicalTower f s ∧
      Nonempty (NonzeroClassicalDetection (mappingConvergence X Y hX hY) (s,s)
        (mappingClass closedBackground f s)) :=
  mappingDetection.detect_non_odd finite_map_separation hX hY f hf

end
end KIP126.AdamsSynthetic.Standard
