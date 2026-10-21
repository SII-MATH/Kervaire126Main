module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Source comparisons with SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

public import KIP126.AdamsSynthetic.Standard
public import KIP126.AdamsSynthetic.Source
public import Mathlib.CategoryTheory.Localization.Predicate
import all KIP126.AdamsSynthetic.Source
import all KIP126.AdamsSynthetic.Internal.Source.DerivedSmash
import all KIP126.AdamsSynthetic.Internal.Source.PointSetRecognition
import all KIP126.AdamsSynthetic.Internal.Source.AdamsSequence
import all KIP126.AdamsSynthetic.Internal.Source.MilnorComparison
import all KIP126.AdamsSynthetic.Internal.Source.SurvivalTransport
import all KIP126.AdamsSynthetic.Internal.Milnor.Cohomology

/-! Source recognition for the fixed background. These declarations constrain
the already selected objects; they do not add hypotheses to Main. Pending
comparisons are individually recorded, rather than counted as constructions.
The ordinary stable source and HF₂ completion are kept distinct. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.Classical.Adams
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Recognition of the fixed ordinary category, sphere, integer homotopy,
HF₂ object, coordinate and normalized actual point-set unit. -/
public def sourceRecognition : ClassicalSourceRecognition Spectrum coefficients := by
  sorry

/-- Tensor comparison on actual good suspension-spectrum generators. This
does not assert an arbitrary-prespectrum derived-smash construction. -/
public def sourceGeneratorTensorRecognition :
    ClassicalSourceGeneratorTensorRecognition sourceRecognition := by
  sorry

/-- Actual mapping-cone comparison, including its inclusion and boundary. -/
public def sourceCofiberRecognition :
    ClassicalSourceCofiberRecognition sourceRecognition := by
  sorry

/-- A levelwise good replacement of the same actual prespectra, with a
specified natural stable equivalence to the identity. -/
public def sourceReplacement : ClassicalSourceReplacementData := by
  sorry

/-- Recognition of the fixed tensor on all actual prespectra by their
replacement followed by the actual even/odd diagonal smash. -/
public def sourceDerivedSmashRecognition :
    ClassicalSourceDerivedSmashRecognition sourceRecognition sourceReplacement := by
  sorry

universe u v

open KIP126.AdamsSynthetic.Source CategoryTheory.MonoidalCategory in
/-- The full natural tensor comparison reflects preservation of actual
stable homotopy groups. Its construction is independent of this flatness result. -/
private theorem sourceReplacementFlatness_of_recognition
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : SourceRecognition C H) (P : SourceReplacementData)
    (D : SourceDerivedSmashRecognition R P) : SourceReplacementFlatness P := by
  intro X Y X' Y' f g hf hg
  haveI : IsIso (sourceLocalization.map f) := Prespectrum.stableEquivalences.Q_inverts f hf
  haveI : IsIso (sourceLocalization.map g) := Prespectrum.stableEquivalences.Q_inverts g hg
  let k := R.equivalence.functor.map (sourceLocalization.map (P.derivedSmashMap f g))
  have heq : k = (D.comparison X Y).inv ≫
      (R.equivalence.functor.map (sourceLocalization.map f) ⊗ₘ
        R.equivalence.functor.map (sourceLocalization.map g)) ≫
      (D.comparison X' Y').hom := by
    have hh := congrArg (fun z => (D.comparison X Y).inv ≫ z) (D.natural f g)
    simpa only [k, Category.assoc, Iso.inv_hom_id_assoc] using hh.symm
  haveI : IsIso k := by rw [heq]; infer_instance
  intro d
  change Function.Bijective (Prespectrum.stableHomotopyMap (P.derivedSmashMap f g) d)
  constructor
  · intro x y h
    obtain ⟨a,rfl⟩ := (R.homotopy (P.derivedSmash X Y) d).surjective x
    obtain ⟨b,rfl⟩ := (R.homotopy (P.derivedSmash X Y) d).surjective y
    apply congrArg (R.homotopy (P.derivedSmash X Y) d)
    apply (cancel_mono k).mp
    apply (R.homotopy (P.derivedSmash X' Y') d).injective
    simpa only [k, R.homotopy_natural] using h
  · intro y
    let b := (R.homotopy (P.derivedSmash X' Y') d).symm y
    refine ⟨R.homotopy (P.derivedSmash X Y) d (b ≫ inv k), ?_⟩
    rw [← R.homotopy_natural]
    change R.homotopy (P.derivedSmash X' Y') d ((b ≫ inv k) ≫ k) = y
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, b, Equiv.apply_symm_apply]

/-- The prescribed diagonal smash preserves stable equivalences after
this same replacement; no arbitrary source tensor is supplied. -/
public theorem sourceReplacement_flat : ClassicalSourceReplacementFlatness sourceReplacement :=
  sourceReplacementFlatness_of_recognition sourceRecognition sourceReplacement
    sourceDerivedSmashRecognition

/-- The recursive fiber tower of the specified coefficient unit. -/
@[no_expose] public def canonicalAdamsTower (X : Spectrum) :
    AbstractAdamsTower coefficients.unit X := Internal.Source.canonicalTower coefficients.unit X

/-- Its nested-subobject spectral sequence, with actual finite cycles and
boundaries and their intersection/union at infinity. -/
@[no_expose] public def canonicalAdamsSequence (X : Spectrum) :
    KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ) :=
  Internal.Source.canonicalSequence coefficients.unit X

/-- Full comparison: the ambient maps, every page and differential, and
infinite cycles/boundaries are identified. E₂ alone would not suffice. -/
public def classical_canonicalIso (X : Spectrum) :
    classical.obj X ≅ canonicalAdamsSequence X := by
  sorry

public abbrev canonicalSphereSequence := canonicalAdamsSequence (SphereSpectrum : Spectrum)
public abbrev classicalSphere_sourceIso : classical.sphere ≅ canonicalSphereSequence :=
  classical_canonicalIso SphereSpectrum

/-- Permanent nonzero survival transports with the same infinite
representative, rather than merely a vector-space isomorphism on E₂. -/
public theorem nonzeroSurvival_source_iff (p : ℤ × ℤ) (x : classical.sphere.Page 2 p) :
    NonzeroSurvival canonicalSphereSequence p
      (classicalSphere_sourceIso.hom.pageMap 2 p x) ↔
        NonzeroSurvival classical.sphere p x :=
  Internal.Source.nonzeroSurvival_iso_iff classicalSphere_sourceIso p x

/-- Actual connecting-map/cofiber first differential, in nonnegative
Milnor coordinates. No first differential is chosen as extra input. -/
@[no_expose] public def canonicalFirstDifferential (s t : ℕ) :
    (canonicalAdamsTower (SphereSpectrum : Spectrum)).FirstPage ((s : ℤ), (t : ℤ)) →ₗ[ℤ]
      (canonicalAdamsTower (SphereSpectrum : Spectrum)).FirstPage
        (((s + 1 : ℕ) : ℤ), (t : ℤ)) :=
  Internal.Source.towerFirstDifferentialNat (canonicalAdamsTower SphereSpectrum) s t

/-- Coordinates of the actual coefficient-tower first page. Their
construction is pending; the following formula fixes their differential. -/
public def milnorCoordinates (s t : ℕ) :
    (canonicalAdamsTower (SphereSpectrum : Spectrum)).FirstPage ((s : ℤ), (t : ℤ)) ≃ₗ[ℤ]
      MilnorCochains s t := by
  sorry

public theorem milnorCoordinates_differential (s t : ℕ)
    (x : (canonicalAdamsTower (SphereSpectrum : Spectrum)).FirstPage ((s : ℤ), (t : ℤ))) :
    milnorCoordinates (s + 1) t (canonicalFirstDifferential s t x) =
      milnorDifferential s t (milnorCoordinates s t x) := by
  sorry

/-- Actual tower cycles map to exactly the cocycles of the specified
polynomial differential. This follows from exactness and the same d₁ formula. -/
public theorem milnorCoordinates_cycle (s t : ℕ)
    (x : (canonicalAdamsTower (SphereSpectrum : Spectrum)).FirstPage ((s : ℤ), (t : ℤ))) :
    x ∈ (canonicalAdamsTower (SphereSpectrum : Spectrum)).cycles 2 (by decide)
      ((s : ℤ), (t : ℤ)) ↔ milnorDifferential s t (milnorCoordinates s t x) = 0 := by
  rw [← milnorCoordinates_differential, LinearEquiv.map_eq_zero_iff]
  exact (Internal.Source.towerFirstDifferentialNat_eq_zero_iff
    (canonicalAdamsTower SphereSpectrum) s t x).symm

/-- The canonical quotient class of an actual second-page tower cycle. -/
@[no_expose] public def canonicalE2ClassOfCycle (s t : ℕ)
    (x : (canonicalAdamsTower (SphereSpectrum : Spectrum)).FirstPage ((s : ℤ), (t : ℤ)))
    (hx : x ∈ (canonicalAdamsTower (SphereSpectrum : Spectrum)).cycles 2 (by decide)
      ((s : ℤ), (t : ℤ))) : canonicalSphereSequence.Page 2 ((s : ℤ), (t : ℤ)) :=
  Internal.Source.canonicalE2ClassOfCycle coefficients.unit SphereSpectrum _ x hx

/-- The E₂ comparison is the descent of the actual E₁ coordinates along
the actual quotient maps and the same full source-sequence isomorphism.
This excludes an unrelated graded linear isomorphism. -/
public theorem sphereE2_milnor_classOfCycle (s t : ℕ)
    (x : (canonicalAdamsTower (SphereSpectrum : Spectrum)).FirstPage ((s : ℤ), (t : ℤ)))
    (hx : x ∈ (canonicalAdamsTower (SphereSpectrum : Spectrum)).cycles 2 (by decide)
      ((s : ℤ), (t : ℤ))) :
    sphereE2_milnorEquiv s t
      (classicalSphere_sourceIso.inv.pageMap 2 _ (canonicalE2ClassOfCycle s t x hx)) =
        milnorClassOfCycle (milnorCoordinates s t x)
          ((milnorCoordinates_cycle s t x).mp hx) := by
  sorry

/-- All standard hᵢ are the specified polynomial cocycles under the same
fixed comparison. -/
public theorem standardHi_milnor (i : ℕ) :
    sphereE2_milnorEquiv 1 (2 ^ i) (standardHi i) = milnorHiClass i := by
  exact (sphereE2_milnorEquiv 1 (2 ^ i)).apply_symm_apply (milnorHiClass i)

/-- Compatibility of the actual sphere E₂ multiplication with the actual
concatenation product in normalized cobar cohomology. -/
public theorem sphereProduct_milnor (s t s' t' : ℕ)
    (x : classical.sphere.Page 2 ((s : ℤ), (t : ℤ)))
    (y : classical.sphere.Page 2 ((s' : ℤ), (t' : ℤ))) :
    sphereE2_milnorEquiv (s + s') (t + t')
      ((eqToHom (congrArg (classical.sphere.Page 2)
        (show ((s : ℤ), (t : ℤ)) + ((s' : ℤ), (t' : ℤ)) =
          (((s + s' : ℕ) : ℤ), ((t + t' : ℕ) : ℤ)) by
            ext <;> simp)))
        (sphereAlgebra.product _ _ x y)) =
      milnorCup (sphereE2_milnorEquiv s t x) (sphereE2_milnorEquiv s' t' y) := by
  sorry

private theorem milnorCup_unit_right_zero (x : MilnorCohomology 0 0) :
    milnorCup x milnorUnitClass = x := by
  change Milnor.cohomologyCup x Milnor.unitClass = x
  obtain ⟨y, hy, rfl⟩ := Milnor.classOfCycle_surjective x
  rw [Milnor.unitClass, Milnor.cohomologyCup_classOfCycle]
  apply congrArg (Milnor.classOf 0 0)
  apply Subtype.ext
  apply Subtype.ext
  change @Milnor.cupPolynomial 0 0 y.val 1 = y.val
  simp only [Milnor.cupPolynomial, map_one, mul_one]
  have hrename : (fun a : Fin 0 × ℕ => (a.1.castAdd 0, a.2)) = id := by
    funext a
    exact Fin.elim0 a.1
  rw [hrename, MvPolynomial.rename_id]
  rfl

public theorem sphereUnit_milnor :
    sphereE2_milnorEquiv 0 0 sphereAlgebra.unit = milnorUnitClass := by
  let x := (sphereE2_milnorEquiv 0 0).symm milnorUnitClass
  have hx : sphereE2_milnorEquiv 0 0 x = milnorUnitClass :=
    (sphereE2_milnorEquiv 0 0).apply_symm_apply milnorUnitClass
  have h := sphereProduct_milnor 0 0 0 0 sphereAlgebra.unit x
  change sphereE2_milnorEquiv 0 0
      (sphereAlgebra.product (0,0) (0,0) sphereAlgebra.unit x) =
    milnorCup (sphereE2_milnorEquiv 0 0 sphereAlgebra.unit)
      (sphereE2_milnorEquiv 0 0 x) at h
  rw [eq_of_heq (sphereAlgebra.unit_left (0,0) x), hx,
    milnorCup_unit_right_zero] at h
  exact h.symm

/-- The actual Main square is the cup square of the specified ξ₁⁶⁴ cocycle. -/
public theorem standardH6Square_milnor :
    sphereE2_milnorEquiv 2 128 standardH6Square = milnorHiSquareClass 6 := by
  have h := sphereProduct_milnor 1 64 1 64 standardH6 standardH6
  simp only [standardH6Square_eq_product] at ⊢
  change sphereE2_milnorEquiv 2 128
    (sphereAlgebra.product (1,64) (1,64) standardH6 standardH6) = _
  change sphereE2_milnorEquiv 2 128
    (sphereAlgebra.product (1,64) (1,64) standardH6 standardH6) = _ at h
  rw [h]
  have hh : sphereE2_milnorEquiv 1 64 standardH6 = milnorHiClass 6 :=
    standardHi_milnor 6
  rw [hh]
  exact (Milnor.hiSquare_eq_cup 6).symm

/-- The actual fixed classical functor on the ordinary concrete source. -/
public def sourceClassical : ClassicalSource ⥤
    KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ) :=
  sourceRecognition.equivalence.functor ⋙ classical.functor

/-- Descent requires the whole spectral sequence, including its infinite
representatives, to invert these precise HF₂ cohomology equivalences. -/
public theorem sourceClassical_inverts_hf2 :
    (classicalHF2Equivalences sourceRecognition).IsInvertedBy sourceClassical := by
  sorry

/-- The classical functor on the actual HF₂-localized source is obtained
by the localization universal property, rather than selected independently. -/
public def localizedClassical : ClassicalHF2LocalizedSource sourceRecognition ⥤
    KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ) := by
  letI := classicalHF2Localization_isLocalization sourceRecognition
  exact CategoryTheory.Localization.lift sourceClassical sourceClassical_inverts_hf2
    (classicalHF2Localization sourceRecognition)

public def sourceLocalizationAdamsIso :
    classicalHF2Localization sourceRecognition ⋙ localizedClassical ≅ sourceClassical := by
  letI := classicalHF2Localization_isLocalization sourceRecognition
  exact CategoryTheory.Localization.fac sourceClassical sourceClassical_inverts_hf2
    (classicalHF2Localization sourceRecognition)

public def localizedSphereSequence :
    KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ) :=
  localizedClassical.obj (classicalHF2LocalizedSphere sourceRecognition)

public def localizedSphere_classicalIso : localizedSphereSequence ≅ classical.sphere :=
  sourceLocalizationAdamsIso.app classicalSourceSphere ≪≫
    classical.functor.mapIso sourceRecognition.sphereIso

public def localizedH6Square : localizedSphereSequence.Page 2 (2,128) :=
  localizedSphere_classicalIso.inv.pageMap 2 (2,128) standardH6Square

/-- The unchanged Main target transports to the actual localized sphere,
conditional only on the separately registered source constructions. -/
public theorem nonzeroSurvival_localized_iff :
    NonzeroSurvival localizedSphereSequence (2,128) localizedH6Square ↔
      NonzeroSurvival classical.sphere (2,128) standardH6Square :=
  Internal.Source.nonzeroSurvival_iso_iff localizedSphere_classicalIso.symm
    (2,128) standardH6Square

end
end KIP126.AdamsSynthetic.Standard
