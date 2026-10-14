module

public import KIP126.Def.AdamsSynthetic.MappingComposition
public import Mathlib.CategoryTheory.Enriched.Basic

@[expose] section

/-! Explicit enrichment on the full converging-sequence category. Its Hom
objects and composition agree with the actual mapping systems. Unit data
are bound on finite pages, E∞ and the actual abutment as well. This repairs
the older convergence-only ambient category, which forgot all finite pages.
Source: KIPBase `multiplicativeSS/AdamsEnriched.lean`, baseline 5aa845241533. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams KIP126.Core.SpectralSequence
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {A : ClassicalAdamsFamily C} {B : ClosedSymmetricTensorTriangulated C}
  {P : ClassicalTowerPresentation unit A} {scope : C → Prop}

/-- A supplied enrichment, rather than a globally postulated one. Every Hom
is this system's actual converging mapping sequence; its full morphisms see
all pages and the same E∞ comparison. -/
public structure MappingEnrichment {S : MappingSpectrumSystem B P scope}
    (M : MappingComposition S) where
  monoidal : MonoidalCategory (ConvergingSequence.{0,v} ℤ)
  enriched : @EnrichedCategory (ConvergingSequence.{0,v} ℤ) _ monoidal (MappingObject scope)
  hom_eq : ∀ X Y : MappingObject scope, enriched.Hom X Y = S.hom X Y
  /-- Elementary tensor products for the composable mapping systems. These
  are requested only for these systems, whose differential degrees agree;
  arbitrary ambient converging sequences need not have compatible degrees. -/
  tensorPairing : letI := monoidal
    ∀ X Y Z : MappingObject scope,
      ConvergingSSPairing (S.hom X Y).underlying (S.hom Y Z).underlying
        ((S.hom X Y ⊗ S.hom Y Z).underlying)
  /-- Actual enriched composition takes elementary page tensors to the
  specified page products. No arbitrary equivalence of pairing records is
  used to give composition its mathematical meaning. -/
  composition_page : letI := monoidal
    ∀ (X Y Z : MappingObject scope) (r : ℤ) (i j : ℤ × ℤ)
      (x : (S.hom X Y).underlying.E.Page r i)
      (y : (S.hom Y Z).underlying.E.Page r j),
      let f : (S.hom X Y ⊗ S.hom Y Z) ⟶ S.hom X Z :=
        eqToHom (congrArg₂ (fun A B : ConvergingSequence.{0,v} ℤ => A ⊗ B)
          (hom_eq X Y).symm (hom_eq Y Z).symm) ≫ enriched.comp X Y Z ≫
            eqToHom (hom_eq X Z)
      f.sequence.pageMap r (i+j) ((tensorPairing X Y Z).ssPairing.pair r i j x y) =
        (M.pairing X Y Z).ssPairing.pair r i j x y
  composition_eInfty : letI := monoidal
    ∀ (X Y Z : MappingObject scope) (i j : ℤ × ℤ)
      (x : ((S.hom X Y).underlying.E.ssData i).eInfty)
      (y : ((S.hom Y Z).underlying.E.ssData j).eInfty),
      let f : (S.hom X Y ⊗ S.hom Y Z) ⟶ S.hom X Z :=
        eqToHom (congrArg₂ (fun A B : ConvergingSequence.{0,v} ℤ => A ⊗ B)
          (hom_eq X Y).symm (hom_eq Y Z).symm) ≫ enriched.comp X Y Z ≫
            eqToHom (hom_eq X Z)
      f.sequence.eInftyMap (i+j) ((tensorPairing X Y Z).eInftyPair i j x y) =
        (M.pairing X Y Z).eInftyPair i j x y
  composition_abutment : letI := monoidal
    ∀ (X Y Z : MappingObject scope) (i j : ℤ)
      (x : (S.hom X Y).underlying.A i) (y : (S.hom Y Z).underlying.A j),
      let f : (S.hom X Y ⊗ S.hom Y Z) ⟶ S.hom X Z :=
        eqToHom (congrArg₂ (fun A B : ConvergingSequence.{0,v} ℤ => A ⊗ B)
          (hom_eq X Y).symm (hom_eq Y Z).symm) ≫ enriched.comp X Y Z ≫
            eqToHom (hom_eq X Z)
      f.convergence.aMap (i+j) ((tensorPairing X Y Z).abutmentPair i j x y) =
        (M.pairing X Y Z).abutmentPair i j x y
  unit_reindex : monoidal.tensorUnit.underlying.conv.reindex (0,0) = (0,0)
  unit_data : ConvergingSSUnit monoidal.tensorUnit.underlying unit_reindex
  identity_page : letI := monoidal
    ∀ (X : MappingObject scope) (r : ℤ),
      let f : 𝟙_ (ConvergingSequence.{0,v} ℤ) ⟶ S.hom X X :=
        enriched.id X ≫ eqToHom (hom_eq X X)
      f.sequence.pageMap r (0,0) (unit_data.page r) = (M.identity X).page r
  identity_eInfty : letI := monoidal
    ∀ X : MappingObject scope,
      let f : 𝟙_ (ConvergingSequence.{0,v} ℤ) ⟶ S.hom X X :=
        enriched.id X ≫ eqToHom (hom_eq X X)
      f.sequence.eInftyMap (0,0) unit_data.eInfty = (M.identity X).eInfty
  identity_abutment : letI := monoidal
    ∀ X : MappingObject scope,
      let f : 𝟙_ (ConvergingSequence.{0,v} ℤ) ⟶ S.hom X X :=
        enriched.id X ≫ eqToHom (hom_eq X X)
      f.convergence.aMap 0 unit_data.abutment = (M.identity X).abutment
end
end KIP126.AdamsSynthetic
