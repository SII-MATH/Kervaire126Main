module

public import KIP126.Def.ClassicalAdams.Moss.Composition.Pairing.Predicates
public import KIP126.Def.ClassicalAdams.Moss.Crossing.Predicates

@[expose] public section

/-!
Moss convergence in the currently constructed mapping model, for the
preceding-page defining systems (`r ≥ 3`) used in MainPaper lines 2537--2545.
This proposition is stated here without a proof. Its objects, signs, and page
conventions have been specified; identifying this formulation with all
hypotheses of Moss (1970), Theorem 1.2, remains a separate comparison with the
literature. The
local Moss source directory currently contains metadata, not that paper's text.
-/

namespace KIP126.Classical.Adams.Moss

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated] [MonoidalPreadditive C]
  [∀ A : C, (tensorLeft A).CommShift ℤ]
  (P : CompositionPairing H R)

/-- Moss implication at four specified actual mapping objects. It keeps both
product-tower weak convergence hypotheses, actual vanishing composites,
the two Moss-direction noncrossing ranges, and the same detection data.
The conclusion is existence of a permanent Massey class detecting a Toda
element; it does not assert that every element of the Massey set survives. -/
def StatementAt (W X Y Z : C)
    (cWX : MappingAdamsConvergence H.unit W X)
    (cXY : MappingAdamsConvergence H.unit X Y)
    (cYZ : MappingAdamsConvergence H.unit Y Z)
    (cWZ : MappingAdamsConvergence H.unit W Z) : Prop :=
  ∀ (r : ℤ) (hr : 3 ≤ r) (i j k : ℤ × ℤ),
    MappingAdamsTower H.unit W Y → MappingAdamsTower H.unit X Z →
    ∀ (a : (mappingSequence H.unit W X).Page r i)
      (b : (mappingSequence H.unit X Y).Page r j)
      (c : (mappingSequence H.unit Y Z).Page r k)
      (α : mappingAbutment W X (stem i))
      (β : mappingAbutment X Y (stem j))
      (γ : mappingAbutment Y Z (stem k)),
    let f := shiftMap W X i (stem j + stem k) α
    let g := shiftMap X Y j (stem k) β
    let h := abutmentMap Y Z k γ
    DetectsAbutment H.unit W X cWX r i a α →
    DetectsAbutment H.unit X Y cXY r j b β →
    DetectsAbutment H.unit Y Z cYZ r k c γ →
    P.comp W X Y r i j a b = 0 → P.comp X Y Z r j k b c = 0 →
    f ≫ g = 0 → g ≫ h = 0 →
    NoMossCrossingForProducts H.unit W X Y Z r i j k →
    ∃ (x : (mappingSequence H.unit W Z).Page r (PageMassey.degree r i j k))
      (ξ : mappingAbutment W Z (stem (PageMassey.degree r i j k))),
      PageMassey.Relation H R P r hr x a b c ∧
      PermanentCycle H.unit W Z r (PageMassey.degree r i j k) x ∧
      DetectsAbutment H.unit W Z cWZ r
        (PageMassey.degree r i j k) x ξ ∧
      Toda.Relation (todaMap r W Z i j k ξ) f g h

/-- The mapping version for a specified family of objects and its fixed
convergence data. Identification of this family with finite spectra is a
separate hypothesis; convergence of every object of the ambient category is
not required. -/
def Statement {ι : Type w} (objects : ι → C)
    (convergence : ∀ X Y : ι, MappingAdamsConvergence H.unit (objects X) (objects Y)) :
    Prop :=
  P.Coherent H R →
    (∀ X Y Z : ι, P.DetectionCompatible H R (objects X) (objects Y) (objects Z)
      (convergence X Y) (convergence Y Z) (convergence X Z)) →
    ∀ W X Y Z : ι, StatementAt H R P (objects W) (objects X) (objects Y) (objects Z)
      (convergence W X) (convergence X Y) (convergence Y Z) (convergence W Z)

/-- The actual sphere specialization of precisely the same statement and data. -/
def SphereStatement (convergence : MappingAdamsConvergence H.unit
    (SphereSpectrum (C := C)) SphereSpectrum) : Prop :=
  P.Coherent H R →
    P.DetectionCompatible H R SphereSpectrum SphereSpectrum SphereSpectrum
      convergence convergence convergence →
    StatementAt H R P SphereSpectrum SphereSpectrum SphereSpectrum SphereSpectrum
      convergence convergence convergence convergence

end
end KIP126.Classical.Adams.Moss
