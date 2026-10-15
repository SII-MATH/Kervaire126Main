module

public import KIP126.Def.ClassicalAdams.Moss.Massey.Predicates
public import KIP126.Def.ClassicalAdams.Moss.Statement.Data

@[expose] public section

namespace KIP126.Classical.Adams.Moss

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated] [MonoidalPreadditive C]
  (P : CompositionPairing H R)

/-- Stem-signed Leibniz for the actual differential and the fixed page product.
The transports only identify the additive bidegrees of the two summands. -/
def CompositionPairing.Leibniz : Prop :=
  ∀ (X Y Z : C) (r : ℤ), 2 ≤ r → ∀ (i j : ℤ × ℤ)
    (a : (mappingSequence H.unit X Y).Page r i)
    (b : (mappingSequence H.unit Y Z).Page r j),
    (mappingSequence H.unit X Z).d r (i + j) (P.comp X Y Z r i j a b) =
      PageMassey.pageCast H.unit X Z rfl (by
        change (i + (r, r - 1)) + j = (i + j) + (r, r - 1)
        abel)
        (P.comp X Y Z r (i + (r, r - 1)) j
          ((mappingSequence H.unit X Y).d r i a) b) +
      (if Even (stem i) then
        PageMassey.pageCast H.unit X Z rfl (by
          change i + (j + (r, r - 1)) = (i + j) + (r, r - 1)
          abel)
          (P.comp X Y Z r i (j + (r, r - 1)) a
            ((mappingSequence H.unit Y Z).d r j b))
      else -PageMassey.pageCast H.unit X Z rfl (by
          change i + (j + (r, r - 1)) = (i + j) + (r, r - 1)
          abel)
          (P.comp X Y Z r i (j + (r, r - 1)) a
            ((mappingSequence H.unit Y Z).d r j b)))

/-- Pairing commutes with passage through common next-cycle representatives. -/
def CompositionPairing.NextPageCompatible : Prop :=
  ∀ (X Y Z : C) (r : ℤ), 2 ≤ r → ∀ (i j : ℤ × ℤ)
    (a : (mappingSequence H.unit X Y).Page r i)
    (b : (mappingSequence H.unit Y Z).Page r j)
    (a' : (mappingSequence H.unit X Y).Page (r + 1) i)
    (b' : (mappingSequence H.unit Y Z).Page (r + 1) j),
    NextPageRelation (mappingSequence H.unit X Y) r i a a' →
    NextPageRelation (mappingSequence H.unit Y Z) r j b b' →
    NextPageRelation (mappingSequence H.unit X Z) r (i + j)
      (P.comp X Y Z r i j a b) (P.comp X Y Z (r + 1) i j a' b')

/-- Ordered composition is associative, with only the additive degree transport. -/
def CompositionPairing.Associative : Prop :=
  ∀ (W X Y Z : C) (r : ℤ), 2 ≤ r → ∀ (i j k : ℤ × ℤ)
    (a : (mappingSequence H.unit W X).Page r i)
    (b : (mappingSequence H.unit X Y).Page r j)
    (c : (mappingSequence H.unit Y Z).Page r k),
    P.comp W Y Z r (i + j) k (P.comp W X Y r i j a b) c =
      PageMassey.pageCast H.unit W Z rfl (by abel)
        (P.comp W X Z r i (j + k) a (P.comp X Y Z r j k b c))

variable [∀ A : C, (tensorLeft A).CommShift ℤ]

/-- Finite-page detection is compatible with actual composition on the fixed
mapping abutments and the same convergence identifications. -/
def CompositionPairing.DetectionCompatible
    (X Y Z : C) (cXY : MappingAdamsConvergence H.unit X Y)
    (cYZ : MappingAdamsConvergence H.unit Y Z)
    (cXZ : MappingAdamsConvergence H.unit X Z) : Prop :=
  ∀ (r : ℤ), 2 ≤ r → ∀ (i j : ℤ × ℤ)
    (a : (mappingSequence H.unit X Y).Page r i)
    (b : (mappingSequence H.unit Y Z).Page r j)
    (α : mappingAbutment X Y (stem i)) (β : mappingAbutment Y Z (stem j)),
    DetectsAbutment H.unit X Y cXY r i a α →
    DetectsAbutment H.unit Y Z cYZ r j b β →
    DetectsAbutment H.unit X Z cXZ r (i + j)
      (P.comp X Y Z r i j a b) (abutmentComposition X Y Z i j α β)

/-- The composition laws required for Moss convergence. These are hypotheses
on one specified composition system; the existence of such a system is not
asserted here. -/
structure CompositionPairing.Coherent : Prop where
  leibniz : P.Leibniz H R
  next : P.NextPageCompatible H R
  associative : P.Associative H R

end
end KIP126.Classical.Adams.Moss
