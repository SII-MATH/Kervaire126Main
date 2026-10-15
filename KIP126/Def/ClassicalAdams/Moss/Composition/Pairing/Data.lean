module

public import KIP126.Def.ClassicalAdams.Moss.Composition.LongLayer.Data
public import KIP126.Def.ClassicalAdams.TowerLongLayer.Internal.Data

@[expose] public section

/-!
Composition data on the actual mapping Adams towers. Every long-layer map
projects to the previously constructed coefficient/stage composition, and
every page operation is specified on all actual long-layer representatives.
Thus this is a construction obligation, not a freely chosen page operation.
No existence or boundary-compatibility proof is asserted here.
-/

namespace KIP126.Classical.Adams.Moss

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated] [MonoidalPreadditive C]

/-- A composition system tied to the actual one-step composition and quotient
maps. The raw internal index `n` is Adams page `n+2`. The two zero fields cover
the negative-filtration degrees, where the natural-number stage construction
is not used. All remaining page values are fixed by the representative field. -/
structure CompositionPairing where
  long : ∀ (X Y Z : C) (n s t : ℕ),
    adamsLongLayer H.unit (mappingObject X Y) (n + 2) (by omega) s ⊗
      adamsLongLayer H.unit (mappingObject Y Z) (n + 2) (by omega) t ⟶
        adamsLongLayer H.unit (mappingObject X Z) (n + 2) (by omega)
          ((s : ℤ) + (t : ℤ))
  projection : ∀ (X Y Z : C) (n s t : ℕ),
    long X Y Z n s t ≫
      adamsLongLayerProjection H.unit (mappingObject X Z) (n + 2) (by omega)
        ((s : ℤ) + (t : ℤ)) =
      longLayerProjectedComposition H R X Y Z (n + 2) (by omega) s t
  page : ∀ (X Y Z : C) (n : ℕ) (p q : ℤ × ℤ),
    (adamsTowerSSData H.unit (mappingObject X Y) p.1 p.2).page (n : WithTop ℕ) →ₗ[ℤ]
      (adamsTowerSSData H.unit (mappingObject Y Z) q.1 q.2).page (n : WithTop ℕ) →ₗ[ℤ]
        (adamsTowerSSData H.unit (mappingObject X Z)
          (p.1 + q.1) (p.2 + q.2)).page (n : WithTop ℕ)
  representatives : ∀ (X Y Z : C) (n s t : ℕ) (i j : ℤ) a b,
    page X Y Z n ((s : ℤ), i) ((t : ℤ), j)
      (adamsLongLayerToInternalPage H.unit (mappingObject X Y) n s i a)
      (adamsLongLayerToInternalPage H.unit (mappingObject Y Z) n t j b) =
      adamsLongLayerToInternalPage H.unit (mappingObject X Z) n
        ((s : ℤ) + (t : ℤ)) (i + j)
        (homotopyTensorPairing (i - s) (j - t)
          ((i + j) - ((s : ℤ) + (t : ℤ))) (by omega) (long X Y Z n s t) a b)
  negative_left : ∀ (X Y Z : C) (n : ℕ) (p q : ℤ × ℤ),
    p.1 < 0 → ∀ a b, page X Y Z n p q a b = 0
  negative_right : ∀ (X Y Z : C) (n : ℕ) (p q : ℤ × ℤ),
    q.1 < 0 → ∀ a b, page X Y Z n p q a b = 0

variable {H R}

/-- Composition on the already defined `Page r`, with the same page convention.
Only `r ≥ 2` is used in the coherence laws and Moss convergence statements. -/
def CompositionPairing.comp (P : CompositionPairing H R)
    (X Y Z : C) (r : ℤ) (p q : ℤ × ℤ) :
    (mappingSequence H.unit X Y).Page r p →ₗ[ℤ]
      (mappingSequence H.unit Y Z).Page r q →ₗ[ℤ]
        (mappingSequence H.unit X Z).Page r (p + q) :=
  P.page X Y Z (r - 2).toNat p q

end
end KIP126.Classical.Adams.Moss
