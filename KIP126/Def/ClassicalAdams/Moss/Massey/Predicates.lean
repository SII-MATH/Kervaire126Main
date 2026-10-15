module

public import KIP126.Def.ClassicalAdams.Moss.Massey.Data

@[expose] public section

/-!
The preceding-page defining-system relation used at MainPaper, lines
2537--2545: two d₂ formulas produce an E₃ Massey class. The scope is `r ≥ 3`.
This does not define the separate E₂ cobar-Massey operation.
-/

namespace KIP126.Classical.Adams.Moss.PageMassey

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C]
  {H : C} (unit : 𝟙_ C ⟶ H)

/-- Actual successor-page passage through one common next-cycle representative.
In particular the earlier class is a cycle; there is no freely chosen
homology identification or successor relation. -/
def Passage (X Y : C) (r : ℤ) (k : ℤ × ℤ)
    (a : (mappingSequence unit X Y).Page (r - 1) k)
    (b : (mappingSequence unit X Y).Page r k) : Prop :=
  NextPageRelation (mappingSequence unit X Y) (r - 1) k a
    (pageCast unit X Y (by omega) rfl b)

variable [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated] [MonoidalPreadditive C]
  (P : CompositionPairing H R)

/-- A triple Massey defining system on `E_(r-1)` representing the given `E_r`
classes. All products are the fixed representative-bound composition system,
and all five passage/differential conditions use this very internal tower. -/
def Relation (r : ℤ) (_hr : 3 ≤ r) {W X Y Z : C} {i j k : ℤ × ℤ}
    (x : (mappingSequence H.unit W Z).Page r (degree r i j k))
    (a : (mappingSequence H.unit W X).Page r i)
    (b : (mappingSequence H.unit X Y).Page r j)
    (c : (mappingSequence H.unit Y Z).Page r k) : Prop :=
  ∃ (a' : (mappingSequence H.unit W X).Page (r - 1) i)
      (b' : (mappingSequence H.unit X Y).Page (r - 1) j)
      (c' : (mappingSequence H.unit Y Z).Page (r - 1) k)
      (y : (mappingSequence H.unit W Y).Page (r - 1)
        (i + j - (r - 1, r - 2)))
      (z : (mappingSequence H.unit X Z).Page (r - 1)
        (j + k - (r - 1, r - 2))),
    Passage H.unit W X r i a' a ∧
    Passage H.unit X Y r j b' b ∧
    Passage H.unit Y Z r k c' c ∧
    precedingDifferential H.unit W Y r i j y =
      P.comp W X Y (r - 1) i j a' b' ∧
    precedingDifferential H.unit X Z r j k z =
      P.comp X Y Z (r - 1) j k b' c' ∧
    Passage H.unit W Z r (degree r i j k)
      (definingValue H R P W X Y Z r i j k a' c' y z) x

/-- The full additive indeterminacy on the same successor page: the sum
of the images of composition with the first and third entries. The two
free classes have precisely the degrees of the defining-system choices. -/
def Indeterminacy (r : ℤ) {W X Y Z : C} {i j k : ℤ × ℤ}
    (a : (mappingSequence H.unit W X).Page r i)
    (c : (mappingSequence H.unit Y Z).Page r k)
    (z : (mappingSequence H.unit W Z).Page r (degree r i j k)) : Prop :=
  ∃ (u : (mappingSequence H.unit W Y).Page r (i + j - (r - 1, r - 2)))
    (v : (mappingSequence H.unit X Z).Page r (j + k - (r - 1, r - 2))),
    z = pageCast H.unit W Z rfl (by unfold degree; abel)
        (P.comp W Y Z r (i + j - (r - 1, r - 2)) k u c) +
      pageCast H.unit W Z rfl (by unfold degree; abel)
        (P.comp W X Z r i (j + k - (r - 1, r - 2)) a v)

end
end KIP126.Classical.Adams.Moss.PageMassey
