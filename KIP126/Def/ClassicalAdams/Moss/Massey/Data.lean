module

public import KIP126.Def.ClassicalAdams.Moss.Composition.Pairing.Data
public import KIP126.Def.SpectralSequence.Permanence.Predicates

@[expose] public section

namespace KIP126.Classical.Adams.Moss.PageMassey

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C]
  {H : C} (unit : 𝟙_ C ⟶ H)

/-- Degree of a defining system on `E_(r-1)` and its class on `E_r`. -/
def degree (r : ℤ) (i j k : ℤ × ℤ) : ℤ × ℤ :=
  i + j + k - (r - 1, r - 2)

/-- Reindex only by the supplied equalities; no page comparison is chosen. -/
def pageCast (X Y : C) {r r' : ℤ} {i i' : ℤ × ℤ}
    (hr : r = r') (hi : i = i')
    (x : (mappingSequence unit X Y).Page r i) :
    (mappingSequence unit X Y).Page r' i' := by
  subst r'
  subst i'
  exact x

/-- The actual Adams differential, transported to a prescribed target degree. -/
def definingDifferential (X Y : C) (r : ℤ) (i j : ℤ × ℤ)
    (y : (mappingSequence unit X Y).Page r (i + j - (r, r - 1))) :
    (mappingSequence unit X Y).Page r (i + j) :=
  pageCast unit X Y rfl (by
    change i + j - (r, r - 1) + (r, r - 1) = i + j
    abel) ((mappingSequence unit X Y).d r _ y)

/-- The same differential on the preceding page, normalizing `(r-1)-1` to
`r-2` before elaborating a complete defining system. -/
def precedingDifferential (X Y : C) (r : ℤ) (i j : ℤ × ℤ)
    (y : (mappingSequence unit X Y).Page (r - 1)
      (i + j - (r - 1, r - 2))) :
    (mappingSequence unit X Y).Page (r - 1) (i + j) :=
  definingDifferential unit X Y (r - 1) i j
    (pageCast unit X Y rfl (by congr 2; omega) y)

variable [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated] [MonoidalPreadditive C]
  (P : CompositionPairing H R)

/-- `y c - (-1)^(stem a) a z`, expressed in the actual preceding page.
The subtraction convention is forced by the stem-signed Leibniz rule. -/
def definingValue (W X Y Z : C) (r : ℤ) (i j k : ℤ × ℤ)
    (a : (mappingSequence H.unit W X).Page (r - 1) i)
    (c : (mappingSequence H.unit Y Z).Page (r - 1) k)
    (y : (mappingSequence H.unit W Y).Page (r - 1)
      (i + j - (r - 1, r - 2)))
    (z : (mappingSequence H.unit X Z).Page (r - 1)
      (j + k - (r - 1, r - 2))) :
    (mappingSequence H.unit W Z).Page (r - 1) (degree r i j k) :=
  let left := pageCast H.unit W Z rfl (by unfold degree; abel)
    (P.comp W Y Z (r - 1) (i + j - (r - 1, r - 2)) k y c)
  let right := pageCast H.unit W Z rfl (by unfold degree; abel)
    (P.comp W X Z (r - 1) i (j + k - (r - 1, r - 2)) a z)
  if Even (i.2 - i.1) then left - right else left + right

end
end KIP126.Classical.Adams.Moss.PageMassey
