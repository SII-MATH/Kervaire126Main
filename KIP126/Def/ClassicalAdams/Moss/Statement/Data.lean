module

public import KIP126.Def.ClassicalAdams.Moss.Massey.Data
public import KIP126.Def.ClassicalAdams.Moss.Detection.Predicates
public import KIP126.Def.StableHomotopy.Toda.Predicates

@[expose] public section

namespace KIP126.Classical.Adams.Moss

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C]
  [∀ A : C, (tensorLeft A).CommShift ℤ]

/-- Stem convention used by both the page signs and the stable composites. -/
def stem (k : ℤ × ℤ) : ℤ := k.2 - k.1

/-- The fixed closed-adjunction interpretation of a mapping abutment element. -/
def abutmentMap (X Y : C) (k : ℤ × ℤ)
    (a : mappingAbutment X Y (stem k)) : X⟦stem k⟧ ⟶ Y :=
  mappingHomotopyEquiv X Y (stem k) a

/-- Suspend the actual stable map using the selected shift-composition iso. -/
def shiftMap (X Y : C) (k : ℤ × ℤ) (n : ℤ)
    (a : mappingAbutment X Y (stem k)) : X⟦stem k + n⟧ ⟶ Y⟦n⟧ :=
  (shiftFunctorAdd C (stem k) n).hom.app X ≫
    (shiftFunctor C n).map (abutmentMap X Y k a)

/-- The abutment product is the actual stable composite; no abutment pairing
is selected independently of the mapping objects. -/
def abutmentComposition (X Y Z : C) (i j : ℤ × ℤ)
    (a : mappingAbutment X Y (stem i)) (b : mappingAbutment Y Z (stem j)) :
    mappingAbutment X Z (stem (i + j)) :=
  (mappingHomotopyEquiv X Z (stem (i + j))).symm
    (eqToHom (congrArg (fun n : ℤ => X⟦n⟧) (by
      dsimp [stem]
      omega : stem (i + j) = stem i + stem j)) ≫
      shiftMap X Y i (stem j) a ≫ abutmentMap Y Z j b)

/-- Convert the detected Massey class to the suspended-source morphism in
the already defined cone-based Toda relation. -/
def todaMap (r : ℤ) (W Z : C) (i j k : ℤ × ℤ)
    (a : mappingAbutment W Z (stem (PageMassey.degree r i j k))) :
    (W⟦stem i + (stem j + stem k)⟧)⟦(1 : ℤ)⟧ ⟶ Z :=
  (shiftFunctorAdd C (stem i + (stem j + stem k)) 1).inv.app W ≫
    eqToHom (congrArg (fun n : ℤ => W⟦n⟧) (by
      dsimp [stem, PageMassey.degree]
      omega : stem i + (stem j + stem k) + 1 =
        stem (PageMassey.degree r i j k))) ≫
      abutmentMap W Z (PageMassey.degree r i j k) a

end
end KIP126.Classical.Adams.Moss
