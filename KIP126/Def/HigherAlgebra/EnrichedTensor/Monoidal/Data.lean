module

public import KIP126.Def.HigherAlgebra.EnrichedTensor.Data

@[expose] public section

/-!
Concrete low-arity comparison paths for a finite tensor presentation. These
paths permit its coherence to be bound to the already chosen associator and
unitors of the model category. Labels and transports are explicit; there is no
second choice of tensor operations or of monoidal coherence in this file.
-/

namespace KIP126.HigherAlgebra.EnrichedTensor

open CategoryTheory MonoidalCategory Operad

universe u v

/-- The two blocks describing a left unit: empty, then singleton. -/
abbrev leftUnitBlocks : two → FintypeCat.{0}
  | false => empty
  | true => Arity.one

/-- The two blocks describing a right unit: singleton, then empty. -/
abbrev rightUnitBlocks : two → FintypeCat.{0}
  | false => Arity.one
  | true => empty

/-- The actual sole remaining label in the empty/singleton decomposition. -/
def leftUnitLabels : Arity.sum two leftUnitBlocks ≃ Arity.one where
  toFun _ := PUnit.unit
  invFun _ := ⟨true, PUnit.unit⟩
  left_inv := by
    rintro ⟨b, i⟩
    cases b
    · exact PEmpty.elim i
    · cases i
      rfl
  right_inv := by intro i; cases i; rfl

/-- The actual sole remaining label in the singleton/empty decomposition. -/
def rightUnitLabels : Arity.sum two rightUnitBlocks ≃ Arity.one where
  toFun _ := PUnit.unit
  invFun _ := ⟨false, PUnit.unit⟩
  left_inv := by
    rintro ⟨b, i⟩
    cases b
    · cases i
      rfl
    · exact PEmpty.elim i
  right_inv := by intro i; cases i; rfl

/-- Two inputs in the left block and one in the right block. -/
abbrev ternaryLeftBlocks : two → FintypeCat.{0}
  | false => two
  | true => Arity.one

/-- One input in the left block and two in the right block. -/
abbrev ternaryRightBlocks : two → FintypeCat.{0}
  | false => Arity.one
  | true => two

/-- The label bijection `(x,y),z ↔ x,(y,z)` used to compare with the model's
actual associator; it preserves the order of all three inputs. -/
def associatorLabels :
    Arity.sum two ternaryLeftBlocks ≃ Arity.sum two ternaryRightBlocks where
  toFun
    | ⟨false, false⟩ => ⟨false, PUnit.unit⟩
    | ⟨false, true⟩ => ⟨true, false⟩
    | ⟨true, _⟩ => ⟨true, true⟩
  invFun
    | ⟨false, _⟩ => ⟨false, false⟩
    | ⟨true, false⟩ => ⟨false, true⟩
    | ⟨true, true⟩ => ⟨true, PUnit.unit⟩
  left_inv := by
    rintro ⟨b, i⟩
    cases b <;> cases i <;> rfl
  right_inv := by
    rintro ⟨b, i⟩
    cases b <;> cases i <;> rfl

variable {M : Type u} [Category.{v} M] [MonoidalCategory M]
  [EnrichedOrdinaryCategory TopCat.{v} M]

/-- Actual colours of the three inputs in the left block decomposition. -/
def ternaryLeftInputs (X Y Z : M) : (b : two) → ternaryLeftBlocks b → M
  | false, false => X
  | false, true => Y
  | true, _ => Z

/-- Actual colours of the three inputs in the right block decomposition. -/
def ternaryRightInputs (X Y Z : M) : (b : two) → ternaryRightBlocks b → M
  | false, _ => X
  | true, false => Y
  | true, true => Z

namespace Presentation

variable (P : Presentation M)

/-- The empty/singleton maps used by the left-unit comparison path. -/
def leftUnitBlockMap (X : M) : (b : two) →
    P.tensorObj (leftUnitBlocks b) (fun _ => X) ⟶ cond b X (𝟙_ M)
  | false => (P.emptyIso (fun _ => X)).hom
  | true => (P.oneIso (fun _ => X)).hom

/-- Flatten, compare each block, and apply the *existing* left unitor. -/
def leftUnitCollapse (X : M) :
    P.tensorObj (Arity.sum two leftUnitBlocks) (fun _ => X) ⟶ X :=
  (P.flatten two leftUnitBlocks (fun _ _ => X)).hom ≫
    P.map two (P.leftUnitBlockMap X) ≫
    (P.binaryIso (fun b => cond b X (𝟙_ M))).hom ≫ (λ_ X).hom

/-- The singleton/empty maps used by the right-unit comparison path. -/
def rightUnitBlockMap (X : M) : (b : two) →
    P.tensorObj (rightUnitBlocks b) (fun _ => X) ⟶ cond b (𝟙_ M) X
  | false => (P.oneIso (fun _ => X)).hom
  | true => (P.emptyIso (fun _ => X)).hom

/-- Flatten, compare each block, and apply the *existing* right unitor. -/
def rightUnitCollapse (X : M) :
    P.tensorObj (Arity.sum two rightUnitBlocks) (fun _ => X) ⟶ X :=
  (P.flatten two rightUnitBlocks (fun _ _ => X)).hom ≫
    P.map two (P.rightUnitBlockMap X) ≫
    (P.binaryIso (fun b => cond b (𝟙_ M) X)).hom ≫ (ρ_ X).hom

/-- Binary/singleton comparisons for the left-associated threefold tensor. -/
def ternaryLeftBlockMap (X Y Z : M) : (b : two) →
    P.tensorObj (ternaryLeftBlocks b) (ternaryLeftInputs X Y Z b) ⟶
      cond b Z (X ⊗ Y)
  | false => (P.binaryIso (ternaryLeftInputs X Y Z false)).hom
  | true => (P.oneIso (fun _ => Z)).hom

/-- The actual comparison to `(X ⊗ Y) ⊗ Z`. -/
def ternaryLeftCollapse (X Y Z : M) :
    P.tensorObj (Arity.sum two ternaryLeftBlocks)
      (fun ij => ternaryLeftInputs X Y Z ij.1 ij.2) ⟶ (X ⊗ Y) ⊗ Z :=
  (P.flatten two ternaryLeftBlocks (ternaryLeftInputs X Y Z)).hom ≫
    P.map two (P.ternaryLeftBlockMap X Y Z) ≫
    (P.binaryIso (fun b => cond b Z (X ⊗ Y))).hom

/-- Singleton/binary comparisons for the right-associated threefold tensor. -/
def ternaryRightBlockMap (X Y Z : M) : (b : two) →
    P.tensorObj (ternaryRightBlocks b) (ternaryRightInputs X Y Z b) ⟶
      cond b (Y ⊗ Z) X
  | false => (P.oneIso (fun _ => X)).hom
  | true => (P.binaryIso (ternaryRightInputs X Y Z true)).hom

/-- The actual comparison to `X ⊗ (Y ⊗ Z)`. -/
def ternaryRightCollapse (X Y Z : M) :
    P.tensorObj (Arity.sum two ternaryRightBlocks)
      (fun ij => ternaryRightInputs X Y Z ij.1 ij.2) ⟶ X ⊗ (Y ⊗ Z) :=
  (P.flatten two ternaryRightBlocks (ternaryRightInputs X Y Z)).hom ≫
    P.map two (P.ternaryRightBlockMap X Y Z) ≫
    (P.binaryIso (fun b => cond b (Y ⊗ Z) X)).hom

/-- Relabelling the three inputs, with the equality of the colour functions
transported explicitly before applying the given tensor comparison. -/
def ternaryRelabel (X Y Z : M) :
    P.tensorObj (Arity.sum two ternaryLeftBlocks)
      (fun ij => ternaryLeftInputs X Y Z ij.1 ij.2) ⟶
    P.tensorObj (Arity.sum two ternaryRightBlocks)
      (fun ij => ternaryRightInputs X Y Z ij.1 ij.2) :=
  eqToHom (congrArg (P.tensorObj (Arity.sum two ternaryLeftBlocks)) (by
    funext ij
    rcases ij with ⟨b, i⟩
    cases b <;> cases i <;> rfl)) ≫
    (P.tensorRelabel associatorLabels
      (fun ij => ternaryRightInputs X Y Z ij.1 ij.2)).hom

end Presentation
end KIP126.HigherAlgebra.EnrichedTensor
