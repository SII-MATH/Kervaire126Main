module

public import KIP126.Def.ClassicalAdams.Moss.Convergence.Predicates

@[expose] public section

/-! Detection means equality in the associated graded of the actual tower filtration. -/

namespace KIP126.Classical.Adams.Moss

open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy

universe u v
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [MonoidalClosed C]
  {H : C} (unit : 𝟙_ C ⟶ H) (X Y : C)

/-- A finite-page class and an E∞ class have the same actual Z∞ representative. -/
def HasEInftyClass (r : ℤ) (k : ℤ × ℤ)
    (x : (mappingSequence unit X Y).Page r k)
    (e : ((mappingSequence unit X Y).ssData k).eInfty) : Prop :=
  let D := (mappingSequence unit X Y).ssData k
  let n : WithTop ℕ := ↑(r - 2).toNat
  ∃ z : (Subobject.underlying.obj (D.Z ⊤) : ModuleCat.{v} ℤ),
    (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n) z = x ∧
      D.pageπ ⊤ z = e

/-- A Z∞ representative, without an assertion that its E∞ image is nonzero. -/
def PermanentCycle (r : ℤ) (k : ℤ × ℤ)
    (x : (mappingSequence unit X Y).Page r k) : Prop :=
  ∃ e, HasEInftyClass unit X Y r k x e

/-- Detection in the associated graded, using the fixed convergence input. -/
def EInftyDetects (c : MappingAdamsConvergence unit X Y) (k : ℤ × ℤ)
    (e : ((mappingSequence unit X Y).ssData k).eInfty)
    (α : mappingAbutment X Y (k.2 - k.1)) : Prop :=
  ∃ a : (Subobject.underlying.obj
      ((mappingFiltration unit X Y).F k.1 (k.2 - k.1)) : ModuleCat.{v} ℤ),
    ((mappingFiltration unit X Y).F k.1 (k.2 - k.1)).arrow a = α ∧
    (c.identification k).hom e = (mappingFiltration unit X Y).toAssociatedGraded
      k.1 (k.2 - k.1) a

/-- A finite-page class detects a specified homotopy class of the actual mapping spectrum. -/
def DetectsAbutment (c : MappingAdamsConvergence unit X Y) (r : ℤ) (k : ℤ × ℤ)
    (x : (mappingSequence unit X Y).Page r k)
    (α : mappingAbutment X Y (k.2 - k.1)) : Prop :=
  ∃ e, HasEInftyClass unit X Y r k x e ∧ EInftyDetects unit X Y c k e α

/-- Detection of an actual stable morphism, via the selected closed adjunction. -/
def DetectsMap [(tensorLeft X).CommShift ℤ]
    (c : MappingAdamsConvergence unit X Y) (r : ℤ) (k : ℤ × ℤ)
    (x : (mappingSequence unit X Y).Page r k) (f : X⟦k.2 - k.1⟧ ⟶ Y) : Prop :=
  DetectsAbutment unit X Y c r k x ((mappingHomotopyEquiv X Y (k.2 - k.1)).symm f)

end
end KIP126.Classical.Adams.Moss
