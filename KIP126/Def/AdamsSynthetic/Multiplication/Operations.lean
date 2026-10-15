module

public import KIP126.Def.Synthetic.Sphere.Actions.Data
public import Mathlib.CategoryTheory.Monoidal.Mon

@[expose] public section

/-! Homotopy multiplication induced by a specified monoid object.
This is the single operation used by quotient algebras and their comparisons. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.Synthetic.Context
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- Product induced by the specified actual monoid object. The factor order
matches sphereAction: its first input acts on the second input. -/
def algebraProduct {A : Syn} (Q : MonObj A) {m n k l : ℤ}
    (x : BiHom m n A) (y : BiHom k l A) : BiHom (m+k) (n+l) A :=
  (SyntheticCategory.biShift_comp (m,n) (k,l)).inv.app S_0_0 ≫
    (biShift_eq_tensor_Smn k l (Smn m n)).hom ≫ (y ⊗ₘ x) ≫ Q.mul

end
end KIP126.AdamsSynthetic
