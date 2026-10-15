module

public import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Data

@[expose] public section

namespace KIP126.SpectralSequence.FilteredComplex

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Solutions
variable {FC : FilteredComplex C} {T : C} {r s k : ℤ}
  {x : T ⟶ FC.assocGraded s k} {y : T ⟶ FC.assocGraded (s + r) (k - 1)}

theorem mem_fiber_iff (z : Representatives FC T r s k) :
    equation FC T r s k z = (x, y, 0) ↔
      FC.IsLift s k z.1 x ∧ FC.IsLift (s + r) (k - 1) z.2 y ∧
        z.1 ≫ (FC.fil s k).arrow ≫ FC.d k =
          z.2 ≫ (FC.fil (s + r) (k - 1)).arrow := by
  simp only [equation, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Prod.mk.injEq, sub_eq_zero, IsLift]

end Solutions
end KIP126.SpectralSequence.FilteredComplex
