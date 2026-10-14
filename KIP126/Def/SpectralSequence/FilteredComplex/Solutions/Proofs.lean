module

import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Data

@[expose] section

namespace KIP126.Core.SpectralSequence.FilteredComplex

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

/-- This fiber is exactly the existing strict representative relation. -/
theorem nonempty_fiber_iff (hr : 0 ≤ r) :
    Nonempty (Fiber FC r s k x y) ↔ FC.RepresentativeRelation r hr s k x y := by
  constructor
  · rintro ⟨⟨z, hz⟩⟩
    obtain ⟨hx, hy, hd⟩ := (mem_fiber_iff z).mp hz
    refine ⟨z.1, z.2, hx, hy, ?_⟩
    apply (cancel_mono (FC.fil s (k - 1)).arrow).mp
    simpa only [Category.assoc, filDiff, fil, d,
      (FC.differential_preserves s k).choose_spec,
      Algebra.Filtration.inclusion_arrow] using hd
  · rintro ⟨xl, yl, hx, hy, hd⟩
    refine ⟨⟨(xl, yl), (mem_fiber_iff _).mpr ⟨hx, hy, ?_⟩⟩⟩
    have h := congrArg (fun a => a ≫ (FC.fil s (k - 1)).arrow) hd
    simpa only [Category.assoc, filDiff, fil, d,
      (FC.differential_preserves s k).choose_spec,
      Algebra.Filtration.inclusion_arrow] using h

/-- Differences between solutions are actual homogeneous representative equations. -/
theorem sub_mem_differences (a b : Fiber FC r s k x y) :
    a.val - b.val ∈ differences FC T r s k := by
  change equation FC T r s k (a.val - b.val) = 0
  rw [map_sub, a.property, b.property, sub_self]

theorem add_mem_fiber (g : differences FC T r s k) (a : Fiber FC r s k x y) :
    equation FC T r s k (g.val + a.val) = (x, y, 0) := by
  rw [map_add, show equation FC T r s k g.val = 0 from g.property,
    zero_add, a.property]

end Solutions
end KIP126.Core.SpectralSequence.FilteredComplex
