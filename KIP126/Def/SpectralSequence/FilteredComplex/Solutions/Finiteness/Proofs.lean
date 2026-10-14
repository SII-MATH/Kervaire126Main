module

import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Proofs

@[expose] section

/-! A strict solution is determined by its source representative. The target
representative is fixed by the differential and its subobject inclusion. -/

namespace KIP126.Core.SpectralSequence.FilteredComplex.Solutions

open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {FC : FilteredComplex C} {T : C} {r s k : ℤ}
  {x : T ⟶ FC.assocGraded s k} {y : T ⟶ FC.assocGraded (s + r) (k - 1)}

theorem source_ambient_injective :
    Function.Injective (fun a : Fiber FC r s k x y =>
      a.val.1 ≫ (FC.fil s k).arrow) := by
  intro a b hab
  have hfirst : a.val.1 = b.val.1 := (cancel_mono _).mp hab
  have ha := ((mem_fiber_iff a.val).mp a.property).2.2
  have hb := ((mem_fiber_iff b.val).mp b.property).2.2
  have hsecond : a.val.2 = b.val.2 := by
    apply (cancel_mono (FC.fil (s + r) (k - 1)).arrow).mp
    rw [← ha, ← hb, hfirst]
  exact Subtype.ext (Prod.ext hfirst hsecond)

/-- Only the source ambient Hom needs to be finite. No target finiteness or
nonemptiness of the solution fiber is required. -/
theorem finite_of_finite_source_hom [Finite (T ⟶ FC.A k)] :
    Finite (Fiber FC r s k x y) :=
  Finite.of_injective _ source_ambient_injective

end KIP126.Core.SpectralSequence.FilteredComplex.Solutions
