module

public import KIP126.Def.Algebra.NestedQuotient.Data

@[expose] public section

namespace KIP126.Algebra.NestedQuotient

universe u v
variable {R : Type u} [Ring R] {A : Type v} [AddCommGroup A] [Module R A]
  {Z Z' Z'' B B' B'' : Submodule R A}

@[simp] theorem map_projection (hZ : Z ≤ Z') (hB : B ≤ B') (x : Z) :
    map hZ hB (projection Z B x) = projection Z' B' (Submodule.inclusion hZ x) := rfl

@[simp] theorem projection_eq_zero (x : Z) :
    projection Z B x = 0 ↔ x.val ∈ B := Submodule.Quotient.mk_eq_zero _

@[simp] theorem map_projection_eq_zero (hZ : Z ≤ Z') (hB : B ≤ B') (x : Z) :
    map hZ hB (projection Z B x) = 0 ↔ x.val ∈ B' :=
  projection_eq_zero (Submodule.inclusion hZ x)

theorem map_id : map (le_refl Z) (le_refl B) = LinearMap.id := by
  ext x
  rfl

theorem map_comp (hZ : Z ≤ Z') (hZ' : Z' ≤ Z'') (hB : B ≤ B') (hB' : B' ≤ B'') :
    (map hZ' hB').comp (map hZ hB) = map (hZ.trans hZ') (hB.trans hB') := by
  ext x
  rfl

/-- Increasing only the boundary cutoff is a surjective quotient map. -/
theorem boundary_map_surjective (hB : B ≤ B') :
    Function.Surjective (map (le_refl Z) hB) := by
  rintro ⟨x⟩
  exact ⟨projection Z B x, rfl⟩

/-- Increasing only the cycle submodule is injective on these subquotients. -/
theorem cycle_map_injective (hZ : Z ≤ Z') :
    Function.Injective (map hZ (le_refl B)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  rintro ⟨x⟩ hx
  change projection Z B x = 0
  exact (projection_eq_zero x).mpr ((map_projection_eq_zero hZ (le_refl B) x).mp hx)

end KIP126.Algebra.NestedQuotient
