module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Top.Data

@[expose] public section

/-! At top weight the boundary cutoff is one, whose actual E₂ boundary
submodule is zero. The existing top-class maps therefore lose no labels. -/

namespace KIP126.Classical.Adams.PageRepresentatives

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Algebra

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (X : C)

/-- The finite top-weight class retains exactly the original cycle label,
including the arithmetically equal cycle cutoff in the codomain. -/
theorem finiteTopClass_bijective (q : ℕ) (p : ℤ × ℤ) :
    Function.Bijective (finiteTopClass H X q p) := by
  constructor
  · apply (injective_iff_map_eq_zero (finiteTopClass H X q p)).mpr
    intro z hz
    have hz' := (NestedQuotient.projection_eq_zero
      (B := boundaries H X (1 + p.2 - p.2) p)
      (Submodule.inclusion (show cycles H X q p ≤
        cycles H X (q - p.2 + p.2) p by rw [sub_add_cancel]) z)).mp hz
    apply Subtype.ext
    simpa only [add_sub_cancel_right, boundaries_one, Submodule.mem_bot,
      Submodule.inclusion_apply, Submodule.coe_zero] using hz'
  · rintro ⟨z⟩
    refine ⟨⟨z.val, ?_⟩, rfl⟩
    simpa only [sub_add_cancel] using z.property

/-- The permanent top-weight class is the quotient by the same zero boundary
submodule, so every class has exactly one permanent-cycle label. -/
theorem permanentTopClass_bijective (p : ℤ × ℤ) :
    Function.Bijective (permanentTopClass H X p) := by
  constructor
  · apply (injective_iff_map_eq_zero (permanentTopClass H X p)).mpr
    intro z hz
    have hz' := (NestedQuotient.projection_eq_zero
      (B := boundaries H X (1 + p.2 - p.2) p) z).mp hz
    apply Subtype.ext
    simpa only [add_sub_cancel_right, boundaries_one, Submodule.mem_bot,
      Submodule.coe_zero] using hz'
  · rintro ⟨z⟩
    exact ⟨z, rfl⟩

end KIP126.Classical.Adams.PageRepresentatives
