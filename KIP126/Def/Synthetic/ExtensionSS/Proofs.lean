module

public import KIP126.Def.Synthetic.ExtensionSS.Data

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory KIP126.Synthetic.Context
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  {F : SyntheticAdamsFamily Syn} {X Y : Syn} {g : X ⟶ Y}

/-- The filtered two-term construction starts with the associated graded. -/
@[simp] theorem SyntheticExtensionData.ess_firstPage (D : SyntheticExtensionData F g)
    (degree : ℤ × ℤ) : (D.ess degree).r₀ = 0 := rfl

/-- Extension differentials preserve stem and weight and raise filtration
by n, moving from the source term to the target term. -/
@[simp] theorem SyntheticExtensionData.ess_diffDeg (D : SyntheticExtensionData F g)
    (degree : ℤ × ℤ) (n : ℤ) : (D.ess degree).diffDeg n = (n, -1) := rfl

theorem SyntheticExtensionData.target_index (D : SyntheticExtensionData F g)
    (degree : ℤ × ℤ) (n s : ℤ) :
    (s, 1) + (D.ess degree).diffDeg n = (s + n, 0) := by
  rw [D.ess_diffDeg]
  ext <;> simp

end KIP126.Synthetic.SpectralSequence
