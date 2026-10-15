module

public import KIP126.Def.Synthetic.Sphere.Data

@[expose] public section

/-!
The actual reindexing maps for suspended bigraded Hom. These use the existing
fully faithful bigraded shifts and their specified composition and ordinary
suspension comparisons; no new suspension or Hom map is chosen.
-/

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- Compare the combined bigraded shift with the ordinary suspension of the
specified vertical shift, using the existing composition and compatibility. -/
noncomputable def biSuspensionIso (q : ℤ) (Q : Syn) :
    (SyntheticCategory.biShift (1, -q)).obj Q ≅
      ((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧ := by
  have h : ((0 : ℤ), -q) + (1, 0) = (1, -q) := by
    ext <;> simp
  simpa only [h] using
    ((SyntheticCategory.biShift_comp (0, -q) (1, 0)).symm.app Q ≪≫
      (SyntheticCategory.biShift_compat (Syn := Syn) 1).app
        ((SyntheticCategory.biShift (0, -q)).obj Q))

/-- The underlying equivalence for the Bockstein landing degree. It is the
inverse of the existing suspension invariance, followed by the specified
ordinary-suspension comparison and the integer degree equalities. -/
noncomputable def biSuspensionHomUnderlyingEquiv (n w q : ℤ) (Q : Syn) :
    BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) ≃
      BiHom (n - 1) (w + q) Q := by
  let e : BiHom (n - 1) (w + q) Q ≃
      BiHom n w (((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧) := by
    simpa only [sub_add_cancel, add_neg_cancel_right] using
      ((susp_invariance (n - 1) (w + q) 1 (-q) Q).trans
        (Iso.homCongr (Iso.refl _) (biSuspensionIso q Q)))
  exact e.symm

end KIP126.Synthetic.Context
