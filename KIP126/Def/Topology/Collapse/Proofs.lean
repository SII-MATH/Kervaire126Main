module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Compactness.LocallyCompact

@[expose] public section

namespace KIP126.Topology

open Set Topology
open scoped OnePoint

/-- Collapsing a nonempty closed subset of a compact Hausdorff space gives
the one-point compactification of its complement, with the actual quotient
and the collapsed point specified. -/
theorem exists_collapse_homeomorph_onePoint
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (S : Set X) (hS : IsClosed S) (x₀ : S) :
    ∃ e : Quot (fun x y : X => x ∈ S ∧ y ∈ S) ≃ₜ OnePoint (Sᶜ : Set X),
      e (Quot.mk _ x₀.val) = ∞ ∧
      ∀ x : (Sᶜ : Set X), e (Quot.mk _ x.val) = (x : OnePoint (Sᶜ : Set X)) := by
  classical
  letI := hS.isOpen_compl.locallyCompactSpace
  let f : X → OnePoint (Sᶜ : Set X) := fun x =>
    if hx : x ∈ S then ∞ else (⟨x, hx⟩ : (Sᶜ : Set X))
  have hfS (x : X) (hx : x ∈ S) : f x = ∞ := dif_pos hx
  have hfC (x : (Sᶜ : Set X)) : f x.val = (x : OnePoint (Sᶜ : Set X)) := by
    simp only [f, dif_neg x.property]
  have hc : Continuous f := by
    apply continuous_def.mpr
    intro U hU
    by_cases hinfty : ∞ ∈ U
    · have hK := (OnePoint.isOpen_iff_of_mem hinfty).mp hU
      have he : f ⁻¹' U = (Subtype.val ''
          (((↑) : (Sᶜ : Set X) → OnePoint (Sᶜ : Set X)) ⁻¹' U)ᶜ)ᶜ := by
        ext x
        by_cases hx : x ∈ S
        · simp [hfS x hx, hinfty, hx]
        · simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_image]
          rw [show f x = (⟨x, hx⟩ : (Sᶜ : Set X)) from dif_neg hx]
          constructor
          · intro hu ⟨y, hy, hyx⟩
            have : y = ⟨x, hx⟩ := Subtype.ext hyx
            exact hy (this ▸ hu)
          · intro hu
            by_contra hn
            exact hu ⟨⟨x, hx⟩, hn, rfl⟩
      rw [he]
      exact (hK.2.image continuous_subtype_val).isClosed.isOpen_compl
    · have he : f ⁻¹' U = Subtype.val ''
          (((↑) : (Sᶜ : Set X) → OnePoint (Sᶜ : Set X)) ⁻¹' U) := by
        ext x
        by_cases hx : x ∈ S
        · simp [hfS x hx, hinfty, hx]
        · simp only [Set.mem_preimage, Set.mem_image]
          rw [show f x = (⟨x, hx⟩ : (Sᶜ : Set X)) from dif_neg hx]
          constructor
          · intro hu
            exact ⟨⟨x, hx⟩, hu, rfl⟩
          · rintro ⟨y, hy, hyx⟩
            have : y = ⟨x, hx⟩ := Subtype.ext hyx
            exact this ▸ hy
      rw [he]
      exact hS.isOpen_compl.isOpenMap_subtype_val _
        ((OnePoint.isOpen_iff_of_notMem hinfty).mp hU)
  have hr : ∀ x y, (x ∈ S ∧ y ∈ S) → f x = f y := by
    intro x y h
    rw [hfS x h.1, hfS y h.2]
  let e : Quot (fun x y : X => x ∈ S ∧ y ∈ S) ≃ OnePoint (Sᶜ : Set X) :=
    { toFun := Quot.lift f hr
      invFun := fun y => y.elim (Quot.mk _ x₀.val) (fun x => Quot.mk _ x.val)
      left_inv := by
        intro q
        induction q using Quot.inductionOn with
        | h x =>
          by_cases hx : x ∈ S
          · change OnePoint.elim (f x) _ _ = _
            rw [hfS x hx]
            exact Quot.sound ⟨x₀.property, hx⟩
          · change OnePoint.elim (f x) _ _ = _
            rw [show f x = (⟨x, hx⟩ : (Sᶜ : Set X)) from dif_neg hx]
            rfl
      right_inv := by
        intro y
        induction y using OnePoint.rec with
        | infty => exact hfS x₀.val x₀.property
        | coe y => exact hfC y }
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := e) (continuous_quot_lift hr hc),
    hfS x₀.val x₀.property, hfC⟩

end KIP126.Topology
