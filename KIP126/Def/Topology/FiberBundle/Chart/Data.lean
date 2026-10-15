module

public import Mathlib.Topology.FiberBundle.Trivialization
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

namespace KIP126.Topology.FiberBundle

open Set

variable {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]

/-- Actual product coordinates on an open inverse image give a bundle
trivialization with precisely that open base set. -/
noncomputable def trivializationOfOpenProduct (p : C(E, B)) (U : Set B) (hU : IsOpen U)
    [Nonempty (p ⁻¹' U)] (e : (p ⁻¹' U) ≃ₜ U × F)
    (he : ∀ z, (e z).1.val = p z.val) : Bundle.Trivialization F p := by
  let S : TopologicalSpace.Opens E := ⟨p ⁻¹' U, hU.preimage p.continuous⟩
  let V : TopologicalSpace.Opens B := ⟨U, hU⟩
  have hS : Nonempty S := inferInstanceAs (Nonempty (p ⁻¹' U))
  have hV : Nonempty V := hS.map (fun z => ⟨p z.val, z.property⟩)
  let j := S.openPartialHomeomorphSubtypeCoe hS
  let k := (V.openPartialHomeomorphSubtypeCoe hV).prod (OpenPartialHomeomorph.refl F)
  let l := (j.symm.trans e.toOpenPartialHomeomorph).trans k
  have hsource : l.source = p ⁻¹' U := by
    simp [l, j, k, S]
  have htarget : l.target = U ×ˢ Set.univ := by
    simp [l, j, k, V]
  refine { toOpenPartialHomeomorph := l
           baseSet := U
           open_baseSet := hU
           source_eq := hsource
           target_eq := htarget
           proj_toFun := ?_ }
  intro x hx
  change (e (j.symm x)).1.val = p x
  rw [he]
  apply congrArg p
  exact j.right_inv (by rw [hsource] at hx; simpa [j, S] using hx)

end KIP126.Topology.FiberBundle
