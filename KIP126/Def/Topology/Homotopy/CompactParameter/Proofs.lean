module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

namespace KIP126.Topology.Homotopy

open Set Filter _root_.Topology

/-- A compact parameter may vary arbitrarily at a point where the entire
continuous family has the same value. This retains continuity of the actual
output even when the chosen time function is discontinuous there. -/
theorem continuousAt_comp_arbitrary_compact_parameter
    {Z X K Y : Type*} [TopologicalSpace Z] [TopologicalSpace X]
    [TopologicalSpace K] [TopologicalSpace Y] [CompactSpace K]
    (H : C(X × K,Y)) (f : Z → X) (g : Z → K) (z : Z)
    (hf : ContinuousAt f z) (hconst : ∀ k, H (f z,k) = H (f z,g z)) :
    ContinuousAt (fun w => H (f w,g w)) z := by
  apply tendsto_nhds.mpr
  intro U hU hz
  have hsub : ({f z} : Set X) ×ˢ (univ : Set K) ⊆ H ⁻¹' U := by
    rintro ⟨x,k⟩ ⟨hx,_⟩
    rcases mem_singleton_iff.mp hx with rfl
    change H (f z,k) ∈ U
    rw [hconst]
    exact hz
  obtain ⟨V,W,hV,_,hx,hK,hVW⟩ := generalized_tube_lemma
    isCompact_singleton isCompact_univ (hU.preimage H.continuous) hsub
  have hVmem : V ∈ 𝓝 (f z) := hV.mem_nhds (hx (mem_singleton _))
  exact Filter.mem_of_superset (hf hVmem) (fun w hw => hVW ⟨hw,hK (mem_univ _)⟩)

end KIP126.Topology.Homotopy
