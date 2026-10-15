module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Simplicial.Proofs
public import KIP126.Def.Topology.SimplicialRealization.CompactlyGenerated.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Relative.Proofs
public import KIP126.Def.StableHomotopy.Spectra.PointSet

@[expose] public section

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory Simplicial Opposite

set_option backward.isDefEq.respectTransparency false

/-- The fixed Dold--Kan realization levels are compactly generated,
by the actual simplex-colimit topology. -/
theorem hf2RealizationLevel_uCompactlyGeneratedSpace (n : ℕ) :
    UCompactlyGeneratedSpace.{0} (hf2RealizationLevel n) :=
  KIP126.Topology.SimplicialRealization.realization_uCompactlyGeneratedSpace _

/-- Every actual simplicial skeleton of the specified coefficient level
has compact realization, using its proved finite sets of simplices. -/
theorem hf2RealizationLevel_compactSpace_skeleton (n k : ℕ) :
    CompactSpace (KIP126.Topology.SimplicialRealization.skeleton (hf2SimplicialSet n) k) :=
  KIP126.Topology.SimplicialRealization.compactSpace_skeleton _ k
    (hf2SimplicialSet_finite n)

/-- The actual zero vertex of each geometric coefficient level is a
closed point inclusion with full homotopy extension. -/
theorem hf2RealizationLevel_isWellBased (n : ℕ) :
    (hf2RealizationLevel n).IsWellBased := by
  let x : (hf2SimplicialSet n).obj (op ⦋0⦌) :=
    (0 : (hf2SimplicialModule n).obj (op ⦋0⦌))
  have hx : SSet.toTop.map (SSet.const x : Δ[0] ⟶ hf2SimplicialSet n) default =
      (hf2RealizationLevel n).point :=
    KIP126.Topology.SimplicialRealization.realization_vertex_eq_unit (hf2SimplicialSet n) x
  constructor
  · rw [← hx]
    exact KIP126.Topology.SimplicialRealization.vertex_isClosed (hf2SimplicialSet n) x
  · intro Y f p hp
    obtain ⟨H,hH0,hHi⟩ := KIP126.Topology.SimplicialRealization.vertex_homotopy_extension
      (hf2SimplicialSet n) x Y f p (by rw [hx]; exact hp)
    rw [hx] at hHi
    exact ⟨H,hH0,hHi⟩

end KIP126.StableHomotopy.Spectra
