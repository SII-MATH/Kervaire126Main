module

public import Mathlib.Analysis.Convex.StdSimplex
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Proofs

@[expose] public section

section

namespace KIP126.Topology.Simplex

/-- Reindexing the original simplex coordinates is an actual
homeomorphism, including when the finite indexing universes differ. -/
noncomputable def reindexHomeomorph {P Q : Type*} [Fintype P] [Fintype Q]
    (e : P ≃ Q) : stdSimplex ℝ P ≃ₜ stdSimplex ℝ Q where
  toFun := stdSimplex.map e
  invFun := stdSimplex.map e.symm
  left_inv x := by
    rw [stdSimplex.map_comp_apply]
    have h : (e.symm : Q → P) ∘ e = id := funext e.symm_apply_apply
    rw [h,stdSimplex.map_id_apply]
  right_inv x := by
    rw [stdSimplex.map_comp_apply]
    have h : (e : P → Q) ∘ e.symm = id := funext e.apply_symm_apply
    rw [h,stdSimplex.map_id_apply]
  continuous_toFun := stdSimplex.continuous_map e
  continuous_invFun := stdSimplex.continuous_map e.symm

end KIP126.Topology.Simplex

end

section

namespace KIP126.Topology.Simplex
open KIP126.Topology.SimplicialRealization

/-- Reindexing retains the entire coordinate boundary, in both directions. -/
theorem reindexHomeomorph_boundary {P Q : Type*} [Fintype P] [Fintype Q]
    (e : P ≃ Q) (x : stdSimplex ℝ P) :
    (∃ p, x p = 0) ↔ ∃ q, reindexHomeomorph e x q = 0 := by
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨e p,?_⟩
    change stdSimplex.map e x (e p) = 0
    rw [simplex_map_apply_injective e e.injective]
    exact hp
  · rintro ⟨q,hq⟩
    obtain ⟨p,rfl⟩ := e.surjective q
    refine ⟨p,?_⟩
    change stdSimplex.map e x (e p) = 0 at hq
    rwa [simplex_map_apply_injective e e.injective] at hq

end KIP126.Topology.Simplex

end
