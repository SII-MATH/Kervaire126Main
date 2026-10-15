module

public import KIP126.Def.Topology.Simplex.Combination.Proofs

@[expose] public section

namespace KIP126.Topology.Simplex

variable {A B : Type*} [Fintype A] [Fintype B]
variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- Pushing simplex weights forward and then taking their vector sum is
the same as taking the original vector sum with the repeated vertices. -/
theorem sum_smul_map (f : A → B) (t : stdSimplex ℝ A) (v : B → E) :
    (∑ b, stdSimplex.map f t b • v b) = ∑ a, t a • v (f a) := by
  classical
  change (∑ b, FunOnFinite.linearMap ℝ ℝ f t b • v b) = _
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_smul]
  calc
    _ = ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), t a • v (f a) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a, t a • v (f a) := Finset.sum_fiberwise Finset.univ f _

/-- Nested simplex combinations give exactly the same ambient vector as
the single combination with their combined coordinates. -/
theorem sum_smul_combinationCoordinates (q : A → stdSimplex ℝ B)
    (t : stdSimplex ℝ A) (v : B → E) :
    (∑ b, combinationCoordinates q t b • v b) =
      ∑ a, t a • ∑ b, q a b • v b := by
  simp only [combinationCoordinates, Finset.sum_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

end KIP126.Topology.Simplex
