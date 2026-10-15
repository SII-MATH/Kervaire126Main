module

public import KIP126.Def.Topology.Simplex.Combination.Data

@[expose] public section

namespace KIP126.Topology.Simplex

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- Barycentric combinations have nonnegative coordinates. -/
theorem combinationCoordinates_nonneg (v : A → stdSimplex ℝ B)
    (t : stdSimplex ℝ A) (b : B) : 0 ≤ combinationCoordinates v t b :=
  Finset.sum_nonneg fun a _ => mul_nonneg (t.property.1 a) ((v a).property.1 b)

/-- A barycentric combination has total mass one. -/
theorem combinationCoordinates_sum (v : A → stdSimplex ℝ B)
    (t : stdSimplex ℝ A) : ∑ b, combinationCoordinates v t b = 1 := by
  unfold combinationCoordinates
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,stdSimplex.sum_eq_one,mul_one]

/-- Barycentric combination depends continuously on the weights. -/
theorem continuous_combinationCoordinates (v : A → stdSimplex ℝ B) :
    Continuous (combinationCoordinates v) := by
  apply continuous_pi
  intro b
  exact continuous_finsetSum _ fun a _ =>
    ((continuous_apply a).comp continuous_subtype_val).mul continuous_const

/-- Combining after aggregating weights is the same as repeating the
corresponding vertices. This includes repeated vertices and hence
simplicial degeneracies. -/
theorem combinationCoordinates_map (f : A → B) (v : B → stdSimplex ℝ C)
    (t : stdSimplex ℝ A) :
    combinationCoordinates v (stdSimplex.map f t) = combinationCoordinates (v ∘ f) t := by
  classical
  funext c
  change ∑ b, FunOnFinite.linearMap ℝ ℝ f t b * v b c = _
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_mul]
  calc
    _ = ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), t a * v (f a) c := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a, t a * v (f a) c := Finset.sum_fiberwise Finset.univ f _
    _ = _ := rfl

/-- Pushing forward a barycentric combination agrees with combining the
pushed-forward vertices. -/
theorem combinationCoordinates_map_target (f : B → C) (v : A → stdSimplex ℝ B)
    (t : stdSimplex ℝ A) :
    FunOnFinite.linearMap ℝ ℝ f (combinationCoordinates v t) =
      combinationCoordinates (fun a => stdSimplex.map f (v a)) t := by
  classical
  funext c
  change FunOnFinite.linearMap ℝ ℝ f (combinationCoordinates v t) c =
    ∑ a, t a * FunOnFinite.linearMap ℝ ℝ f (v a) c
  simp only [FunOnFinite.linearMap_apply_apply,combinationCoordinates]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- A barycentric combination of points on one face stays on that face. -/
theorem combinationCoordinates_zero (v : A → stdSimplex ℝ B)
    (t : stdSimplex ℝ A) (b : B) (hv : ∀ a, v a b = 0) :
    combinationCoordinates v t b = 0 := by
  simp [combinationCoordinates,hv]

/-- A coordinate of a convex combination vanishes exactly when each
vertex carrying nonzero weight has that coordinate zero. -/
theorem combinationCoordinates_eq_zero_iff (v : A → stdSimplex ℝ B)
    (t : stdSimplex ℝ A) (b : B) :
    combinationCoordinates v t b = 0 ↔ ∀ a, t a = 0 ∨ v a b = 0 := by
  rw [combinationCoordinates,Finset.sum_eq_zero_iff_of_nonneg]
  · simp only [Finset.mem_univ,true_implies,mul_eq_zero]
  · intro a _
    exact mul_nonneg (t.property.1 a) ((v a).property.1 b)

/-- Unit weight at a vertex recovers the specified point exactly. -/
theorem combinationCoordinates_vertex (v : A → stdSimplex ℝ B) [DecidableEq A] (a : A) :
    combinationCoordinates v (stdSimplex.vertex a) = (v a).val := by
  classical
  funext b
  simp [combinationCoordinates,stdSimplex.vertex,Pi.single_apply]
  rfl

end KIP126.Topology.Simplex
