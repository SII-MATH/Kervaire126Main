module

public import KIP126.Def.Topology.Simplex.ClosedBall.Data
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FunProp

@[expose] public section

namespace KIP126.Topology.Simplex

open Set Metric Bornology
open scoped BigOperators Topology

/-- The coordinate simplex is closed. -/
theorem coordinateSimplex_isClosed (n : ℕ) : IsClosed (coordinateSimplex n) := by
  have he : coordinateSimplex n = (⋂ i : Fin n, {x | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
    ext x
    simp [coordinateSimplex]
  rw [he]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

/-- The coordinate simplex is convex in its full-dimensional ambient space. -/
theorem coordinateSimplex_convex (n : ℕ) : Convex ℝ (coordinateSimplex n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.2), mul_nonneg hb (sub_nonneg.mpr hy.2)]

/-- Its coordinate bounds make the simplex bounded. -/
theorem coordinateSimplex_isBounded (n : ℕ) : IsBounded (coordinateSimplex n) := by
  apply (isCompact_Icc : IsCompact (Icc (0 : Fin n → ℝ) 1)).isBounded.subset
  intro x hx
  refine ⟨hx.1, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

/-- The interior consists exactly of positive retained coordinates with
strictly positive omitted coordinate. -/
theorem coordinateSimplex_interior (n : ℕ) :
    interior (coordinateSimplex n) = {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
  cases n with
  | zero =>
    have he : coordinateSimplex 0 = Set.univ := by ext x; simp [coordinateSimplex]
    simp [he]
  | succ n =>
    let s : (Fin (n+1) → ℝ) →L[ℝ] ℝ :=
      { toFun := fun x => ∑ i, x i
        map_add' := by intros; simp [Finset.sum_add_distrib]
        map_smul' := by intros; simp [Finset.mul_sum]
        cont := continuous_finsetSum _ fun i _ => continuous_apply i }
    have hs : Function.Surjective s := by
      intro a
      exact ⟨Pi.single 0 a, by simp [s]⟩
    have he : coordinateSimplex (n+1) =
        (⋂ i : Fin (n+1), (fun x : Fin (n+1) → ℝ => x i) ⁻¹' Ici 0) ∩ s ⁻¹' Iic 1 := by
      ext x
      simp [coordinateSimplex, s]
    rw [he, interior_inter, interior_iInter_of_finite]
    simp_rw [← IsOpenMap.preimage_interior_eq_interior_preimage
      (isOpenMap_eval _) (continuous_apply _), interior_Ici,
      ← IsOpenMap.preimage_interior_eq_interior_preimage (s.isOpenMap hs) s.continuous,
      interior_Iic]
    ext x
    simp [s]

/-- The barycenter is an interior point, also in dimension zero. -/
theorem coordinateSimplex_interior_nonempty (n : ℕ) :
    (interior (coordinateSimplex n)).Nonempty := by
  rw [coordinateSimplex_interior]
  refine ⟨fun _ => 1 / ((n : ℝ) + 1), ?_, ?_⟩
  · intro i
    positivity
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div]
    apply (div_lt_one (by positivity : (0 : ℝ) < n + 1)).mpr
    linarith

/-- All barycentric coordinates are positive precisely on the interior
of the full-dimensional coordinate simplex. -/
theorem coordinateHomeomorph_mem_interior (n : ℕ)
    (x : stdSimplex ℝ (Fin (n+1))) :
    (coordinateHomeomorph n x).1 ∈ interior (coordinateSimplex n) ↔
      ∀ i, 0 < x.1 i := by
  rw [coordinateSimplex_interior]
  have hs := x.2.2
  rw [Fin.sum_univ_succ] at hs
  change ((∀ i : Fin n, 0 < x.1 i.succ) ∧ ∑ i : Fin n, x.1 i.succ < 1) ↔ _
  constructor
  · intro h i
    induction i using Fin.cases with
    | zero => linarith [h.2]
    | succ i => exact h.1 i
  · intro h
    exact ⟨fun i => h i.succ, by linarith [h 0]⟩

/-- The geometric simplex boundary is exactly the topological frontier
in full-dimensional simplex coordinates. -/
theorem coordinateHomeomorph_mem_frontier (n : ℕ)
    (x : stdSimplex ℝ (Fin (n+1))) :
    (coordinateHomeomorph n x).1 ∈ frontier (coordinateSimplex n) ↔
      ∃ i, x.1 i = 0 := by
  rw [frontier, (coordinateSimplex_isClosed n).closure_eq]
  simp only [Set.mem_sdiff, (coordinateHomeomorph n x).2, true_and,
    coordinateHomeomorph_mem_interior, not_forall, not_lt]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, le_antisymm hi (x.2.1 i)⟩,
    fun ⟨i, hi⟩ => ⟨i, hi.le⟩⟩

/-- The standard geometric simplex is a closed ball, with exactly its
zero-coordinate boundary mapped to the boundary sphere. -/
theorem exists_stdSimplex_closedBall_homeomorph (n : ℕ) :
    ∃ e : stdSimplex ℝ (Fin (n+1)) ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1,
      ∀ x, (∃ i, x.1 i = 0) ↔ ‖(e x).1‖ = 1 := by
  obtain ⟨h, hi, hc, hf⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (coordinateSimplex_convex n) (coordinateSimplex_interior_nonempty n)
      (coordinateSimplex_isBounded n)
  rw [(coordinateSimplex_isClosed n).closure_eq] at hc
  have hs : ∀ x, x ∈ coordinateSimplex n ↔ h x ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := by
    intro x
    rw [← hc]
    exact h.injective.mem_set_image.symm
  let e := (coordinateHomeomorph n).trans (h.subtype hs)
  refine ⟨e, ?_⟩
  intro x
  rw [← coordinateHomeomorph_mem_frontier]
  have hx : h (coordinateHomeomorph n x).1 ∈ Metric.sphere (0 : Fin n → ℝ) 1 ↔
      (coordinateHomeomorph n x).1 ∈ frontier (coordinateSimplex n) := by
    rw [← hf]
    exact h.injective.mem_set_image
  simpa [e, Metric.mem_sphere] using hx.symm

end KIP126.Topology.Simplex
