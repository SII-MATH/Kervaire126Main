module

public import KIP126.Def.Topology.Simplex.BarycentricSubdivisionMesh.Data
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace KIP126.Topology.Simplex.BarycentricSubdivisionMesh

open scoped Classical

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem avg_eq_centerMass (v : ι → E) (s : Finset ι) :
    avg v s = s.centerMass (fun _ => (1 : ℝ)) v := by
  simp [avg, Finset.centerMass]

theorem card_smul_avg (v : ι → E) (s : Finset ι) :
    (s.card : ℝ) • avg v s = ∑ i ∈ s, v i := by
  by_cases hs : s = ∅
  · subst s
    simp [avg]
  · have hc : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hs))
    rw [avg, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- A finite average stays within every closed ball containing its vertices. -/
theorem dist_avg_point_le (v : ι → E) (s : Finset ι) (hs : s.Nonempty)
    (z : E) (D : ℝ) (h : ∀ i ∈ s, dist (v i) z ≤ D) :
    dist (avg v s) z ≤ D := by
  rw [avg_eq_centerMass]
  exact (convex_closedBall z D).centerMass_mem
    (fun _ _ => zero_le_one)
    (by simpa using (Nat.cast_pos.mpr (Finset.card_pos.mpr hs) : (0 : ℝ) < s.card)) h

/-- Two finite averages obey the same cross-distance bound as their vertices. -/
theorem dist_avg_avg_le {κ : Type*} (v : ι → E) (w : κ → E)
    (s : Finset ι) (t : Finset κ) (hs : s.Nonempty) (ht : t.Nonempty)
    (D : ℝ) (h : ∀ i ∈ s, ∀ j ∈ t, dist (v i) (w j) ≤ D) :
    dist (avg v s) (avg w t) ≤ D := by
  rw [dist_comm]
  apply dist_avg_point_le w t ht
  intro j hj
  rw [dist_comm]
  exact dist_avg_point_le v s hs (w j) D (fun i hi => h i hi j hj)

/-- Splitting a finite average over a face and its complement. -/
theorem avg_decompose (v : ι → E) {s t : Finset ι} (h : s ⊆ t) :
    avg v t = ((s.card : ℝ) / t.card) • avg v s +
      (((t \ s).card : ℝ) / t.card) • avg v (t \ s) := by
  have hsum : (∑ i ∈ t, v i) = (∑ i ∈ s, v i) + ∑ i ∈ t \ s, v i := by
    rw [← Finset.sum_sdiff h, add_comm]
  calc
    avg v t = (t.card : ℝ)⁻¹ • ((∑ i ∈ s, v i) + ∑ i ∈ t \ s, v i) := by
      rw [avg, hsum]
    _ = (t.card : ℝ)⁻¹ • ((s.card : ℝ) • avg v s +
        ((t \ s).card : ℝ) • avg v (t \ s)) := by
      rw [card_smul_avg, card_smul_avg]
    _ = _ := by
      rw [smul_add, smul_smul, smul_smul]
      simp only [div_eq_mul_inv, mul_comm]

/-- Nested face barycenters satisfy the sharp finite-cardinality mesh bound. -/
theorem dist_avg_subset_le (v : ι → E) {s t : Finset ι} (hst : s ⊆ t)
    (hs : s.Nonempty) (D : ℝ) (_hD : 0 ≤ D)
    (h : ∀ i ∈ t, ∀ j ∈ t, dist (v i) (v j) ≤ D) :
    dist (avg v s) (avg v t) ≤ (1 - (s.card : ℝ) / t.card) * D := by
  by_cases he : s = t
  · subst t
    have hc : (s.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hs))
    simp [hc]
  · have ht : t.Nonempty := hs.mono hst
    have hr : (t \ s).Nonempty := Finset.sdiff_nonempty.mpr (by
      intro hts
      exact he (Finset.Subset.antisymm hst hts))
    have hct : (t.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr ht))
    have hc : (s.card : ℝ) + (t \ s).card = t.card := by
      have hh : s.card + (t \ s).card = t.card :=
        (Nat.add_comm _ _).trans (Finset.card_sdiff_add_card_eq_card hst)
      exact_mod_cast hh
    have hpq : (s.card : ℝ) / t.card + ((t \ s).card : ℝ) / t.card = 1 := by
      rw [← add_div, hc, div_self hct]
    have hq : 0 ≤ ((t \ s).card : ℝ) / t.card := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hd : avg v s - avg v t =
        (((t \ s).card : ℝ) / t.card) • (avg v s - avg v (t \ s)) := by
      rw [avg_decompose v hst]
      have hs' : avg v s = ((s.card : ℝ) / t.card + ((t \ s).card : ℝ) / t.card) • avg v s := by
        rw [hpq, one_smul]
      nth_rw 1 [hs']
      module
    have hab : dist (avg v s) (avg v (t \ s)) ≤ D :=
      dist_avg_avg_le v v s (t \ s) hs hr D
        (fun i hi j hj => h i (hst hi) j (Finset.mem_sdiff.mp hj).1)
    calc
      dist (avg v s) (avg v t) = (((t \ s).card : ℝ) / t.card) *
          dist (avg v s) (avg v (t \ s)) := by
        rw [dist_eq_norm, hd, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq, dist_eq_norm]
      _ ≤ (((t \ s).card : ℝ) / t.card) * D := mul_le_mul_of_nonneg_left hab hq
      _ = (1 - (s.card : ℝ) / t.card) * D := by congr 1; linarith

/-- A uniform bound on the size of the larger face gives the standard
strict barycentric subdivision contraction factor. -/
theorem dist_avg_subset_le_card_bound (v : ι → E) {s t : Finset ι} (hst : s ⊆ t)
    (hs : s.Nonempty) (N : ℕ) (_hN : 0 < N) (htN : t.card ≤ N)
    (D : ℝ) (hD : 0 ≤ D) (h : ∀ i ∈ t, ∀ j ∈ t, dist (v i) (v j) ≤ D) :
    dist (avg v s) (avg v t) ≤ (1 - 1 / (N : ℝ)) * D := by
  apply (dist_avg_subset_le v hst hs D hD h).trans
  apply mul_le_mul_of_nonneg_right _ hD
  apply sub_le_sub_left
  have ht : (0 : ℝ) < t.card := Nat.cast_pos.mpr (Finset.card_pos.mpr (hs.mono hst))
  have htn : (t.card : ℝ) ≤ N := by exact_mod_cast htN
  have hs1 : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.card_pos.mpr hs
  calc
    (1 : ℝ) / N ≤ 1 / (t.card : ℝ) := one_div_le_one_div_of_le ht htn
    _ ≤ (s.card : ℝ) / t.card := div_le_div_of_nonneg_right hs1 ht.le

/-- A convex combination stays within each common vertex ball. -/
theorem dist_combination_point_le {A : Type*} [Fintype A]
    (v : A → E) (t : stdSimplex ℝ A) (z : E) (D : ℝ)
    (h : ∀ i, dist (v i) z ≤ D) : dist (∑ i, t i • v i) z ≤ D :=
  (convex_closedBall z D).sum_mem (fun i _ => t.property.1 i)
    (stdSimplex.sum_eq_one t) (fun i _ => h i)

/-- Pairwise vertex distance bounds persist under independent convex combinations. -/
theorem dist_combination_combination_le {A B : Type*} [Fintype A] [Fintype B]
    (v : A → E) (w : B → E) (t : stdSimplex ℝ A) (s : stdSimplex ℝ B)
    (D : ℝ) (h : ∀ i j, dist (v i) (w j) ≤ D) :
    dist (∑ i, t i • v i) (∑ j, s j • w j) ≤ D := by
  rw [dist_comm]
  apply dist_combination_point_le
  intro j
  rw [dist_comm]
  exact dist_combination_point_le v t (w j) D (fun i => h i j)


/-- Every pair of face barycenters in one nested flag obeys the same
strict subdivision contraction estimate. -/
theorem dist_flag_avg_le {A : Type*} [LinearOrder A]
    (v : ι → E) (c : A → Finset ι) (hc : Monotone c)
    (hne : ∀ i, (c i).Nonempty) (N : ℕ) (hN : 0 < N)
    (hcard : ∀ i, (c i).card ≤ N) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ k, ∀ i ∈ c k, ∀ j ∈ c k, dist (v i) (v j) ≤ D) (i j : A) :
    dist (avg v (c i)) (avg v (c j)) ≤ (1 - 1 / (N : ℝ)) * D := by
  rcases le_total i j with hij | hji
  · exact dist_avg_subset_le_card_bound v (hc hij) (hne i) N hN (hcard j) D hD (h j)
  · rw [dist_comm]
    exact dist_avg_subset_le_card_bound v (hc hji) (hne j) N hN (hcard i) D hD (h i)

/-- The entire simplex spanned by a flag of face barycenters has the
standard contracted diameter, including its boundary and zero weights. -/
theorem dist_flag_combinations_le {A : Type*} [Fintype A] [LinearOrder A]
    (v : ι → E) (c : A → Finset ι) (hc : Monotone c)
    (hne : ∀ i, (c i).Nonempty) (N : ℕ) (hN : 0 < N)
    (hcard : ∀ i, (c i).card ≤ N) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ k, ∀ i ∈ c k, ∀ j ∈ c k, dist (v i) (v j) ≤ D)
    (t s : stdSimplex ℝ A) :
    dist (∑ i, t i • avg v (c i)) (∑ i, s i • avg v (c i)) ≤
      (1 - 1 / (N : ℝ)) * D :=
  dist_combination_combination_le _ _ t s _
    (dist_flag_avg_le v c hc hne N hN hcard D hD h)

theorem contraction_nonneg (N : ℕ) (hN : 0 < N) : 0 ≤ 1 - 1 / (N : ℝ) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact sub_nonneg.mpr ((div_le_one (by exact_mod_cast hN : (0 : ℝ) < N)).mpr hn)

theorem contraction_lt_one (N : ℕ) (hN : 0 < N) : 1 - 1 / (N : ℝ) < 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  exact sub_lt_self _ (one_div_pos.mpr hn)

/-- Averaging the actual standard coordinate vertices gives the uniform
face barycenter used by the geometric subdivision projection. -/
theorem avg_single_apply {V : Type*} [Fintype V] (s : Finset V) (j : V) :
    avg (fun i : V => Pi.single i (1 : ℝ)) s j =
      if j ∈ s then (s.card : ℝ)⁻¹ else 0 := by
  simp [avg, Pi.smul_apply, Finset.sum_apply, Pi.single_apply]

end KIP126.Topology.Simplex.BarycentricSubdivisionMesh
