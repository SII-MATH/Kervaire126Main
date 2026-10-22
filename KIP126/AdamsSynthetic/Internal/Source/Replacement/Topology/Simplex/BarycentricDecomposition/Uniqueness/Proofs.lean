module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.BarycentricDecomposition.Uniqueness.Basic

@[expose] section

namespace KIP126.Topology.Simplex.BarycentricDecomposition

open scoped Classical

variable {V : Type*} [Fintype V]

/-- The positive coordinate values of a strict positive flag combination
are exactly its successive tail masses. -/
theorem flagSum_range_eq_levels (y : stdSimplex ℝ V) {m : ℕ}
    (c : Fin m → Finset V) (hc : StrictMono c) (hne : ∀ i, (c i).Nonempty)
    (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hy : ∀ j, y j = flagSum c a j) :
    Set.range (fun i : Fin m => tailMass a i.val) = (levels y : Set ℝ) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := strict_flag_new_vertex c hc hne i
    exact (mem_levels y _).mpr ⟨tailMass_pos a ha i, j,
      (hy j).trans (flagSum_eq_tailMass c a i j hj)⟩
  · intro hz
    obtain ⟨hz, j, hj⟩ := (mem_levels y _).mp hz
    have hp : 0 < flagSum c a j := by rw [← hy j, hj]; exact hz
    obtain ⟨i, hi⟩ := positive_flagSum_first c hc.monotone a j hp
    exact ⟨i, (flagSum_eq_tailMass c a i j hi).symm.trans ((hy j).symm.trans hj)⟩

/-- The number of faces in any strict positive representation equals the
number of distinct positive coordinates. -/
theorem strict_flagSum_card (y : stdSimplex ℝ V) {m : ℕ}
    (c : Fin m → Finset V) (hc : StrictMono c) (hne : ∀ i, (c i).Nonempty)
    (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hy : ∀ j, y j = flagSum c a j) :
    m = (levels y).card := by
  have hr := flagSum_range_eq_levels y c hc hne a ha hy
  let f : Fin m → levels y := fun i => ⟨tailMass a i.val, by
    change tailMass a i.val ∈ (levels y : Set ℝ)
    rw [← hr]
    exact ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact (tailMass_strictAnti a ha).injective (congrArg Subtype.val h)
    · intro z
      have hz : z.val ∈ Set.range (fun i : Fin m => tailMass a i.val) := hr.symm ▸ z.property
      obtain ⟨i, hi⟩ := hz
      exact ⟨i, Subtype.ext hi⟩
  simpa only [Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_congr (Equiv.ofBijective f hf)

/-- Agreement of all finite tail masses implies agreement at every natural cut. -/
theorem tailMass_eq_of_fin_eq {m : ℕ} (a b : Fin m → ℝ)
    (h : ∀ i : Fin m, tailMass a i.val = tailMass b i.val) (r : ℕ) :
    tailMass a r = tailMass b r := by
  by_cases hr : r < m
  · exact h ⟨r, hr⟩
  · have hz (v : Fin m → ℝ) : tailMass v r = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact if_neg (by omega)
    rw [hz a, hz b]

/-- A strict positive face representation is unique, including its number
of faces and its constant per-vertex masses. -/
theorem strict_flagSum_unique (y : stdSimplex ℝ V) {m n : ℕ}
    (c : Fin m → Finset V) (hc : StrictMono c) (hne : ∀ i, (c i).Nonempty)
    (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hy : ∀ j, y j = flagSum c a j)
    (d : Fin n → Finset V) (hd : StrictMono d) (hnd : ∀ i, (d i).Nonempty)
    (b : Fin n → ℝ) (hb : ∀ i, 0 < b i) (hy' : ∀ j, y j = flagSum d b j) :
    m = n ∧ HEq c d ∧ HEq a b := by
  have hmn : m = n := (strict_flagSum_card y c hc hne a ha hy).trans
    (strict_flagSum_card y d hd hnd b hb hy').symm
  subst n
  have ht : (fun i : Fin m => tailMass a i.val) = (fun i : Fin m => tailMass b i.val) :=
    ((tailMass_strictAnti a ha).range_inj (tailMass_strictAnti b hb)).mp
      ((flagSum_range_eq_levels y c hc hne a ha hy).trans
        (flagSum_range_eq_levels y d hd hnd b hb hy').symm)
  have hcuts : ∀ r, tailMass a r = tailMass b r :=
    tailMass_eq_of_fin_eq a b (fun i => congrFun ht i)
  have hcd : c = d := by
    funext i
    apply Finset.ext
    intro j
    rw [mem_flag_iff_tailMass_le c hc.monotone a ha,
      mem_flag_iff_tailMass_le d hd.monotone b hb, ← hy j, ← hy' j, hcuts]
  have hab : a = b := by
    funext i
    rw [← tailMass_sub_succ a i, ← tailMass_sub_succ b i, hcuts, hcuts]
  exact ⟨rfl, heq_of_eq hcd, heq_of_eq hab⟩

/-- Strict flags and strictly positive simplex weights have unique
barycentric representations. The heterogeneous equalities retain the
actual flags and weights while their finite index sizes are compared. -/
theorem strict_flag_unique (y : stdSimplex ℝ V) {m n : ℕ}
    (c : Fin m → Finset V) (hc : StrictMono c) (hne : ∀ i, (c i).Nonempty)
    (t : stdSimplex ℝ (Fin m)) (ht : ∀ i, 0 < t i)
    (hy : ∀ j, y j = ∑ i, t i * (if j ∈ c i then ((c i).card : ℝ)⁻¹ else 0))
    (d : Fin n → Finset V) (hd : StrictMono d) (hnd : ∀ i, (d i).Nonempty)
    (s : stdSimplex ℝ (Fin n)) (hs : ∀ i, 0 < s i)
    (hy' : ∀ j, y j = ∑ i, s i * (if j ∈ d i then ((d i).card : ℝ)⁻¹ else 0)) :
    m = n ∧ HEq c d ∧ HEq t s := by
  let a : Fin m → ℝ := fun i => t i * ((c i).card : ℝ)⁻¹
  let b : Fin n → ℝ := fun i => s i * ((d i).card : ℝ)⁻¹
  have ha : ∀ i, 0 < a i := fun i => mul_pos (ht i)
    (inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr (hne i))))
  have hb : ∀ i, 0 < b i := fun i => mul_pos (hs i)
    (inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr (hnd i))))
  have hya : ∀ j, y j = flagSum c a j := by
    intro j
    rw [hy j]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : j ∈ c i <;> simp [a, h]
  have hyb : ∀ j, y j = flagSum d b j := by
    intro j
    rw [hy' j]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : j ∈ d i <;> simp [b, h]
  obtain ⟨hmn, hcd, hab⟩ := strict_flagSum_unique y c hc hne a ha hya d hd hnd b hb hyb
  subst n
  have hcd' : c = d := eq_of_heq hcd
  have hab' : a = b := eq_of_heq hab
  have hts : t = s := by
    apply stdSimplex.ext
    funext i
    have h := congrFun hab' i
    dsimp [a, b] at h
    rw [← hcd'] at h
    exact mul_right_cancel₀ (inv_ne_zero (ne_of_gt
      (Nat.cast_pos.mpr (Finset.card_pos.mpr (hne i))))) h
  exact ⟨rfl, hcd, heq_of_eq hts⟩

end KIP126.Topology.Simplex.BarycentricDecomposition
