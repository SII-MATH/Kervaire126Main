module
import all KIP126.AdamsComputation.Internal.ArchiveData
import all KIP126.AdamsComputation.Internal.NativeAlgebra

/-! Private enumeration and projection tools for the fixed native quotient.
No actual spectral page or comparison enters these constructions. -/

@[expose] section
open scoped BigOperators
namespace KIP126.Computation.Table.Internal
open KIP126.Computation.CachedStandard
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

private def enumerateMonomials {n : ℕ} (degree : Fin n → ℕ × ℕ)
    (candidates : List (Fin n)) : ℕ → ℕ → ℕ → ℕ → List (List (Fin n))
  | 0, _, s, t => if s = 0 ∧ t = 0 then [[]] else []
  | fuel + 1, lower, s, t =>
      if s = 0 ∧ t = 0 then [[]]
      else candidates.flatMap fun i =>
        if lower ≤ i.val ∧ (degree i).1 ≤ s ∧ (degree i).2 ≤ t then
          (enumerateMonomials degree candidates fuel i.val
            (s - (degree i).1) (t - (degree i).2)).map
              (fun m => i :: m)
        else []

private def monomialPowers {n : ℕ} (w : List (Fin n)) : Fin n →₀ ℕ :=
  (w.map fun i => Finsupp.single i 1).sum

private theorem enumerateMonomials_complete {n : ℕ} (degree : Fin n → ℕ × ℕ)
    (candidates : List (Fin n)) (positive : ∀ i, 0 < (degree i).1)
    (fuel lower s t : ℕ) (m : Fin n →₀ ℕ)
    (hweight : Finsupp.weight degree m = (s,t)) (hbound : s ≤ fuel)
    (hindices : ∀ i ∈ m.support, i ∈ candidates ∧ lower ≤ i.val) :
    ∃ w ∈ enumerateMonomials degree candidates fuel lower s t, monomialPowers w = m := by
  induction fuel generalizing lower s t m with
  | zero =>
    have hs : s = 0 := by omega
    have hm : m = 0 := by
      by_contra hm
      obtain ⟨i,hi⟩ := Finsupp.support_nonempty_iff.mpr hm
      have hweight' : Finsupp.weight (fun i => (degree i).1) m = s := by
        simpa only [Finsupp.weight_apply, Finsupp.sum, Prod.fst_sum, Prod.smul_fst] using
          congrArg Prod.fst hweight
      have hle := Finsupp.le_weight_of_ne_zero' (fun i => (degree i).1)
        (Finsupp.mem_support_iff.mp hi)
      rw [hweight'] at hle
      have hp := positive i
      omega
    subst m
    have ht : t = 0 := by simpa using (congrArg Prod.snd hweight).symm
    exact ⟨[], by simp [enumerateMonomials, hs, ht], rfl⟩
  | succ fuel ih =>
    by_cases hm : m = 0
    · subst m
      have hs : s = 0 := by simpa using (congrArg Prod.fst hweight).symm
      have ht : t = 0 := by simpa using (congrArg Prod.snd hweight).symm
      exact ⟨[], by simp [enumerateMonomials, hs, ht], rfl⟩
    have hne : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm
    let i := m.support.min' hne
    have hi : i ∈ m.support := Finset.min'_mem _ _
    have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp hi
    let m' := m - Finsupp.single i 1
    have hw' : Finsupp.weight degree m' + degree i = (s,t) :=
      (Finsupp.weight_sub_single_add (w := degree) hmi).trans hweight
    have hs' := congrArg Prod.fst hw'
    have ht' := congrArg Prod.snd hw'
    simp only [Prod.fst_add, Prod.snd_add] at hs' ht'
    have hds : (degree i).1 ≤ s := by omega
    have hdt : (degree i).2 ≤ t := by omega
    have hmweight : Finsupp.weight degree m' = (s - (degree i).1,t - (degree i).2) := by
      apply Prod.ext <;> simp only [] <;> omega
    have hmfuel : s - (degree i).1 ≤ fuel := by have hp := positive i; omega
    have hsub : ∀ j ∈ m'.support, j ∈ candidates ∧ i.val ≤ j.val := by
      intro j hj
      have hj' : j ∈ m.support := by
        apply Finsupp.mem_support_iff.mpr
        intro hz
        have hle : m' j ≤ m j := Nat.sub_le _ _
        have hn : m' j ≠ 0 := Finsupp.mem_support_iff.mp hj
        omega
      refine ⟨(hindices j hj').1, ?_⟩
      exact Fin.le_iff_val_le_val.mp (Finset.min'_le _ _ hj')
    obtain ⟨w, hmem, hw⟩ := ih i.val (s - (degree i).1) (t - (degree i).2) m' hmweight hmfuel hsub
    have hsnonzero : ¬ (s = 0 ∧ t = 0) := by
      intro hz
      have hp := positive i
      omega
    refine ⟨i :: w, ?_, ?_⟩
    · simp only [enumerateMonomials, if_neg hsnonzero]
      apply List.mem_flatMap.mpr
      refine ⟨i, (hindices i hi).1, ?_⟩
      rw [if_pos ⟨(hindices i hi).2,hds,hdt⟩]
      exact List.mem_map.mpr ⟨w,hmem,rfl⟩
    · change Finsupp.single i 1 + monomialPowers w = m
      rw [hw]
      exact (add_comm _ _).trans (Finsupp.sub_add_single_one_cancel hmi)

private theorem thetaCandidates_positive : ∀ i : Fin archiveGeneratorCount, 0 < (archiveGeneratorDegree i).1 := by decide

private def thetaX (i : Fin archiveGeneratorCount) := nativeProjection archiveGeneratorCount archiveSourceRelations (MvPolynomial.X i)

private theorem thetaProjectedWord (w : List (Fin archiveGeneratorCount)) :
    nativeProjection archiveGeneratorCount archiveSourceRelations (MvPolynomial.monomial (monomialPowers w) 1) =
      (w.map thetaX).prod := by
  induction w with
  | nil => simp [monomialPowers]
  | cons i w ih =>
    change nativeProjection archiveGeneratorCount archiveSourceRelations
      (MvPolynomial.monomial (Finsupp.single i 1 + monomialPowers w) 1) = _
    rw [MvPolynomial.monomial_single_add,map_mul,pow_one,ih]
    rfl

end
end KIP126.Computation.Table.Internal
