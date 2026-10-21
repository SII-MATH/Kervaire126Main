module

import Mathlib.Data.ZMod.Basic
import all KIP126.E2Computation.Internal.ArchiveData
import all KIP126.E2Computation.Internal.NativeAlgebra
import all KIP126.E2Computation.Internal.FixedRelations
import all KIP126.E2Computation.Internal.RelationCertificate
import all KIP126.E2Computation.Internal.RelationCertificates

/-! Coefficient invariant on the fixed native quotient. All archive checks,
coefficient formulas and nondivisibility arguments use the original ordered
generator and relation data, independently of the actual-page comparison. -/

@[expose] section
namespace KIP126.Computation.CachedStandard
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

namespace MigrationFastCheck
open KIP126.Computation.RelationCertificate
private theorem coeffPowers_eq_false_of_badOutside (n : ℕ) (allowed : List ℕ) (ns : List ℕ) :
    ∀ target : List (Fin n), (∀ j∈target, j.val∈allowed) →
      badOutside allowed ns = true → coeffPowers n target ns = false := by
  induction ns using List.twoStepInduction with
  | nil => simp [badOutside]
  | singleton i => simp [badOutside]
  | cons_cons i a rest ih =>
    intro target ht hb
    simp only [coeffPowers]
    by_cases hi : i<n
    · rw [dif_pos hi]
      by_cases ha : a=0
      · rw [if_pos ha]
        apply ih target ht
        simpa only [badOutside,ha,lt_self_iff_false,decide_false,Bool.and_false,Bool.false_or] using hb
      · rw [if_neg ha]
        by_cases hc : a=1 ∧ (⟨i,hi⟩ : Fin n)∈target
        · have hai : i∈allowed := ht ⟨i,hi⟩ hc.2
          have hrest : badOutside allowed rest = true := by
            simpa only [badOutside,List.contains_iff_mem.mpr hai,Bool.not_true,Bool.false_and,Bool.false_or] using hb
          have herase : ∀j∈target.erase ⟨i,hi⟩, j.val∈allowed :=
            fun j hj => ht j (List.mem_of_mem_erase hj)
          simp only [hc.1,decide_true,Bool.true_and,List.contains_iff_mem.mpr hc.2,if_true]
          exact ih _ herase hrest
        · simp only [Bool.and_eq_true,decide_eq_true_eq,List.contains_iff_mem]
          rw [if_neg hc]
    · rw [dif_neg hi]

private theorem top_subset : ∀ ts∈top, ∀ j∈ts, j.val∈allowed := by
  intro ts ht j hj
  simp only [top,List.mem_cons,List.mem_nil_iff,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl <;>
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hj
  all_goals rcases hj with rfl|rfl|rfl <;> decide
private theorem proper_subset : ∀ ts∈proper, ∀ j∈ts, j.val∈allowed := by
  intro ts ht j hj
  simp only [proper,List.mem_cons,List.mem_nil_iff,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hj
  all_goals rcases hj with rfl|rfl <;> decide
private theorem top_nonempty : ∀ ts∈top, ts.isEmpty=false := by decide

private theorem monCountGood_top (cs : List Char) :
    (monCountGood cs).1 = (top.map fun ts => if coeffChars 2914 ts cs then 1 else 0).sum := by
  unfold monCountGood
  by_cases he : cs.isEmpty=true
  · rw [if_pos he]
    have h : (top.map fun ts => if coeffChars 2914 ts cs then (1:ℕ) else 0).sum=0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨ts,ht,rfl⟩ := List.mem_map.mp hx
      simp only [coeffChars,he,if_true,top_nonempty ts ht,Bool.false_eq_true,if_false]
    exact h.symm
  · rw [if_neg he]
    dsimp only
    split
    · rename_i ho
      have h : (top.map fun ts => if coeffChars 2914 ts cs then (1:ℕ) else 0).sum=0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨ts,ht,rfl⟩ := List.mem_map.mp hx
        rw [coeffChars,if_neg he,coeffPowers_eq_false_of_badOutside 2914 allowed _ ts (top_subset ts ht) ho]
        rfl
      exact h.symm
    · simp only [coeffChars,if_neg he]

private theorem monCountGood_proper (cs : List Char) (h : (monCountGood cs).2=true) :
    ∀ts∈proper, coeffChars 2914 ts cs=false := by
  intro ts ht
  unfold monCountGood at h
  by_cases he : cs.isEmpty=true
  · rw [if_pos he] at h
    contradiction
  · rw [if_neg he] at h
    dsimp only at h
    split at h
    · rename_i ho
      rw [coeffChars,if_neg he]
      exact coeffPowers_eq_false_of_badOutside 2914 allowed _ ts (proper_subset ts ht) ho
    · have hh := List.all_eq_true.mp h ts ht
      simpa only [coeffChars,if_neg he,Bool.not_eq_true'] using hh

private theorem good_implies_row (cs : List Char) (h : good cs=true) :
    rowCount 2914 top cs %2=0 ∧ ∀mon∈cs.splitOn ';', ∀ts∈proper, coeffChars 2914 ts mon=false := by
  simp only [good,Bool.and_eq_true,decide_eq_true_eq] at h
  constructor
  · have hsum : (((cs.splitOn ';').map monCountGood).map Prod.fst).sum=rowCount 2914 top cs := by
      simp only [List.map_map,Function.comp_def,rowCount]
      congr 1
      apply List.map_congr_left
      intro mon hm
      exact monCountGood_top mon
    rw [hsum] at h
    exact h.1
  · intro mon hm
    have hh : (monCountGood mon).2=true := List.all_eq_true.mp h.2 (monCountGood mon) (List.mem_map.mpr ⟨mon,hm,rfl⟩)
    exact monCountGood_proper mon hh
end MigrationFastCheck

/- Private coefficient invariant for the historical T nondivisibility certificates.
The functional is verified on the entire fixed native relation ideal. -/
namespace MigrationRows
open KIP126.Computation.RelationCertificate
noncomputable section
open MvPolynomial
private theorem charsToNat_eq (cs : List Char) : (String.ofList cs).toNat?.getD 0 = KIP126.Computation.RelationCertificate.charsToNat cs := by
  simp only [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
    String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList,
    String.copy_toSlice,String.toList_ofList]
  change (if KIP126.Computation.RelationCertificate.charsIsNat cs then some (cs.foldl (fun n c => if c = '_' then n else n*10+(c.toNat-'0'.toNat)) 0) else none).getD 0 = _
  unfold KIP126.Computation.RelationCertificate.charsToNat
  split <;> rfl
noncomputable def targetDegree {n : ℕ} (target : List (Fin n)) : Fin n →₀ ℕ :=
  (target.map (fun i => Finsupp.single i 1)).sum

theorem targetDegree_apply {n : ℕ} (target : List (Fin n)) (hn : target.Nodup)
    (i : Fin n) : targetDegree target i = if i ∈ target then 1 else 0 := by
  induction target with
  | nil => simp [targetDegree]
  | cons j rest ih =>
    have hnd := List.nodup_cons.mp hn
    simp only [targetDegree, List.map_cons, List.sum_cons, Finsupp.add_apply]
    rw [show ((rest.map (fun i => Finsupp.single i 1)).sum) i =
      if i ∈ rest then 1 else 0 from ih hnd.2]
    by_cases hij : j = i
    · subst j
      simp [hnd.1]
    · simp [Ne.symm hij]

theorem targetDegree_erase {n : ℕ} (target : List (Fin n)) (hn : target.Nodup)
    (i : Fin n) (hi : i ∈ target) :
    targetDegree target - Finsupp.single i 1 = targetDegree (target.erase i) := by
  ext j
  rw [Finsupp.tsub_apply, targetDegree_apply target hn,
    targetDegree_apply (target.erase i) (hn.erase i)]
  by_cases hji : j = i
  · subst j
    simp [hi, hn.not_mem_erase]
  · simp [hji,List.mem_erase_of_ne hji]

theorem targetDegree_eq_zero {n : ℕ} (target : List (Fin n)) :
    targetDegree target = 0 ↔ target = [] := by
  constructor
  · intro hz
    cases target with
    | nil => rfl
    | cons i rest =>
      have h := congrArg (fun d : Fin n →₀ ℕ => d i) hz
      simp [targetDegree] at h
  · rintro rfl
    rfl

theorem coeffPowers_correct (n : ℕ) (ns : List ℕ) :
    ∀ (target : List (Fin n)), target.Nodup →
      MvPolynomial.coeff (targetDegree target) (KIP126.Computation.CachedStandard.nativePolynomialOfPowers n ns) =
        if KIP126.Computation.RelationCertificate.coeffPowers n target ns then (1 : ZMod 2) else 0 := by
  classical
  induction ns using List.twoStepInduction with
  | nil =>
    intro target hn
    have hz : (0 : Fin n →₀ ℕ) = targetDegree target ↔ target.isEmpty = true := by
      rw [eq_comm, targetDegree_eq_zero, List.isEmpty_iff]
    simp only [KIP126.Computation.CachedStandard.nativePolynomialOfPowers, KIP126.Computation.RelationCertificate.coeffPowers, MvPolynomial.coeff_one, hz]
  | singleton i =>
    intro target hn
    simp [KIP126.Computation.CachedStandard.nativePolynomialOfPowers, KIP126.Computation.RelationCertificate.coeffPowers]
  | cons_cons i a rest ih =>
    intro target hn
    simp only [KIP126.Computation.CachedStandard.nativePolynomialOfPowers, KIP126.Computation.RelationCertificate.coeffPowers]
    by_cases hi : i < n
    · simp only [dif_pos hi]
      by_cases ha0 : a = 0
      · simp only [ha0, if_true, pow_zero, one_mul]
        exact ih target hn
      · rw [if_neg ha0, MvPolynomial.X_pow_eq_monomial,
          MvPolynomial.coeff_monomial_mul']
        have hle : Finsupp.single (⟨i,hi⟩ : Fin n) a ≤ targetDegree target ↔
            a = 1 ∧ (⟨i,hi⟩ : Fin n) ∈ target := by
          rw [Finsupp.single_le_iff, targetDegree_apply target hn]
          by_cases hm : (⟨i,hi⟩ : Fin n) ∈ target
          · simp only [hm, if_true, and_true]
            omega
          · simp only [hm, if_false, and_false]
            exact ⟨fun h => ha0 (Nat.eq_zero_of_le_zero h), False.elim⟩
        simp only [hle, one_mul, Bool.and_eq_true, decide_eq_true_eq,
          List.contains_iff_mem]
        by_cases hcond : a = 1 ∧ (⟨i,hi⟩ : Fin n) ∈ target
        · rw [if_pos hcond, if_pos hcond, hcond.1,
            targetDegree_erase target hn _ hcond.2]
          exact ih (target.erase ⟨i,hi⟩) (hn.erase _)
        · rw [if_neg hcond, if_neg hcond]
          rfl
    · simp [hi]


private theorem coeffChars_correct (n : ℕ) (target : List (Fin n)) (hn : target.Nodup) (cs : List Char) :
    coeff (targetDegree target) (KIP126.Computation.CachedStandard.nativeMonomialOfString n (String.ofList cs)) =
      if KIP126.Computation.RelationCertificate.coeffChars n target cs then (1 : ZMod 2) else 0 := by
  classical
  by_cases he : cs = []
  · subst cs
    simp only [KIP126.Computation.CachedStandard.nativeMonomialOfString, String.ofList_nil,
      KIP126.Computation.RelationCertificate.coeffChars, List.isEmpty_nil, if_true, MvPolynomial.coeff_one]
    have hz : (0 : Fin n →₀ ℕ) = targetDegree target ↔ target.isEmpty = true := by
      rw [eq_comm,targetDegree_eq_zero,List.isEmpty_iff]
    simp only [hz]
  · have hs : String.ofList cs ≠ "" := by simpa using he
    rw [KIP126.Computation.CachedStandard.nativeMonomialOfString, if_neg hs]
    rw [show "," = String.singleton ',' from rfl, KIP126.Computation.CachedStandard.namedRelation_splitOn_char]
    simp only [String.toList_ofList,List.map_map]
    simp only [Function.comp_def,charsToNat_eq]
    rw [coeffPowers_correct n _ target hn]
    simp only [KIP126.Computation.RelationCertificate.coeffChars, show cs.isEmpty = false from Bool.eq_false_iff.mpr (fun h => he (List.isEmpty_iff.mp h)), Bool.false_eq_true, if_false]

end
end MigrationRows
open MvPolynomial
noncomputable section
namespace HistoricalMigration
variable {σ R : Type*} [CommRing R]

def coefficientFunctional (C : Finset (σ →₀ ℕ)) : MvPolynomial σ R →ₗ[R] R :=
  ∑ c ∈ C, MvPolynomial.lcoeff R c

theorem coefficientFunctional_apply (C : Finset (σ →₀ ℕ)) (p : MvPolynomial σ R) :
    coefficientFunctional C p = ∑ c ∈ C, coeff c p := by
  simp [coefficientFunctional]

theorem coefficientFunctional_mul_monomial (C : Finset (σ →₀ ℕ))
    (q : σ →₀ ℕ) (a : R) (r : MvPolynomial σ R) :
    coefficientFunctional C (monomial q a * r) =
      a * coefficientFunctional C (monomial q 1 * r) := by
  classical
  simp only [coefficientFunctional_apply, coeff_monomial_mul']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  split_ifs <;> simp

theorem coefficientFunctional_zero_of_no_divisor (C : Finset (σ →₀ ℕ))
    (q : σ →₀ ℕ) (r : MvPolynomial σ R)
    (h : ¬ ∃ c ∈ C, q ≤ c) :
    coefficientFunctional C (monomial q 1 * r) = 0 := by
  classical
  rw [coefficientFunctional_apply]
  apply Finset.sum_eq_zero
  intro c hc
  rw [coeff_monomial_mul', if_neg (fun hq => h ⟨c,hc,hq⟩)]

theorem coefficientFunctional_zero_of_proper_divisors (C : Finset (σ →₀ ℕ))
    (r : MvPolynomial σ R) (hr : coefficientFunctional C r = 0)
    (hproper : ∀ c ∈ C, ∀ d : σ →₀ ℕ, d ≤ c → d ≠ c → coeff d r = 0)
    (q : σ →₀ ℕ) : coefficientFunctional C (monomial q 1 * r) = 0 := by
  classical
  by_cases hq : q = 0
  · subst q
    simpa using hr
  rw [coefficientFunctional_apply]
  apply Finset.sum_eq_zero
  intro c hc
  rw [coeff_monomial_mul']
  by_cases hqc : q ≤ c
  · rw [if_pos hqc, one_mul]
    apply hproper c hc (c-q) tsub_le_self
    intro heq
    have hsum := tsub_add_cancel_of_le hqc
    rw [heq] at hsum
    exact hq (add_left_cancel (hsum.trans (add_zero c).symm))
  · rw [if_neg hqc]

theorem coefficientFunctional_mul_zero (C : Finset (σ →₀ ℕ)) (r : MvPolynomial σ R)
    (h : ∀ q : σ →₀ ℕ, (∃ c ∈ C, q ≤ c) →
      coefficientFunctional C (monomial q 1 * r) = 0)
    (p : MvPolynomial σ R) : coefficientFunctional C (p*r) = 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add, hp, hq, add_zero]
  | monomial q a =>
    rw [coefficientFunctional_mul_monomial]
    by_cases hq : ∃ c ∈ C, q ≤ c
    · rw [h q hq, mul_zero]
    · rw [coefficientFunctional_zero_of_no_divisor C q r hq, mul_zero]

theorem coefficientFunctional_span_zero (C : Finset (σ →₀ ℕ))
    (S : Set (MvPolynomial σ R))
    (h : ∀ r ∈ S, ∀ q : σ →₀ ℕ, (∃ c ∈ C, q ≤ c) →
      coefficientFunctional C (monomial q 1 * r) = 0)
    (p : MvPolynomial σ R) (hp : p ∈ Ideal.span S) :
    coefficientFunctional C p = 0 := by
  classical
  have hmul : ∀ p ∈ Ideal.span S, ∀ a, coefficientFunctional C (a*p) = 0 := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem r hr => intro a; exact coefficientFunctional_mul_zero C r (h r hr) a
    | zero => intro a; simp
    | add p q _ _ hp hq => intro a; simp only [mul_add, map_add, hp a, hq a, add_zero]
    | smul a p _ hp =>
      intro b
      change coefficientFunctional C (b * (a*p)) = 0
      rw [← mul_assoc]
      exact hp (b*a)
  simpa using hmul p hp 1
end HistoricalMigration

end
noncomputable section
open Finsupp
namespace HistoricalMigration
variable {σ : Type*} [DecidableEq σ]

theorem three_squarefree_subsets (a b c : σ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (d : σ →₀ ℕ) (hd : d ≤ single a 1 + single b 1 + single c 1)
    (hne : d ≠ single a 1 + single b 1 + single c 1) :
    d = 0 ∨ d = single a 1 ∨ d = single b 1 ∨ d = single c 1 ∨
      d = single a 1 + single b 1 ∨ d = single a 1 + single c 1 ∨
      d = single b 1 + single c 1 := by
  have ha : d a ≤ 1 := by simpa [hab,hac] using hd a
  have hb : d b ≤ 1 := by simpa [Ne.symm hab,hbc] using hd b
  have hc : d c ≤ 1 := by simpa [Ne.symm hac,Ne.symm hbc] using hd c
  have decomp : d = single a (d a) + single b (d b) + single c (d c) := by
    ext i
    by_cases hia : i = a
    · subst i; simp [hab,hac]
    by_cases hib : i = b
    · subst i; simp [Ne.symm hab,hbc]
    by_cases hic : i = c
    · subst i; simp [Ne.symm hac,Ne.symm hbc]
    have hi : d i = 0 := by simpa [Ne.symm hia,Ne.symm hib,Ne.symm hic] using hd i
    simp [hia,hib,hic,hi]
  have ha' : d a = 0 ∨ d a = 1 := by omega
  have hb' : d b = 0 ∨ d b = 1 := by omega
  have hc' : d c = 0 ∨ d c = 1 := by omega
  rcases ha' with ha'|ha' <;> rcases hb' with hb'|hb' <;> rcases hc' with hc'|hc' <;>
    simp only [ha',hb',hc',single_zero,zero_add,add_zero] at decomp <;>
    simp_all

theorem two_squarefree_subsets (a b : σ) (hab : a ≠ b)
    (d : σ →₀ ℕ) (hd : d ≤ single a 1 + single b 1)
    (hne : d ≠ single a 1 + single b 1) :
    d = 0 ∨ d = single a 1 ∨ d = single b 1 := by
  have ha : d a ≤ 1 := by simpa [hab] using hd a
  have hb : d b ≤ 1 := by simpa [Ne.symm hab] using hd b
  have decomp : d = single a (d a) + single b (d b) := by
    ext i
    by_cases hia : i = a
    · subst i; simp [hab]
    by_cases hib : i = b
    · subst i; simp [Ne.symm hab]
    have hi : d i = 0 := by simpa [Ne.symm hia,Ne.symm hib] using hd i
    simp [hia,hib,hi]
  have ha' : d a = 0 ∨ d a = 1 := by omega
  have hb' : d b = 0 ∨ d b = 1 := by omega
  rcases ha' with ha'|ha' <;> rcases hb' with hb'|hb' <;>
    simp only [ha',hb',single_zero,zero_add,add_zero] at decomp <;> simp_all
end HistoricalMigration

end
namespace MigrationRows
open KIP126.Computation.RelationCertificate
noncomputable section
open MvPolynomial
open KIP126.Computation.CachedStandard
private theorem rowCoeff_correct (n : ℕ) (target : List (Fin n)) (hn : target.Nodup) (cs : List Char) :
    coeff (targetDegree target) (nativeRelationPolynomial n (String.ofList cs)) =
      (((cs.splitOn ';').map fun mon => if coeffChars n target mon then (1:ℕ) else 0).sum : ZMod 2) := by
  classical
  rw [nativeRelationPolynomial, show ";"=String.singleton ';' from rfl,namedRelation_splitOn_char]
  simp only [String.toList_ofList,List.map_map,Function.comp_def]
  induction (cs.splitOn ';') with
  | nil => simp
  | cons mon rest ih =>
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    rw [MvPolynomial.coeff_add,coeffChars_correct n target hn mon,ih]
    split_ifs <;> simp
private theorem sum_rowCoeff (n : ℕ) (targets : List (List (Fin n)))
    (hn : ∀ ts∈targets, ts.Nodup) (cs : List Char) :
    (targets.map fun target => coeff (targetDegree target)
      (nativeRelationPolynomial n (String.ofList cs))).sum = (rowCount n targets cs : ZMod 2) := by
  classical
  have hswap {α β : Type} (xs : List α) (ys : List β) (f : α → β → ℕ) :
      (xs.map fun a => (ys.map fun b => f a b).sum).sum =
      (ys.map fun b => (xs.map fun a => f a b).sum).sum := by
    induction xs with
    | nil => simp
    | cons a rest ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [ih,← List.sum_map_add]
  have row : (targets.map fun target => coeff (targetDegree target)
      (nativeRelationPolynomial n (String.ofList cs))).sum =
      (((targets.map fun ts => ((cs.splitOn ';').map fun mon => if coeffChars n ts mon then (1:ℕ) else 0).sum).sum : ℕ) : ZMod 2) := by
    induction targets with
    | nil => simp
    | cons ts rest ih =>
      simp only [List.map_cons,List.sum_cons,Nat.cast_add]
      rw [rowCoeff_correct n ts (hn ts (by simp)) cs,ih (fun t ht => hn t (by simp [ht]))]
  rw [row]
  congr 1
  exact hswap targets (cs.splitOn ';') (fun ts mon => if coeffChars n ts mon then 1 else 0)

end
end MigrationRows

noncomputable section
open MvPolynomial MigrationRows HistoricalMigration KIP126.Computation.RelationCertificate
private abbrev migrationN := 2914
private def migrationTopLists : List (List (Fin migrationN)) :=
  [[⟨1,by decide⟩,⟨7,by decide⟩,⟨275,by decide⟩],
   [⟨4,by decide⟩,⟨320,by decide⟩], [⟨7,by decide⟩,⟨287,by decide⟩], [⟨70,by decide⟩,⟨98,by decide⟩]]
private def migrationProperLists : List (List (Fin migrationN)) :=
  [[],[⟨1,by decide⟩],[⟨7,by decide⟩],[⟨275,by decide⟩],
   [⟨1,by decide⟩,⟨7,by decide⟩],[⟨1,by decide⟩,⟨275,by decide⟩],[⟨7,by decide⟩,⟨275,by decide⟩],
   [⟨4,by decide⟩],[⟨320,by decide⟩],[⟨287,by decide⟩],[⟨70,by decide⟩],[⟨98,by decide⟩]]
private def migrationC : Finset (Fin migrationN →₀ ℕ) :=
  (migrationTopLists.map targetDegree).toFinset
private def migrationL := coefficientFunctional (R:=ZMod 2) migrationC
private def migrationRowGood (cs : List Char) : Prop :=
  rowCount migrationN migrationTopLists cs % 2 = 0 ∧
  ∀ mon ∈ cs.splitOn ';', ∀ ts∈migrationProperLists, coeffChars migrationN ts mon = false

private theorem migrationTopLists_nodup : ∀ ts∈migrationTopLists, ts.Nodup := by decide
private theorem migrationProperLists_nodup : ∀ ts∈migrationProperLists, ts.Nodup := by decide
private theorem migrationTargetDegrees_nodup : (migrationTopLists.map targetDegree).Nodup := by
  simp only [migrationTopLists,List.map_cons,List.map_nil,targetDegree,List.sum_cons,List.sum_nil,add_zero]
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,and_true,not_or,not_false_eq_true]
  repeat' constructor
  all_goals intro h
  all_goals first
    | solve | have hh := congrArg (fun d : Fin migrationN →₀ ℕ => d ⟨1,by decide⟩) h; norm_num [Finsupp.single_apply] at hh
    | solve | have hh := congrArg (fun d : Fin migrationN →₀ ℕ => d ⟨4,by decide⟩) h; norm_num [Finsupp.single_apply] at hh
    | solve | have hh := congrArg (fun d : Fin migrationN →₀ ℕ => d ⟨7,by decide⟩) h; norm_num [Finsupp.single_apply] at hh
private theorem migrationC_apply (p : nativePoly migrationN) :
    migrationL p = (migrationTopLists.map fun ts => coeff (targetDegree ts) p).sum := by
  classical
  rw [migrationL,coefficientFunctional_apply,migrationC,List.sum_toFinset _ migrationTargetDegrees_nodup]
  simp only [List.map_map,Function.comp_def]

private theorem migration_proper_cover (c : Fin migrationN →₀ ℕ) (hc : c∈migrationC)
    (d : Fin migrationN →₀ ℕ) (hd : d≤c) (hne : d≠c) :
    ∃ ts∈migrationProperLists, d=targetDegree ts := by
  classical
  simp only [migrationC,List.mem_toFinset,List.mem_map] at hc
  obtain ⟨ts,ht,rfl⟩ := hc
  simp only [migrationTopLists,List.mem_cons,List.mem_nil_iff,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl
  · have h := three_squarefree_subsets (⟨1,by decide⟩ : Fin migrationN) ⟨7,by decide⟩ ⟨275,by decide⟩
      (by decide) (by decide) (by decide) d (by simpa [targetDegree,add_assoc] using hd)
      (by simpa [targetDegree,add_assoc] using hne)
    rcases h with h|h|h|h|h|h|h <;> rw [h] <;>
      simp [migrationProperLists,targetDegree]
  · have h := two_squarefree_subsets (⟨4,by decide⟩ : Fin migrationN) ⟨320,by decide⟩
      (by decide) d (by simpa [targetDegree] using hd) (by simpa [targetDegree] using hne)
    rcases h with h|h|h <;> rw [h] <;> simp [migrationProperLists,targetDegree]
  · have h := two_squarefree_subsets (⟨7,by decide⟩ : Fin migrationN) ⟨287,by decide⟩
      (by decide) d (by simpa [targetDegree] using hd) (by simpa [targetDegree] using hne)
    rcases h with h|h|h <;> rw [h] <;> simp [migrationProperLists,targetDegree]
  · have h := two_squarefree_subsets (⟨70,by decide⟩ : Fin migrationN) ⟨98,by decide⟩
      (by decide) d (by simpa [targetDegree] using hd) (by simpa [targetDegree] using hne)
    rcases h with h|h|h <;> rw [h] <;> simp [migrationProperLists,targetDegree]

private theorem migrationRow_L_zero (cs : List Char) (h : migrationRowGood cs) :
    migrationL (nativeRelationPolynomial migrationN (String.ofList cs)) = 0 := by
  rw [migrationC_apply,MigrationRows.sum_rowCoeff _ _ migrationTopLists_nodup]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero h.1)

private theorem migrationRow_proper_zero (cs : List Char) (h : migrationRowGood cs)
    (c : Fin migrationN →₀ ℕ) (hc : c∈migrationC) (d : Fin migrationN →₀ ℕ)
    (hd : d≤c) (hne : d≠c) : coeff d (nativeRelationPolynomial migrationN (String.ofList cs)) = 0 := by
  obtain ⟨ts,ht,rfl⟩ := migration_proper_cover c hc d hd hne
  rw [MigrationRows.rowCoeff_correct _ _ (migrationProperLists_nodup ts ht)]
  have hz : ((cs.splitOn ';').map fun mon => if KIP126.Computation.RelationCertificate.coeffChars migrationN ts mon then (1:ℕ) else 0).sum=0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨mon,hm,rfl⟩ := List.mem_map.mp hx
    rw [h.2 mon hm ts ht]
    rfl
  rw [hz,Nat.cast_zero]

private theorem migrationIdeal_L_zero
    (cert : ∀ code∈archiveSourceRelations, migrationRowGood code.toList)
    (p : nativePoly migrationN) (hp : p ∈ nativeIdeal migrationN archiveSourceRelations) : migrationL p=0 := by
  apply coefficientFunctional_span_zero migrationC _ _ p hp
  rintro r ⟨code,hcode,rfl⟩ q hq
  apply coefficientFunctional_zero_of_proper_divisors migrationC
  · have h := migrationRow_L_zero code.toList (cert code hcode)
    simpa only [String.ofList_toList,migrationL] using h
  · intro c hc d hd hne
    have h := migrationRow_proper_zero code.toList (cert code hcode) c hc d hd hne
    simpa only [String.ofList_toList,migrationL] using h
private theorem migrationL_X_mul (i : Fin migrationN) (hi : i.val=0 ∨ i.val=2)
    (p : nativePoly migrationN) : migrationL (MvPolynomial.X i * p) = 0 := by
  classical
  rw [migrationC_apply]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨ts,ht,rfl⟩ := List.mem_map.mp hx
  have hz : targetDegree ts i=0 := by
    rw [MigrationRows.targetDegree_apply ts (migrationTopLists_nodup ts ht)]
    have hni : i∉ts := by
      intro him
      have hall : ∀ ts∈migrationTopLists, ∀ j∈ts, j.val≠0 ∧ j.val≠2 := by
        intro vs hv k hk
        simp only [migrationTopLists,List.mem_cons,List.mem_nil_iff,or_false] at hv
        rcases hv with rfl|rfl|rfl|rfl <;>
          simp only [List.mem_cons,List.mem_nil_iff,or_false] at hk
        all_goals rcases hk with rfl|rfl|rfl <;> decide
      have h := hall ts ht i him
      rcases hi with hi|hi
      · exact h.1 hi
      · exact h.2 hi
    simp only [hni,if_false]
  rw [MvPolynomial.coeff_X_mul',if_neg]
  intro hle
  exact (Finsupp.mem_support_iff.mp hle) hz

private theorem migrationL_target : migrationL (MvPolynomial.X ⟨1,by decide⟩ *
    (MvPolynomial.X ⟨7,by decide⟩ * MvPolynomial.X ⟨275,by decide⟩)) = 1 := by
  classical
  rw [migrationC_apply]
  simp only [migrationTopLists,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  have mon : (MvPolynomial.X (⟨1,by decide⟩ : Fin migrationN) *
      (MvPolynomial.X ⟨7,by decide⟩ * MvPolynomial.X ⟨275,by decide⟩) : nativePoly migrationN) =
      MvPolynomial.monomial (targetDegree [⟨1,by decide⟩,⟨7,by decide⟩,⟨275,by decide⟩]) 1 := by
    simp only [MvPolynomial.X,MvPolynomial.monomial_mul,one_mul,targetDegree,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero]
  rw [mon]
  simp only [MvPolynomial.coeff_monomial]
  have hn := migrationTargetDegrees_nodup
  simp only [migrationTopLists,List.map_cons,List.map_nil,List.nodup_cons,List.mem_cons,
    or_false,not_or,List.not_mem_nil,List.nodup_nil,and_true] at hn
  rcases hn with ⟨⟨hab,hac,had⟩,⟨⟨hbc,hbd⟩,hcd⟩⟩
  simp only [if_true,if_neg hab,if_neg hac,if_neg had]
  simp

private theorem migration_projection_X_not_target
    (cert : ∀ code∈archiveSourceRelations, migrationRowGood code.toList)
    (i : Fin migrationN) (hi : i.val=0 ∨ i.val=2)
    (p : nativePoly migrationN) :
    nativeProjection migrationN archiveSourceRelations (MvPolynomial.X i*p) ≠
    nativeProjection migrationN archiveSourceRelations (MvPolynomial.X ⟨1,by decide⟩ *
      (MvPolynomial.X ⟨7,by decide⟩ * MvPolynomial.X ⟨275,by decide⟩)) := by
  intro h
  have hm : MvPolynomial.X i*p - (MvPolynomial.X ⟨1,by decide⟩ *
      (MvPolynomial.X ⟨7,by decide⟩ * MvPolynomial.X ⟨275,by decide⟩)) ∈
      nativeIdeal migrationN archiveSourceRelations := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change nativeProjection migrationN archiveSourceRelations _ = 0
    rw [map_sub,h,sub_self]
  have hz := migrationIdeal_L_zero cert _ hm
  rw [map_sub,migrationL_X_mul i hi p,migrationL_target,zero_sub] at hz
  exact one_ne_zero (neg_eq_zero.mp hz)

private theorem migration_source_X_not_target
    (cert : ∀ code∈archiveSourceRelations, migrationRowGood code.toList)
    (i : Fin migrationN) (hi : i.val=0 ∨ i.val=2)
    (a : nativeAlgebra migrationN archiveSourceRelations) :
    (nativeProjection migrationN archiveSourceRelations (MvPolynomial.X i))*a ≠
    (nativeProjection migrationN archiveSourceRelations (MvPolynomial.X ⟨1,by decide⟩ *
      (MvPolynomial.X ⟨7,by decide⟩ * MvPolynomial.X ⟨275,by decide⟩))) := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
  change nativeProjection migrationN archiveSourceRelations (MvPolynomial.X i) *
    nativeProjection migrationN archiveSourceRelations p ≠ _
  rw [← map_mul]
  exact migration_projection_X_not_target cert i hi p

private theorem migrationArchiveChecked :
    ∀ code∈archiveSourceRelations, migrationRowGood code.toList := by
  intro code hc
  exact MigrationFastCheck.good_implies_row code.toList (migrationArchiveFastChecked code hc)

end
end KIP126.Computation.CachedStandard
