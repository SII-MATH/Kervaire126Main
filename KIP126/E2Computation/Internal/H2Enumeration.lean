module
import all KIP126.E2Computation.Internal.MonomialEnumeration
import Mathlib.Data.List.Perm.Subperm
/-! Pure fixed enumeration and gate certificates for the h₂ annihilation in
weight (13,135). All candidates, factors, exceptions and finite checks retain
their original order and values. -/

@[expose] section
namespace KIP126.Computation.Table.Internal
open KIP126.Computation.CachedStandard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000
private theorem flatMap_filter_local {α β : Type} (cs : List α) (p : α → Bool) (f : α → List β) :
    (cs.filter p).flatMap f = cs.flatMap (fun i => if p i then f i else []) := by
  induction cs with
  | nil => rfl
  | cons i cs ih =>
    simp only [List.filter_cons, List.flatMap_cons]
    split <;> simp_all

private theorem enumerateMonomials_filter {n : ℕ} (degree : Fin n → ℕ × ℕ)
    (fuel lower s t : ℕ) (cs : List (Fin n)) (p : Fin n → Bool)
    (hp : ∀ i ∈ cs, lower ≤ i.val → (degree i).2 ≤ t → p i = true) :
    enumerateMonomials degree (cs.filter p) fuel lower s t =
      enumerateMonomials degree cs fuel lower s t := by
  induction fuel generalizing lower s t with
  | zero => rfl
  | succ fuel ih =>
    simp only [enumerateMonomials]
    split
    · rfl
    · rw [flatMap_filter_local]
      apply List.flatMap_congr
      intro i hi
      split
      next hpi =>
        split
        next he =>
          rw [ih i.val (s - (degree i).1) (t - (degree i).2)]
          intro j hj hji hjt
          exact hp j hj (le_trans he.1 hji) (le_trans hjt (Nat.sub_le _ _))
        next he => rfl
      next hpi =>
        symm
        split
        next he => exact False.elim (hpi (hp i hi he.1 he.2.2))
        next he => rfl


private theorem takeWhile_le_eq_filter {α : Type} (v : α → ℕ) (cs : List α)
    (hs : cs.Pairwise fun a b => v a ≤ v b) (t : ℕ) :
    cs.takeWhile (fun a => v a ≤ t) = cs.filter (fun a => v a ≤ t) := by
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    obtain ⟨ha, hs⟩ := List.pairwise_cons.mp hs
    by_cases hat : v a ≤ t
    · simp only [List.takeWhile_cons, List.filter_cons, decide_eq_true hat, if_true]
      rw [ih hs]
    · simp only [List.takeWhile_cons, List.filter_cons, decide_eq_false hat, Bool.false_eq_true, if_false]
      symm
      apply List.filter_eq_nil_iff.mpr
      intro b hb
      simp only [decide_eq_true_eq]
      have hab := ha b hb
      omega

private theorem dropWhile_lt_eq_filter {α : Type} (v : α → ℕ) (cs : List α)
    (hs : cs.Pairwise fun a b => v a ≤ v b) (lower : ℕ) :
    cs.dropWhile (fun a => v a < lower) = cs.filter (fun a => lower ≤ v a) := by
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    obtain ⟨ha, hs⟩ := List.pairwise_cons.mp hs
    by_cases hal : v a < lower
    · have hna : ¬lower ≤ v a := by omega
      simp only [List.dropWhile_cons, List.filter_cons, decide_eq_true hal, decide_eq_false hna,
        Bool.false_eq_true, if_true, if_false]
      exact ih hs
    · have hla : lower ≤ v a := by omega
      simp only [List.dropWhile_cons, List.filter_cons, decide_eq_false hal, decide_eq_true hla,
        Bool.false_eq_true, if_true, if_false]
      congr 1
      symm
      apply List.filter_eq_self.mpr
      intro b hb
      simp only [decide_eq_true_eq]
      exact le_trans hla (ha b hb)

private abbrev Decorated (n : ℕ) := Fin n × ℕ × ℕ
private def cachedTrim {n : ℕ} (cs : List (Decorated n)) (lower t : ℕ) :=
  (cs.dropWhile (fun v => v.1.val < lower)).takeWhile (fun v => v.2.2 ≤ t)
private theorem cachedTrim_eq {n : ℕ} (cs : List (Decorated n))
    (hi : cs.Pairwise fun a b => a.1.val ≤ b.1.val)
    (ht : cs.Pairwise fun a b => a.2.2 ≤ b.2.2) (lower t : ℕ) :
    cachedTrim cs lower t = cs.filter (fun v => lower ≤ v.1.val ∧ v.2.2 ≤ t) := by
  unfold cachedTrim
  rw [takeWhile_le_eq_filter (fun v : Decorated n => v.2.2) _
    (ht.sublist (List.dropWhile_sublist _))]
  rw [dropWhile_lt_eq_filter (fun v : Decorated n => v.1.val) cs hi lower, List.filter_filter]
  apply List.filter_congr
  intro i hi
  simp only [Bool.decide_and, Bool.and_comm]
private def cachedEnumerate {n : ℕ} (cs : List (Decorated n)) :
    ℕ → ℕ → ℕ → ℕ → List (List (Fin n))
  | 0, _, s, t => if s = 0 ∧ t = 0 then [[]] else []
  | fuel+1, lower, s, t =>
    if s = 0 ∧ t = 0 then [[]] else
    let trimmed := cs.filter fun v => lower ≤ v.1.val ∧ v.2.2 ≤ t
    trimmed.flatMap fun v =>
      if lower ≤ v.1.val ∧ v.2.1 ≤ s ∧ v.2.2 ≤ t then
        (cachedEnumerate trimmed fuel v.1.val
          (s-v.2.1) (t-v.2.2)).map (fun w => v.1::w)
      else []
private theorem cachedFilter_map {n : ℕ} (degree : Fin n → ℕ × ℕ)
    (cs : List (Decorated n)) (hd : ∀ v ∈ cs, v.2 = degree v.1) (lower t : ℕ) :
    (cs.filter (fun v => lower ≤ v.1.val ∧ v.2.2 ≤ t)).map Prod.fst =
    (cs.map Prod.fst).filter (fun i => lower ≤ i.val ∧ (degree i).2 ≤ t) := by
  induction cs with
  | nil => rfl
  | cons v cs ih =>
    have hv := hd v (by simp)
    have ht := ih (fun v hv => hd v (by simp [hv]))
    simp only [List.filter_cons, List.map_cons]
    rw [hv]
    split <;> simp_all

private def trimPrefixCheck {n : ℕ} (cs : List (Decorated n))
    (gate good : List (Fin n) → Bool) : ℕ → ℕ → ℕ → ℕ → List (Fin n) → Bool
  | 0, _, s, t, pre => if gate pre then true else if s=0 ∧ t=0 then good pre else true
  | fuel+1, lower, s, t, pre =>
    if gate pre then true else if s=0 ∧ t=0 then good pre else
      let trimmed := cachedTrim cs lower t
      trimmed.all fun v => if lower≤v.1.val ∧ v.2.1≤s ∧ v.2.2≤t then
        trimPrefixCheck trimmed gate good fuel v.1.val (s-v.2.1) (t-v.2.2) (pre++[v.1])
      else true
private theorem trimPrefixCheck_sound {n : ℕ} (degree : Fin n → ℕ×ℕ)
    (cs : List (Decorated n)) (hd : ∀ v∈cs, v.2=degree v.1)
    (hi : cs.Pairwise fun a b => a.1.val ≤ b.1.val)
    (ht : cs.Pairwise fun a b => a.2.2 ≤ b.2.2)
    (gate good : List (Fin n) → Bool)
    (sound : ∀ pre, gate pre = true → ∀ suf, good (pre++suf) = true)
    (fuel lower s t : ℕ) (pre : List (Fin n))
    (hc : trimPrefixCheck cs gate good fuel lower s t pre = true) :
    (enumerateMonomials degree (cs.map Prod.fst) fuel lower s t).all
      (fun w => good (pre++w)) = true := by
  induction fuel generalizing lower s t pre cs with
  | zero =>
    by_cases hg : gate pre = true
    · exact List.all_eq_true.mpr (fun w hw => sound pre hg w)
    · simp only [trimPrefixCheck, hg, Bool.false_eq_true, if_false] at hc
      simp only [enumerateMonomials]
      split
      next hz => simpa [hz] using hc
      · rfl
  | succ fuel ih =>
    by_cases hg : gate pre = true
    · exact List.all_eq_true.mpr (fun w hw => sound pre hg w)
    simp only [trimPrefixCheck, hg, Bool.false_eq_true, if_false] at hc
    by_cases hz : s=0 ∧ t=0
    · simpa [enumerateMonomials,hz] using hc
    ·
      rw [if_neg hz] at hc
      rw [cachedTrim_eq cs hi ht] at hc
      rw [← enumerateMonomials_filter degree (fuel+1) lower s t (cs.map Prod.fst)
        (fun i => decide (lower ≤ i.val ∧ (degree i).2 ≤ t)) (by
          intro i hi hil hit
          simp only [decide_eq_true_eq]
          exact ⟨hil,hit⟩)]
      rw [← cachedFilter_map degree cs hd lower t]
      simp only [enumerateMonomials, if_neg hz, List.all_flatMap, List.all_map]
      apply List.all_eq_true.mpr
      intro v hv
      have hvd := hd v (List.mem_filter.mp hv).1
      have hcv := List.all_eq_true.mp hc v hv
      simp only [Function.comp_def]
      rw [← hvd]
      split
      next hcond =>
        rw [if_pos hcond] at hcv
        have hh := ih (cs := cs.filter (fun v => lower ≤ v.1.val ∧ v.2.2 ≤ t))
          (fun v hv => hd v (List.mem_filter.mp hv).1) (hi.filter _) (ht.filter _)
          v.1.val (s-v.2.1) (t-v.2.2) (pre++[v.1]) hcv
        simpa only [List.all_map, Function.comp_def, List.append_assoc,
          List.singleton_append] using hh
      next hcond => rfl

private def h2Candidates : List (Fin archiveGeneratorCount) := [⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩,⟨10,by decide⟩,⟨11,by decide⟩,⟨12,by decide⟩,⟨13,by decide⟩,⟨14,by decide⟩,⟨15,by decide⟩,⟨16,by decide⟩,⟨17,by decide⟩,⟨18,by decide⟩,⟨19,by decide⟩,⟨20,by decide⟩,⟨21,by decide⟩,⟨22,by decide⟩,⟨23,by decide⟩,⟨24,by decide⟩,⟨25,by decide⟩,⟨26,by decide⟩,⟨27,by decide⟩,⟨28,by decide⟩,⟨29,by decide⟩,⟨30,by decide⟩,⟨31,by decide⟩,⟨32,by decide⟩,⟨33,by decide⟩,⟨34,by decide⟩,⟨35,by decide⟩,⟨36,by decide⟩,⟨37,by decide⟩,⟨38,by decide⟩,⟨39,by decide⟩,⟨40,by decide⟩,⟨42,by decide⟩,⟨43,by decide⟩,⟨45,by decide⟩,⟨46,by decide⟩,⟨48,by decide⟩,⟨51,by decide⟩,⟨52,by decide⟩,⟨53,by decide⟩,⟨54,by decide⟩,⟨57,by decide⟩,⟨59,by decide⟩,⟨60,by decide⟩,⟨61,by decide⟩,⟨63,by decide⟩,⟨64,by decide⟩,⟨66,by decide⟩,⟨67,by decide⟩,⟨68,by decide⟩,⟨69,by decide⟩,⟨70,by decide⟩,⟨72,by decide⟩,⟨73,by decide⟩,⟨74,by decide⟩,⟨75,by decide⟩,⟨76,by decide⟩,⟨79,by decide⟩,⟨80,by decide⟩,⟨81,by decide⟩,⟨82,by decide⟩,⟨83,by decide⟩,⟨84,by decide⟩,⟨85,by decide⟩,⟨86,by decide⟩,⟨89,by decide⟩,⟨90,by decide⟩,⟨91,by decide⟩,⟨92,by decide⟩,⟨93,by decide⟩,⟨94,by decide⟩,⟨95,by decide⟩,⟨96,by decide⟩,⟨98,by decide⟩,⟨99,by decide⟩,⟨101,by decide⟩,⟨103,by decide⟩,⟨104,by decide⟩,⟨105,by decide⟩,⟨106,by decide⟩,⟨107,by decide⟩,⟨108,by decide⟩,⟨109,by decide⟩,⟨113,by decide⟩,⟨114,by decide⟩,⟨115,by decide⟩,⟨118,by decide⟩,⟨119,by decide⟩,⟨120,by decide⟩,⟨121,by decide⟩,⟨122,by decide⟩,⟨124,by decide⟩,⟨126,by decide⟩,⟨127,by decide⟩,⟨128,by decide⟩,⟨129,by decide⟩,⟨130,by decide⟩,⟨131,by decide⟩,⟨132,by decide⟩,⟨133,by decide⟩,⟨134,by decide⟩,⟨139,by decide⟩,⟨141,by decide⟩,⟨142,by decide⟩,⟨143,by decide⟩,⟨144,by decide⟩,⟨148,by decide⟩,⟨150,by decide⟩,⟨151,by decide⟩,⟨155,by decide⟩,⟨157,by decide⟩,⟨158,by decide⟩,⟨163,by decide⟩,⟨164,by decide⟩,⟨169,by decide⟩,⟨170,by decide⟩,⟨174,by decide⟩,⟨177,by decide⟩,⟨178,by decide⟩,⟨179,by decide⟩,⟨181,by decide⟩,⟨187,by decide⟩,⟨188,by decide⟩,⟨189,by decide⟩,⟨190,by decide⟩,⟨191,by decide⟩,⟨192,by decide⟩,⟨195,by decide⟩,⟨196,by decide⟩,⟨197,by decide⟩,⟨198,by decide⟩,⟨201,by decide⟩,⟨202,by decide⟩,⟨203,by decide⟩,⟨204,by decide⟩,⟨209,by decide⟩,⟨212,by decide⟩,⟨213,by decide⟩,⟨214,by decide⟩,⟨216,by decide⟩,⟨221,by decide⟩,⟨222,by decide⟩,⟨229,by decide⟩,⟨230,by decide⟩,⟨231,by decide⟩,⟨234,by decide⟩,⟨235,by decide⟩,⟨239,by decide⟩,⟨240,by decide⟩,⟨241,by decide⟩,⟨242,by decide⟩,⟨243,by decide⟩,⟨250,by decide⟩,⟨251,by decide⟩,⟨261,by decide⟩,⟨262,by decide⟩,⟨263,by decide⟩,⟨264,by decide⟩,⟨268,by decide⟩,⟨269,by decide⟩,⟨270,by decide⟩,⟨271,by decide⟩,⟨272,by decide⟩,⟨273,by decide⟩,⟨275,by decide⟩,⟨280,by decide⟩,⟨281,by decide⟩,⟨282,by decide⟩,⟨287,by decide⟩,⟨288,by decide⟩,⟨289,by decide⟩,⟨294,by decide⟩,⟨307,by decide⟩,⟨308,by decide⟩,⟨309,by decide⟩,⟨310,by decide⟩,⟨311,by decide⟩,⟨312,by decide⟩,⟨313,by decide⟩,⟨314,by decide⟩,⟨319,by decide⟩,⟨320,by decide⟩,⟨321,by decide⟩,⟨322,by decide⟩,⟨323,by decide⟩,⟨324,by decide⟩,⟨329,by decide⟩,⟨330,by decide⟩,⟨331,by decide⟩,⟨332,by decide⟩,⟨333,by decide⟩,⟨335,by decide⟩,⟨336,by decide⟩,⟨337,by decide⟩,⟨338,by decide⟩,⟨339,by decide⟩,⟨340,by decide⟩,⟨341,by decide⟩,⟨351,by decide⟩,⟨352,by decide⟩,⟨353,by decide⟩,⟨363,by decide⟩,⟨364,by decide⟩,⟨365,by decide⟩,⟨366,by decide⟩,⟨367,by decide⟩,⟨368,by decide⟩,⟨371,by decide⟩,⟨372,by decide⟩,⟨373,by decide⟩,⟨374,by decide⟩,⟨375,by decide⟩,⟨376,by decide⟩,⟨377,by decide⟩,⟨378,by decide⟩,⟨386,by decide⟩,⟨387,by decide⟩,⟨388,by decide⟩,⟨389,by decide⟩,⟨390,by decide⟩,⟨391,by decide⟩,⟨392,by decide⟩,⟨393,by decide⟩,⟨394,by decide⟩,⟨395,by decide⟩,⟨396,by decide⟩,⟨397,by decide⟩,⟨398,by decide⟩,⟨399,by decide⟩,⟨400,by decide⟩,⟨407,by decide⟩,⟨408,by decide⟩,⟨409,by decide⟩,⟨410,by decide⟩,⟨411,by decide⟩,⟨412,by decide⟩,⟨413,by decide⟩,⟨414,by decide⟩,⟨415,by decide⟩]
private theorem h2Candidates_complete : ∀ i : Fin archiveGeneratorCount,
    (archiveGeneratorDegree i).1 ≤ 13 → (archiveGeneratorDegree i).2 ≤ 135 → i ∈ h2Candidates := by decide
private def h2Factors : List (List (Fin archiveGeneratorCount)) := [[⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩],
[⟨0,by decide⟩,⟨1,by decide⟩],
[⟨0,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩],
[⟨2,by decide⟩,⟨3,by decide⟩],
[⟨0,by decide⟩,⟨4,by decide⟩],
[⟨0,by decide⟩,⟨0,by decide⟩,⟨26,by decide⟩],
[⟨18,by decide⟩,⟨69,by decide⟩],
[⟨2,by decide⟩,⟨7,by decide⟩,⟨7,by decide⟩],
[⟨7,by decide⟩,⟨8,by decide⟩],
[⟨0,by decide⟩,⟨11,by decide⟩],
[⟨7,by decide⟩,⟨18,by decide⟩],
[⟨2,by decide⟩,⟨36,by decide⟩],
[⟨2,by decide⟩,⟨38,by decide⟩],
[⟨0,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩,⟨13,by decide⟩],
[⟨0,by decide⟩,⟨0,by decide⟩,⟨230,by decide⟩],
[⟨0,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩,⟨80,by decide⟩],
[⟨0,by decide⟩,⟨70,by decide⟩],
[⟨2,by decide⟩,⟨34,by decide⟩],
[⟨0,by decide⟩,⟨5,by decide⟩],
[⟨10,by decide⟩,⟨18,by decide⟩,⟨18,by decide⟩],
[⟨7,by decide⟩,⟨10,by decide⟩],
[⟨0,by decide⟩,⟨158,by decide⟩],
[⟨2,by decide⟩,⟨143,by decide⟩],
[⟨7,by decide⟩,⟨17,by decide⟩],
[⟨0,by decide⟩,⟨28,by decide⟩],
[⟨0,by decide⟩,⟨33,by decide⟩],
[⟨0,by decide⟩,⟨35,by decide⟩],
[⟨0,by decide⟩,⟨24,by decide⟩],
[⟨0,by decide⟩,⟨25,by decide⟩],
[⟨2,by decide⟩,⟨26,by decide⟩],
[⟨7,by decide⟩,⟨43,by decide⟩],
[⟨0,by decide⟩,⟨48,by decide⟩],
[⟨2,by decide⟩,⟨128,by decide⟩],
[⟨2,by decide⟩,⟨129,by decide⟩],
[⟨2,by decide⟩,⟨37,by decide⟩],
[⟨10,by decide⟩,⟨142,by decide⟩],
[⟨17,by decide⟩,⟨94,by decide⟩],
[⟨0,by decide⟩,⟨76,by decide⟩],
[⟨1,by decide⟩,⟨2,by decide⟩],
[⟨2,by decide⟩,⟨4,by decide⟩],
[⟨2,by decide⟩,⟨96,by decide⟩],
[⟨2,by decide⟩,⟨2,by decide⟩,⟨11,by decide⟩],
[⟨7,by decide⟩,⟨29,by decide⟩],
[⟨10,by decide⟩,⟨70,by decide⟩],
[⟨2,by decide⟩,⟨12,by decide⟩],
[⟨2,by decide⟩,⟨2,by decide⟩,⟨53,by decide⟩],
[⟨7,by decide⟩,⟨9,by decide⟩],
[⟨2,by decide⟩,⟨13,by decide⟩,⟨76,by decide⟩],
[⟨2,by decide⟩,⟨288,by decide⟩],
[⟨2,by decide⟩,⟨5,by decide⟩],
[⟨2,by decide⟩,⟨28,by decide⟩],
[⟨2,by decide⟩,⟨109,by decide⟩],
[⟨9,by decide⟩,⟨33,by decide⟩],
[⟨9,by decide⟩,⟨203,by decide⟩],
[⟨9,by decide⟩,⟨204,by decide⟩],
[⟨2,by decide⟩,⟨148,by decide⟩],
[⟨29,by decide⟩,⟨142,by decide⟩],
[⟨2,by decide⟩,⟨48,by decide⟩],
[⟨2,by decide⟩,⟨57,by decide⟩],
[⟨2,by decide⟩,⟨61,by decide⟩],
[⟨7,by decide⟩,⟨32,by decide⟩],
[⟨35,by decide⟩,⟨95,by decide⟩],
[⟨2,by decide⟩,⟨2,by decide⟩,⟨43,by decide⟩],
[⟨2,by decide⟩,⟨45,by decide⟩],
[⟨9,by decide⟩,⟨142,by decide⟩],
[⟨9,by decide⟩,⟨25,by decide⟩],
[⟨10,by decide⟩,⟨25,by decide⟩],
[⟨10,by decide⟩,⟨216,by decide⟩],
[⟨13,by decide⟩,⟨35,by decide⟩],
[⟨6,by decide⟩,⟨11,by decide⟩],
[⟨7,by decide⟩,⟨11,by decide⟩],
[⟨7,by decide⟩,⟨33,by decide⟩],
[⟨2,by decide⟩,⟨108,by decide⟩],
[⟨2,by decide⟩,⟨52,by decide⟩],
[⟨2,by decide⟩,⟨261,by decide⟩],
[⟨8,by decide⟩,⟨134,by decide⟩],
[⟨9,by decide⟩,⟨120,by decide⟩],
[⟨9,by decide⟩,⟨35,by decide⟩],
[⟨10,by decide⟩,⟨235,by decide⟩],
[⟨11,by decide⟩,⟨25,by decide⟩],
[⟨18,by decide⟩,⟨76,by decide⟩],
[⟨18,by decide⟩,⟨23,by decide⟩],
[⟨18,by decide⟩,⟨73,by decide⟩],
[⟨24,by decide⟩,⟨174,by decide⟩],
[⟨43,by decide⟩,⟨139,by decide⟩],
[⟨2,by decide⟩,⟨46,by decide⟩],
[⟨2,by decide⟩,⟨81,by decide⟩],
[⟨2,by decide⟩,⟨407,by decide⟩]]
private def h2Exceptions : List (List (Fin archiveGeneratorCount)) := [[⟨0,by decide⟩,⟨0,by decide⟩,⟨69,by decide⟩,⟨79,by decide⟩],
[⟨0,by decide⟩,⟨0,by decide⟩,⟨371,by decide⟩],
[⟨0,by decide⟩,⟨18,by decide⟩,⟨188,by decide⟩],
[⟨0,by decide⟩,⟨68,by decide⟩,⟨86,by decide⟩],
[⟨0,by decide⟩,⟨74,by decide⟩,⟨74,by decide⟩],
[⟨0,by decide⟩,⟨74,by decide⟩,⟨75,by decide⟩],
[⟨0,by decide⟩,⟨75,by decide⟩,⟨75,by decide⟩],
[⟨2,by decide⟩,⟨2,by decide⟩,⟨64,by decide⟩,⟨69,by decide⟩],
[⟨2,by decide⟩,⟨67,by decide⟩,⟨76,by decide⟩],
[⟨2,by decide⟩,⟨68,by decide⟩,⟨74,by decide⟩],
[⟨2,by decide⟩,⟨68,by decide⟩,⟨75,by decide⟩],
[⟨6,by decide⟩,⟨53,by decide⟩,⟨69,by decide⟩],
[⟨9,by decide⟩,⟨239,by decide⟩]]
private def h2WordGood (w : List (Fin archiveGeneratorCount)) : Bool :=
  h2Factors.any (fun f => decide (List.Subperm f (⟨2,by decide⟩ :: w))) || h2Exceptions.contains w
private def h2Decorated : List (Decorated archiveGeneratorCount) := [
(⟨0,by decide⟩,1,1),
(⟨1,by decide⟩,1,2),
(⟨2,by decide⟩,1,4),
(⟨3,by decide⟩,1,8),
(⟨4,by decide⟩,3,11),
(⟨5,by decide⟩,5,14),
(⟨6,by decide⟩,5,16),
(⟨7,by decide⟩,1,16),
(⟨8,by decide⟩,4,18),
(⟨9,by decide⟩,4,21),
(⟨10,by decide⟩,4,22),
(⟨11,by decide⟩,3,22),
(⟨12,by decide⟩,7,23),
(⟨13,by decide⟩,4,24),
(⟨14,by decide⟩,9,26),
(⟨15,by decide⟩,9,28),
(⟨16,by decide⟩,8,30),
(⟨17,by decide⟩,7,30),
(⟨18,by decide⟩,1,32),
(⟨19,by decide⟩,8,33),
(⟨20,by decide⟩,7,33),
(⟨21,by decide⟩,11,35),
(⟨22,by decide⟩,7,36),
(⟨23,by decide⟩,6,36),
(⟨24,by decide⟩,5,36),
(⟨25,by decide⟩,4,36),
(⟨26,by decide⟩,4,37),
(⟨27,by decide⟩,13,38),
(⟨28,by decide⟩,6,38),
(⟨29,by decide⟩,7,39),
(⟨30,by decide⟩,13,40),
(⟨31,by decide⟩,12,42),
(⟨32,by decide⟩,7,42),
(⟨33,by decide⟩,6,42),
(⟨34,by decide⟩,5,42),
(⟨35,by decide⟩,4,42),
(⟨36,by decide⟩,6,44),
(⟨37,by decide⟩,4,44),
(⟨38,by decide⟩,3,44),
(⟨39,by decide⟩,12,45),
(⟨40,by decide⟩,11,45),
(⟨42,by decide⟩,9,48),
(⟨43,by decide⟩,4,48),
(⟨45,by decide⟩,10,51),
(⟨46,by decide⟩,9,51),
(⟨48,by decide⟩,7,53),
(⟨51,by decide⟩,9,54),
(⟨52,by decide⟩,8,54),
(⟨53,by decide⟩,7,55),
(⟨54,by decide⟩,6,56),
(⟨57,by decide⟩,5,57),
(⟨59,by decide⟩,13,60),
(⟨60,by decide⟩,13,60),
(⟨61,by decide⟩,6,60),
(⟨63,by decide⟩,13,63),
(⟨64,by decide⟩,10,63),
(⟨66,by decide⟩,10,64),
(⟨67,by decide⟩,7,64),
(⟨68,by decide⟩,6,64),
(⟨69,by decide⟩,1,64),
(⟨70,by decide⟩,4,65),
(⟨72,by decide⟩,10,66),
(⟨73,by decide⟩,7,67),
(⟨74,by decide⟩,6,67),
(⟨75,by decide⟩,6,67),
(⟨76,by decide⟩,5,67),
(⟨79,by decide⟩,10,69),
(⟨80,by decide⟩,9,69),
(⟨81,by decide⟩,9,70),
(⟨82,by decide⟩,8,70),
(⟨83,by decide⟩,8,70),
(⟨84,by decide⟩,7,70),
(⟨85,by decide⟩,7,70),
(⟨86,by decide⟩,6,70),
(⟨89,by decide⟩,10,72),
(⟨90,by decide⟩,10,72),
(⟨91,by decide⟩,6,72),
(⟨92,by decide⟩,5,72),
(⟨93,by decide⟩,5,72),
(⟨94,by decide⟩,4,72),
(⟨95,by decide⟩,7,73),
(⟨96,by decide⟩,4,73),
(⟨98,by decide⟩,10,74),
(⟨99,by decide⟩,4,74),
(⟨101,by decide⟩,10,75),
(⟨103,by decide⟩,10,76),
(⟨104,by decide⟩,10,76),
(⟨105,by decide⟩,9,76),
(⟨106,by decide⟩,9,76),
(⟨107,by decide⟩,8,76),
(⟨108,by decide⟩,8,77),
(⟨109,by decide⟩,6,77),
(⟨113,by decide⟩,13,78),
(⟨114,by decide⟩,11,78),
(⟨115,by decide⟩,10,79),
(⟨118,by decide⟩,13,81),
(⟨119,by decide⟩,13,82),
(⟨120,by decide⟩,8,82),
(⟨121,by decide⟩,7,82),
(⟨122,by decide⟩,6,82),
(⟨124,by decide⟩,12,83),
(⟨126,by decide⟩,13,84),
(⟨127,by decide⟩,13,84),
(⟨128,by decide⟩,7,84),
(⟨129,by decide⟩,7,84),
(⟨130,by decide⟩,6,84),
(⟨131,by decide⟩,5,84),
(⟨132,by decide⟩,4,84),
(⟨133,by decide⟩,9,85),
(⟨134,by decide⟩,8,85),
(⟨139,by decide⟩,9,87),
(⟨141,by decide⟩,10,88),
(⟨142,by decide⟩,4,88),
(⟨143,by decide⟩,3,88),
(⟨144,by decide⟩,12,89),
(⟨148,by decide⟩,6,91),
(⟨150,by decide⟩,13,92),
(⟨151,by decide⟩,12,92),
(⟨155,by decide⟩,12,93),
(⟨157,by decide⟩,10,94),
(⟨158,by decide⟩,7,94),
(⟨163,by decide⟩,4,96),
(⟨164,by decide⟩,10,97),
(⟨169,by decide⟩,13,98),
(⟨170,by decide⟩,12,98),
(⟨174,by decide⟩,8,99),
(⟨177,by decide⟩,12,100),
(⟨178,by decide⟩,11,100),
(⟨179,by decide⟩,10,100),
(⟨181,by decide⟩,8,101),
(⟨187,by decide⟩,12,102),
(⟨188,by decide⟩,11,102),
(⟨189,by decide⟩,10,102),
(⟨190,by decide⟩,8,102),
(⟨191,by decide⟩,7,102),
(⟨192,by decide⟩,10,103),
(⟨195,by decide⟩,12,104),
(⟨196,by decide⟩,10,104),
(⟨197,by decide⟩,8,104),
(⟨198,by decide⟩,7,104),
(⟨201,by decide⟩,12,105),
(⟨202,by decide⟩,10,105),
(⟨203,by decide⟩,7,106),
(⟨204,by decide⟩,7,106),
(⟨209,by decide⟩,10,107),
(⟨212,by decide⟩,12,108),
(⟨213,by decide⟩,9,108),
(⟨214,by decide⟩,7,108),
(⟨216,by decide⟩,8,109),
(⟨221,by decide⟩,10,110),
(⟨222,by decide⟩,7,110),
(⟨229,by decide⟩,11,112),
(⟨230,by decide⟩,7,112),
(⟨231,by decide⟩,6,112),
(⟨234,by decide⟩,13,113),
(⟨235,by decide⟩,9,113),
(⟨239,by decide⟩,9,114),
(⟨240,by decide⟩,7,114),
(⟨241,by decide⟩,6,114),
(⟨242,by decide⟩,5,114),
(⟨243,by decide⟩,12,115),
(⟨250,by decide⟩,12,116),
(⟨251,by decide⟩,9,116),
(⟨261,by decide⟩,12,119),
(⟨262,by decide⟩,11,119),
(⟨263,by decide⟩,10,119),
(⟨264,by decide⟩,7,119),
(⟨268,by decide⟩,13,120),
(⟨269,by decide⟩,10,120),
(⟨270,by decide⟩,9,120),
(⟨271,by decide⟩,9,120),
(⟨272,by decide⟩,8,120),
(⟨273,by decide⟩,6,120),
(⟨275,by decide⟩,12,121),
(⟨280,by decide⟩,13,122),
(⟨281,by decide⟩,10,122),
(⟨282,by decide⟩,9,122),
(⟨287,by decide⟩,13,123),
(⟨288,by decide⟩,10,123),
(⟨289,by decide⟩,9,123),
(⟨294,by decide⟩,13,125),
(⟨307,by decide⟩,13,126),
(⟨308,by decide⟩,13,126),
(⟨309,by decide⟩,12,126),
(⟨310,by decide⟩,11,126),
(⟨311,by decide⟩,10,127),
(⟨312,by decide⟩,10,127),
(⟨313,by decide⟩,9,127),
(⟨314,by decide⟩,9,127),
(⟨319,by decide⟩,13,128),
(⟨320,by decide⟩,11,128),
(⟨321,by decide⟩,10,128),
(⟨322,by decide⟩,9,128),
(⟨323,by decide⟩,7,128),
(⟨324,by decide⟩,1,128),
(⟨329,by decide⟩,13,129),
(⟨330,by decide⟩,12,129),
(⟨331,by decide⟩,11,129),
(⟨332,by decide⟩,10,129),
(⟨333,by decide⟩,9,129),
(⟨335,by decide⟩,12,130),
(⟨336,by decide⟩,11,130),
(⟨337,by decide⟩,10,130),
(⟨338,by decide⟩,9,130),
(⟨339,by decide⟩,6,130),
(⟨340,by decide⟩,5,130),
(⟨341,by decide⟩,4,130),
(⟨351,by decide⟩,11,131),
(⟨352,by decide⟩,8,131),
(⟨353,by decide⟩,7,131),
(⟨363,by decide⟩,12,132),
(⟨364,by decide⟩,12,132),
(⟨365,by decide⟩,11,132),
(⟨366,by decide⟩,9,132),
(⟨367,by decide⟩,8,132),
(⟨368,by decide⟩,6,132),
(⟨371,by decide⟩,11,133),
(⟨372,by decide⟩,10,133),
(⟨373,by decide⟩,9,133),
(⟨374,by decide⟩,9,133),
(⟨375,by decide⟩,8,133),
(⟨376,by decide⟩,8,133),
(⟨377,by decide⟩,6,133),
(⟨378,by decide⟩,5,133),
(⟨386,by decide⟩,11,134),
(⟨387,by decide⟩,11,134),
(⟨388,by decide⟩,10,134),
(⟨389,by decide⟩,10,134),
(⟨390,by decide⟩,9,134),
(⟨391,by decide⟩,9,134),
(⟨392,by decide⟩,8,134),
(⟨393,by decide⟩,8,134),
(⟨394,by decide⟩,8,134),
(⟨395,by decide⟩,8,134),
(⟨396,by decide⟩,7,134),
(⟨397,by decide⟩,7,134),
(⟨398,by decide⟩,6,134),
(⟨399,by decide⟩,6,134),
(⟨400,by decide⟩,5,134),
(⟨407,by decide⟩,13,135),
(⟨408,by decide⟩,12,135),
(⟨409,by decide⟩,11,135),
(⟨410,by decide⟩,11,135),
(⟨411,by decide⟩,11,135),
(⟨412,by decide⟩,10,135),
(⟨413,by decide⟩,10,135),
(⟨414,by decide⟩,9,135),
(⟨415,by decide⟩,8,135)]
private theorem h2Decorated_degrees : ∀ v ∈ h2Decorated, v.2 = archiveGeneratorDegree v.1 := by decide
private theorem h2Decorated_candidates : h2Decorated.map Prod.fst = h2Candidates := by decide

private def h2GateTable : Array (List (Fin h2Factors.length)) := #[
[⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨9,by decide⟩,⟨13,by decide⟩,⟨14,by decide⟩,⟨15,by decide⟩,⟨16,by decide⟩,⟨18,by decide⟩,⟨21,by decide⟩,⟨24,by decide⟩,⟨25,by decide⟩,⟨26,by decide⟩,⟨27,by decide⟩,⟨28,by decide⟩,⟨31,by decide⟩,⟨37,by decide⟩],
[⟨1,by decide⟩,⟨38,by decide⟩],
[⟨0,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨7,by decide⟩,⟨11,by decide⟩,⟨12,by decide⟩,⟨13,by decide⟩,⟨15,by decide⟩,⟨17,by decide⟩,⟨22,by decide⟩,⟨29,by decide⟩,⟨32,by decide⟩,⟨33,by decide⟩,⟨34,by decide⟩,⟨38,by decide⟩,⟨39,by decide⟩,⟨40,by decide⟩,⟨41,by decide⟩,⟨44,by decide⟩,⟨45,by decide⟩,⟨47,by decide⟩,⟨48,by decide⟩,⟨49,by decide⟩,⟨50,by decide⟩,⟨51,by decide⟩,⟨55,by decide⟩,⟨57,by decide⟩,⟨58,by decide⟩,⟨59,by decide⟩,⟨62,by decide⟩,⟨63,by decide⟩,⟨72,by decide⟩,⟨73,by decide⟩,⟨74,by decide⟩,⟨85,by decide⟩,⟨86,by decide⟩,⟨87,by decide⟩],
[⟨3,by decide⟩],
[⟨4,by decide⟩,⟨39,by decide⟩],
[⟨18,by decide⟩,⟨49,by decide⟩],
[⟨69,by decide⟩],
[⟨7,by decide⟩,⟨8,by decide⟩,⟨10,by decide⟩,⟨20,by decide⟩,⟨23,by decide⟩,⟨30,by decide⟩,⟨42,by decide⟩,⟨46,by decide⟩,⟨60,by decide⟩,⟨70,by decide⟩,⟨71,by decide⟩],
[⟨8,by decide⟩,⟨75,by decide⟩],
[⟨46,by decide⟩,⟨52,by decide⟩,⟨53,by decide⟩,⟨54,by decide⟩,⟨64,by decide⟩,⟨65,by decide⟩,⟨76,by decide⟩,⟨77,by decide⟩],
[⟨19,by decide⟩,⟨20,by decide⟩,⟨35,by decide⟩,⟨43,by decide⟩,⟨66,by decide⟩,⟨67,by decide⟩,⟨78,by decide⟩],
[⟨9,by decide⟩,⟨41,by decide⟩,⟨69,by decide⟩,⟨70,by decide⟩,⟨79,by decide⟩],
[⟨44,by decide⟩],
[⟨13,by decide⟩,⟨47,by decide⟩,⟨68,by decide⟩],
[],
[],
[],
[⟨23,by decide⟩,⟨36,by decide⟩],
[⟨6,by decide⟩,⟨10,by decide⟩,⟨19,by decide⟩,⟨80,by decide⟩,⟨81,by decide⟩,⟨82,by decide⟩],
[],
[],
[],
[],
[⟨81,by decide⟩],
[⟨27,by decide⟩,⟨83,by decide⟩],
[⟨28,by decide⟩,⟨65,by decide⟩,⟨66,by decide⟩,⟨79,by decide⟩],
[⟨5,by decide⟩,⟨29,by decide⟩],
[],
[⟨24,by decide⟩,⟨50,by decide⟩],
[⟨42,by decide⟩,⟨56,by decide⟩],
[],
[],
[⟨60,by decide⟩],
[⟨25,by decide⟩,⟨52,by decide⟩,⟨71,by decide⟩],
[⟨17,by decide⟩],
[⟨26,by decide⟩,⟨61,by decide⟩,⟨68,by decide⟩,⟨77,by decide⟩],
[⟨11,by decide⟩],
[⟨34,by decide⟩],
[⟨12,by decide⟩],
[],
[],
[],
[],
[⟨30,by decide⟩,⟨62,by decide⟩,⟨84,by decide⟩],
[],
[⟨63,by decide⟩],
[⟨85,by decide⟩],
[],
[⟨31,by decide⟩,⟨57,by decide⟩],
[],
[],
[],
[⟨73,by decide⟩],
[⟨45,by decide⟩],
[],
[],
[],
[⟨58,by decide⟩],
[],
[],
[],
[⟨59,by decide⟩],
[],
[],
[],
[],
[],
[],
[],
[⟨6,by decide⟩],
[⟨16,by decide⟩,⟨43,by decide⟩],
[],
[],
[⟨82,by decide⟩],
[],
[],
[⟨37,by decide⟩,⟨47,by decide⟩,⟨80,by decide⟩],
[],
[],
[],
[⟨15,by decide⟩],
[⟨86,by decide⟩],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[⟨36,by decide⟩],
[⟨61,by decide⟩],
[⟨40,by decide⟩],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[⟨72,by decide⟩],
[⟨51,by decide⟩],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[⟨76,by decide⟩],
[],
[],
[],
[],
[],
[],
[],
[⟨32,by decide⟩],
[⟨33,by decide⟩],
[],
[],
[],
[],
[⟨75,by decide⟩],
[],
[],
[],
[],
[⟨84,by decide⟩],
[],
[],
[⟨35,by decide⟩,⟨56,by decide⟩,⟨64,by decide⟩],
[⟨22,by decide⟩],
[],
[],
[],
[],
[⟨55,by decide⟩],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[⟨21,by decide⟩],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[⟨83,by decide⟩],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[⟨53,by decide⟩],
[⟨54,by decide⟩],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[⟨67,by decide⟩],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[⟨14,by decide⟩],
[],
[],
[],
[],
[⟨78,by decide⟩],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[⟨74,by decide⟩],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[⟨48,by decide⟩],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[],
[⟨87,by decide⟩]]
private def h2IndexedGate (pre : List (Fin archiveGeneratorCount)) : Bool :=
  match pre.getLast? with
  | none => false
  | some i => ((h2GateTable[i.val]?).getD []).any fun k =>
      (h2Factors.get k).isSubperm (⟨2,by decide⟩::pre)
private theorem h2IndexedGate_sound (pre : List (Fin archiveGeneratorCount)) (hg : h2IndexedGate pre = true)
    (suf : List (Fin archiveGeneratorCount)) : h2WordGood (pre++suf) = true := by
  unfold h2IndexedGate at hg
  split at hg
  · cases hg
  · obtain ⟨k,hk,hsub⟩ := List.any_eq_true.mp hg
    have hp : (h2Factors.get k).Subperm (⟨2,by decide⟩::pre) := List.isSubperm_iff.mp hsub
    have hs : (⟨2,by decide⟩::pre).Sublist (⟨2,by decide⟩::(pre++suf)) := by
      simpa using (List.prefix_append (⟨2,by decide⟩::pre) suf).sublist
    have ht := hp.trans hs.subperm
    unfold h2WordGood
    rw [Bool.or_eq_true]
    left
    apply List.any_eq_true.mpr
    exact ⟨h2Factors.get k,List.get_mem _ _,by simpa only [decide_eq_true_eq] using ht⟩

private theorem h2Decorated_indexSorted : h2Decorated.Pairwise (fun a b => a.1.val ≤ b.1.val) := by decide
private theorem h2Decorated_degreeSorted : h2Decorated.Pairwise (fun a b => a.2.2 ≤ b.2.2) := by decide
private theorem h2PrefixChecked :
    trimPrefixCheck h2Decorated h2IndexedGate h2WordGood 13 0 13 135 [] = true := by decide +kernel
private theorem h2EnumerationChecked :
    (enumerateMonomials archiveGeneratorDegree h2Candidates 13 0 13 135).all h2WordGood = true := by
  have hh := trimPrefixCheck_sound archiveGeneratorDegree h2Decorated h2Decorated_degrees
    h2Decorated_indexSorted h2Decorated_degreeSorted
    h2IndexedGate h2WordGood h2IndexedGate_sound 13 0 13 135 [] h2PrefixChecked
  simpa only [h2Decorated_candidates,List.nil_append] using hh

end
end KIP126.Computation.Table.Internal
end
