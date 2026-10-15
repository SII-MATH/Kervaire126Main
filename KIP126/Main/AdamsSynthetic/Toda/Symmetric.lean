module

public import KIP126.Main.AdamsSynthetic.Context
import KIP126.Main.AdamsSynthetic.Toda.Product
import KIP126.Def.Comparison.ClassicalSynthetic.RealizationTower.Proofs
import KIP126.Def.ClassicalAdams.TowerNaturality.Proofs
import KIP126.Def.ClassicalAdams.TowerNaturality.Unit.Proofs
import KIP126.Def.ClassicalAdams.TowerResolution.Proofs
import KIP126.Def.ClassicalAdams.MapFiltration.Proofs
import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
import KIP126.Def.Synthetic.Context.Coherence.Proofs
import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
import KIP126.Def.Synthetic.Localization.Recovery.Proofs
import KIP126.Def.SpectralSequence.Permanence.Proofs
import KIP126.Def.StableHomotopy.Context.Mapping.Data
import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace KIP126.Main.AdamsSynthetic.Toda

open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Literature.AdamsSynthetic

set_option maxHeartbeats 12000000 in
/-- The symmetric synthetic Toda bracket for every order-two theta. -/
theorem symmetric_bracket : ∀ θ : BiHom 62 64 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn),
    θ + θ = 0 → TripleToda syntheticTwo θ syntheticTwo
      (lambdaMultiply 2 (sphereProduct etaClass θ)) := by
  have hstar : ∀ θ : BiHom 62 64 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn),
      sphereProduct (lambdaMultiply 2 etaClass) θ =
        lambdaMultiply 2 (sphereProduct etaClass θ) := by
    intro θ
    exact secondary_star_product adamsComparison etaClass θ
  -- Remaining symmetric Toda comparison for every order-two theta
  -- (MainPaper, lines 2550-2551), not just the selected theta_5.
  -- Continue with the synthetic secondary-operation comparison; the
  -- C-motivic tau * eta formula alone does not identify this lambda^2 value.
  open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
    CategoryTheory.MonoidalCategory KIP126.StableHomotopy
    KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
    KIP126.Synthetic.SpectralSequence KIP126.SpectralSequence
    KIP126.Steenrod.Milnor MvPolynomial in
  open scoped BigOperators TensorProduct DirectSum in
  set_option backward.isDefEq.respectTransparency false in
  classical
  let Syn := KIP126.Def.standardSyntheticContext.Syn
  let C := KIP126.Def.standardHF2AdamsContext.stableContext.Spectrum
  let H := KIP126.Def.standardHF2AdamsContext.stableContext.hf2
  let M := KIP126.Def.standardHF2AdamsContext.milnorCoordinates.toMilnor
  let D := adamsComparison
  have length_zero_trivial (t : ℕ) (ht : t ≠ 0) : Subsingleton (cochains 0 t) := by
    have hz (x : cochains 0 t) : x = 0 := by
      apply Subtype.ext
      change x.val = 0
      by_contra h
      exact ht (MvPolynomial.IsWeightedHomogeneous.inj_right h x.property.1
        (MvPolynomial.isWeightedHomogeneous_of_isEmpty
          (R := KIP126.Algebra.F2) weight x.val))
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩

  have hi_nonzero (i : ℕ) : Sphere.Internal.hi H M i ≠ 0 := by
    intro hz
    have hz' : MilnorCohomology.hi H M i = 0 := by
      apply (MilnorCohomology.comparison H M 1 (2 ^ i)).injective
      simpa only [map_zero, MilnorCohomology.comparison_hi] using hz
    obtain ⟨b, hb⟩ := (MilnorCohomology.hi_eq_zero_iff H M i).mp hz'
    haveI := length_zero_trivial (2 ^ i) (pow_ne_zero _ (by decide))
    have hb0 : b = 0 := Subsingleton.elim _ _
    rw [hb0, map_zero] at hb
    have hp := congrArg Subtype.val hb.symm
    exact pow_ne_zero _ (MvPolynomial.X_ne_zero ((0 : Fin 1), 0)) hp


  have low_support (d : ℕ →₀ ℕ) (hd : slotWeight d ≤ 4) :
      d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
    have hz (j : ℕ) (hj : 2 ≤ j) : d j = 0 := by
      by_contra hn
      have hw := Finsupp.le_weight_of_ne_zero'
        (fun j : ℕ => 2 ^ (j + 1) - 1) hn
      have hp : 2 ^ 3 ≤ 2 ^ (j + 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      change 2 ^ (j + 1) - 1 ≤ slotWeight d at hw
      norm_num at hp
      omega
    ext j
    rcases j with _ | _ | j
    · simp
    · simp
    · simp [hz (j + 2) (by omega)]

  have low_weight (d : ℕ →₀ ℕ) (hd : slotWeight d ≤ 4) :
      slotWeight d = d 0 + 3 * d 1 := by
    conv_lhs => rw [low_support d hd]
    simp [slotWeight, map_add, Finsupp.weight_single, mul_comm]

  have weight_one (d : ℕ →₀ ℕ) (hd : slotWeight d = 1) :
      d = Finsupp.single 0 1 := by
    have hw := low_weight d (by omega)
    have h0 : d 0 = 1 := by omega
    have h1 : d 1 = 0 := by omega
    rw [low_support d (by omega), h0, h1]
    simp

  have weight_two (d : ℕ →₀ ℕ) (hd : slotWeight d = 2) :
      d = Finsupp.single 0 2 := by
    have hw := low_weight d (by omega)
    have h0 : d 0 = 2 := by omega
    have h1 : d 1 = 0 := by omega
    rw [low_support d (by omega), h0, h1]
    simp

  have slot_positive (d : ℕ →₀ ℕ) (hd : d ≠ 0) : 1 ≤ slotWeight d := by
    apply Nat.one_le_iff_ne_zero.mpr
    have hp : 0 < slotWeight d := by
      change 0 < d.sum (fun j n => n • (2 ^ (j + 1) - 1))
      apply Finsupp.sum_pos _ hd
      intro j hj
      have hn : 0 < d j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
      have hw : 0 < 2 ^ (j + 1) - 1 := by
        have hh : 2 ≤ 2 ^ (j + 1) := by
          rw [pow_succ]
          have := Nat.one_le_pow j 2 (by decide)
          omega
        omega
      exact Nat.mul_pos hn hw
    omega

  have word_excess {s k : ℕ} (d : MilnorWord s ((s : ℤ) + k)) :
      ∑ i : Fin s, (slotWeight (d.val i) - 1) = k := by
    have hs : ∑ i : Fin s, slotWeight (d.val i) = s + k := by
      have ht := d.property.1
      dsimp only [wordDegree] at ht
      exact_mod_cast ht
    have he : (∑ i : Fin s, (slotWeight (d.val i) - 1)) + s = s + k := by
      calc
        _ = ∑ i : Fin s, ((slotWeight (d.val i) - 1) + 1) := by
          simp [Finset.sum_add_distrib]
        _ = ∑ i : Fin s, slotWeight (d.val i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hp := slot_positive (d.val i) (d.property.2 i)
          omega
        _ = s + k := hs
    omega

  have stem_one_word {s : ℕ} (d : MilnorWord s ((s : ℤ) + 1)) :
      ∃ i : Fin s, d.val i = Finsupp.single 0 2 ∧
        ∀ j : Fin s, j ≠ i → d.val j = Finsupp.single 0 1 := by
    let e : Fin s → ℕ := fun i => slotWeight (d.val i) - 1
    have he : ∑ i, e i = 1 := word_excess d
    obtain ⟨i, hi, hei⟩ := Finset.sum_pos_iff.mp (show 0 < ∑ i, e i by omega)
    have hbi : e i ≤ ∑ j, e j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
    have hei' : e i = 1 := by omega
    have hw : slotWeight (d.val i) = 2 := by
      have hp := slot_positive (d.val i) (d.property.2 i)
      dsimp only [e] at hei'
      omega
    refine ⟨i, weight_two _ hw, ?_⟩
    intro j hji
    have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin s)) e hi
    have hz : ∑ k ∈ Finset.univ.erase i, e k = 0 := by omega
    have hej : e j = 0 := by
      have hb : e j ≤ ∑ k ∈ Finset.univ.erase i, e k :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) (by simp [hji])
      omega
    apply weight_one
    have hp := slot_positive (d.val j) (d.property.2 j)
    dsimp only [e] at hej
    omega

  let stemOneWord (s : ℕ) (i : Fin s) : MilnorWord s ((s : ℤ) + 1) :=
    ⟨fun j => Finsupp.single 0 (1 + if j = i then 1 else 0), by
      constructor
      · simp [wordDegree, slotWeight, Finsupp.weight_single, Finset.sum_add_distrib]
      · intro j
        apply Finsupp.single_ne_zero.mpr
        omega⟩

  have stemOneWord_surjective (s : ℕ) : Function.Surjective (stemOneWord s) := by
    intro d
    obtain ⟨i, hi, hrest⟩ := stem_one_word d
    refine ⟨i, ?_⟩
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst j
      simpa only [stemOneWord, if_pos rfl, ite_true] using hi.symm
    · simpa [stemOneWord, hji] using (hrest j hji).symm

  have stemOneWord_injective (s : ℕ) : Function.Injective (stemOneWord s) := by
    intro i j hij
    by_contra hne
    have h := congrArg (fun d : MilnorWord s ((s : ℤ) + 1) => d.val i 0) hij
    simp [stemOneWord, hne] at h

  let stemOneWordEquiv (s : ℕ) :
      Fin s ≃ MilnorWord s ((s : ℤ) + 1) :=
    Equiv.ofBijective (stemOneWord s)
      ⟨stemOneWord_injective s, stemOneWord_surjective s⟩

  let x : TensorPower 1 := X (0, 0)
  let u : TensorPower 1 := X (0, 0) ^ 2
  let p : TensorPower 1 := X (0, 1)
  let q : TensorPower 1 := X (0, 0) ^ 3 + X (0, 1)
  let t : TensorPower 1 := X (0, 0) * X (0, 1)
  let z : TensorPower 1 := X (0, 0) ^ 4

  have dx : differentialPolynomial 1 x = 0 := by
    simpa [x, hiPolynomial] using hiPolynomial_differential 0

  have du : differentialPolynomial 1 u = 0 := by
    simpa [u, hiPolynomial] using hiPolynomial_differential 1

  have dp : differentialPolynomial 1 p = cupPolynomial u x := by
    simp [differentialPolynomial, p, u, x, cupPolynomial, insertLeft, insertRight,
      splitSlot, coproductGenerator, xi, Fin.sum_univ_succ, Finset.sum_range_succ]
    ring_nf
    simp [CharTwo.two_eq_zero]

  have dq : differentialPolynomial 1 q = cupPolynomial x u := by
    have hc (a b : TensorPower 2) : (a + b) ^ 3 =
        a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 := by
      calc
        _ = (a ^ 2 + b ^ 2) * (a + b) := by rw [pow_succ, CharTwo.add_sq]
        _ = _ := by ring
    simp [differentialPolynomial, q, u, x, cupPolynomial, insertLeft, insertRight,
      splitSlot, coproductGenerator, xi, Fin.sum_univ_succ, Finset.sum_range_succ, hc]
    ring_nf
    simp [CharTwo.two_eq_zero]

  let xc : cochains 1 1 :=
    ⟨x, by
      change IsCochain 1 x
      simpa [x, hiPolynomial] using hiPolynomial_mem 0⟩

  let uc : cochains 1 2 :=
    ⟨u, by
      change IsCochain 2 u
      simpa [u, hiPolynomial] using hiPolynomial_mem 1⟩

  let pc : cochains 1 3 := ⟨p, by
    constructor
    · simpa [p, weight] using
        (isWeightedHomogeneous_X (R := ZMod 2) (@weight 1) (0, 1))
    · change p ∈ (⨅ slot : Fin 1, LinearMap.ker (augmentSlot slot).toLinearMap)
      rw [Submodule.mem_iInf]
      intro slot
      have hs : slot = 0 := Subsingleton.elim _ _
      subst slot
      simp [LinearMap.mem_ker, augmentSlot, p]⟩

  let qc : cochains 1 3 := ⟨q, by
    constructor
    · have hh := (isWeightedHomogeneous_X (R := ZMod 2) (@weight 1) (0, 0)).pow 3
      have hp := pc.property.1
      change IsWeightedHomogeneous weight p 3 at hp
      have hh' : IsWeightedHomogeneous weight ((X ((0 : Fin 1), 0) : TensorPower 1) ^ 3) 3 :=
        by simpa [weight] using hh
      exact hh'.add hp
    · change q ∈ (⨅ slot : Fin 1, LinearMap.ker (augmentSlot slot).toLinearMap)
      rw [Submodule.mem_iInf]
      intro slot
      have hs : slot = 0 := Subsingleton.elim _ _
      subst slot
      simp [LinearMap.mem_ker, augmentSlot, q]⟩

  have dxc : differential 1 1 xc = 0 := Subtype.ext dx
  have duc : differential 1 2 uc = 0 := Subtype.ext du
  have dpc : differential 1 3 pc = cup uc xc := Subtype.ext dp
  have dqc : differential 1 3 qc = cup xc uc := Subtype.ext dq
  let xpow : (s : ℕ) → cochains s s :=
    Nat.rec
      (⟨1, by
        constructor
        · change IsWeightedHomogeneous (@weight 0) (1 : TensorPower 0) 0
          exact isWeightedHomogeneous_one (R := ZMod 2) (@weight 0)
        · change (1 : TensorPower 0) ∈
            (⨅ slot : Fin 0, LinearMap.ker (augmentSlot slot).toLinearMap)
          rw [Submodule.mem_iInf]
          intro slot
          exact Fin.elim0 slot⟩ : cochains 0 0)
      (fun s v => cup v xc)

  have dxpow (s : ℕ) : differential s s (xpow s) = 0 := by
    induction s with
    | zero =>
      apply Subtype.ext
      simp [differential, xpow, differentialPolynomial, insertLeft, insertRight,
        CharTwo.add_self_eq_zero]
    | succ s ih =>
      change differential _ _ (cup (xpow s) xc) = 0
      simp only [differential_cup, ih, dxc, cup_zero_left, cup_zero_right,
        map_zero, zero_add]

  have reindex_trans {s s' s'' t t' t'' : ℕ}
      (hs : s = s') (ht : t = t') (hs' : s' = s'') (ht' : t' = t'')
      (a : cochains s t) :
      reindex hs' ht' (reindex hs ht a) = reindex (hs.trans hs') (ht.trans ht') a := by
    subst s'
    subst s''
    subst t'
    subst t''
    rfl

  have reindex_cup_val_general {s s' t t' n m : ℕ}
      (hs : s + s' = n) (ht : t + t' = m) (a : cochains s t) (b : cochains s' t') :
      (reindex hs ht (cup a b)).val =
        blockRename (n := n) 0 (by omega) a.val * blockRename s (by omega) b.val := by
    subst n
    subst m
    exact cupPolynomial_blocks a.val b.val

  have cup_assoc {s s' s'' t t' t'' : ℕ}
      (a : cochains s t) (b : cochains s' t') (c : cochains s'' t'') :
      reindex (Nat.add_assoc s s' s'') (Nat.add_assoc t t' t'') (cup (cup a b) c) =
        cup a (cup b c) := by
    apply Subtype.ext
    rw [reindex_cup_val_general]
    change blockRename 0 _ (cupPolynomial a.val b.val) *
      blockRename (s + s') _ c.val = cupPolynomial a.val (cupPolynomial b.val c.val)
    simp only [cupPolynomial_blocks, map_mul, blockRename_comp, Nat.zero_add, Nat.add_zero]
    ring

  have xpow_val (s : ℕ) : (xpow s).val = ∏ i : Fin s, X (i, 0) := by
    induction s with
    | zero => simp [xpow]
    | succ s ih =>
      change cupPolynomial (xpow s).val xc.val = _
      rw [cupPolynomial, ih, map_prod]
      simp only [rename_X, xc, x]
      have hc (i : Fin s) : i.castAdd 1 = i.castSucc := Fin.ext rfl
      have hz : (0 : Fin 1).natAdd s = Fin.last s := Fin.ext (by simp)
      simpa only [hc, hz] using
        (Fin.prod_univ_castSucc (fun i : Fin (s + 1) => X (i, 0))).symm

  have xpow_cup (a b : ℕ) : cup (xpow a) (xpow b) = xpow (a + b) := by
    apply Subtype.ext
    change cupPolynomial (xpow a).val (xpow b).val = (xpow (a + b)).val
    rw [cupPolynomial, xpow_val, xpow_val, xpow_val, map_prod, map_prod]
    simp only [rename_X]
    exact (Fin.prod_univ_add (fun i : Fin (a + b) => X (i, 0))).symm

  have single_u_val (a b : ℕ) :
      (cup (cup (xpow a) uc) (xpow b)).val =
        (xpow (a + 1 + b)).val * X ((⟨a, by omega⟩ : Fin (a + 1 + b)), 0) := by
    have hx : cup (cup (xpow a) xc) (xpow b) = xpow (a + 1 + b) :=
      xpow_cup (a + 1) b
    rw [← hx]
    change cupPolynomial (cupPolynomial (xpow a).val uc.val) (xpow b).val =
      cupPolynomial (cupPolynomial (xpow a).val xc.val) (xpow b).val * _
    simp only [cupPolynomial, uc, xc, u, x, map_mul, map_pow, rename_X]
    have hi : ((0 : Fin 1).natAdd a).castAdd b =
        (⟨a, by omega⟩ : Fin (a + 1 + b)) := Fin.ext (by simp)
    rw [hi]
    ring


  have pure_word_exponents {s : ℕ} (e : Fin s → ℕ) :
      (slotExponentsEquiv s).symm (fun i => Finsupp.single 0 (e i)) =
        ∑ i : Fin s, Finsupp.single (i, 0) (e i) := by
    apply (slotExponentsEquiv s).injective
    rw [Equiv.apply_symm_apply]
    funext i
    ext j
    change Finsupp.single 0 (e i) j =
      (∑ k : Fin s, Finsupp.single (k, 0) (e k)) (i, j)
    by_cases hj : j = 0
    · subst j
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, hj, Ne.symm hj]

  have pure_word_polynomial {s : ℕ} (e : Fin s → ℕ) :
      (monomial ((slotExponentsEquiv s).symm (fun i => Finsupp.single 0 (e i))) 1 :
        TensorPower s) = ∏ i : Fin s, X (i, 0) ^ e i := by
    rw [pure_word_exponents, monomial_sum_one]
    simp only [← X_pow_eq_monomial]

  have unique_u_polynomial {s : ℕ} (i : Fin s) :
      (monomial ((slotExponentsEquiv s).symm
        (fun j => Finsupp.single 0 (1 + if j = i then 1 else 0))) 1 : TensorPower s) =
        (xpow s).val * X (i, 0) := by
    rw [pure_word_polynomial, xpow_val]
    simp only [pow_add, pow_one, Finset.prod_mul_distrib]
    congr 1
    simp [apply_ite]

  have stem_one_word_polynomial {s t : ℕ} (d : MilnorWord s t)
      (ht : t = s + 1) :
      ∃ i : Fin s, ((cochainsWordEquiv s t).symm (Finsupp.single d 1)).val =
        (xpow s).val * X (i, 0) := by
    have hd : wordDegree d.val = (s : ℤ) + 1 := by
      rw [d.property.1, ht]
      push_cast
      rfl
    let d' : MilnorWord s ((s : ℤ) + 1) := ⟨d.val, hd, d.property.2⟩
    obtain ⟨i, hi⟩ := stemOneWord_surjective s d'
    refine ⟨i, ?_⟩
    rw [cochainsWordEquiv_symm_single_val]
    have hv : d.val = fun j => Finsupp.single 0 (1 + if j = i then 1 else 0) :=
      (congrArg Subtype.val hi).symm
    rw [hv]
    exact unique_u_polynomial i

  let degree_one_two_equiv : cochains 1 2 ≃ₗ[ZMod 2] ZMod 2 :=
    (cochainsWordEquiv 1 2).trans
      ((Finsupp.domLCongr (R := ZMod 2) (stemOneWordEquiv 1).symm).trans
        (Finsupp.uniqueLinearEquiv (ZMod 2) (ZMod 2) (0 : Fin 1)))

  let Boundary {s t : ℕ} (w : cochains s t) : Prop :=
    ∃ (n : ℕ) (h : n + 1 = s) (v : cochains n t),
      reindex h rfl (differential n t v) = w

  have boundary_reindex {s s' t t' : ℕ} (hs : s = s') (ht : t = t')
      {w : cochains s t} (hw : Boundary w) : Boundary (reindex hs ht w) := by
    subst s'
    subst t'
    exact hw

  have boundary_cup_cycle {s s' t t' : ℕ} {w : cochains s t} (hw : Boundary w)
      (v : cochains s' t') (hv : differential s' t' v = 0) : Boundary (cup w v) := by
    obtain ⟨n, hs, a, ha⟩ := hw
    subst s
    change differential n t a = w at ha
    subst w
    refine ⟨n + s', by omega, cup a v, ?_⟩
    rw [differential_cup, hv, cup_zero_right, map_zero, add_zero, reindex_trans]
    rfl

  have cycle_cup_boundary {s s' t t' : ℕ} (v : cochains s t)
      (hv : differential s t v = 0) {w : cochains s' t'} (hw : Boundary w) :
      Boundary (cup v w) := by
    obtain ⟨n, hs, a, ha⟩ := hw
    subst s'
    change differential n t' a = w at ha
    subst w
    refine ⟨s + n, by omega, cup v a, ?_⟩
    rw [differential_cup, hv, cup_zero_left, map_zero, zero_add, reindex_trans]
    rfl

  have ux_boundary : Boundary (cup uc xc) := ⟨1, rfl, pc, dpc⟩
  have xu_boundary : Boundary (cup xc uc) := ⟨1, rfl, qc, dqc⟩

  have xpow_one : xpow 1 = xc := by
    apply Subtype.ext
    simp [xpow, cup, cupPolynomial, xc, x]

  have boundary_assoc_left {s s' s'' t t' t'' : ℕ}
      (a : cochains s t) (b : cochains s' t') (c : cochains s'' t'')
      (h : Boundary (cup a (cup b c))) : Boundary (cup (cup a b) c) := by
    have hh := boundary_reindex (Nat.add_assoc s s' s'').symm
      (Nat.add_assoc t t' t'').symm h
    rw [← cup_assoc, reindex_trans] at hh
    exact hh

  have single_u_boundary (a b : ℕ) (hab : 1 ≤ a + b) :
      Boundary (cup (cup (xpow a) uc) (xpow b)) := by
    cases a with
    | zero =>
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ b)
      have hb := boundary_cup_cycle ux_boundary (xpow c) (dxpow c)
      have hb' := boundary_reindex (Nat.add_assoc 1 1 c) (Nat.add_assoc 2 1 c) hb
      rw [cup_assoc, ← xpow_one, xpow_cup] at hb'
      have hh := cycle_cup_boundary (xpow 0) (dxpow 0) hb'
      have hh' := boundary_assoc_left (xpow 0) uc (xpow (1 + c)) hh
      exact hh'
    | succ a =>
      have hb := cycle_cup_boundary (xpow a) (dxpow a) xu_boundary
      have hb' := boundary_assoc_left (xpow a) xc uc hb
      exact boundary_cup_cycle hb' (xpow b) (dxpow b)

  have reindex_unique_u_val {s s' t t' : ℕ} (hs : s = s') (ht : t = t')
      (w : cochains s t) (i : Fin s)
      (hw : w.val = (xpow s).val * X (i, 0)) :
      (reindex hs ht w).val = (xpow s').val * X (Fin.cast hs i, 0) := by
    subst s'
    subst t'
    exact hw

  have basis_boundary (n : ℕ) (d : MilnorWord (n + 2) ((n + 3 : ℕ) : ℤ)) :
      Boundary ((cochainsWordEquiv (n + 2) (n + 3)).symm (Finsupp.single d 1)) := by
    obtain ⟨i, hi⟩ := stem_one_word_polynomial d (by omega)
    let a := i.val
    let b := n + 1 - i.val
    have hi' := i.isLt
    have hs : a + 1 + b = n + 2 := by dsimp [a, b]; omega
    have ht : a + 2 + b = n + 3 := by dsimp [a, b]; omega
    have hab : 1 ≤ a + b := by dsimp [a, b]; omega
    have hb := boundary_reindex hs ht (single_u_boundary a b hab)
    have he : reindex hs ht (cup (cup (xpow a) uc) (xpow b)) =
        (cochainsWordEquiv (n + 2) (n + 3)).symm (Finsupp.single d 1) := by
      apply Subtype.ext
      rw [reindex_unique_u_val hs ht _ _ (single_u_val a b), hi]
      congr 2
    rwa [he] at hb

  have boundary_mem_range {n t : ℕ} {w : cochains (n + 1) t} (hw : Boundary w) :
      w ∈ LinearMap.range (differential n t) := by
    obtain ⟨m, hm, v, hv⟩ := hw
    have hmn : m = n := by omega
    subst m
    exact ⟨v, hv⟩

  have stem_one_surjective (n : ℕ) : Function.Surjective (differential (n + 1) (n + 3)) := by
    intro w
    have hw : w ∈ LinearMap.range (differential (n + 1) (n + 3)) := by
      let e := cochainsWordEquiv (n + 2) (n + 3)
      have hgen (z : MilnorWord (n + 2) ((n + 3 : ℕ) : ℤ) →₀ ZMod 2) :
          e.symm z ∈ LinearMap.range (differential (n + 1) (n + 3)) := by
        induction z using Finsupp.induction_linear with
        | zero => simp
        | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
        | single d r =>
          have hd := boundary_mem_range (basis_boundary n d)
          have hr := Submodule.smul_mem (LinearMap.range (differential (n + 1) (n + 3))) r hd
          simpa only [e, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one] using hr
      simpa only [e, LinearEquiv.symm_apply_apply] using hgen (e w)
    exact hw


  have cohomology_stem_one_zero (n : ℕ) :
      Subsingleton (MilnorCohomology.Cohomology H M (n + 2) (n + 3)) := by
    have hz (z : MilnorCohomology.Cohomology H M (n + 2) (n + 3)) : z = 0 := by
      obtain ⟨x, rfl⟩ := (MilnorCohomology.boundariesInCycles H M (n + 2) (n + 3)).mkQ_surjective z
      apply (MilnorCohomology.classOf_eq_zero_iff H M x).mpr
      exact stem_one_surjective n x.val
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩

  have e2_stem_one_zero (n : ℕ) :
      Subsingleton (E2 H SphereSpectrum ((n + 2 : ℕ) : ℤ) ((n + 3 : ℕ) : ℤ)) := by
    letI := cohomology_stem_one_zero n
    exact (MilnorCohomology.comparison H M (n + 2) (n + 3)).symm.injective.subsingleton

  have all_e2_stem_one_zero (j : ℤ) (hj : 0 ≤ j) (hj1 : j ≠ 1) :
      Subsingleton (E2 H SphereSpectrum j (1 + j)) := by
    lift j to ℕ using hj
    cases j with
    | zero =>
      letI : IsEmpty (MilnorWord 0 (1 : ℤ)) := ⟨fun d => by
        have hd := milnorWord_zero_degree d
        norm_num at hd⟩
      letI : Subsingleton (cochains 0 1) := (cochainsWordEquiv 0 1).injective.subsingleton
      letI : Subsingleton (MilnorCohomology.Cohomology H M 0 1) := inferInstance
      exact (MilnorCohomology.comparison H M 0 1).symm.injective.subsingleton
    | succ j =>
      cases j with
      | zero => exact (hj1 rfl).elim
      | succ n =>
        simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
          add_assoc, add_comm, add_left_comm] using e2_stem_one_zero n

  have cochain_stem_one_nonzero_unique (x y : cochains 1 2) (hx : x ≠ 0) (hy : y ≠ 0) :
      x = y := by
    have hf (r : ZMod 2) : r = 0 ∨ r = 1 := by fin_cases r <;> simp
    have hxe : degree_one_two_equiv x ≠ 0 :=
      fun h => hx (degree_one_two_equiv.map_eq_zero_iff.mp h)
    have hye : degree_one_two_equiv y ≠ 0 :=
      fun h => hy (degree_one_two_equiv.map_eq_zero_iff.mp h)
    apply degree_one_two_equiv.injective
    exact ((hf _).resolve_left hxe).trans ((hf _).resolve_left hye).symm

  have cohomology_stem_one_nonzero_unique
      (x y : MilnorCohomology.Cohomology H M 1 2) (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
    obtain ⟨a, rfl⟩ := (MilnorCohomology.boundariesInCycles H M 1 2).mkQ_surjective x
    obtain ⟨b, rfl⟩ := (MilnorCohomology.boundariesInCycles H M 1 2).mkQ_surjective y
    have ha : a.val ≠ 0 := by
      intro h
      have ha0 : a = 0 := Subtype.ext h
      exact hx (by rw [ha0, map_zero])
    have hb : b.val ≠ 0 := by
      intro h
      have hb0 : b = 0 := Subtype.ext h
      exact hy (by rw [hb0, map_zero])
    have hab : a = b := Subtype.ext (cochain_stem_one_nonzero_unique a.val b.val ha hb)
    exact congrArg _ hab

  have e2_stem_one_nonzero_unique (x y : E2 H SphereSpectrum 1 2)
      (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
    let e := MilnorCohomology.comparison H M 1 2
    apply e.symm.injective
    exact cohomology_stem_one_nonzero_unique _ _
      (fun h => hx (e.symm.map_eq_zero_iff.mp h))
      (fun h => hy (e.symm.map_eq_zero_iff.mp h))



  let diagonalWord (s : ℕ) : MilnorWord s (s : ℤ) :=
    ⟨fun _ => Finsupp.single 0 1, by
      constructor
      · simp [wordDegree, slotWeight, Finsupp.weight_single]
      · intro i
        exact Finsupp.single_ne_zero.mpr (by decide)⟩

  have diagonalWord_unique (s : ℕ) (d : MilnorWord s (s : ℤ)) :
      d = diagonalWord s := by
    have he : ∑ i : Fin s, (slotWeight (d.val i) - 1) = 0 := by
      let d' : MilnorWord s ((s : ℤ) + 0) :=
        ⟨d.val, by simpa only [add_zero] using d.property⟩
      exact word_excess d'
    apply Subtype.ext
    funext i
    have hb : slotWeight (d.val i) - 1 ≤
        ∑ j : Fin s, (slotWeight (d.val j) - 1) :=
      Finset.single_le_sum (f := fun j : Fin s => slotWeight (d.val j) - 1)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have hp := slot_positive (d.val i) (d.property.2 i)
    change d.val i = Finsupp.single 0 1
    exact weight_one _ (by omega)

  have diagonalWord_subsingleton (s : ℕ) : Subsingleton (MilnorWord s (s : ℤ)) :=
    ⟨fun a b => (diagonalWord_unique s a).trans (diagonalWord_unique s b).symm⟩

  have xpow_ne_zero (s : ℕ) : xpow s ≠ 0 := by
    intro h
    have hp : (xpow s).val = 0 := congrArg Subtype.val h
    rw [xpow_val] at hp
    have hn : (∏ i : Fin s, (MvPolynomial.X (i, 0) : TensorPower s)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact MvPolynomial.X_ne_zero _
    exact hn hp

  have diagonal_cochain_classify (s : ℕ) (v : cochains s s) :
      v = 0 ∨ v = xpow s := by
    letI := diagonalWord_subsingleton s
    let e : cochains s s ≃ₗ[ZMod 2] ZMod 2 :=
      (cochainsWordEquiv s s).trans
        (Finsupp.uniqueLinearEquiv (ZMod 2) (ZMod 2) (diagonalWord s))
    have two_values (r : ZMod 2) : r = 0 ∨ r = 1 := by
      fin_cases r <;> simp
    by_cases hv : v = 0
    · exact Or.inl hv
    · right
      have hv' : e v ≠ 0 := fun h => hv (e.map_eq_zero_iff.mp h)
      have hx' : e (xpow s) ≠ 0 := fun h => xpow_ne_zero s (e.map_eq_zero_iff.mp h)
      apply e.injective
      exact ((two_values _).resolve_left hv').trans
        ((two_values _).resolve_left hx').symm

  have reindex_cycle_local {s s' t t' : ℕ} (hs : s = s') (ht : t = t')
      (v : cochains s t) (hv : differential s t v = 0) :
      differential s' t' (reindex hs ht v) = 0 := by
    subst s'
    subst t'
    exact hv

  have stem_one_cochain_isCycle (s t : ℕ) (ht : t = s + 1)
      (v : cochains s t) : differential s t v = 0 := by
    let e := cochainsWordEquiv s t
    have basis_closed (d : MilnorWord s (t : ℤ)) :
        differential s t (e.symm (Finsupp.single d 1)) = 0 := by
      obtain ⟨i, hi⟩ := stem_one_word_polynomial d ht
      let a := i.val
      let b := s - 1 - i.val
      have hi' := i.isLt
      have hs : a + 1 + b = s := by dsimp [a, b]; omega
      have hdeg : a + 2 + b = t := by dsimp [a, b]; omega
      let w := cup (cup (xpow a) uc) (xpow b)
      have hw : differential (a + 1 + b) (a + 2 + b) w = 0 :=
        cup_isCycle (cup (xpow a) uc) (xpow b)
          (cup_isCycle (xpow a) uc (dxpow a) duc) (dxpow b)
      have regrade_single {n n' d d' : ℕ} (hn : n = n') (hd : d = d')
          (z : cochains n d) (j : Fin n)
          (hz : z.val = (xpow n).val * MvPolynomial.X (j, 0)) :
          (reindex hn hd z).val =
            (xpow n').val * MvPolynomial.X (Fin.cast hn j, 0) := by
        subst n'
        subst d'
        exact hz
      have he : reindex hs hdeg w = e.symm (Finsupp.single d 1) := by
        apply Subtype.ext
        rw [regrade_single hs hdeg w _ (single_u_val a b), hi]
        congr 2
      rw [← he]
      exact reindex_cycle_local hs hdeg w hw
    have all_closed (z : MilnorWord s (t : ℤ) →₀ ZMod 2) :
        differential s t (e.symm z) = 0 := by
      induction z using Finsupp.induction_linear with
      | zero => simp only [map_zero]
      | add a b ha hb => simp only [map_add, ha, hb, add_zero]
      | single d r =>
        have hr : Finsupp.single d r = r • Finsupp.single d (1 : ZMod 2) := by
          simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hr, map_smul, map_smul, basis_closed, smul_zero]
    simpa only [e, LinearEquiv.symm_apply_apply] using all_closed (e v)

  have diagonal_cohomology_ne_zero (s : ℕ) :
      MilnorCohomology.ofCocycle H M (xpow s) (dxpow s) ≠ 0 := by
    cases s with
    | zero =>
      intro h
      exact xpow_ne_zero 0
        ((MilnorCohomology.ofCocycle_zero_eq_zero_iff H M 0 _ _).mp h)
    | succ n =>
      intro h
      obtain ⟨v, hv⟩ :=
        (MilnorCohomology.ofCocycle_succ_eq_zero_iff H M n (n + 1) _ _).mp h
      have hz := stem_one_cochain_isCycle n (n + 1) rfl v
      exact xpow_ne_zero (n + 1) (hv.symm.trans hz)

  have diagonal_cohomology_classify (s : ℕ)
      (z : MilnorCohomology.Cohomology H M s s) :
      z = 0 ∨ z = MilnorCohomology.ofCocycle H M (xpow s) (dxpow s) := by
    obtain ⟨v, rfl⟩ := (MilnorCohomology.boundariesInCycles H M s s).mkQ_surjective z
    rcases diagonal_cochain_classify s v.val with hv | hv
    · left
      have h : v = 0 := Subtype.ext hv
      change MilnorCohomology.classOf H M s s v = 0
      rw [h, map_zero]
    · right
      have h : v = ⟨xpow s, dxpow s⟩ := Subtype.ext hv
      change MilnorCohomology.classOf H M s s v =
        MilnorCohomology.classOf H M s s ⟨xpow s, dxpow s⟩
      rw [h]

  let diagonalE2 (s : ℕ) : E2 H SphereSpectrum (s : ℤ) (s : ℤ) :=
    MilnorCohomology.comparison H M s s
      (MilnorCohomology.ofCocycle H M (xpow s) (dxpow s))

  have diagonalE2_ne_zero (s : ℕ) : diagonalE2 s ≠ 0 := by
    intro h
    exact diagonal_cohomology_ne_zero s
      ((MilnorCohomology.comparison H M s s).map_eq_zero_iff.mp h)

  have diagonalE2_classify (s : ℕ) (z : E2 H SphereSpectrum (s : ℤ) (s : ℤ)) :
      z = 0 ∨ z = diagonalE2 s := by
    let e := MilnorCohomology.comparison H M s s
    rcases diagonal_cohomology_classify s (e.symm z) with h | h
    · left
      exact e.symm.map_eq_zero_iff.mp h
    · right
      apply e.symm.injective
      simpa only [diagonalE2, e, LinearEquiv.symm_apply_apply] using h

  have diagonalE2_product (a b : ℕ) :
      Sphere.Internal.product H M (diagonalE2 a) (diagonalE2 b) =
        diagonalE2 (a + b) := by
    simp only [Sphere.Internal.product, diagonalE2, LinearEquiv.symm_apply_apply,
      MilnorCohomology.cup_ofCocycle]
    congr 1
    unfold MilnorCohomology.ofCocycle
    congr 1
    exact Subtype.ext (xpow_cup a b)

  have diagonalE2_one : diagonalE2 1 = Sphere.Internal.hi H M 0 := by
    have hx : xpow 1 = hiCochain 0 := by
      rw [xpow_one]
      apply Subtype.ext
      simp only [xc, x, hiCochain, hiPolynomial, pow_zero, pow_one]
    change MilnorCohomology.comparison H M 1 1
        (MilnorCohomology.ofCocycle H M (xpow 1) (dxpow 1)) = _
    rw [← MilnorCohomology.comparison_hi]
    congr 1
    unfold MilnorCohomology.ofCocycle MilnorCohomology.hi
    congr 1
    exact Subtype.ext hx

  have cycles_top_of_small_page
      (D : SSData (ModuleCat ℤ))
      (hsmall : ∀ a b : D.page 0, a ≠ 0 → b ≠ 0 → a = b)
      (z : (Subobject.underlying.obj (D.Z ⊤) : ModuleCat ℤ))
      (hz : (Subobject.ofLE _ _
        (D.Z_anti (show (0 : WithTop ℕ) ≤ ⊤ from le_top)) ≫ D.pageπ 0) z ≠ 0) :
      D.Z ⊤ = D.Z 0 := by
    let z₀ := (Subobject.ofLE _ _
      (D.Z_anti (show (0 : WithTop ℕ) ≤ ⊤ from le_top))) z
    have hz₀ : D.pageπ 0 z₀ ≠ 0 := hz
    let W := (ModuleCat.subobjectModule D.V) (D.Z ⊤)
    have hboundary : (ModuleCat.subobjectModule D.V) (D.B 0) ≤ W :=
      (ModuleCat.subobjectModule D.V).monotone
        ((D.B_mono (show (0 : WithTop ℕ) ≤ ⊤ from le_top)).trans (D.B_le_Z ⊤))
    have hzmem : (D.Z 0).arrow z₀ ∈ W := by
      change (Subobject.ofLE _ _ (D.Z_anti le_top) ≫ (D.Z 0).arrow) z ∈ W
      rw [Subobject.ofLE_arrow]
      exact ⟨z, rfl⟩
    have hle : (ModuleCat.subobjectModule D.V) (D.Z 0) ≤ W := by
      intro v hv
      obtain ⟨a, rfl⟩ := hv
      by_cases ha : D.pageπ 0 a = 0
      · exact hboundary ((subobject_cokernel_π_eq_zero_iff
          (D.B 0) (D.Z 0) (D.B_le_Z 0) a).mp ha)
      · have heq := hsmall (D.pageπ 0 a) (D.pageπ 0 z₀) ha hz₀
        have hsub : D.pageπ 0 (a - z₀) = 0 := by
          rw [map_sub, heq, sub_self]
        have hsubmem : (D.Z 0).arrow (a - z₀) ∈ W :=
          hboundary ((subobject_cokernel_π_eq_zero_iff
            (D.B 0) (D.Z 0) (D.B_le_Z 0) (a - z₀)).mp hsub)
        have hsum := W.add_mem hsubmem hzmem
        simpa only [map_sub, sub_add_cancel] using hsum
    apply le_antisymm (D.Z_anti (show (0 : WithTop ℕ) ≤ ⊤ from le_top))
    simpa only [W, OrderIso.symm_apply_apply] using
      (ModuleCat.subobjectModule D.V).symm.monotone hle

  have outgoing_zero_of_cycles_top
      {ι : Type} [AddCommGroup ι] [DecidableEq ι]
      (E : KIP126.SpectralSequence (ModuleCat ℤ) ι) (k : ι)
      (hZ : (E.ssData k).Z ⊤ = (E.ssData k).Z 0)
      (r : ℤ) (hr : E.r₀ ≤ r) : E.d r k = 0 := by
    let D := E.ssData k
    have hstage (n : WithTop ℕ) : D.Z n = D.Z 0 := by
      apply le_antisymm (D.Z_anti bot_le)
      calc
        D.Z 0 = D.Z ⊤ := hZ.symm
        _ ≤ D.Z n := D.Z_anti le_top
    let n := (r - E.r₀).toNat
    have hsucc : D.Z (↑(n + 1) : WithTop ℕ) = D.Z ↑n :=
      (hstage _).trans (hstage _).symm
    let i := Subobject.ofLE (D.Z (↑(n + 1) : WithTop ℕ)) (D.Z ↑n)
      (D.Z_anti (by exact_mod_cast Nat.le_succ n))
    haveI : IsIso i := by
      change IsIso (Subobject.isoOfEq _ _ hsucc).hom
      infer_instance
    haveI : Epi (D.pageπ ↑n) := inferInstanceAs (Epi (cokernel.π _))
    apply zero_of_epi_comp (i ≫ D.pageπ ↑n)
    apply PageHomology.comp_eq_zero_of_image_le_kernel
    exact (E.Z_succ r k hr).ge

  have infinity_zero_iff_of_boundaries_eq
      (D : SSData (ModuleCat ℤ)) (n : WithTop ℕ)
      (hB : D.B ⊤ = D.B n)
      (z : (Subobject.underlying.obj (D.Z ⊤) : ModuleCat ℤ)) :
      D.pageπ ⊤ z = 0 ↔
        (Subobject.ofLE _ _ (D.Z_anti le_top) ≫ D.pageπ n) z = 0 := by
    constructor
    · intro hz
      have hb := (subobject_cokernel_π_eq_zero_iff
        (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) z).mp hz
      rw [hB] at hb
      apply (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n)
        (D.B_le_Z n) ((Subobject.ofLE _ _ (D.Z_anti le_top)) z)).mpr
      change (Subobject.ofLE _ _ (D.Z_anti le_top) ≫ (D.Z n).arrow) z ∈ _
      rwa [Subobject.ofLE_arrow]
    · intro hz
      have he := D.infinity_projection_eq_of_page_projection_eq n z 0
        (by simpa only [map_zero] using hz)
      simpa only [map_zero] using he


  let E := D.family.sphere.sequence
  have page_zero_of_initial (T : SSData (ModuleCat ℤ))
      (h : Subsingleton (T.page 0)) (n : WithTop ℕ) : Subsingleton (T.page n) := by
    have hB : T.B 0 = T.Z 0 := T.eq_of_page_isZero 0
      (@ModuleCat.isZero_of_subsingleton _ _ _ h)
    have he : T.B n = T.Z n := le_antisymm (T.B_le_Z n)
      ((T.Z_anti bot_le).trans (hB.ge.trans (T.B_mono bot_le)))
    exact ModuleCat.subsingleton_of_isZero (T.page_isZero_of_eq n he)
  have e2_above_weight (s t w : ℤ) (htw : t < w) :
      Subsingleton (D.family.sphere.E₂ (s,t,w)) := by
    let A := (SyntheticCategory.biShift (0,0)).obj (D.nu.functor.obj (SphereSpectrum : C))
    let e : A ≅ (S_0_0 : Syn) :=
      SyntheticCategory.biShift_zero.app _ ≪≫ D.nu.unitIso
    let q := D.family.functor.mapIso e
    let ep : (D.family.obj A).E₂ (s,t,w) ≅ D.family.sphere.E₂ (s,t,w) :=
      { hom := q.hom.toSSDataMorphism.pageMap (s,t,w) 0
        inv := q.inv.toSSDataMorphism.pageMap (s,t,w) 0
        hom_inv_id := by
          rw [← SSDataMorphism.pageMap_comp]
          change (q.hom ≫ q.inv).toSSDataMorphism.pageMap (s,t,w) 0 = _
          rw [q.hom_inv_id]
          exact SSDataMorphism.pageMap_id _ _ _
        inv_hom_id := by
          rw [← SSDataMorphism.pageMap_comp]
          change (q.inv ≫ q.hom).toSSDataMorphism.pageMap (s,t,w) 0 = _
          rw [q.inv_hom_id]
          exact SSDataMorphism.pageMap_id _ _ _ }
    have hh := literature.theorems.synthetic_e2_weight_vanishing .sphere 0 s t w (by omega)
    letI : Subsingleton ((D.family.obj A).E₂ (s,t,w)) := by
      simpa only [A, D, ClassicalObject.obj] using hh
    exact ep.symm.toLinearEquiv.injective.subsingleton
  have e2_negative (s t w : ℤ) (hs : s < 0) :
      Subsingleton (D.family.sphere.E₂ (s,t,w)) := by
    by_cases htw : t < w
    · exact e2_above_weight s t w htw
    · have hk : t - ((t-w).toNat : ℤ) = w := by omega
      let e : E2 H SphereSpectrum s t ≃ₗ[ℤ] D.family.sphere.E₂ (s,t,w) := by
        have he := D.sphereE2 s t (t-w).toNat
        rw [hk] at he
        exact he
      letI := adamsTowerInternal_page_subsingleton_of_negative H.unit (SphereSpectrum : C)
        2 s t hs
      exact e.symm.injective.subsingleton
  have classical_below_diagonal (s t : ℕ) (hts : t < s) :
      Subsingleton (E2 H SphereSpectrum s t) := by
    letI : IsEmpty (MilnorWord s (t : ℤ)) := ⟨fun d => by
      have hb : s ≤ ∑ i : Fin s, slotWeight (d.val i) := by
        calc
          s = ∑ _i : Fin s, 1 := by simp
          _ ≤ ∑ i : Fin s, slotWeight (d.val i) :=
            Finset.sum_le_sum (fun i _ => slot_positive _ (d.property.2 i))
      have he : ∑ i : Fin s, slotWeight (d.val i) = t := by
        have hd := d.property.1
        dsimp only [wordDegree] at hd
        exact_mod_cast hd
      omega⟩
    letI : Subsingleton (cochains s t) := (cochainsWordEquiv s t).injective.subsingleton
    letI : Subsingleton (MilnorCohomology.Cohomology H M s t) := inferInstance
    exact (MilnorCohomology.comparison H M s t).symm.injective.subsingleton
  have e2_below_diagonal (s t : ℤ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hts : t < s) :
      Subsingleton (D.family.sphere.E₂ (s,t,0)) := by
    let e : E2 H SphereSpectrum s t ≃ₗ[ℤ] D.family.sphere.E₂ (s,t,0) := by
      have he := D.sphereE2 s t t.toNat
      rw [Int.toNat_of_nonneg ht, sub_self] at he
      exact he
    have hc : Subsingleton (E2 H SphereSpectrum s t) := by
      lift s to ℕ using hs
      lift t to ℕ using ht
      exact classical_below_diagonal s t (by omega)
    letI := hc
    exact e.symm.injective.subsingleton
  have h1_detect (k : ℕ) : KIP126.Synthetic.SpectralSequence.Detects D.sphereConvergence
      (1,2,2-(k : ℤ)) (D.sphereE2 1 2 k (Sphere.Internal.hi H M 1))
      (lambdaMultiply k etaClass) := by
    have h := D.comparisonCompatible.homotopy_lambda 1 2 k etaClass
    have he := literature.sources.sourceComparisons.synthetic_eta
    change D.sphereFirstQuotient 1 2 (quotientClass 1 etaClass) = Sphere.Internal.hi H M 1 at he
    simpa only [he] using h
  have h1_boundaries (w : ℤ) : (E.ssData (1,2,w)).B ⊤ = (E.ssData (1,2,w)).B 0 := by
    have hb := boundaries_top_eq_of_d_eq_zero E 2
      (by change D.family.sphere.sequence.r₀ ≤ 2; rw [D.family.sphere.firstPage]) (1,2,w)
    suffices hd : ∀ r : ℤ, 2 ≤ r → E.d r ((1,2,w)-E.diffDeg r) = 0 by
      have he := hb hd
      rw [show E.r₀ = 2 from D.family.sphere.firstPage] at he
      exact he
    intro r hr
    have hdeg : (1,2,w) - E.diffDeg r = (1-r,3-r,w) := by
      rw [D.family.sphere.differentialDegree]
      ext <;> simp [syntheticAdamsDifferentialDegree] <;> omega
    have hs : Subsingleton (E.Page r ((1,2,w) - E.diffDeg r)) := by
      rw [hdeg]
      exact page_zero_of_initial (E.ssData (1-r,3-r,w))
        (e2_negative (1-r) (3-r) w (by omega)) _
    letI := hs
    ext z
    have hz : z = 0 := Subsingleton.elim _ _
    simp only [hz, map_zero]

  have small_synthetic (w : ℤ) (hw : w ≤ 1) :
      ∀ a b : BiHom 1 w (S_0_0 : Syn), a ≠ 0 → b ≠ 0 → a = b := by
    classical
    let unit := nuCoefficientUnit H.unit D.nu
    let F := towerFiltration unit (S_0_0 : Syn)
    have inf_zero (T : SSData (ModuleCat ℤ)) (hT : Subsingleton (T.page 0)) :
        IsZero T.eInfty := by
      letI := hT
      haveI : Epi (T.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
      haveI : Subsingleton T.eInfty := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (T.pageπ ⊤)).mp inferInstance a
        obtain ⟨z', rfl⟩ := (ModuleCat.epi_iff_surjective (T.pageπ ⊤)).mp inferInstance b
        exact T.infinity_projection_eq_of_page_projection_eq 0 z z' (Subsingleton.elim _ _)
      exact ModuleCat.isZero_of_subsingleton _
    have inf_small (T : SSData (ModuleCat ℤ))
        (hT : ∀ a b : T.page 0, a ≠ 0 → b ≠ 0 → a = b) :
        ∀ a b : T.eInfty, a ≠ 0 → b ≠ 0 → a = b := by
      haveI : Epi (T.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
      intro a b ha hb
      obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (T.pageπ ⊤)).mp inferInstance a
      obtain ⟨z', hz'⟩ := (ModuleCat.epi_iff_surjective (T.pageπ ⊤)).mp inferInstance b
      let q := Subobject.ofLE _ _ (T.Z_anti (show (0 : WithTop ℕ) ≤ ⊤ from le_top)) ≫
        T.pageπ 0
      have hqz : q z ≠ 0 := by
        intro hq
        apply ha
        rw [← hz]
        have he := T.infinity_projection_eq_of_page_projection_eq 0 z 0
          (by simpa only [map_zero] using hq)
        simpa only [map_zero] using he
      have hqz' : q z' ≠ 0 := by
        intro hq
        apply hb
        rw [← hz']
        have he := T.infinity_projection_eq_of_page_projection_eq 0 z' 0
          (by simpa only [map_zero] using hq)
        simpa only [map_zero] using he
      rw [← hz, ← hz']
      exact T.infinity_projection_eq_of_page_projection_eq 0 z z'
        (hT (q z) (q z') hqz hqz')

    have stem_equiv (j : ℤ) (hj : 0 ≤ j) :
        E2 H SphereSpectrum j (1 + j) ≃ₗ[ℤ] D.family.sphere.E₂ (j, 1 + j, w) := by
      have hk : (((1 + j - w).toNat : ℕ) : ℤ) = 1 + j - w :=
        Int.toNat_of_nonneg (by omega)
      have he := D.sphereE2 j (1 + j) (1 + j - w).toNat
      have ht : 1 + j - (((1 + j - w).toNat : ℕ) : ℤ) = w := by omega
      rw [ht] at he
      exact he
    have vanish_inf (j : ℤ) (hj : 0 ≤ j) (hj1 : j ≠ 1) :
        IsZero ((D.family.sphere.sequence.ssData (j, 1 + j, w)).eInfty) := by
      let e := stem_equiv j hj
      letI := all_e2_stem_one_zero j hj hj1
      have hs : Subsingleton (D.family.sphere.E₂ (j, 1 + j, w)) :=
        e.symm.injective.subsingleton
      exact inf_zero _ hs
    have small_inf :
        ∀ a b : (D.family.sphere.sequence.ssData (1, 2, w)).eInfty,
          a ≠ 0 → b ≠ 0 → a = b := by
      apply inf_small
      let e : E2 H SphereSpectrum 1 2 ≃ₗ[ℤ] D.family.sphere.E₂ (1, 2, w) :=
        stem_equiv 1 (by decide)
      intro a b ha hb
      apply e.symm.injective
      apply e2_stem_one_nonzero_unique
      · intro hz
        apply ha
        apply e.symm.injective
        simpa only [map_zero] using hz
      · intro hz
        apply hb
        apply e.symm.injective
        simpa only [map_zero] using hz

    have all_in_one (a : BiHom 1 w (S_0_0 : Syn)) :
        FiltrationAtLeast unit 1 a := by
      apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
        0 1 1 w (by decide) (fun j hj hj1 => vanish_inf j hj (by omega)) a).mp
      refine ⟨a, ?_⟩
      change a ≫ adamsTowerMap unit (S_0_0 : Syn) 0 0 _ = a
      rw [adamsTowerMap_self]
      change a ≫ 𝟙 (S_0_0 : Syn) = a
      exact Category.comp_id a
    have tail_zero (a : BiHom 1 w (S_0_0 : Syn))
        (ha : FiltrationAtLeast unit 2 a) : a = 0 := by
      exact D.sphereConvergence.eq_zero_of_eInfty_isZero_ge
        2 1 w (D.homotopySeparated .sphere 1 w)
        (fun j hj => vanish_inf j (by omega) (by omega)) a ha
    let eg : (D.family.sphere.sequence.ssData (1, 2, w)).eInfty ≅
        F.associatedGraded 1 (1, w) := by
      simpa only [Int.reduceSub, SyntheticObject.obj, SyntheticAdamsFamily.sphere, F, unit, H] using
        D.sphereConvergence.identification (1, 2, w)
    have small_graded (a b : F.associatedGraded 1 (1, w))
        (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
      apply eg.symm.toLinearEquiv.injective
      apply small_inf
      · intro hz
        apply ha
        apply eg.symm.toLinearEquiv.injective
        simpa only [map_zero] using hz
      · intro hz
        apply hb
        apply eg.symm.toLinearEquiv.injective
        simpa only [map_zero] using hz
    have graded_kernel (z : (Subobject.underlying.obj (F.F 1 (1, w)) : ModuleCat ℤ))
        (hz : F.toAssociatedGraded 1 (1, w) z = 0) :
        (F.F 1 (1, w)).arrow z = 0 := by
      apply tail_zero
      have hb := (subobject_cokernel_π_eq_zero_iff
        (F.F 2 (1, w)) (F.F 1 (1, w)) (F.mono 1 (1, w)) z).mp hz
      simpa only [F, towerFiltration, FiltrationAtLeast,
        OrderIso.apply_symm_apply] using hb
    have lift_to_one (a : BiHom 1 w (S_0_0 : Syn)) :
        ∃ z : (Subobject.underlying.obj (F.F 1 (1, w)) : ModuleCat ℤ),
          (F.F 1 (1, w)).arrow z = a := by
      have hm : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0 : Syn) (1,w)))
          (F.F 1 (1,w)) := by
        simpa only [F, towerFiltration, FiltrationAtLeast,
          OrderIso.apply_symm_apply] using all_in_one a
      exact hm
    intro a b ha hb
    obtain ⟨za, hza⟩ := lift_to_one a
    obtain ⟨zb, hzb⟩ := lift_to_one b
    have hga : F.toAssociatedGraded 1 (1, w) za ≠ 0 := by
      intro hz
      exact ha (hza.symm.trans (graded_kernel za hz))
    have hgb : F.toAssociatedGraded 1 (1, w) zb ≠ 0 := by
      intro hz
      exact hb (hzb.symm.trans (graded_kernel zb hz))
    have hab := small_graded _ _ hga hgb
    have hk := graded_kernel (za - zb) (by rw [map_sub, hab, sub_self])
    apply sub_eq_zero.mp
    simpa only [map_sub, hza, hzb] using hk

  have synthetic_stem_one_double_zero (w : ℤ) (hw : w ≤ 1)
      (a : BiHom 1 w (S_0_0 : Syn)) : a + a = 0 := by
    by_cases ha : a = 0
    · simp only [ha, add_zero]
    · have hn : -a ≠ 0 := neg_ne_zero.mpr ha
      have he : -a = a := small_synthetic w hw (-a) a hn ha
      calc
        a + a = a + (-a) := congrArg (fun z => a + z) he.symm
        _ = 0 := add_neg_cancel a

  have classical_stem_one_double_zero
      (a : HomotopyGroup (1 : ℤ)
        (SphereSpectrum (C := KIP126.Classical.Adams.standardFoundation.Spectrum))) :
      a + a = 0 := by
    letI := D.nu.additive
    letI := D.recovery.nu_faithful
    let em := nuSphereOne D
    let I (b : HomotopyGroup (1 : ℤ) SphereSpectrum) : BiHom 1 1 (S_0_0 : Syn) :=
      em.inv ≫ D.nu.functor.map b ≫ D.nu.unitIso.hom
    have inj : Function.Injective I := by
      intro b c hbc
      apply D.nu.functor.map_injective
      apply (cancel_epi em.inv).mp
      apply (cancel_mono D.nu.unitIso.hom).mp
      simpa only [I, Category.assoc] using hbc
    have izero : I 0 = 0 := by
      simp only [I, Functor.map_zero, zero_comp, comp_zero]
    have iadd : I (a + a) = I a + I a := by
      simp only [I, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
    apply inj
    rw [iadd, izero]
    exact synthetic_stem_one_double_zero 1 (by decide) (I a)

  have classical_eta_double_zero :
      literature.sources.sourceComparisons.classicalSource.eta +
        literature.sources.sourceComparisons.classicalSource.eta = 0 :=
    classical_stem_one_double_zero literature.sources.sourceComparisons.classicalSource.eta

  have h1_cycles : (E.ssData (1,2,0)).Z ⊤ = (E.ssData (1,2,0)).Z 0 := by
    have hdet : KIP126.Synthetic.SpectralSequence.Detects D.sphereConvergence
        (1,2,0) (D.sphereE2 1 2 2 (Sphere.Internal.hi H M 1))
        (lambdaMultiply 2 etaClass) := h1_detect 2
    obtain ⟨ei, ⟨_, z, hz, _⟩, _⟩ := hdet
    refine cycles_top_of_small_page (E.ssData (1,2,0)) ?_ z ?_
    · intro a b ha hb
      let e := D.sphereE2 1 2 2
      apply e.symm.injective
      exact e2_stem_one_nonzero_unique _ _
        (fun h => ha (e.symm.map_eq_zero_iff.mp h))
        (fun h => hb (e.symm.map_eq_zero_iff.mp h))
    · intro hz0
      exact hi_nonzero 1 ((D.sphereE2 1 2 2).map_eq_zero_iff.mp (hz.symm.trans hz0))
  have h1_out (r : ℤ) (hr : 2 ≤ r) : E.d r (1,2,0) = 0 := by
    apply outgoing_zero_of_cycles_top (ι := Tridegree) E ((1 : ℤ),2,0) h1_cycles r
    simpa only [E, D.family.sphere.firstPage] using hr
  have diagonal_in (s : ℕ) (r : ℤ) (hr : 2 ≤ r) :
      E.d r (((s : ℤ),(s : ℤ),(0 : ℤ)) - E.diffDeg r) = 0 := set_option maxHeartbeats 100000 in by
    have hd : ((s : ℤ),(s : ℤ),(0 : ℤ)) - E.diffDeg r = ((s : ℤ)-r,(s : ℤ)-r+1,0) := by
      rw [D.family.sphere.differentialDegree]
      ext <;> simp [syntheticAdamsDifferentialDegree] <;> omega
    rw [hd]
    by_cases hq : (s : ℤ)-r = 1
    · rw [hq]
      exact h1_out r hr
    · have hz : Subsingleton (D.family.sphere.E₂ ((s : ℤ)-r,(s : ℤ)-r+1,0)) := by
        by_cases hneg : (s : ℤ)-r < 0
        · exact e2_negative _ _ _ hneg
        · have hc := all_e2_stem_one_zero ((s : ℤ)-r) (by omega) hq
          rw [add_comm 1 ((s : ℤ)-r)] at hc
          letI := hc
          let e : E2 H SphereSpectrum ((s : ℤ)-r) ((s : ℤ)-r+1) ≃ₗ[ℤ]
              D.family.sphere.E₂ ((s : ℤ)-r,(s : ℤ)-r+1,0) := by
            have he := D.sphereE2 ((s : ℤ)-r) ((s : ℤ)-r+1) ((s : ℤ)-r+1).toNat
            rw [Int.toNat_of_nonneg (show 0 ≤ (s : ℤ)-r+1 by omega), sub_self] at he
            exact he
          exact e.symm.injective.subsingleton
      haveI : Subsingleton (E.Page r ((s : ℤ)-r,(s : ℤ)-r+1,0)) :=
        page_zero_of_initial _ hz _
      ext z
      have hz : z = 0 := Subsingleton.elim _ _
      simp only [hz, map_zero]
  have diagonal_boundaries (s : ℕ) :
      (E.ssData ((s : ℤ),(s : ℤ),(0 : ℤ))).B ⊤ = (E.ssData ((s : ℤ),(s : ℤ),(0 : ℤ))).B 0 := by
    have h := boundaries_top_eq_of_d_eq_zero E 2
      (by rw [show E.r₀ = 2 from D.family.sphere.firstPage]) ((s : ℤ),(s : ℤ),(0 : ℤ))
      (diagonal_in s)
    rw [show E.r₀ = 2 from D.family.sphere.firstPage] at h
    exact h
  have two_detect : KIP126.Synthetic.SpectralSequence.Detects D.sphereConvergence
      (1,1,0) (D.sphereE2 1 1 1 (Sphere.Internal.hi H M 0)) syntheticTwo := by
    have h := D.comparisonCompatible.homotopy_lambda 1 1 1 literature.sources.sourceComparisons.todaSource.h0
    have hl : D.sphereFirstQuotient 1 1 (quotientClass 1 literature.sources.sourceComparisons.todaSource.h0) =
        Sphere.Internal.hi H M 0 := literature.theorems.toda_h0_label
    rw [hl, literature.theorems.toda_lambda_h0] at h
    exact h
  have synthetic_two_product (a : BiHom 0 0 (S_0_0 : Syn)) :
      sphereProduct syntheticTwo a = a + a := by
    letI := D.shiftAdditive (0,0)
    have hunit := D.shiftCoherence.left_unit (0,0) (S_0_0 : Syn)
    have hu : (SyntheticCategory.biShift_comp (0,0) (0,0)).hom.app (S_0_0 : Syn) =
        (SyntheticCategory.biShift (0,0)).map
          (SyntheticCategory.biShift_zero.hom.app (S_0_0 : Syn)) := by
      simp only [biShiftAddIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
        eqToHom_app, eqToHom_refl, Category.comp_id] at hunit
      exact hunit
    simp only [sphereProduct, syntheticTwo, Functor.map_comp, Functor.map_nsmul,
      CategoryTheory.Functor.map_id, Preadditive.comp_nsmul, Category.comp_id]
    rw [← hu]
    simp only [Category.assoc, Preadditive.comp_nsmul, Preadditive.nsmul_comp,
      Iso.inv_hom_id_app_assoc, Category.id_comp, two_nsmul]
    simp only [Preadditive.add_comp, Preadditive.comp_add,
      Iso.inv_hom_id_app_assoc]
  have lambda_eta_nonzero : lambdaMultiply 2 etaClass ≠ 0 := by
    intro hz
    have hdet : KIP126.Synthetic.SpectralSequence.Detects D.sphereConvergence
        (1,2,0) (D.sphereE2 1 2 2 (Sphere.Internal.hi H M 1))
        (lambdaMultiply 2 etaClass) := h1_detect 2
    obtain ⟨ei, ⟨_, z, he2, heinf⟩, a, ha, hgr⟩ := hdet
    have ha0 : a = 0 := by
      apply (ModuleCat.mono_iff_injective
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)).F 1 (1,0)).arrow).mp
        inferInstance
      rw [map_zero]
      exact ha.trans hz
    have hei : ei = 0 := by
      apply (ModuleCat.mono_iff_injective (D.sphereConvergence.identification (1,2,0)).hom).mp
        inferInstance
      simpa only [ha0, map_zero] using hgr
    have hzinf : (E.ssData (1,2,0)).pageπ ⊤ z = 0 := heinf.trans hei
    have he20 := (infinity_zero_iff_of_boundaries_eq _ 0 (h1_boundaries 0) z).mp hzinf
    exact hi_nonzero 1 ((D.sphereE2 1 2 2).map_eq_zero_iff.mp (he2.symm.trans he20))

  have zero_stem_no_two_torsion
      (diag : (s : ℕ) → E2 H SphereSpectrum s s)
      (diag_classify : ∀ (s : ℕ) (z : E2 H SphereSpectrum s s),
        z = 0 ∨ z = diag s)
      (diag_ne : ∀ s : ℕ, diag s ≠ 0)
      (diag_product : ∀ s : ℕ,
        Sphere.Internal.product H M (Sphere.Internal.hi H M 0) (diag s) = diag (1 + s))
      (hB : ∀ s : ℕ,
        (D.family.sphere.sequence.ssData (s, s, 0)).B ⊤ =
          (D.family.sphere.sequence.ssData (s, s, 0)).B 0)
      (two_detect : Detects D.sphereConvergence (1, 1, 0)
        (D.sphereE2 1 1 1 (Sphere.Internal.hi H M 0))
        (syntheticTwo : BiHom 0 0 (S_0_0 : Syn)))
      (product_two : ∀ a : BiHom 0 0 (S_0_0 : Syn),
        sphereProduct syntheticTwo a = a + a) :
      ∀ a : BiHom 0 0 (S_0_0 : Syn), a + a = 0 → a = 0 := by
    classical
    let S : Syn := S_0_0
    let unit := nuCoefficientUnit H.unit D.nu
    let F := towerFiltration unit S
    let E := D.family.sphere.sequence
    let ee (s : ℕ) : E2 H SphereSpectrum s s ≃ₗ[ℤ]
        D.family.sphere.E₂ (s, s, (s : ℤ)-s) := D.sphereE2 s s s
    let dx (s : ℕ) : D.family.sphere.E₂ (s, s, (s : ℤ)-s) := ee s (diag s)
    have hdx (s : ℕ) : dx s ≠ 0 := by
      intro h
      apply diag_ne s
      exact (ee s).map_eq_zero_iff.mp h

    have detected_nonzero (s : ℕ)
        (x : D.family.sphere.E₂ (s, s, (s : ℤ)-s)) (hx : x ≠ 0)
        (α : BiHom ((s : ℤ) - s) ((s : ℤ)-s) S)
        (hdet : Detects D.sphereConvergence (s, s, (s : ℤ)-s) x α) : α ≠ 0 := by
      obtain ⟨e, ⟨_, z, hzx, hze⟩, b, hb, hgr⟩ := hdet
      intro hα
      have hb0 : b = 0 := by
        apply (ModuleCat.mono_iff_injective (F.F s ((s : ℤ)-s,(s : ℤ)-s)).arrow).mp
          inferInstance
        rw [map_zero]
        exact hb.trans hα
      have he0 : e = 0 := by
        apply (ModuleCat.mono_iff_injective
          (D.sphereConvergence.identification (s, s, (s : ℤ)-s)).hom).mp inferInstance
        simpa only [hb0, map_zero] using hgr
      let T := E.ssData (s, s, (s : ℤ)-s)
      have hz0 : T.pageπ ⊤ z = 0 := hze.trans he0
      have hmem := (subobject_cokernel_π_eq_zero_iff
        (T.B ⊤) (T.Z ⊤) (T.B_le_Z ⊤) z).mp hz0
      have hbound : T.B ⊤ = T.B 0 := by
        dsimp only [T, E]
        rw [Int.sub_self]
        exact hB s
      rw [hbound] at hmem
      apply hx
      rw [← hzx]
      apply (subobject_cokernel_π_eq_zero_iff (T.B 0) (T.Z 0)
        (T.B_le_Z 0) ((Subobject.ofLE _ _ (T.Z_anti le_top)) z)).mpr
      change (Subobject.ofLE _ _ (T.Z_anti le_top) ≫ (T.Z 0).arrow) z ∈ _
      rwa [Subobject.ofLE_arrow]

    have detects_diagonal_of_exact (s : ℕ)
        (a : BiHom ((s : ℤ)-s) ((s : ℤ)-s) S)
        (ha : FiltrationAtLeast unit s a)
        (hnext : ¬ FiltrationAtLeast unit ((s : ℤ) + 1) a) :
        Detects D.sphereConvergence (s, s, (s : ℤ)-s) (dx s) a := by
      let T := E.ssData (s, s, (s : ℤ)-s)
      let eg : T.eInfty ≅ F.associatedGraded s ((s : ℤ)-s, (s : ℤ)-s) := by
        exact D.sphereConvergence.identification (s, s, (s : ℤ)-s)
      have hamem : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy S ((s : ℤ)-s, (s : ℤ)-s)))
          (F.F s ((s : ℤ)-s, (s : ℤ)-s)) := by
        simpa only [F, towerFiltration, FiltrationAtLeast,
          OrderIso.apply_symm_apply] using ha
      obtain ⟨aF, haF⟩ := hamem
      have hgraded : F.toAssociatedGraded s ((s : ℤ)-s, (s : ℤ)-s) aF ≠ 0 := by
        intro hz
        apply hnext
        have hm := (subobject_cokernel_π_eq_zero_iff
          (F.F ((s : ℤ) + 1) ((s : ℤ)-s, (s : ℤ)-s)) (F.F s ((s : ℤ)-s, (s : ℤ)-s))
          (F.mono s ((s : ℤ)-s, (s : ℤ)-s)) aF).mp hz
        rw [haF] at hm
        simpa only [F, towerFiltration, FiltrationAtLeast,
          OrderIso.apply_symm_apply] using hm
      let einf := eg.inv (F.toAssociatedGraded s ((s : ℤ)-s, (s : ℤ)-s) aF)
      have heinf : einf ≠ 0 := by
        intro hz
        apply hgraded
        exact eg.symm.toLinearEquiv.map_eq_zero_iff.mp hz
      haveI : Epi (T.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
      obtain ⟨z, hz⟩ :=
        (ModuleCat.epi_iff_surjective (T.pageπ ⊤)).mp inferInstance einf
      let x : T.page 0 := (Subobject.ofLE _ _ (T.Z_anti le_top) ≫ T.pageπ 0) z
      have hx : x ≠ 0 := by
        intro hx0
        have he := T.infinity_projection_eq_of_page_projection_eq 0 z 0
          (by simpa only [map_zero] using hx0)
        apply heinf
        rw [← hz]
        simpa only [map_zero] using he
      have hxdiag : x = dx s := by
        rcases diag_classify s ((ee s).symm x) with hz0 | hzdiag
        · exact (hx ((ee s).symm.map_eq_zero_iff.mp hz0)).elim
        · change x = ee s (diag s)
          rw [← hzdiag, LinearEquiv.apply_symm_apply]
      refine ⟨einf, ⟨by decide, z, ?_, hz⟩, aF, haF, ?_⟩
      · exact hxdiag
      · change (eg.inv ≫ eg.hom) (F.toAssociatedGraded s ((s : ℤ)-s, (s : ℤ)-s) aF) = _
        rw [eg.inv_hom_id]
        rfl

    intro a hdouble
    by_contra ha
    have hzero : FiltrationAtLeast unit 0 a := by
      refine ⟨a, ?_⟩
      change a ≫ adamsTowerMap unit S 0 0 _ = a
      rw [adamsTowerMap_self]
      exact Category.comp_id a
    have hex : ∃ q : ℕ, ¬ FiltrationAtLeast unit q a := by
      by_contra hn
      apply ha
      apply D.homotopySeparated .sphere 0 0 a
      intro q
      by_contra hq
      exact hn ⟨q, hq⟩
    let q := Nat.find hex
    have hq : ¬ FiltrationAtLeast unit q a := Nat.find_spec hex
    have hqpos : 0 < q := by
      by_contra hn
      have hq0 : q = 0 := by omega
      apply hq
      simpa only [hq0, Nat.cast_zero] using hzero
    let s := q - 1
    have hs : FiltrationAtLeast unit s a := by
      by_contra hnot
      exact Nat.find_min hex (show s < q by dsimp only [s]; omega) hnot
    have hsnext : ¬ FiltrationAtLeast unit ((s : ℤ) + 1) a := by
      have hsq : (s : ℤ) + 1 = q := by dsimp only [s]; omega
      simpa only [hsq] using hq
    have filtration_regrade {m m' w w' : ℤ}
        (hm : m = m') (hw : w = w') (k : ℤ) (b : BiHom m w S) :
        FiltrationAtLeast unit k (homotopyRegrade hm hw b) ↔
          FiltrationAtLeast unit k b := by
      subst m'
      subst w'
      rfl
    have regrade_zero {m m' w w' : ℤ} (hm : m = m') (hw : w = w') :
        homotopyRegrade hm hw (0 : BiHom m w S) = 0 := by
      subst m'
      subst w'
      rfl
    have product_regrade_zero (m w : ℤ) (hm : 0 = m) (hw : 0 = w) :
        sphereProduct syntheticTwo (homotopyRegrade hm hw a) = 0 := by
      subst m
      subst w
      change sphereProduct syntheticTwo a = 0
      exact (product_two a).trans hdouble
    let aa : BiHom ((s : ℤ)-s) ((s : ℤ)-s) S :=
      homotopyRegrade (by simp) (by simp) a
    have haa : FiltrationAtLeast unit s aa :=
      (filtration_regrade (by simp) (by simp) s a).mpr hs
    have haanext : ¬ FiltrationAtLeast unit ((s : ℤ)+1) aa := by
      intro hh
      exact hsnext ((filtration_regrade (by simp) (by simp) ((s : ℤ)+1) a).mp hh)
    have hdet := detects_diagonal_of_exact s aa haa haanext
    have hprod := D.multiplicationCompatible 1 1 s s 1 s
      (Sphere.Internal.hi H M 0) (diag s) syntheticTwo aa two_detect hdet
    have hprodval : sphereProduct syntheticTwo aa = 0 :=
      product_regrade_zero _ _ (by simp) (by simp)
    have hp := diag_product s
    dsimp only [H, M] at hp
    rw [hp] at hprod
    have hprod0 : Detects D.sphereConvergence
        ((1+s : ℕ), (1+s : ℕ), ((1+s : ℕ) : ℤ)-(1+s : ℕ))
        (dx (1+s)) 0 := by
      simpa only [diag_product, hprodval, regrade_zero, dx, ee] using hprod
    exact detected_nonzero (1+s) (dx (1+s)) (hdx (1+s)) 0 hprod0 rfl

  have diagonal_h0_product (s : ℕ) :
      Sphere.Internal.product H M (Sphere.Internal.hi H M 0) (diagonalE2 s) =
        diagonalE2 (1 + s) := by
    rw [← diagonalE2_one]
    exact diagonalE2_product 1 s
  have bihom_zero_no_two_torsion :
      ∀ a : BiHom 0 0 (S_0_0 : Syn), a + a = 0 → a = 0 :=
    zero_stem_no_two_torsion diagonalE2 diagonalE2_classify
      diagonalE2_ne_zero diagonal_h0_product diagonal_boundaries
      two_detect synthetic_two_product

  have sphere_end_no_two_torsion :
      ∀ a : (S_0_0 : Syn) ⟶ S_0_0, a + a = 0 → a = 0 := by
    intro a ha
    let e : Smn 0 0 ≅ (S_0_0 : Syn) :=
      SyntheticCategory.biShift_zero.app (S_0_0 : Syn)
    have hz : e.hom ≫ a = 0 := by
      apply bihom_zero_no_two_torsion
      rw [← Preadditive.comp_add, ha, comp_zero]
    apply (cancel_epi e.hom).mp
    simpa only [comp_zero] using hz


  open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
    CategoryTheory.MonoidalCategory KIP126.StableHomotopy
    KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
    KIP126.SpectralSequence KIP126.Algebra KIP126.Steenrod.Milnor in
  open scoped BigOperators TensorProduct DirectSum in
  set_option backward.isDefEq.respectTransparency false in
  have classical_toda_nonzero : ¬ Toda.Relation
      (0 : (Sphere (C := C) 1)⟦(1 : ℤ)⟧ ⟶ SphereSpectrum)
      ((2 : ℕ) • 𝟙 (Sphere (C := C) 1))
      literature.sources.sourceComparisons.classicalSource.eta ((2 : ℕ) • 𝟙 SphereSpectrum) := by
    classical
    have length_zero_trivial (t : ℕ) (ht : t ≠ 0) : Subsingleton (cochains 0 t) := by
      have hz (x : cochains 0 t) : x = 0 := by
        apply Subtype.ext
        change x.val = 0
        by_contra h
        exact ht (MvPolynomial.IsWeightedHomogeneous.inj_right h x.property.1
          (MvPolynomial.isWeightedHomogeneous_of_isEmpty
            (R := KIP126.Algebra.F2) weight x.val))
      exact ⟨fun x y => (hz x).trans (hz y).symm⟩

    have hi_nonzero (i : ℕ) : Sphere.Internal.hi H M i ≠ 0 := by
      intro hz
      have hz' : MilnorCohomology.hi H M i = 0 := by
        apply (MilnorCohomology.comparison H M 1 (2 ^ i)).injective
        simpa only [map_zero, MilnorCohomology.comparison_hi] using hz
      obtain ⟨b, hb⟩ := (MilnorCohomology.hi_eq_zero_iff H M i).mp hz'
      haveI := length_zero_trivial (2 ^ i) (pow_ne_zero _ (by decide))
      have hb0 : b = 0 := Subsingleton.elim _ _
      rw [hb0, map_zero] at hb
      have hp := congrArg Subtype.val hb.symm
      exact pow_ne_zero _ (MvPolynomial.X_ne_zero ((0 : Fin 1), 0)) hp

    have detection_first_nonzero (d : ℤ)
        (c : TowerDetection.Convergence H.unit (SphereSpectrum : C))
        (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (1, d))
        (hx : x ≠ 0) (α : HomotopyGroup (d - 1) (SphereSpectrum : C))
        (hdet : TowerDetection.Detects c (1, d) x α) :
        AdamsFiltrationAtLeast H α 1 ∧ ¬ AdamsFiltrationAtLeast H α 2 := by
      let E := adamsTowerInternalSpectralSequence H.unit (SphereSpectrum : C)
      let T := E.ssData (1, d)
      let F := TowerDetection.filtration H.unit (SphereSpectrum : C)
      obtain ⟨z, hz, a, ha, hgr⟩ := hdet
      have hmem : α ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum 1 (d - 1) := by
        have hm : (F.F 1 (d - 1)).arrow a ∈
            (ModuleCat.subobjectModule _) (F.F 1 (d - 1)) := ⟨a, rfl⟩
        rw [ha] at hm
        simpa only [F, TowerDetection.filtration, OrderIso.apply_symm_apply] using hm
      refine ⟨hmem, ?_⟩
      intro hnext
      have hgr0 : F.toAssociatedGraded 1 (d - 1) a = 0 := by
        apply (subobject_cokernel_π_eq_zero_iff (F.F 2 (d - 1))
          (F.F 1 (d - 1)) (F.mono 1 (d - 1)) a).mpr
        rw [ha]
        have hnmem : α ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum 2 (d - 1) := hnext
        simpa only [F, TowerDetection.filtration, OrderIso.apply_symm_apply] using hnmem
      have hz0 : T.pageπ ⊤ z = 0 := by
        apply (ModuleCat.mono_iff_injective (c.identification (1, d)).hom).mp inferInstance
        rw [map_zero]
        exact hgr.trans hgr0
      have hb : T.B ⊤ = T.B 0 := by
        apply boundaries_top_eq_of_d_eq_zero E 2 (by rfl)
        intro r hr
        haveI : Subsingleton (E.Page r ((1, d) - E.diffDeg r)) :=
          adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum
            r (1 - r) (d - (r - 1)) (by omega)
        ext q
        have hq : q = 0 := Subsingleton.elim _ _
        simp only [hq, map_zero]
      have hzmem := (subobject_cokernel_π_eq_zero_iff (T.B ⊤) (T.Z ⊤)
        (T.B_le_Z ⊤) z).mp hz0
      rw [hb] at hzmem
      apply hx
      rw [← hz]
      apply (subobject_cokernel_π_eq_zero_iff (T.B 0) (T.Z 0)
        (T.B_le_Z 0) ((Subobject.ofLE _ _ (T.Z_anti le_top)) z)).mpr
      change (Subobject.ofLE _ _ (T.Z_anti le_top) ≫ (T.Z 0).arrow) z ∈ _
      rwa [Subobject.ofLE_arrow]
    have two_filtration := detection_first_nonzero 1
      literature.sources.sourceComparisons.classicalSource.convergence
      (Sphere.Internal.hi H M 0) (hi_nonzero 0) _ literature.theorems.classical_two_detection
    have eta_filtration := detection_first_nonzero 2
      literature.sources.sourceComparisons.classicalSource.convergence
      (Sphere.Internal.hi H M 1) (hi_nonzero 1) _ literature.theorems.classical_eta_detection
    letI := KIP126.Def.standardHF2AdamsContext.tensorStructure
    open scoped TensorProduct DirectSum in
    have low_cooperation_calculation :
        let R := KIP126.Def.standardHF2AdamsContext.cooperationStructure.ring
        let B := KIP126.Def.standardHF2AdamsContext.cooperationStructure.basis
        let K := KIP126.Def.standardHF2AdamsContext.cooperationStructure.kunneth
        letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
          fun i => mod2HomologyModule H R i H.HF2
        (∀ (x1 : Mod2Cooperations H 1) (u2 : Mod2Cooperations H 2),
          cooperationMilnorPolynomial H R B 1 x1 = MvPolynomial.X ((0 : Fin 1), 0) →
          cooperationMilnorPolynomial H R B 2 u2 = MvPolynomial.X ((0 : Fin 1), 0) ^ 2 →
          ∀ (a b : Mod2Cooperations H 3) (c : Mod2Cooperations H 4),
          cooperationTensorDiagonal H R K 3 a =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3 a +
            DirectSum.lof (ZMod 2) ℤ _ 2 (u2 ⊗ₜ[ZMod 2] x1) +
            DirectSum.lof (ZMod 2) ℤ _ 3 (a ⊗ₜ[ZMod 2]
              (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                (sub_self (3 : ℤ)).symm) (cooperationUnit H)) →
          cooperationTensorDiagonal H R K 3 b =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3 b +
            DirectSum.lof (ZMod 2) ℤ _ 1 (x1 ⊗ₜ[ZMod 2] u2) +
            DirectSum.lof (ZMod 2) ℤ _ 3 (b ⊗ₜ[ZMod 2]
              (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                (sub_self (3 : ℤ)).symm) (cooperationUnit H)) →
          cooperationTensorDiagonal H R K 4 c ≠
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 4 c +
            (DirectSum.lof (ZMod 2) ℤ
              (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (4 - i) H.HF2)
              1 (x1 ⊗ₜ[ZMod 2] a) +
            DirectSum.lof (ZMod 2) ℤ
              (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (4 - i) H.HF2)
              3 (b ⊗ₜ[ZMod 2] x1)) +
            DirectSum.lof (ZMod 2) ℤ _ 4 (c ⊗ₜ[ZMod 2]
              (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                (sub_self (4 : ℤ)).symm) (cooperationUnit H))) ∧
        (∀ (d : ℤ) (p : PositiveMonomial d) (k : ℕ),
          (k = 1 ∨ k = 2) → p.val = Finsupp.single 0 k →
          mod2TensorCoaction H R K H.HF2 d (B.basis d p).val =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2)
              d (B.basis d p).val +
            DirectSum.lof (ZMod 2) ℤ _ d
              (((B.basis d p).val : mod2HomologyF2 H R d H.HF2) ⊗ₜ[ZMod 2]
              (LinearEquiv.cast (R := ZMod 2)
                (M := fun i => mod2HomologyF2 H R i H.HF2) (sub_self d).symm)
                (cooperationUnit H))) := by
      open scoped BigOperators TensorProduct DirectSum in
      open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
        KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor
        KIP126.Algebra MvPolynomial in
      set_option maxHeartbeats 4000000 in
      exact by
        classical
        let R := KIP126.Def.standardHF2AdamsContext.cooperationStructure.ring
        let B := KIP126.Def.standardHF2AdamsContext.cooperationStructure.basis
        let K := KIP126.Def.standardHF2AdamsContext.cooperationStructure.kunneth
        letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
          fun i => mod2HomologyModule H R i H.HF2
        letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
          fun i => mod2HF2HomotopyModule H R i
        let x : TensorPower 1 := X (0, 0)
        let u : TensorPower 1 := X (0, 0) ^ 2
        let p : TensorPower 1 := X (0, 1)
        let q : TensorPower 1 := X (0, 0) ^ 3 + X (0, 1)
        let t : TensorPower 1 := X (0, 0) * X (0, 1)
        let z : TensorPower 1 := X (0, 0) ^ 4

        have dz : differentialPolynomial 1 z = 0 := by
          simpa [z, hiPolynomial] using hiPolynomial_differential 2

        have dp : differentialPolynomial 1 p = cupPolynomial u x := by
          simp [differentialPolynomial, p, u, x, cupPolynomial, insertLeft, insertRight,
            splitSlot, coproductGenerator, xi, Fin.sum_univ_succ, Finset.sum_range_succ]
          ring_nf
          simp [CharTwo.two_eq_zero]

        have dq : differentialPolynomial 1 q = cupPolynomial x u := by
          have hc (a b : TensorPower 2) : (a + b) ^ 3 =
              a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 := by
            calc
              _ = (a ^ 2 + b ^ 2) * (a + b) := by rw [pow_succ, CharTwo.add_sq]
              _ = _ := by ring
          simp [differentialPolynomial, q, u, x, cupPolynomial, insertLeft, insertRight,
            splitSlot, coproductGenerator, xi, Fin.sum_univ_succ, Finset.sum_range_succ, hc]
          ring_nf
          simp [CharTwo.two_eq_zero]

        have dt : differentialPolynomial 1 t =
            cupPolynomial q x + cupPolynomial u u + cupPolynomial x p := by
          simp [differentialPolynomial, t, q, u, x, p, cupPolynomial, insertLeft, insertRight,
            splitSlot, coproductGenerator, xi, Fin.sum_univ_succ, Finset.sum_range_succ]
          ring_nf
          simp [CharTwo.two_eq_zero]

        have low_exponents (d : (Fin 1 × ℕ) →₀ ℕ)
            (hd : Finsupp.weight weight d ≤ 4) :
            d = Finsupp.single (0,0) (d (0,0)) + Finsupp.single (0,1) (d (0,1)) := by
          apply singleSlot_exponents_eq_two
          intro j hj
          by_contra hn
          have hw := Finsupp.le_weight_of_ne_zero' weight hn
          have hp : 2 ^ 3 ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide) (by omega)
          change 2 ^ (j + 1) - 1 ≤ Finsupp.weight weight d at hw
          norm_num at hp
          omega

        have degree_four_monomial (d : (Fin 1 × ℕ) →₀ ℕ)
            (hd : Finsupp.weight weight d = 4) :
            monomial d (1 : F2) = z ∨ monomial d (1 : F2) = t := by
          have he := low_exponents d (by omega)
          have hd' : d (0,0) + 3 * d (0,1) = 4 :=
            (singleSlot_two_weight _ _).symm.trans ((congrArg (Finsupp.weight weight) he).symm.trans hd)
          by_cases hy : d (0,1) = 0
          · have hx : d (0,0) = 4 := by omega
            left
            rw [he, hx, hy]
            simp [z, X_pow_eq_monomial]
          · have hx : d (0,0) = 1 := by omega
            have hy' : d (0,1) = 1 := by omega
            right
            rw [he, hx, hy']
            simp [t, X, monomial_mul]

        let eps : TensorPower 2 →ₗ[F2] F2 :=
          lcoeff F2 (Finsupp.single (0,0) 2 + Finsupp.single (1,0) 2) +
            lcoeff F2 (Finsupp.single (0,0) 1 + Finsupp.single (1,1) 1)

        have eps_uu : eps (cupPolynomial u u) = 1 := by
          simp only [cupPolynomial, u, map_pow, rename_X]
          simp [eps, X_pow_eq_monomial, monomial_mul,
            coeff_monomial, Finsupp.ext_iff, Finsupp.single_apply]
          intro h
          have := h 0
          norm_num at this

        have eps_qx : eps (cupPolynomial q x) = 0 := by
          have hm : cupPolynomial q x =
              monomial (Finsupp.single (0,0) 3 + Finsupp.single (1,0) 1) (1 : F2) +
              monomial (Finsupp.single (0,1) 1 + Finsupp.single (1,0) 1) (1 : F2) := by
            simp only [cupPolynomial, q, x, map_add, map_pow, rename_X, add_mul]
            rw [X_pow_eq_monomial]
            simp [X, monomial_mul]
          have he (d : (Fin 2 × ℕ) →₀ ℕ) (h1 : d (0,0) ≠ 1) (h2 : d (0,0) ≠ 2) :
              eps (monomial d (1 : F2)) = 0 := by
            have hn1 : d ≠ Finsupp.single (0,0) 1 + Finsupp.single (1,1) 1 := by
              intro hd
              apply h1
              simpa using congrArg (fun e => e (0,0)) hd
            have hn2 : d ≠ Finsupp.single (0,0) 2 + Finsupp.single (1,0) 2 := by
              intro hd
              apply h2
              simpa using congrArg (fun e => e (0,0)) hd
            simp [eps, coeff_monomial, hn1, hn2]
          rw [hm, map_add, he _ (by norm_num) (by norm_num), he _ (by norm_num) (by norm_num), add_zero]

        have eps_xp : eps (cupPolynomial x p) = 1 := by
          simp only [cupPolynomial, x, p, rename_X]
          simp [eps, X, monomial_mul,
            coeff_monomial, Finsupp.ext_iff, Finsupp.single_apply]
          intro h
          have := h 0
          norm_num at this

        have eps_differential (b : cochains 1 4) : eps (differential 1 4 b).val = 0 := by
          let f := eps.comp ((differentialPolynomial 1).comp (cochains 1 4).subtype)
          have hf : f = 0 := by
            apply (cochainsMonomialBasis 1 4).ext
            intro d
            change eps (differentialPolynomial 1 (cochainsMonomialBasis 1 4 d).val) = 0
            rw [cochainsMonomialBasis_val]
            rcases degree_four_monomial d.val d.property.1 with h | h
            · rw [h, dz, map_zero]
            · rw [h, dt, map_add, map_add, eps_uu, eps_qx, eps_xp]
              decide
          exact LinearMap.congr_fun hf b

        have toda_not_boundary (b : cochains 1 4) :
            (differential 1 4 b).val ≠ cupPolynomial x p + cupPolynomial q x := by
          intro hb
          have h := eps_differential b
          rw [hb, map_add, eps_xp, eps_qx, add_zero] at h
          exact one_ne_zero h

        have degree_three_monomial (d : (Fin 1 × ℕ) →₀ ℕ)
            (hd : Finsupp.weight weight d = 3) :
            monomial d (1 : F2) = q + p ∨ monomial d (1 : F2) = p := by
          have he := low_exponents d (by omega)
          have hd' : d (0,0) + 3 * d (0,1) = 3 :=
            (singleSlot_two_weight _ _).symm.trans ((congrArg (Finsupp.weight weight) he).symm.trans hd)
          by_cases hy : d (0,1) = 0
          · have hx : d (0,0) = 3 := by omega
            left
            rw [he, hx, hy]
            simp [q, p, add_assoc, CharTwo.add_self_eq_zero, X_pow_eq_monomial]
          · have hx : d (0,0) = 0 := by omega
            have hy' : d (0,1) = 1 := by omega
            right
            rw [he, hx, hy']
            simp [p, X]

        let retractThree : TensorPower 2 →ₗ[F2] TensorPower 1 :=
          (lcoeff F2 (Finsupp.single (0,0) 1 + Finsupp.single (1,0) 2)).smulRight q +
            (lcoeff F2 (Finsupp.single (0,0) 2 + Finsupp.single (1,0) 1)).smulRight p

        have retractThree_xu : retractThree (cupPolynomial x u) = q := by
          have hne : (Finsupp.single ((0 : Fin 2),0) 1 + Finsupp.single (1,0) 2 :
              (Fin 2 × ℕ) →₀ ℕ) ≠ Finsupp.single (0,0) 2 + Finsupp.single (1,0) 1 := by
            intro he
            have := congrArg (fun e => e (0,0)) he
            norm_num at this
          simp only [cupPolynomial, x, u, map_pow, rename_X]
          rw [X_pow_eq_monomial]
          simp [retractThree, X, monomial_mul, coeff_monomial, hne]

        have retractThree_ux : retractThree (cupPolynomial u x) = p := by
          have hne : (Finsupp.single ((0 : Fin 2),0) 2 + Finsupp.single (1,0) 1 :
              (Fin 2 × ℕ) →₀ ℕ) ≠ Finsupp.single (0,0) 1 + Finsupp.single (1,0) 2 := by
            intro he
            have := congrArg (fun e => e (0,0)) he
            norm_num at this
          simp only [cupPolynomial, x, u, map_pow, rename_X]
          rw [X_pow_eq_monomial]
          simp [retractThree, X, monomial_mul, coeff_monomial, hne]

        have retractThree_differential (b : cochains 1 3) :
            retractThree (differential 1 3 b).val = b.val := by
          let f := retractThree.comp ((differentialPolynomial 1).comp (cochains 1 3).subtype)
          have hf : f = (cochains 1 3).subtype := by
            apply (cochainsMonomialBasis 1 3).ext
            intro d
            change retractThree (differentialPolynomial 1 (cochainsMonomialBasis 1 3 d).val) =
              (cochainsMonomialBasis 1 3 d).val
            rw [cochainsMonomialBasis_val]
            rcases degree_three_monomial d.val d.property.1 with h | h
            · rw [h, map_add, dq, dp, map_add, retractThree_xu, retractThree_ux]
            · rw [h, dp, retractThree_ux]
          exact LinearMap.congr_fun hf b

        let MilnorPair (n : ℤ) := Σ i : ℤ, MilnorMonomial i × MilnorMonomial (n - i)

        /- Put the two exponent vectors in distinct slots of the existing model. -/
        let milnorPairExponents {n : ℤ} (d : MilnorPair n) : (Fin 2 × ℕ) →₀ ℕ :=
          d.2.1.val.mapDomain (fun j => ((0 : Fin 2), j)) +
            d.2.2.val.mapDomain (fun j => ((1 : Fin 2), j))

        /- The full basis derived from the already constructed linear coordinates,
        not an additional existence input. -/
        let cooperationMilnorBasis (n : ℤ) :
            Module.Basis (MilnorMonomial n) F2 (mod2HomologyF2 H R n H.HF2) :=
          Module.Basis.ofRepr (cooperationMilnorEquiv H R B n)

        /- Tensor the derived full bases and take the basis of their direct sum. -/
        let cooperationTensorMilnorBasis (n : ℤ) :
            Module.Basis (MilnorPair n) F2
              (cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n) :=
          letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
            fun i => mod2HomologyModule H R i H.HF2
          DFinsupp.basis fun i => (cooperationMilnorBasis i).tensorProduct (R := F2) (S := F2)
            (cooperationMilnorBasis (n - i))

        have milnorMonomialPolynomial_zero :
            milnorMonomialPolynomial zeroMilnorMonomial = 1 := by
          simp [milnorMonomialPolynomial, zeroMilnorMonomial]

        have cooperationMilnorPolynomial_unit :
            cooperationMilnorPolynomial H R B 0 (cooperationUnit H) = 1 := by
          simp [cooperationMilnorPolynomial, cooperationMilnorEquiv_unit,
            Finsupp.linearCombination_single, milnorMonomialPolynomial_zero]

        have cooperationMilnorPolynomial_reduced_basis (n : ℤ) (d : PositiveMonomial n) :
            cooperationMilnorPolynomial H R B n ((B.basis n) d).val =
              milnorMonomialPolynomial (⟨d.val, d.property.1⟩ : MilnorMonomial n) := by
          change Finsupp.linearCombination F2 milnorMonomialPolynomial
            (cooperationMilnorEquiv H R B n ((B.basis n) d).val) = _
          erw [cooperationMilnorEquiv_reduced_basis H R B n d]
          simp only [Finsupp.linearCombination_single, one_smul]

        have cooperationTensorMilnorPolynomial_lof_tmul (n i : ℤ)
            (a : Mod2Cooperations H i) (b : Mod2Cooperations H (n - i)) :
            letI : ∀ j, Module F2 (Mod2Cooperations H j) :=
              fun j => mod2HomologyModule H R j H.HF2
            cooperationTensorMilnorPolynomial H R B n (DirectSum.lof F2 ℤ _ i (a ⊗ₜ[F2] b)) =
              cupPolynomial (cooperationMilnorPolynomial H R B i a)
                (cooperationMilnorPolynomial H R B (n - i) b) := by
          simp only [cooperationTensorMilnorPolynomial, DirectSum.toModule_lof,
            LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
            cupPolynomial, AlgHom.toLinearMap_apply]
          rfl


        have milnorPairExponents_zero {n : ℤ} (d : MilnorPair n) (j : ℕ) :
            milnorPairExponents d (0, j) = d.2.1.val j := by
          have hi : Function.Injective (fun j : ℕ => ((0 : Fin 2), j)) := fun _ _ h =>
            congrArg Prod.snd h
          have hn : (0, j) ∉ Set.range (fun k : ℕ => ((1 : Fin 2), k)) := by simp
          simp only [milnorPairExponents, Finsupp.add_apply, Finsupp.mapDomain_apply hi,
            Finsupp.mapDomain_notin_range _ _ hn, add_zero]

        have milnorPairExponents_one {n : ℤ} (d : MilnorPair n) (j : ℕ) :
            milnorPairExponents d (1, j) = d.2.2.val j := by
          have hi : Function.Injective (fun j : ℕ => ((1 : Fin 2), j)) := fun _ _ h =>
            congrArg Prod.snd h
          have hn : (1, j) ∉ Set.range (fun k : ℕ => ((0 : Fin 2), k)) := by simp
          simp only [milnorPairExponents, Finsupp.add_apply, Finsupp.mapDomain_apply hi,
            Finsupp.mapDomain_notin_range _ _ hn, zero_add]

        /- The first exponent vector also recovers its summand degree by weight. -/
        have milnorPairExponents_injective (n : ℤ) :
            Function.Injective (milnorPairExponents (n := n)) := by
          rintro ⟨i, a, b⟩ ⟨i', a', b'⟩ h
          have ha : a.val = a'.val := by
            ext j
            have hh := congrArg (fun d => d (0, j)) h
            simpa only [milnorPairExponents_zero] using hh
          have hi : i = i' := a.property.symm.trans ((congrArg (fun d => (slotWeight d : ℤ)) ha).trans a'.property)
          subst i'
          have haa : a = a' := Subtype.ext ha
          have hb : b = b' := by
            apply Subtype.ext
            ext j
            have hh := congrArg (fun d => d (1, j)) h
            simpa only [milnorPairExponents_one] using hh
          cases haa
          cases hb
          rfl

        /- Concatenating two basis monomials gives their two-slot exponent vector. -/
        have cup_milnorMonomialPolynomial {n : ℤ} (d : MilnorPair n) :
            cupPolynomial (milnorMonomialPolynomial d.2.1) (milnorMonomialPolynomial d.2.2) =
              MvPolynomial.monomial (milnorPairExponents d) (1 : F2) := by
          simp only [cupPolynomial, milnorMonomialPolynomial, MvPolynomial.rename_monomial,
            ← Finsupp.mapDomain_comp, MvPolynomial.monomial_mul, mul_one]
          rfl

        have cooperationMilnorPolynomial_basis (n : ℤ) (d : MilnorMonomial n) :
            cooperationMilnorPolynomial H R B n (cooperationMilnorBasis n d) =
              milnorMonomialPolynomial d := by
          simp [cooperationMilnorBasis, Module.Basis.coe_ofRepr, cooperationMilnorPolynomial,
            Finsupp.linearCombination_single]

        /- Single-slot polynomial coordinates lose no cooperation classes. -/
        have cooperationTensorMilnorBasis_apply (n : ℤ) (d : MilnorPair n) :
            letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
              fun i => mod2HomologyModule H R i H.HF2
            cooperationTensorMilnorBasis n d = DirectSum.lof F2 ℤ _ d.1
              (cooperationMilnorBasis d.1 d.2.1 ⊗ₜ[F2]
                cooperationMilnorBasis (n - d.1) d.2.2) := by
          change (cooperationTensorMilnorBasis n).repr.symm (Finsupp.single d 1) = _
          dsimp only [cooperationTensorMilnorBasis, DFinsupp.basis]
          erw [LinearEquiv.symm_trans_apply]
          simp only [LinearEquiv.symm_symm]
          erw [DFinsupp.mapRange.linearEquiv_symm]
          simp only [sigmaFinsuppLequivDFinsupp]
          erw [DFinsupp.mapRange.linearEquiv_apply]
          erw [sigmaFinsuppEquivDFinsupp_single]
          erw [DFinsupp.mapRange_single, Module.Basis.repr_symm_single_one,
            Module.Basis.tensorProduct_apply']
          rfl

        have cooperationTensorMilnorPolynomial_basis (n : ℤ) (d : MilnorPair n) :
            cooperationTensorMilnorPolynomial H R B n (cooperationTensorMilnorBasis n d) =
              MvPolynomial.monomial (milnorPairExponents d) (1 : F2) := by
          rw [cooperationTensorMilnorBasis_apply]
          erw [cooperationTensorMilnorPolynomial_lof_tmul]
          rw [cooperationMilnorPolynomial_basis, cooperationMilnorPolynomial_basis,
            cup_milnorMonomialPolynomial]

        /- The tensor polynomial map is faithful across all total-degree summands,
        not only within a chosen pair of factors. -/
        have cooperationTensorMilnorPolynomial_injective (n : ℤ) :
            Function.Injective (cooperationTensorMilnorPolynomial H R B n) := by
          apply LinearMap.injective_of_linearIndependent (cooperationTensorMilnorBasis n).span_eq
          have hl := (MvPolynomial.basisMonomials (Fin 2 × ℕ) F2).linearIndependent.comp _
            (milnorPairExponents_injective n)
          simpa only [Function.comp_def, cooperationTensorMilnorPolynomial_basis,
            MvPolynomial.coe_basisMonomials] using hl


        have cooperationPolynomial_cast (i j : ℤ) (h : i = j)
            (a : Mod2Cooperations H i) :
            cooperationMilnorPolynomial H R B j
              ((LinearEquiv.cast (R := F2) (M := fun k => mod2HomologyF2 H R k H.HF2) h) a) =
              cooperationMilnorPolynomial H R B i a := by
          subst j
          rfl

        have cooperationPolynomial_left_unit (n : ℤ) (a : Mod2Cooperations H n) :
            cooperationTensorMilnorPolynomial H R B n
              (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) n a) =
              insertLeft 1 (cooperationMilnorPolynomial H R B n a) := by
          rw [cooperationTensorUnit_apply, cooperationTensorMilnorPolynomial_lof_tmul,
            cooperationPolynomial_cast, cooperationMilnorPolynomial_unit]
          simp [cupPolynomial, insertLeft]

        have cooperationPolynomial_right_unit (n : ℤ) (a : Mod2Cooperations H n) :
            letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
              fun i => mod2HomologyModule H R i H.HF2
            cooperationTensorMilnorPolynomial H R B n
              (DirectSum.lof F2 ℤ _ n (a ⊗ₜ[F2]
                (LinearEquiv.cast (R := F2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                  (sub_self n).symm) (cooperationUnit H))) =
              insertRight 1 (cooperationMilnorPolynomial H R B n a) := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
            fun i => mod2HomologyModule H R i H.HF2
          rw [cooperationTensorMilnorPolynomial_lof_tmul, cooperationPolynomial_cast,
            cooperationMilnorPolynomial_unit]
          simp only [cupPolynomial, map_one, mul_one]
          rfl

        let singleWordEquiv (t : ℤ) : PositiveMonomial t ≃ MilnorWord 1 t :=
          { toFun := fun a => ⟨fun _ => a.val, by simpa [wordDegree] using a.property.1,
              fun _ => a.property.2⟩
            invFun := fun d => ⟨d.val 0, by simpa [wordDegree] using d.property.1, d.property.2 0⟩
            left_inv := fun a => rfl
            right_inv := by
              intro d
              apply Subtype.ext
              funext i
              fin_cases i
              rfl }

        have singleWord_exponents (t : ℤ) (a : PositiveMonomial t) :
            (slotExponentsEquiv 1).symm (singleWordEquiv t a).val =
              a.val.mapDomain (fun j => ((0 : Fin 1), j)) := by
          have hi : Function.Injective (fun j : ℕ => ((0 : Fin 1), j)) := fun _ _ h =>
            congrArg Prod.snd h
          apply (slotExponentsEquiv 1).injective
          rw [Equiv.apply_symm_apply]
          funext i
          fin_cases i
          ext j
          simp [slotExponentsEquiv, singleWordEquiv, Finsupp.mapDomain_apply hi]

        let reducedCochainEquiv :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (n : ℕ),
            LinearMap.ker (cooperationCounitF2 H R n) ≃ₗ[F2] cochains 1 n := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro n
          exact (B.basis n).repr.trans
              ((Finsupp.domLCongr (R := F2) (singleWordEquiv n)).trans (cochainsWordEquiv 1 n).symm)


        have reducedCochainEquiv_val :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (n : ℕ)
            (a : LinearMap.ker (cooperationCounitF2 H R n)),
            (reducedCochainEquiv n a).val = cooperationMilnorPolynomial H R B n a.val := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro n a
          let f := (cochains 1 n).subtype.comp (reducedCochainEquiv n).toLinearMap
          let g := (cooperationMilnorPolynomial H R B n).comp
            (LinearMap.ker (cooperationCounitF2 H R n)).subtype
          have h : f = g := by
            apply (B.basis n).ext
            intro d
            change ((cochainsWordEquiv 1 n).symm
              (Finsupp.domLCongr (R := F2) (singleWordEquiv n)
                ((B.basis n).repr (B.basis n d)))).val =
              cooperationMilnorPolynomial H R B n (B.basis n d).val
            rw [Module.Basis.repr_self, Finsupp.domLCongr_single,
              cochainsWordEquiv_symm_single_val, singleWord_exponents,
              cooperationMilnorPolynomial_reduced_basis]
            rfl
          exact LinearMap.congr_fun h a

        let positiveReduced :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (n : ℕ) (hn : n ≠ 0) (a : Mod2Cooperations H n),
            LinearMap.ker (cooperationCounitF2 H R n) := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro n hn a
          haveI := H.homotopy_vanishes n (by exact_mod_cast hn)
          exact ⟨a, Subsingleton.elim _ _⟩

        let positiveCochain :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (n : ℕ) (hn : n ≠ 0) (a : Mod2Cooperations H n),
            cochains 1 n := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro n hn a
          exact reducedCochainEquiv n (positiveReduced n hn a)


        have positiveCochain_val :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (n : ℕ) (hn : n ≠ 0) (a : Mod2Cooperations H n),
            (positiveCochain n hn a).val = cooperationMilnorPolynomial H R B n a := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro n hn a
          exact reducedCochainEquiv_val n (positiveReduced n hn a)


        have reduced_coproduct :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (hM : Mod2MilnorCoproductCompatible H R K B) (n : ℤ)
            (a : LinearMap.ker (cooperationCounitF2 H R n)),
            cooperationTensorMilnorPolynomial H R B n (cooperationTensorDiagonal H R K n a.val) =
              splitSlot (0 : Fin 1) (cooperationMilnorPolynomial H R B n a.val) := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro hM n a
          let f := ((cooperationTensorMilnorPolynomial H R B n).comp
            (cooperationTensorDiagonal H R K n)).comp (LinearMap.ker (cooperationCounitF2 H R n)).subtype
          let g := ((splitSlot (0 : Fin 1)).toLinearMap.comp
            (cooperationMilnorPolynomial H R B n)).comp (LinearMap.ker (cooperationCounitF2 H R n)).subtype
          have he : f = g := by
            apply (B.basis n).ext
            intro d
            change cooperationTensorMilnorPolynomial H R B n
              (cooperationTensorDiagonal H R K n (B.basis n d).val) =
              splitSlot (0 : Fin 1) (cooperationMilnorPolynomial H R B n (B.basis n d).val)
            rw [cooperationMilnorPolynomial_reduced_basis]
            exact hM n d
          exact LinearMap.congr_fun he a

        let reducedDiagonal :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (n : ℤ) (a : Mod2Cooperations H n),
            cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro n a
          exact cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) n a +
            cooperationTensorDiagonal H R K n a +
            DirectSum.lof F2 ℤ _ n (a ⊗ₜ[F2]
              (LinearEquiv.cast (R := F2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                (sub_self n).symm) (cooperationUnit H))


        have reducedDiagonal_eq_of (n : ℤ) (a : Mod2Cooperations H n)
            (d : cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n) :
            letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
            cooperationTensorDiagonal H R K n a =
              cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) n a + d +
              DirectSum.lof F2 ℤ _ n (a ⊗ₜ[F2]
                (LinearEquiv.cast (R := F2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                  (sub_self n).symm) (cooperationUnit H)) →
            reducedDiagonal n a = d := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          intro h
          have hdouble (z : cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n) : z + z = 0 := by
            simpa only [add_smul, one_smul] using
              (show ((1 : F2) + 1) • z = 0 by rw [show (1 : F2) + 1 = 0 by decide, zero_smul])
          dsimp only [reducedDiagonal]
          rw [h]
          calc
            _ = (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) n a +
                cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) n a) + d +
                (DirectSum.lof F2 ℤ _ n (a ⊗ₜ[F2]
                  (LinearEquiv.cast (R := F2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                    (sub_self n).symm) (cooperationUnit H)) +
                 DirectSum.lof F2 ℤ _ n (a ⊗ₜ[F2]
                  (LinearEquiv.cast (R := F2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                    (sub_self n).symm) (cooperationUnit H))) := by abel
            _ = d := by rw [hdouble, hdouble, zero_add, add_zero]

        have reducedDiagonal_polynomial :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (hM : Mod2MilnorCoproductCompatible H R K B)
            (n : ℕ) (hn : n ≠ 0) (a : Mod2Cooperations H n),
            cooperationTensorMilnorPolynomial H R B n (reducedDiagonal n a) =
              (differential 1 n (positiveCochain n hn a)).val := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro hM n hn a
          change cooperationTensorMilnorPolynomial H R B n (reducedDiagonal n a) =
            differentialPolynomial 1 (positiveCochain n hn a).val
          rw [positiveCochain_val n hn a]
          dsimp only [reducedDiagonal]
          rw [map_add, map_add, cooperationPolynomial_left_unit, cooperationPolynomial_right_unit]
          have hc := reduced_coproduct hM n (positiveReduced n hn a)
          change cooperationTensorMilnorPolynomial H R B n (cooperationTensorDiagonal H R K n a) =
            splitSlot (0 : Fin 1) (cooperationMilnorPolynomial H R B n a) at hc
          erw [hc]
          simp only [differentialPolynomial, LinearMap.add_apply, LinearMap.sum_apply,
            AlgHom.toLinearMap_apply, Fin.sum_univ_one]
          abel

        have toda_obstruction :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (hM : Mod2MilnorCoproductCompatible H R K B)
            (x1 : Mod2Cooperations H 1) (u2 : Mod2Cooperations H 2)
            (hx : cooperationMilnorPolynomial H R B 1 x1 = x)
            (hu : cooperationMilnorPolynomial H R B 2 u2 = u)
            (a b : Mod2Cooperations H 3) (c : Mod2Cooperations H 4)
            (ha : reducedDiagonal 3 a = DirectSum.lof F2 ℤ _ 2 (u2 ⊗ₜ[F2] x1))
            (hb : reducedDiagonal 3 b = DirectSum.lof F2 ℤ _ 1 (x1 ⊗ₜ[F2] u2)),
            reducedDiagonal 4 c ≠
              DirectSum.lof F2 ℤ
                (fun i => Mod2Cooperations H i ⊗[F2] mod2HomologyF2 H R (4 - i) H.HF2) 1 (x1 ⊗ₜ[F2] a) + DirectSum.lof F2 ℤ
                (fun i => Mod2Cooperations H i ⊗[F2] mod2HomologyF2 H R (4 - i) H.HF2) 3 (b ⊗ₜ[F2] x1) := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro hM x1 u2 hx hu a b c ha hb
          have hpa : cooperationMilnorPolynomial H R B 3 a = p := by
            have he := congrArg (cooperationTensorMilnorPolynomial H R B 3) ha
            erw [reducedDiagonal_polynomial hM 3 (by decide),
              cooperationTensorMilnorPolynomial_lof_tmul, hu, hx] at he
            have hr := congrArg retractThree he
            rw [retractThree_differential, positiveCochain_val 3 (by decide) a, retractThree_ux] at hr
            exact hr
          have hpb : cooperationMilnorPolynomial H R B 3 b = q := by
            have he := congrArg (cooperationTensorMilnorPolynomial H R B 3) hb
            erw [reducedDiagonal_polynomial hM 3 (by decide),
              cooperationTensorMilnorPolynomial_lof_tmul, hx, hu] at he
            have hr := congrArg retractThree he
            rw [retractThree_differential, positiveCochain_val 3 (by decide) b, retractThree_xu] at hr
            exact hr
          intro hc
          have he := congrArg (cooperationTensorMilnorPolynomial H R B 4) hc
          erw [reducedDiagonal_polynomial hM 4 (by decide), map_add,
            cooperationTensorMilnorPolynomial_lof_tmul, cooperationTensorMilnorPolynomial_lof_tmul,
            hx, hpa, hpb] at he
          exact toda_not_boundary (positiveCochain 4 (by decide) c) he
        have hM : Mod2MilnorCoproductCompatible H R K B :=
          KIP126.Def.standardHF2AdamsContext.cooperationStructure.coproduct
        constructor
        · intro x1 u2 hx hu a b c ha hb hc
          apply toda_obstruction hM x1 u2 hx hu a b c
            (reducedDiagonal_eq_of 3 a _ ha) (reducedDiagonal_eq_of 3 b _ hb)
          exact reducedDiagonal_eq_of 4 c _ hc
        · intro d pLow k hk hp
          have hp0 : milnorMonomialPolynomial (⟨pLow.val, pLow.property.1⟩ : MilnorMonomial d) =
              (MvPolynomial.X ((0 : Fin 1), 0)) ^ k := by
            simp only [milnorMonomialPolynomial, hp, Finsupp.mapDomain_single,
              MvPolynomial.X_pow_eq_monomial]
          apply cooperationTensorMilnorPolynomial_injective d
          change cooperationTensorMilnorPolynomial H R B d
            (cooperationTensorDiagonal H R K d (B.basis d pLow).val) = _
          rw [hM d pLow, map_add, cooperationPolynomial_left_unit,
            cooperationPolynomial_right_unit, cooperationMilnorPolynomial_reduced_basis d pLow, hp0]
          have hpow (a b : TensorPower 2) : (a + b) ^ k = a ^ k + b ^ k := by
            rcases hk with rfl | rfl
            · simp
            · exact add_pow_char_pow a b 2 1
          simp [splitSlot, coproductGenerator, xi, Finset.sum_range_succ,
            insertLeft, insertRight, hpow, add_comm]
    obtain ⟨low_cooperation_obstructions, low_basis_primitive⟩ := low_cooperation_calculation

    open KIP126.Algebra in
    open scoped TensorProduct DirectSum in
    have firstLift_hurewicz_ne_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))  {X : C} (n : ℤ)
        (α : HomotopyGroup n X) (hn : ¬ AdamsFiltrationAtLeast H α 2)
        (a : HomotopyGroup n (adamsTower H.unit X 1))
        (ha : a ≫ adamsTowerMap H.unit X 0 1 (by decide) = α) :
        a ≫ adamsUnit H.unit (adamsTower H.unit X 1) ≠ 0 := by
      intro hz
      obtain ⟨a₂, ha₂⟩ := (adamsResolutionTriangle H.unit X 1).coyoneda_exact₂
        (adamsResolutionTriangle_distinguished H.unit X 1) a hz
      change a = a₂ ≫ adamsTowerStep H.unit X 1 at ha₂
      apply hn
      refine ⟨a₂, ?_⟩
      rw [adamsTowerMap_succ H.unit X 0 1 (by decide), ← Category.assoc, ← ha₂]
      exact ha

    have firstLift_reduced_ne_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  (d : ℤ)
        (α : HomotopyGroup (d - 1) (SphereSpectrum : C))
        (hn : ¬ AdamsFiltrationAtLeast H α 2)
        (a : HomotopyGroup (d - 1) (adamsTower H.unit SphereSpectrum 1))
        (ha : a ≫ adamsTowerMap H.unit SphereSpectrum 0 1 (by decide) = α) :
        sphereFirstTowerHomologyEquiv H R d
          (a ≫ adamsUnit H.unit (adamsTower H.unit SphereSpectrum 1)) ≠ 0 := by
      intro hz
      apply firstLift_hurewicz_ne_zero H (d - 1) α hn a ha
      exact (sphereFirstTowerHomologyEquiv H R d).map_eq_zero_iff.mp hz


    have unique_nonzero_reduced {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  (B : Mod2ReducedMilnorBasis H R) (d : ℤ)
        (p : PositiveMonomial d) (hp : ∀ q : PositiveMonomial d, q = p) :
        letI := mod2HomologyModule H R d H.HF2
        letI := mod2HF2HomotopyModule H R d
        ∀ b : LinearMap.ker (cooperationCounitF2 H R d), b ≠ 0 → b = B.basis d p := by
      letI := mod2HomologyModule H R d H.HF2
      letI := mod2HF2HomotopyModule H R d
      intro b hb
      apply (B.basis d).repr.injective
      rw [Module.Basis.repr_self]
      have hc : (B.basis d).repr b p ≠ 0 := by
        intro hc
        apply hb
        apply (B.basis d).repr.injective
        ext q
        rw [hp q, hc, map_zero, Finsupp.zero_apply]
      have htwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      have hone : (B.basis d).repr b p = 1 := (htwo _).resolve_left hc
      ext q
      rw [hp q, hone, Finsupp.single_eq_same]


    have firstLift_cooperation_identification {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)
        (B : Mod2ReducedMilnorBasis H R) (d : ℤ)
        (p : PositiveMonomial d) (hp : ∀ q : PositiveMonomial d, q = p)
        (α : HomotopyGroup (d - 1) (SphereSpectrum : C))
        (hn : ¬ AdamsFiltrationAtLeast H α 2)
        (a : HomotopyGroup (d - 1) (adamsTower H.unit SphereSpectrum 1))
        (ha : a ≫ adamsTowerMap H.unit SphereSpectrum 0 1 (by decide) = α) :
        letI := mod2HomologyModule H R d H.HF2
        letI := mod2HF2HomotopyModule H R d
        (sphereFirstTowerHomologyEquiv H R d
          (a ≫ adamsUnit H.unit (adamsTower H.unit SphereSpectrum 1))).val =
            (B.basis d p).val := by
      letI := mod2HomologyModule H R d H.HF2
      letI := mod2HF2HomotopyModule H R d
      let b := sphereFirstTowerHomologyEquiv H R d
        (a ≫ adamsUnit H.unit (adamsTower H.unit SphereSpectrum 1))
      let b₂ : LinearMap.ker (cooperationCounitF2 H R d) := ⟨b.val, b.property⟩
      have hb₂ : b₂ ≠ 0 := by
        intro hz
        apply firstLift_reduced_ne_zero H R d α hn a ha
        apply Subtype.ext
        exact congrArg Subtype.val hz
      exact congrArg Subtype.val (unique_nonzero_reduced H R B d p hp b₂ hb₂)


    let mod2HomologyConnecting {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ) :
        Mod2Homology H n T.Z →+ Mod2Homology H (n - 1) T.X :=
      connectingHomomorphism (T.map (tensorLeft H.HF2)) n

    let mod2HomologyConnectingF2 {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  (T : HoCofiberSequence (C := C)) (n : ℤ) :
        mod2HomologyF2 H R n T.Z →ₗ[ZMod 2] mod2HomologyF2 H R (n - 1) T.X :=
      letI := mod2HomologyModule H R n T.Z
      letI := mod2HomologyModule H R (n - 1) T.X
      (mod2HomologyConnecting H T n).toZModLinearMap 2

    have homology_bottom_injective {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : H.HF2 ◁ T.f = 0) :
        Function.Injective (Mod2Homology.pushforward H T.g n) := by
      let U := T.map (tensorLeft H.HF2)
      have hU : U.f = 0 := hf
      haveI : Mono U.g := (Triangle.mk U.f U.g U.h).mono₂ U.distinguished hU
      intro x y hxy
      exact (cancel_mono U.g).1 hxy

    have homology_connecting_surjective {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : H.HF2 ◁ T.f = 0) :
        Function.Surjective (mod2HomologyConnecting H T n) := by
      intro x
      exact (lesHomotopyExactH (T.map (tensorLeft H.HF2)) n x).mp (by
        change x ≫ (H.HF2 ◁ T.f) = 0
        rw [hf, comp_zero])

    have homology_connecting_injective {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hy : Subsingleton (Mod2Homology H n T.Y)) :
        Function.Injective (mod2HomologyConnecting H T n) := by
      apply (injective_iff_map_eq_zero (mod2HomologyConnecting H T n)).mpr
      intro z hz
      obtain ⟨y, hyz⟩ := (les_homotopy_exact_g (T.map (tensorLeft H.HF2)) n z).mp hz
      have hy0 : y = 0 := hy.elim _ _
      simpa only [hy0, map_zero] using hyz.symm

    let homology_top_equiv {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : H.HF2 ◁ T.f = 0)
        (hy : Subsingleton (Mod2Homology H n T.Y)) :
        mod2HomologyF2 H R n T.Z ≃ₗ[ZMod 2] mod2HomologyF2 H R (n - 1) T.X :=
      LinearEquiv.ofBijective (mod2HomologyConnectingF2 H R T n)
        ⟨homology_connecting_injective H T n hy,
          homology_connecting_surjective H T n hf⟩

    have homology_bottom_surjective {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hx : Subsingleton (Mod2Homology H (n - 1) T.X)) :
        Function.Surjective (Mod2Homology.pushforward H T.g n) := by
      intro z
      exact (les_homotopy_exact_g (T.map (tensorLeft H.HF2)) n z).mp (hx.elim _ _)

    let homology_bottom_equiv {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : H.HF2 ◁ T.f = 0)
        (hx : Subsingleton (Mod2Homology H (n - 1) T.X)) :
        mod2HomologyF2 H R n T.Y ≃ₗ[ZMod 2] mod2HomologyF2 H R n T.Z :=
      LinearEquiv.ofBijective (mod2HomologyF2Map H R T.g n).hom
        ⟨homology_bottom_injective H T n hf,
          homology_bottom_surjective H T n hx⟩

    have homology_middle_subsingleton {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hy : Subsingleton (Mod2Homology H n T.Y))
        (hx : Subsingleton (Mod2Homology H (n - 1) T.X)) :
        Subsingleton (Mod2Homology H n T.Z) := by
      letI := hx
      exact (homology_connecting_injective H T n hy).subsingleton


    let sphereHomologyShiftEquiv {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ]  (n m : ℤ) :
        Mod2Homology H n (Sphere (C := C) m) ≃ HomotopyGroup (n - m) H.HF2 := by
      let F := shiftFunctor C m
      let a : Sphere (C := C) n ≅ F.obj (Sphere (C := C) (n - m)) :=
        (shiftFunctorAdd' C (n - m) m n (by omega)).app SphereSpectrum
      let e : H.HF2 ⊗ Sphere (C := C) m ≅ F.obj H.HF2 :=
        ((tensorLeft H.HF2).commShiftIso m).app SphereSpectrum ≪≫
          F.mapIso (ρ_ H.HF2)
      exact (Iso.homCongr a e).trans (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm

    have sphereHomologyShiftSubsingleton {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (n m : ℤ) (hn : n ≠ m) :
        Subsingleton (Mod2Homology H n (Sphere (C := C) m)) := by
      letI := H.homotopy_vanishes (n - m) (sub_ne_zero.mpr hn)
      exact (sphereHomologyShiftEquiv H n m).injective.subsingleton

    have sphereHomologySubsingleton {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (n : ℤ) (hn : n ≠ 0) :
        Subsingleton (Mod2Homology H n (SphereSpectrum : C)) := by
      letI := H.homotopy_vanishes n hn
      let e : Mod2Homology H n (SphereSpectrum : C) ≃+ HomotopyGroup n H.HF2 :=
        ((homotopyGroupFunctor n).mapIso (ρ_ H.HF2)).addCommGroupIsoToAddEquiv
      exact e.injective.subsingleton


    have twoCell_otherDegrees {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
        (d : ℤ) (f : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (n : ℤ) (hn0 : n ≠ 0) (hnd : n ≠ d) :
        Subsingleton (Mod2Homology H n (HasFunctorialCofiber.cofib f)) := by
      exact homology_middle_subsingleton H (HoCofiberSequence.ofMorphism f) n
        (sphereHomologySubsingleton H n hn0)
        (sphereHomologyShiftSubsingleton H (n - 1) (d - 1) (by omega))

    let twoCell_bottom_equiv {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)
        (d : ℤ) (hd : d ≠ 0)
        (f : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (hf : H.HF2 ◁ f = 0) :
        mod2HomologyF2 H R 0 SphereSpectrum ≃ₗ[ZMod 2]
          mod2HomologyF2 H R 0 (HasFunctorialCofiber.cofib f) :=
      homology_bottom_equiv H R (HoCofiberSequence.ofMorphism f) 0 hf
        (sphereHomologyShiftSubsingleton H (-1) (d - 1) (by omega))

    let twoCell_top_equiv {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)
        (d : ℤ) (hd : d ≠ 0)
        (f : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (hf : H.HF2 ◁ f = 0) :
        mod2HomologyF2 H R d (HasFunctorialCofiber.cofib f) ≃ₗ[ZMod 2]
          mod2HomologyF2 H R (d - 1) (Sphere (C := C) (d - 1)) :=
      homology_top_equiv H R (HoCofiberSequence.ofMorphism f) d hf
        (sphereHomologySubsingleton H d hd)


    have twoCell_comparison_to_unit {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (d : ℤ)
        (α : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (a : Sphere (C := C) (d - 1) ⟶ adamsTower H.unit SphereSpectrum 1)
        (ha : a ≫ adamsTowerMap H.unit SphereSpectrum 0 1 (by decide) = α) :
        ∃ φ : HasFunctorialCofiber.cofib α ⟶ H.HF2 ⊗ SphereSpectrum,
          HasFunctorialCofiber.cofibι α ≫ φ = adamsUnit H.unit SphereSpectrum ∧
          HasFunctorialCofiber.cofibδ α ≫ (shiftFunctor C (1 : ℤ)).map a =
            φ ≫ adamsResolutionConnecting H.unit SphereSpectrum 0 := by
      obtain ⟨φ, hφ, hδ⟩ := complete_distinguished_triangle_morphism
        (Triangle.mk α (HasFunctorialCofiber.cofibι α) (HasFunctorialCofiber.cofibδ α))
        (adamsResolutionTriangle H.unit SphereSpectrum 0)
        (HasFunctorialCofiber.cofib_distinguished α)
        (adamsResolutionTriangle_distinguished H.unit SphereSpectrum 0)
        a (𝟙 SphereSpectrum) (by
          change α ≫ 𝟙 SphereSpectrum = a ≫ adamsTowerStep H.unit SphereSpectrum 0
          simpa only [adamsTowerMap, adamsTowerComposite, eqToHom_refl,
            Category.id_comp, Category.comp_id] using ha.symm)
      refine ⟨φ, ?_, hδ⟩
      simpa only [Triangle.mk_mor₂, adamsResolutionTriangle, Triangle.mk,
        adamsTower, Category.id_comp] using hφ

    have twoCell_comparison_bottom {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
        {X : C} (i : SphereSpectrum ⟶ X) (φ : X ⟶ H.HF2)
        (hiφ : i ≫ φ = H.unit) :
        Mod2Homology.pushforward H φ 0
          (Mod2Homology.pushforward H i 0
            ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ adamsUnit H.unit SphereSpectrum)) =
          cooperationUnit H := by
      change (((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ adamsUnit H.unit SphereSpectrum) ≫
        H.HF2 ◁ i) ≫ H.HF2 ◁ φ = _
      rw [Category.assoc, Category.assoc, ← whiskerLeft_comp]
      erw [mod2AdamsUnit_naturality H (i ≫ φ)]
      rw [hiφ]
      simp [cooperationUnit, Mod2EilenbergMacLane.unit]

    have twoCell_comparison_connecting {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
        (d : ℤ) (α : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (a : Sphere (C := C) (d - 1) ⟶ adamsTower H.unit SphereSpectrum 1)
        (φ : HasFunctorialCofiber.cofib α ⟶ H.HF2 ⊗ SphereSpectrum)
        (hδ : HasFunctorialCofiber.cofibδ α ≫ (shiftFunctor C (1 : ℤ)).map a =
          φ ≫ adamsResolutionConnecting H.unit SphereSpectrum 0)
        (z : Mod2Homology H d (HasFunctorialCofiber.cofib α)) :
        adamsHomologyBoundary H SphereSpectrum d (Mod2Homology.pushforward H φ d z) =
          Mod2Homology.pushforward H a (d - 1)
            (mod2HomologyConnecting H (HoCofiberSequence.ofMorphism α) d z) := by
      let T := (HoCofiberSequence.ofMorphism α).map (tensorLeft H.HF2)
      let U := adamsHomologySequence H SphereSpectrum
      have hlast : (H.HF2 ◁ φ) ≫ U.h = T.h ≫ (H.HF2 ◁ a)⟦(1 : ℤ)⟧' := by
        change (H.HF2 ◁ φ) ≫ (H.HF2 ◁ adamsResolutionConnecting H.unit SphereSpectrum 0) ≫ _ =
          ((H.HF2 ◁ HasFunctorialCofiber.cofibδ α) ≫ _) ≫ _
        rw [← Category.assoc, ← whiskerLeft_comp, ← hδ, whiskerLeft_comp, Category.assoc]
        have hn := ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.naturality a
        change (H.HF2 ◁ (shiftFunctor C (1 : ℤ)).map a) ≫
            ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app
              (adamsTower H.unit SphereSpectrum 1) =
          ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app (Sphere (C := C) (d - 1)) ≫
            (shiftFunctor C (1 : ℤ)).map (H.HF2 ◁ a) at hn
        simpa only [Category.assoc, U, adamsHomologySequence,
          HoCofiberSequence.ofMorphism, adamsTower] using congrArg
          (fun f => (H.HF2 ◁ HasFunctorialCofiber.cofibδ α) ≫ f) hn
      exact connectingHomomorphism_naturality T U (H.HF2 ◁ a) (H.HF2 ◁ φ) hlast d z

    have twoCell_comparison_top_boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
        (d : ℤ) (α : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (a : Sphere (C := C) (d - 1) ⟶ adamsTower H.unit SphereSpectrum 1)
        (φ : HasFunctorialCofiber.cofib α ⟶ H.HF2 ⊗ SphereSpectrum)
        (hδ : HasFunctorialCofiber.cofibδ α ≫ (shiftFunctor C (1 : ℤ)).map a =
          φ ≫ adamsResolutionConnecting H.unit SphereSpectrum 0)
        (z : Mod2Homology H d (HasFunctorialCofiber.cofib α))
        (hz : mod2HomologyConnecting H (HoCofiberSequence.ofMorphism α) d z =
          adamsUnit H.unit (Sphere (C := C) (d - 1))) :
        adamsHomologyBoundary H SphereSpectrum d (Mod2Homology.pushforward H φ d z) =
          a ≫ adamsUnit H.unit (adamsTower H.unit SphereSpectrum 1) := by
      rw [twoCell_comparison_connecting H d α a φ hδ z, hz]
      exact mod2AdamsUnit_naturality H a

    have twoCell_comparison_top_cooperation {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)
        (d : ℤ) (hd : d ≠ 0)
        (α : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (a : Sphere (C := C) (d - 1) ⟶ adamsTower H.unit SphereSpectrum 1)
        (φ : HasFunctorialCofiber.cofib α ⟶ H.HF2 ⊗ SphereSpectrum)
        (hδ : HasFunctorialCofiber.cofibδ α ≫ (shiftFunctor C (1 : ℤ)).map a =
          φ ≫ adamsResolutionConnecting H.unit SphereSpectrum 0)
        (z : Mod2Homology H d (HasFunctorialCofiber.cofib α))
        (hz : mod2HomologyConnecting H (HoCofiberSequence.ofMorphism α) d z =
          adamsUnit H.unit (Sphere (C := C) (d - 1))) :
        Mod2Homology.pushforward H (φ ≫ (ρ_ H.HF2).hom) d z =
          (sphereFirstTowerHomologyEquiv H R d
            (a ≫ adamsUnit H.unit (adamsTower H.unit SphereSpectrum 1))).val := by
      rw [← twoCell_comparison_top_boundary H d α a φ hδ z hz,
        sphereFirstTowerHomologyEquiv_boundary]
      have hzero : adamsHomologyAction H R SphereSpectrum d
          (Mod2Homology.pushforward H φ d z) = 0 :=
        (sphereHomologySubsingleton H d hd).elim _ _
      rw [hzero, map_zero, sub_zero]
      change z ≫ H.HF2 ◁ (φ ≫ (ρ_ H.HF2).hom) =
        (z ≫ H.HF2 ◁ φ) ≫ H.HF2 ◁ (ρ_ H.HF2).hom
      rw [whiskerLeft_comp, Category.assoc]

    let sphereZeroCoordinate {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] (R : Mod2RingStructure H)  : mod2HomologyF2 H R 0 SphereSpectrum ≃ₗ[ZMod 2] ZMod 2 :=
      (sphereHomologyCoefficientF2Equiv H R 0).trans (mod2Pi0LinearEquiv H R)

    have sphereZeroCoordinate_unit {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  :
        sphereZeroCoordinate H R
          ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ adamsUnit H.unit SphereSpectrum) = 1 := by
      change H.pi0Equiv (((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫
        adamsUnit H.unit SphereSpectrum) ≫ (ρ_ H.HF2).hom) = 1
      have hu : adamsUnit H.unit (SphereSpectrum : C) ≫ (ρ_ H.HF2).hom = H.unit := by
        simp only [adamsUnit, Category.assoc, rightUnitor_naturality,
          ← unitors_equal, Iso.inv_hom_id_assoc]
      rw [Category.assoc, hu]
      simp [Mod2EilenbergMacLane.unit]

    have tensor_zero_of_first_filtration {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  {X Y : C} (f : X ⟶ Y)
        (hf : AdamsFiltrationAtLeast H f 1) : H.HF2 ◁ f = 0 := by
      obtain ⟨l, hl⟩ := hf
      rw [← hl, whiskerLeft_comp,
        mod2_adamsTowerMap_eq_zero H R Y 0 1 (by decide), comp_zero]

    have tensorCoaction_apply {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (X : C) (n : ℤ) (x : Mod2Homology H n X) :
        mod2TensorCoaction H R K X n x = K.comparison X n (mod2CoactionMap H X n x) := rfl

    have tensorCoaction_counit {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (X : C) (n : ℤ) (x : Mod2Homology H n X) :
        cooperationTensorAugmentation H R (fun i => mod2HomologyF2 H R i X) n
          (mod2TensorCoaction H R K X n x) = x := by
      rw [tensorCoaction_apply, K.action_comparison]
      change (x ≫ mod2Coaction H X) ≫ mod2FreeAction H R X = x
      rw [Category.assoc, mod2Coaction_counit, Category.comp_id]

    have tensorCoaction_naturality {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  {X Y : C} (f : X ⟶ Y) (n : ℤ)
        (x : Mod2Homology H n X) :
        mod2TensorCoaction H R K Y n (Mod2Homology.pushforward H f n x) =
          cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X)
            (fun i => (mod2HomologyF2Map H R f i).hom) n
            (mod2TensorCoaction H R K X n x) := by
      rw [tensorCoaction_apply, ← mod2CoactionMap_naturality, K.naturality]
      rfl

    have tensorUnit_naturality {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
        (V : ℤ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        {W : ℤ → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 2) (W i)]
        (f : ∀ i, V i →ₗ[ZMod 2] W i) (n : ℤ) (x : V n) :
        cooperationTensorMap H R V f n (cooperationTensorUnit H R V n x) =
          cooperationTensorUnit H R W n (f n x) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      have hc (i j : ℤ) (h : i = j) (z : V i) :
          f j ((LinearEquiv.cast (R := ZMod 2) (M := V) h) z) =
            (LinearEquiv.cast (R := ZMod 2) (M := W) h) (f i z) := by
        subst j
        rfl
      simp [cooperationTensorUnit, cooperationTensorMap, gradedTensorMapRight]
      exact congrArg (fun z : W (n - 0) =>
        DirectSum.lof (ZMod 2) ℤ (fun i => Mod2Cooperations H i ⊗[ZMod 2] W (n - i)) 0
          (cooperationUnit H ⊗ₜ[ZMod 2] z)) (hc n (n - 0) (sub_zero n).symm x)


    have pureTensorCoefficient_injective
        {A W : Type} [AddCommGroup A] [AddCommGroup W]
        [Module (ZMod 2) A] [Module (ZMod 2) W]
        (y : W) (ev : W →ₗ[ZMod 2] ZMod 2) (hy : ev y = 1) :
        Function.Injective (fun a : A => a ⊗ₜ[ZMod 2] y) := by
      intro a b hab
      have h := congrArg (fun z => TensorProduct.rid (ZMod 2) A (ev.lTensor A z)) hab
      simpa [hy] using h


    have coaction_coefficient_identification {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
        {X : C} (φ : X ⟶ H.HF2) (d : ℤ)
        (ed : mod2HomologyF2 H R d X)
        (e0 : mod2HomologyF2 H R (d - d) X)
        (u0 : mod2HomologyF2 H R (d - d) H.HF2)
        (ev : mod2HomologyF2 H R (d - d) H.HF2 →ₗ[ZMod 2] ZMod 2)
        (hu0 : ev u0 = 1)
        (b c : mod2HomologyF2 H R d H.HF2)
        (hφd : Mod2Homology.pushforward H φ d ed = b)
        (hφ0 : Mod2Homology.pushforward H φ (d - d) e0 = u0)
        (hprimitive : mod2TensorCoaction H R K H.HF2 d b =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) d b +
            DirectSum.lof (ZMod 2) ℤ _ d (b ⊗ₜ[ZMod 2] u0))
        (hexpansion : mod2TensorCoaction H R K X d ed =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) d ed +
            DirectSum.lof (ZMod 2) ℤ _ d (c ⊗ₜ[ZMod 2] e0)) :
        c = b := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      have hnat := tensorCoaction_naturality H R K φ d ed
      rw [hφd, hprimitive, hexpansion, map_add] at hnat
      erw [tensorUnit_naturality H R (fun i => mod2HomologyF2 H R i X) (fun i => (mod2HomologyF2Map H R φ i).hom) d ed] at hnat
      change _ = cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) d
        (Mod2Homology.pushforward H φ d ed) + _ at hnat
      rw [hφd] at hnat
      have hsum := add_left_cancel hnat
      simp only [cooperationTensorMap, gradedTensorMapRight, DirectSum.lmap_lof,
        TensorProduct.map_tmul, LinearMap.id_apply] at hsum
      change DirectSum.lof (ZMod 2) ℤ
          (fun i => mod2HomologyF2 H R i H.HF2 ⊗[ZMod 2]
            mod2HomologyF2 H R (d - i) H.HF2) d (b ⊗ₜ[ZMod 2] u0) =
        DirectSum.lof (ZMod 2) ℤ
          (fun i => mod2HomologyF2 H R i H.HF2 ⊗[ZMod 2]
            mod2HomologyF2 H R (d - i) H.HF2) d
          (c ⊗ₜ[ZMod 2] Mod2Homology.pushforward H φ (d - d) e0) at hsum
      rw [hφ0] at hsum
      have ht : b ⊗ₜ[ZMod 2] u0 = c ⊗ₜ[ZMod 2] u0 := by
        have he := congrArg (fun z => z d) hsum
        simpa only [DirectSum.lof_apply] using he
      exact (pureTensorCoefficient_injective u0 ev hu0 ht).symm

    have directSum_two_decompose
        (A : ℤ → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module (ZMod 2) (A i)]
        (a b : ℤ) (hab : a ≠ b)
        (h : ∀ i, i ≠ a → i ≠ b → Subsingleton (A i)) (z : ⨁ i, A i) :
        z = DirectSum.lof (ZMod 2) ℤ A a (z a) + DirectSum.lof (ZMod 2) ℤ A b (z b) := by
      ext i
      by_cases hia : i = a
      · subst i
        change z a = (DirectSum.lof (ZMod 2) ℤ A a (z a)) a +
          (DirectSum.lof (ZMod 2) ℤ A b (z b)) a
        have hz : (DirectSum.lof (ZMod 2) ℤ A b (z b)) a = 0 :=
          DirectSum.of_eq_of_ne b a (z b) hab
        rw [DirectSum.lof_apply, hz, add_zero]
      · by_cases hib : i = b
        · subst i
          change z b = (DirectSum.lof (ZMod 2) ℤ A a (z a)) b +
            (DirectSum.lof (ZMod 2) ℤ A b (z b)) b
          have hz : (DirectSum.lof (ZMod 2) ℤ A a (z a)) b = 0 :=
            DirectSum.of_eq_of_ne a b (z a) (Ne.symm hab)
          rw [DirectSum.lof_apply, hz, zero_add]
        · letI := h i hia hib
          exact Subsingleton.elim _ _

    let cooperationZeroEquiv {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  : mod2HomologyF2 H R 0 H.HF2 ≃ₗ[ZMod 2] ZMod 2 := by
      letI := mod2HomologyModule H R 0 H.HF2
      letI := mod2HF2HomotopyModule H R 0
      have hs : Subsingleton (LinearMap.ker (cooperationCounitF2 H R 0)) := by
        letI : IsEmpty (PositiveMonomial 0) :=
          ⟨fun d => (lt_irrefl 0) (positiveMonomial_degree_pos d)⟩
        exact (B.basis 0).repr.injective.subsingleton
      have hinj : Function.Injective (cooperationCounitF2 H R 0) := by
        apply LinearMap.ker_eq_bot.mp
        apply bot_unique
        intro x hx
        change x = 0
        exact congrArg Subtype.val (hs.elim (⟨x, hx⟩ :
          LinearMap.ker (cooperationCounitF2 H R 0)) 0)
      exact (LinearEquiv.ofBijective (cooperationCounitF2 H R 0)
        ⟨hinj, cooperationCounit_surjective H R 0⟩).trans (mod2Pi0LinearEquiv H R)

    have cooperationZeroEquiv_unit {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  : cooperationZeroEquiv H R B (cooperationUnit H) = 1 := by
      change H.pi0Equiv (cooperationCounit H R 0 (cooperationUnit H)) = 1
      rw [cooperationCounit_unit, AddEquiv.apply_symm_apply]


    have cooperation_twoCell_decompose {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)
        (V : ℤ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (d : ℤ) (hd : d ≠ 0)
        (hV : ∀ i, i ≠ 0 → i ≠ d → Subsingleton (V i))
        (e0 : V (d - d) ≃ₗ[ZMod 2] ZMod 2)
        (z : cooperationTensor H R V d) :
        ∃ (w : V d) (c : mod2HomologyF2 H R d H.HF2),
          z = cooperationTensorUnit H R V d w +
            DirectSum.lof (ZMod 2) ℤ _ d (c ⊗ₜ[ZMod 2] e0.symm 1) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      let L : (mod2HomologyF2 H R 0 H.HF2 ⊗[ZMod 2] V (d - 0)) ≃ₗ[ZMod 2] V d :=
        ((TensorProduct.congr (cooperationZeroEquiv H R B)
          (LinearEquiv.refl (ZMod 2) (V (d - 0)))).trans
          (TensorProduct.lid (ZMod 2) (V (d - 0)))).trans
          (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero d))
      let T : (Mod2Cooperations H d ⊗[ZMod 2] V (d - d)) ≃ₗ[ZMod 2]
          Mod2Cooperations H d :=
        (TensorProduct.congr (LinearEquiv.refl (ZMod 2) _) e0).trans
          (TensorProduct.rid (ZMod 2) _)
      refine ⟨L (z 0), T (z d), ?_⟩
      have hdec := directSum_two_decompose
        (fun i => Mod2Cooperations H i ⊗[ZMod 2] V (d - i)) 0 d (Ne.symm hd)
        (fun i hi0 hid => by
          letI := hV (d - i) (by omega) (by omega)
          infer_instance) z
      have hcast (i j : ℤ) (h : i = j) (w : V j) :
          (LinearEquiv.cast (R := ZMod 2) (M := V) h)
            ((LinearEquiv.cast (R := ZMod 2) (M := V) h.symm) w) = w := by
        subst j
        rfl
      have hleft : z 0 = cooperationUnit H ⊗ₜ[ZMod 2]
          (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero d).symm) (L (z 0)) := by
        have hL (w : V d) : L (cooperationUnit H ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero d).symm) w) = w := by
          let cw := (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero d).symm) w
          have ht := TensorProduct.congr_tmul (cooperationZeroEquiv H R B)
            (LinearEquiv.refl (ZMod 2) (V (d - 0)))
            (cooperationUnit H : mod2HomologyF2 H R 0 H.HF2) cw
          have ht' := congrArg (fun z : ZMod 2 ⊗[ZMod 2] V (d - 0) =>
            (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero d))
              (TensorProduct.lid (ZMod 2) (V (d - 0)) z)) ht
          change L (cooperationUnit H ⊗ₜ[ZMod 2] cw) =
            (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero d))
              ((cooperationZeroEquiv H R B (cooperationUnit H)) • cw) at ht'
          rw [cooperationZeroEquiv_unit H R B, one_smul] at ht'
          exact ht'.trans (hcast (d - 0) d (sub_zero d) w)
        apply L.injective
        rw [hL]
      have hright : z d = T (z d) ⊗ₜ[ZMod 2] e0.symm 1 := by
        have hT (a : Mod2Cooperations H d) : T (a ⊗ₜ[ZMod 2] e0.symm 1) = a := by
          dsimp only [T, LinearEquiv.trans_apply]
          rw [TensorProduct.congr_tmul]
          simp only [LinearEquiv.refl_apply, LinearEquiv.apply_symm_apply,
            TensorProduct.rid_tmul, one_smul]
        apply T.injective
        rw [hT]
      rw [hleft, hright] at hdec
      exact hdec

    have positiveTensor_augmentation_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
        (V : ℤ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (n k : ℤ) (hk : k ≠ 0) (a : Mod2Cooperations H k) (x : V (n - k)) :
        letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
          fun i => mod2HomologyModule H R i H.HF2
        cooperationTensorAugmentation H R V n
          (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x)) = 0 := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
        fun i => mod2HF2HomotopyModule H R i
      simp only [cooperationTensorAugmentation, LinearMap.comp_apply,
        cooperationTensorCounit, gradedTensorMap_lof_tmul,
        cooperationCounitF2_eq_zero_of_ne H R k hk, LinearMap.zero_apply,
        TensorProduct.zero_tmul, map_zero]


    have twoCell_coaction_expansion {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  (K : Mod2CooperationKunneth H R)
        (X : C) (d : ℤ) (hd : d ≠ 0)
        (hX : ∀ i, i ≠ 0 → i ≠ d → Subsingleton (Mod2Homology H i X))
        (e0 : mod2HomologyF2 H R (d - d) X ≃ₗ[ZMod 2] ZMod 2)
        (ed : mod2HomologyF2 H R d X) :
        ∃ c : mod2HomologyF2 H R d H.HF2,
          mod2TensorCoaction H R K X d ed =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) d ed +
              DirectSum.lof (ZMod 2) ℤ _ d (c ⊗ₜ[ZMod 2] e0.symm 1) := by
      obtain ⟨w, c, hc⟩ := cooperation_twoCell_decompose H R B
        (fun i => mod2HomologyF2 H R i X) d hd hX e0
        (mod2TensorCoaction H R K X d ed)
      have he := congrArg (cooperationTensorAugmentation H R
        (fun i => mod2HomologyF2 H R i X) d) hc
      have hactual : cooperationTensorAugmentation H R
          (fun i => mod2HomologyF2 H R i X) d
          (mod2TensorCoaction H R K X d ed) = ed := by
        change cooperationTensorAugmentation H R _ d
          (K.comparison X d (mod2CoactionMap H X d ed)) = ed
        rw [K.action_comparison]
        change (ed ≫ mod2Coaction H X) ≫ mod2FreeAction H R X = ed
        rw [Category.assoc, mod2Coaction_counit, Category.comp_id]
      rw [hactual, map_add, cooperationTensorUnit_augmentation,
        positiveTensor_augmentation_zero H R _ d d hd, add_zero] at he
      exact ⟨c, he ▸ hc⟩

    have homologyPushforward_cast {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  {X Y : C} (f : X ⟶ Y)
        (i j : ℤ) (h : i = j) (x : mod2HomologyF2 H R i X) :
        Mod2Homology.pushforward H f j
          ((LinearEquiv.cast (R := ZMod 2) (M := fun k => mod2HomologyF2 H R k X) h) x) =
        (LinearEquiv.cast (R := ZMod 2) (M := fun k => mod2HomologyF2 H R k Y) h)
          (Mod2Homology.pushforward H f i x) := by
      subst j
      rfl

    have homologyCast_cancel {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  (X : C) (i j : ℤ) (h : i = j)
        (x : mod2HomologyF2 H R j X) :
        (LinearEquiv.cast (R := ZMod 2) (M := fun k => mod2HomologyF2 H R k X) h)
          ((LinearEquiv.cast (R := ZMod 2) (M := fun k => mod2HomologyF2 H R k X) h.symm) x) = x := by
      subst j
      rfl


    have twoCell_actual_coaction {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R) (K : Mod2CooperationKunneth H R)
        (d : ℤ) (hd : d ≠ 0) (p : PositiveMonomial d)
        (hp : ∀ q : PositiveMonomial d, q = p)
        (α : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (hF1 : AdamsFiltrationAtLeast H α 1)
        (hF2 : ¬ AdamsFiltrationAtLeast H α 2)
        (hprimitive :
          letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
            fun i => mod2HomologyModule H R i H.HF2
          mod2TensorCoaction H R K H.HF2 d (B.basis d p).val =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) d (B.basis d p).val +
            DirectSum.lof (ZMod 2) ℤ _ d
              (((B.basis d p).val : mod2HomologyF2 H R d H.HF2) ⊗ₜ[ZMod 2]
              (LinearEquiv.cast (R := ZMod 2)
                (M := fun i => mod2HomologyF2 H R i H.HF2) (sub_self d).symm)
                (cooperationUnit H))) :
        letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
          fun i => mod2HomologyModule H R i H.HF2
        ∃ (ed : mod2HomologyF2 H R d (HasFunctorialCofiber.cofib α))
          (q0 : mod2HomologyF2 H R 0 (HasFunctorialCofiber.cofib α) ≃ₗ[ZMod 2] ZMod 2),
          ed ≠ 0 ∧
          mod2HomologyConnecting H (HoCofiberSequence.ofMorphism α) d ed =
            adamsUnit H.unit (Sphere (C := C) (d - 1)) ∧
          q0 (Mod2Homology.pushforward H (HasFunctorialCofiber.cofibι α) 0
            ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ adamsUnit H.unit SphereSpectrum)) = 1 ∧
          mod2TensorCoaction H R K (HasFunctorialCofiber.cofib α) d ed =
            cooperationTensorUnit H R
              (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α)) d ed +
              DirectSum.lof (ZMod 2) ℤ _ d
                (((B.basis d p).val : mod2HomologyF2 H R d H.HF2) ⊗ₜ[ZMod 2]
                (LinearEquiv.cast (R := ZMod 2)
                  (M := fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α))
                  (sub_self d).symm) (q0.symm 1)) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
        fun i => mod2HF2HomotopyModule H R i
      have hα : H.HF2 ◁ α = 0 := tensor_zero_of_first_filtration H R α hF1
      obtain ⟨a, ha⟩ := hF1
      obtain ⟨φ', hiφ', hδ⟩ := twoCell_comparison_to_unit H d α a ha
      let φ := φ' ≫ (ρ_ H.HF2).hom
      have hiφ : HasFunctorialCofiber.cofibι α ≫ φ = H.unit := by
        dsimp only [φ]
        rw [← Category.assoc, hiφ']
        simp only [adamsUnit, Category.assoc, rightUnitor_naturality,
          ← unitors_equal, Iso.inv_hom_id_assoc]
      let Etop := twoCell_top_equiv H R d hd α hα
      let ed := Etop.symm (adamsUnit H.unit (Sphere (C := C) (d - 1)))
      have hed : mod2HomologyConnecting H
          (HoCofiberSequence.ofMorphism α) d ed =
            adamsUnit H.unit (Sphere (C := C) (d - 1)) :=
        Etop.apply_symm_apply _
      let Ebottom := twoCell_bottom_equiv H R d hd α hα
      let q0 := Ebottom.symm.trans (sphereZeroCoordinate H R)
      let s0 : mod2HomologyF2 H R 0 SphereSpectrum :=
        (shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ adamsUnit H.unit SphereSpectrum
      have hq0 : q0 (Mod2Homology.pushforward H (HasFunctorialCofiber.cofibι α) 0 s0) = 1 := by
        change sphereZeroCoordinate H R (Ebottom.symm (Ebottom s0)) = 1
        rw [Ebottom.symm_apply_apply]
        exact sphereZeroCoordinate_unit H R
      have hbottom : q0.symm 1 =
          Mod2Homology.pushforward H (HasFunctorialCofiber.cofibι α) 0 s0 := by
        apply q0.injective
        rw [q0.apply_symm_apply, hq0]
      have hφ0 : Mod2Homology.pushforward H φ 0 (q0.symm 1) = cooperationUnit H := by
        rw [hbottom]
        exact twoCell_comparison_bottom H (HasFunctorialCofiber.cofibι α) φ hiφ
      have hφd : Mod2Homology.pushforward H φ d ed = (B.basis d p).val := by
        calc
          _ = (sphereFirstTowerHomologyEquiv H R d
              (a ≫ adamsUnit H.unit (adamsTower H.unit SphereSpectrum 1))).val :=
            twoCell_comparison_top_cooperation H R d hd α a φ' hδ ed hed
          _ = _ := firstLift_cooperation_identification H R B d p hp α hF2 a ha
      have hneq : ed ≠ 0 := by
        intro hz
        have hz' : (B.basis d p).val = 0 := by simpa only [hz, map_zero] using hφd.symm
        exact (B.basis d).ne_zero p (Subtype.ext hz')
      let e0 : mod2HomologyF2 H R (d - d) (HasFunctorialCofiber.cofib α) ≃ₗ[ZMod 2] ZMod 2 :=
        (LinearEquiv.cast (R := ZMod 2)
          (M := fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α)) (sub_self d)).trans q0
      let u0 : mod2HomologyF2 H R (d - d) H.HF2 :=
        (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i H.HF2)
          (sub_self d).symm) (cooperationUnit H)
      let ev : mod2HomologyF2 H R (d - d) H.HF2 →ₗ[ZMod 2] ZMod 2 :=
        ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i H.HF2)
          (sub_self d)).trans (cooperationZeroEquiv H R B)).toLinearMap
      have hu0 : ev u0 = 1 := by
        simp only [ev, u0, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
          homologyCast_cancel H R H.HF2 (d-d) 0 (sub_self d) (cooperationUnit H)]
        exact cooperationZeroEquiv_unit H R B
      have hφe0 : Mod2Homology.pushforward H φ (d - d) (e0.symm 1) = u0 := by
        change Mod2Homology.pushforward H φ (d - d)
          ((LinearEquiv.cast (R := ZMod 2)
            (M := fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α))
            (sub_self d).symm) (q0.symm 1)) = u0
        rw [homologyPushforward_cast, hφ0]
      obtain ⟨c, hc⟩ := twoCell_coaction_expansion H R B K (HasFunctorialCofiber.cofib α)
        d hd (twoCell_otherDegrees H d α) e0 ed
      have hcb : c = (B.basis d p).val :=
        coaction_coefficient_identification H R K φ d ed (e0.symm 1) u0 ev hu0
          (B.basis d p).val c hφd hφe0 hprimitive hc
      rw [hcb] at hc
      exact ⟨ed, q0, hneq, hed, hq0, hc⟩

    let boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ) :
        Mod2Homology H n T.Z →+ Mod2Homology H (n - 1) T.X :=
      connectingHomomorphism (T.map (tensorLeft H.HF2)) n


    have bottom_injective_of_homology_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : Mod2Homology.pushforward H T.f n = 0) :
        Function.Injective (Mod2Homology.pushforward H T.g n) := by
      apply (injective_iff_map_eq_zero (Mod2Homology.pushforward H T.g n)).mpr
      intro y hy
      obtain ⟨x, hx⟩ := (les_homotopy_exact_f (T.map (tensorLeft H.HF2)) n y).mp hy
      have hx0 : inducedMap (T.map (tensorLeft H.HF2)).f n x = 0 := by
        change Mod2Homology.pushforward H T.f n x = 0
        rw [hf, AddMonoidHom.zero_apply]
      exact hx.symm.trans hx0

    have boundary_surjective_of_homology_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : Mod2Homology.pushforward H T.f (n - 1) = 0) :
        Function.Surjective (boundary H T n) := by
      intro x
      apply (lesHomotopyExactH (T.map (tensorLeft H.HF2)) n x).mp
      change Mod2Homology.pushforward H T.f (n - 1) x = 0
      rw [hf, AddMonoidHom.zero_apply]

    have boundary_injective_of_target_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hy : Subsingleton (Mod2Homology H n T.Y)) :
        Function.Injective (boundary H T n) := by
      apply (injective_iff_map_eq_zero (boundary H T n)).mpr
      intro z hz
      obtain ⟨y, hyz⟩ := (les_homotopy_exact_g (T.map (tensorLeft H.HF2)) n z).mp hz
      have hy0 : y = 0 := hy.elim _ _
      simpa only [hy0, map_zero] using hyz.symm

    let boundaryEquiv_of_homology_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H)  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : Mod2Homology.pushforward H T.f (n - 1) = 0)
        (hy : Subsingleton (Mod2Homology H n T.Y)) :
        mod2HomologyF2 H R n T.Z ≃ₗ[ZMod 2] mod2HomologyF2 H R (n - 1) T.X := by
      letI := mod2HomologyModule H R n T.Z
      letI := mod2HomologyModule H R (n - 1) T.X
      exact LinearEquiv.ofBijective ((boundary H T n).toZModLinearMap 2)
        ⟨boundary_injective_of_target_zero H T n hy,
          boundary_surjective_of_homology_zero H T n hf⟩

    let bottomEquiv_of_homology_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H)  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : Mod2Homology.pushforward H T.f n = 0)
        (hx : Subsingleton (Mod2Homology H (n - 1) T.X)) :
        mod2HomologyF2 H R n T.Y ≃ₗ[ZMod 2] mod2HomologyF2 H R n T.Z :=
      LinearEquiv.ofBijective (mod2HomologyF2Map H R T.g n).hom
        ⟨bottom_injective_of_homology_zero H T n hf, fun z =>
          (les_homotopy_exact_g (T.map (tensorLeft H.HF2)) n z).mp (hx.elim _ _)⟩

    have pushforward_zero_of_disjoint_support {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C]  {X Y : C} (f : X ⟶ Y) (n : ℤ)
        (h : Subsingleton (Mod2Homology H n X) ∨ Subsingleton (Mod2Homology H n Y)) :
        Mod2Homology.pushforward H f n = 0 := by
      ext x
      rcases h with hx | hy
      · rw [hx.elim x 0, map_zero, AddMonoidHom.zero_apply]
      · exact hy.elim _ _


    have pushforward_zero_of_surjective_precomposition {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C]
        {A X Y : C} (j : A ⟶ X) (t : X ⟶ Y) (n : ℤ)
        (hj : Function.Surjective (Mod2Homology.pushforward H j n))
        (hjt : Mod2Homology.pushforward H (j ≫ t) n = 0) :
        Mod2Homology.pushforward H t n = 0 := by
      ext x
      obtain ⟨a, rfl⟩ := hj x
      have h := congrArg (fun f : Mod2Homology H n A →+ Mod2Homology H n Y => f a) hjt
      simpa only [Mod2Homology.pushforward, inducedMap, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, whiskerLeft_comp, Category.assoc, AddMonoidHom.zero_apply] using h

    have twice_map_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H)  {X Y : C} (f : X ⟶ Y) (n : ℤ) :
        Mod2Homology.pushforward H (2 • f) n = 0 := by
      ext x
      change x ≫ (tensorLeft H.HF2).map (2 • f) = 0
      rw [Functor.map_nsmul, Preadditive.comp_nsmul]
      exact mod2Homology_two_nsmul_zero H R n Y _

    have homology_boundary_factor {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (x : Mod2Homology H n T.Z) :
        connectingHomomorphism (T.map (tensorLeft H.HF2)) n x =
          mod2HomologyDesuspend H T.X n (Mod2Homology.pushforward H T.h n x) := by
      rw [connectingHomomorphism_eq_desuspend]
      simp only [HoCofiberSequence.map,
        mod2HomologyDesuspend, homotopyDesuspend, Mod2Homology.pushforward, inducedMap,
        AddMonoidHom.comp_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        Functor.id_obj, eqToHom_refl, Category.id_comp, Category.comp_id]
      change (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
        (shiftFunctor C (-1)).map (x ≫ H.HF2 ◁ T.h ≫ _) ≫ _ =
          (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
            (shiftFunctor C (-1)).map ((x ≫ H.HF2 ◁ T.h) ≫ _) ≫ _
      rw [Category.assoc]
      rfl

    have mapped_boundary_comp {C : Type 1} [StableHomotopyCategory.{1,0} C]  (T : HoCofiberSequence (C := C))
        (F G : C ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ]
        [F.IsTriangulated] [G.IsTriangulated]
        (n : ℤ) (x : HomotopyGroup n (G.obj (F.obj T.Z))) :
        connectingHomomorphism ((T.map F).map G) n x =
          connectingHomomorphism (T.map (F ⋙ G)) n x := by
      have hlast : 𝟙 _ ≫ (T.map (F ⋙ G)).h =
          ((T.map F).map G).h ≫ (𝟙 (G.obj (F.obj T.X)))⟦(1 : ℤ)⟧' := by
        simp [HoCofiberSequence.map, Functor.commShiftIso_comp_hom_app,
          Functor.map_comp, Category.assoc]
      have h := connectingHomomorphism_naturality ((T.map F).map G) (T.map (F ⋙ G))
        (𝟙 _) (𝟙 _) hlast n x
      simpa [inducedMap] using h.symm

    have mapped_boundary_naturality {C : Type 1} [StableHomotopyCategory.{1,0} C]  (T : HoCofiberSequence (C := C))
        (F G : C ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ]
        [F.IsTriangulated] [G.IsTriangulated]
        (α : F ⟶ G) [α.CommShift ℤ] (n : ℤ) (x : HomotopyGroup n (F.obj T.Z)) :
        connectingHomomorphism (T.map G) n (inducedMap (α.app T.Z) n x) =
          inducedMap (α.app T.X) (n - 1) (connectingHomomorphism (T.map F) n x) := by
      apply connectingHomomorphism_naturality (T.map F) (T.map G)
        (α.app T.X) (α.app T.Z) (n := n) (z := x)
      change α.app T.Z ≫ G.map T.h ≫ (G.commShiftIso (1 : ℤ)).hom.app T.X =
        (F.map T.h ≫ (F.commShiftIso (1 : ℤ)).hom.app T.X) ≫ _
      rw [← Category.assoc, ← α.naturality T.h, Category.assoc,
        ← NatTrans.shift_app_comm, ← Category.assoc]

    have double_homology_boundary_factor {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (x : Mod2Homology H n (H.HF2 ⊗ T.Z)) :
        connectingHomomorphism ((T.map (tensorLeft H.HF2)).map (tensorLeft H.HF2)) n x =
          mod2DoubleHomologyDesuspend H T.X n
            (Mod2Homology.pushforward H (H.HF2 ◁ T.h) n x) := by
      rw [homology_boundary_factor]
      change mod2HomologyDesuspend H (H.HF2 ⊗ T.X) n
        (x ≫ H.HF2 ◁ (H.HF2 ◁ T.h ≫ _)) =
          mod2HomologyDesuspend H (H.HF2 ⊗ T.X) n
            ((x ≫ H.HF2 ◁ (H.HF2 ◁ T.h)) ≫ H.HF2 ◁ _)
      rw [whiskerLeft_comp, Category.assoc]

    have coaction_boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  [(mod2UnitNatTrans H).CommShift ℤ]
        (T : HoCofiberSequence (C := C)) (n : ℤ) (x : Mod2Homology H n T.Z) :
        connectingHomomorphism ((T.map (tensorLeft H.HF2)).map (tensorLeft H.HF2)) n
          (mod2CoactionMap H T.Z n x) =
        mod2CoactionMap H T.X (n - 1)
          (connectingHomomorphism (T.map (tensorLeft H.HF2)) n x) := by
      let F := tensorLeft H.HF2
      let α : F ⟶ F ⋙ F := F.leftUnitor.inv ≫ Functor.whiskerRight (mod2UnitNatTrans H) F
      have h := mapped_boundary_naturality T F (F ⋙ F) α n x
      change connectingHomomorphism ((T.map F).map F) n _ = _
      rw [mapped_boundary_comp]
      convert! h using 1 <;>
        simp [α, F, mod2CoactionMap, mod2Coaction, mod2UnitNatTrans] <;> rfl

    let boundaryF2 {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H)  (T : HoCofiberSequence (C := C)) (n : ℤ) :
        mod2HomologyF2 H R n T.Z →ₗ[ZMod 2] mod2HomologyF2 H R (n - 1) T.X :=
      letI := mod2HomologyModule H R n T.Z
      letI := mod2HomologyModule H R (n - 1) T.X
      let f : Mod2Homology H n T.Z →+ Mod2Homology H (n - 1) T.X :=
        connectingHomomorphism (T.map (tensorLeft H.HF2)) n
      f.toZModLinearMap 2

    have tensorLowerMap_comp {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H)  (V W U : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, AddCommGroup (W i)] [∀ i, AddCommGroup (U i)]
        [∀ i, Module (ZMod 2) (V i)] [∀ i, Module (ZMod 2) (W i)] [∀ i, Module (ZMod 2) (U i)]
        (f : ∀ i, V i →ₗ[ZMod 2] W i) (g : ∀ i, W i →ₗ[ZMod 2] U (i - 1)) (n : ℤ) :
        (cooperationTensorLowerMap H R W U g n).comp (cooperationTensorMap H R V f n) =
          cooperationTensorLowerMap H R V U (fun i => (g i).comp (f i)) n := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
      exact KIP126.Algebra.gradedTensorLowerMap_comp (Mod2Cooperations H) f g n

    have kunneth_boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        (T : HoCofiberSequence (C := C)) (n : ℤ)
        (x : Mod2Homology H n (H.HF2 ⊗ T.Z)) :
        K.comparison T.X (n - 1)
          (connectingHomomorphism ((T.map (tensorLeft H.HF2)).map (tensorLeft H.HF2)) n x) =
          cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i T.Z)
            (fun i => mod2HomologyF2 H R i T.X) (boundaryF2 H R T) n
            (K.comparison T.Z n x) := by
      rw [double_homology_boundary_factor, hK, K.naturality]
      have hg : (fun i => (mod2HomologyDesuspendF2 H R T.X i).comp
          ((mod2HomologyF2Map H R T.h i).hom)) = boundaryF2 H R T := by
        funext i
        ext z
        change mod2HomologyDesuspend H T.X i
          (Mod2Homology.pushforward H T.h i z) =
            connectingHomomorphism (T.map (tensorLeft H.HF2)) i z
        exact (homology_boundary_factor H T i z).symm
      rw [← LinearMap.comp_apply, tensorLowerMap_comp, hg]


    have tensorCoaction_boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  [(mod2UnitNatTrans H).CommShift ℤ]
        (hK : Mod2KunnethSuspensionCompatible H R K)
        (T : HoCofiberSequence (C := C)) (n : ℤ) (x : Mod2Homology H n T.Z) :
        mod2TensorCoaction H R K T.X (n - 1)
          (connectingHomomorphism (T.map (tensorLeft H.HF2)) n x) =
          cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i T.Z)
            (fun i => mod2HomologyF2 H R i T.X) (boundaryF2 H R T) n
            (mod2TensorCoaction H R K T.Z n x) := by
      rw [tensorCoaction_apply, ← coaction_boundary, kunneth_boundary H R K hK]
      rfl

    have compare_cones_of_factorization {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)]
        {A B X : C} (f : A ⟶ X) (g : B ⟶ X) (a : A ⟶ B)
        (ha : a ≫ g = f) :
        ∃ c : HasFunctorialCofiber.cofib f ⟶ HasFunctorialCofiber.cofib g,
          HasFunctorialCofiber.cofibι f ≫ c = HasFunctorialCofiber.cofibι g ∧
          HasFunctorialCofiber.cofibδ f ≫ (shiftFunctor C (1 : ℤ)).map a =
            c ≫ HasFunctorialCofiber.cofibδ g := by
      obtain ⟨c, hc, hδ⟩ := complete_distinguished_triangle_morphism
        (Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f))
        (Triangle.mk g (HasFunctorialCofiber.cofibι g) (HasFunctorialCofiber.cofibδ g))
        (HasFunctorialCofiber.cofib_distinguished f)
        (HasFunctorialCofiber.cofib_distinguished g) a (𝟙 X) (by
          change f ≫ 𝟙 X = a ≫ g
          simpa only [Category.comp_id] using ha.symm)
      refine ⟨c, ?_, hδ⟩
      change HasFunctorialCofiber.cofibι f ≫ c = 𝟙 X ≫ HasFunctorialCofiber.cofibι g at hc
      simpa only [Category.id_comp] using hc


    have triple_cone_geometry {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)]
        {A B X Y : C} (f : A ⟶ B) (g : B ⟶ X) (h : X ⟶ Y)
        (hToda : KIP126.StableHomotopy.Toda.Relation 0 f g h) :
        ∃ (Q : C) (i : B ⟶ Q) (p : Q ⟶ A⟦(1 : ℤ)⟧)
          (_ : Triangle.mk f i p ∈ distTriang C)
          (b : Q ⟶ X) (t : HasFunctorialCofiber.cofib b ⟶ Y),
          i ≫ b = g ∧ b ≫ h = 0 ∧ HasFunctorialCofiber.cofibι b ≫ t = h ∧
          (∃ c : HasFunctorialCofiber.cofib g ⟶ HasFunctorialCofiber.cofib b,
            HasFunctorialCofiber.cofibι g ≫ c = HasFunctorialCofiber.cofibι b ∧
            HasFunctorialCofiber.cofibδ g ≫ (shiftFunctor C (1 : ℤ)).map i =
              c ≫ HasFunctorialCofiber.cofibδ b) ∧
          (∃ c : HasFunctorialCofiber.cofib h ⟶ HasFunctorialCofiber.cofib t,
            HasFunctorialCofiber.cofibι h ≫ c = HasFunctorialCofiber.cofibι t ∧
            HasFunctorialCofiber.cofibδ h ≫
                (shiftFunctor C (1 : ℤ)).map (HasFunctorialCofiber.cofibι b) =
              c ≫ HasFunctorialCofiber.cofibδ t) := by
      obtain ⟨Q, i, p, hT, b, hb, hb0⟩ := hToda
      have hbh : b ≫ h = 0 := by simpa only [comp_zero] using hb0.symm
      obtain ⟨t, ht⟩ := (Triangle.mk b (HasFunctorialCofiber.cofibι b)
        (HasFunctorialCofiber.cofibδ b)).yoneda_exact₂
        (HasFunctorialCofiber.cofib_distinguished b) h hbh
      change h = HasFunctorialCofiber.cofibι b ≫ t at ht
      exact ⟨Q, i, p, hT, b, t, hb, hbh, ht.symm,
        compare_cones_of_factorization g b i hb,
        compare_cones_of_factorization h t (HasFunctorialCofiber.cofibι b) ht.symm⟩

    have tensor_rank_one
        {A V : Type} [AddCommGroup A] [AddCommGroup V]
        [Module (ZMod 2) A] [Module (ZMod 2) V]
        (q : V ≃ₗ[ZMod 2] ZMod 2) (z : A ⊗[ZMod 2] V) :
        ∃ a : A, z = a ⊗ₜ[ZMod 2] q.symm 1 := by
      let e : A ⊗[ZMod 2] V ≃ₗ[ZMod 2] A :=
        (TensorProduct.congr (LinearEquiv.refl (ZMod 2) A) q).trans
          (TensorProduct.rid (ZMod 2) A)
      refine ⟨e z, ?_⟩
      apply e.injective
      change e z = TensorProduct.rid (ZMod 2) A
        (TensorProduct.congr (LinearEquiv.refl (ZMod 2) A) q
          (e z ⊗ₜ[ZMod 2] q.symm 1))
      rw [TensorProduct.congr_tmul]
      simp only [LinearEquiv.refl_apply, LinearEquiv.apply_symm_apply,
        TensorProduct.rid_tmul, one_smul]


    have directSum_supported_decomposition
        (A : ℤ → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module (ZMod 2) (A i)]
        (S : Finset ℤ) (hS : ∀ i, i ∉ S → Subsingleton (A i))
        (z : ⨁ i, A i) :
        z = ∑ i ∈ S, DirectSum.lof (ZMod 2) ℤ A i (z i) := by
      classical
      have hs : z.support ⊆ S := by
        intro i hi
        by_contra his
        exact (DFinsupp.mem_support_iff.mp hi) ((hS i his).elim _ _)
      calc
        z = ∑ i ∈ z.support, DirectSum.lof (ZMod 2) ℤ A i (z i) :=
          (DirectSum.sum_support_of z).symm
        _ = _ := Finset.sum_subset hs (fun i hiS hiz => by
          have hi0 : z i = 0 := by
            simpa only [DFinsupp.mem_support_iff, not_not] using hiz
          rw [hi0, map_zero])

    have tensorCoaction_coassoc {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (hD : Mod2KunnethDiagonalCompatible H R K)
        (X : C) (n : ℤ) (x : mod2HomologyF2 H R n X) :
        cooperationTensorComultiply H R K (fun i => mod2HomologyF2 H R i X) n
          (mod2TensorCoaction H R K X n x) =
          cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X)
            (mod2TensorCoaction H R K X) n (mod2TensorCoaction H R K X n x) := by
      rw [tensorCoaction_apply, ← hD]
      change cooperationTensorMap H R _ (fun i => (K.comparison X i).toLinearMap) n
        (mod2TensorCoaction H R K (H.HF2 ⊗ X) n
          (Mod2Homology.pushforward H (adamsUnit H.unit X) n x)) = _
      rw [tensorCoaction_naturality, ← LinearMap.comp_apply, cooperationTensorMap_comp]
      rfl

    let rowProjection {R : Type} [CommRing R]  (A V : ℤ → Type)
        [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
        [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
        (q : V 0 →ₗ[R] R) (n : ℤ) : gradedTensor R A V n →ₗ[R] A n :=
      DirectSum.toModule R ℤ _ fun k =>
        if h : k = n then by
          subst k
          exact (TensorProduct.rid R (A n)).toLinearMap.comp
            ((q.comp (LinearEquiv.cast (R := R) (M := V) (sub_self n)).toLinearMap).lTensor (A n))
        else 0

    have rowProjection_lof_self {R : Type} [CommRing R] (A : ℤ → Type) (V : ℤ → Type) [(i : ℤ) → AddCommGroup (A i)] [(i : ℤ) → Module R (A i)] [(i : ℤ) → AddCommGroup (V i)] [(i : ℤ) → Module R (V i)] (q : V 0 →ₗ[R] R)  (n : ℤ) (a : A n) (x : V (n-n)) :
        rowProjection A V q n (DirectSum.lof R ℤ _ n (a ⊗ₜ[R] x)) =
          q ((LinearEquiv.cast (R := R) (M := V) (sub_self n)) x) • a := by
      simp [rowProjection]

    have rowProjection_lof_ne {R : Type} [CommRing R] (A : ℤ → Type) (V : ℤ → Type) [(i : ℤ) → AddCommGroup (A i)] [(i : ℤ) → Module R (A i)] [(i : ℤ) → AddCommGroup (V i)] [(i : ℤ) → Module R (V i)] (q : V 0 →ₗ[R] R)  (n k : ℤ) (hkn : k ≠ n) (a : A k) (x : V (n-k)) :
        rowProjection A V q n (DirectSum.lof R ℤ _ k (a ⊗ₜ[R] x)) = 0 := by
      simp [rowProjection, hkn]

    have cast_cast {R : Type} [CommRing R] (V : ℤ → Type) [(i : ℤ) → AddCommGroup (V i)] [(i : ℤ) → Module R (V i)]  (i j k : ℤ) (h : i = j) (h' : j = k) (x : V i) :
        (LinearEquiv.cast (R := R) (M := V) h')
          ((LinearEquiv.cast (R := R) (M := V) h) x) =
        (LinearEquiv.cast (R := R) (M := V) (h.trans h')) x := by
      subst j
      subst k
      rfl


    have rowProjection_assoc {R : Type} [CommRing R] (A : ℤ → Type) (B : ℤ → Type) (V : ℤ → Type) [(i : ℤ) → AddCommGroup (A i)] [(i : ℤ) → Module R (A i)] [(i : ℤ) → AddCommGroup (B i)] [(i : ℤ) → Module R (B i)] [(i : ℤ) → AddCommGroup (V i)] [(i : ℤ) → Module R (V i)] (q : V 0 →ₗ[R] R)  (n : ℤ) :
        (gradedTensorMapRight A (rowProjection B V q) n).comp
            (gradedTensorAssoc A B V n) =
          rowProjection (gradedTensor R A B) V q n := by
      ext k j a b x i
      change (gradedTensorMapRight A (rowProjection B V q) n
        (gradedTensorAssoc A B V n
          (DirectSum.lof R ℤ _ k ((DirectSum.lof R ℤ _ j (a ⊗ₜ[R] b)) ⊗ₜ[R] x)))) i =
        (rowProjection (gradedTensor R A B) V q n
          (DirectSum.lof R ℤ _ k ((DirectSum.lof R ℤ _ j (a ⊗ₜ[R] b)) ⊗ₜ[R] x))) i
      apply congrArg (fun z : gradedTensor R A B n => z i)
      rw [gradedTensorAssoc_lof_tmul]
      simp only [gradedTensorMapRight, DirectSum.lmap_lof, LinearMap.lTensor_tmul]
      by_cases hkn : k = n
      · subst k
        rw [rowProjection_lof_self, rowProjection_lof_self]
        rw [cast_cast]
        simp only [TensorProduct.tmul_smul, map_smul]
      · rw [rowProjection_lof_ne _ _ _ _ _ (by omega), TensorProduct.tmul_zero, map_zero,
          rowProjection_lof_ne _ _ _ _ _ hkn]


    have rowProjection_map {R : Type} [CommRing R] (A : ℤ → Type) (B : ℤ → Type) (V : ℤ → Type) [(i : ℤ) → AddCommGroup (A i)] [(i : ℤ) → Module R (A i)] [(i : ℤ) → AddCommGroup (B i)] [(i : ℤ) → Module R (B i)] [(i : ℤ) → AddCommGroup (V i)] [(i : ℤ) → Module R (V i)] (q : V 0 →ₗ[R] R)  (f : ∀ i, A i →ₗ[R] B i) (n : ℤ) :
        (rowProjection B V q n).comp (gradedTensorMap f V n) =
          (f n).comp (rowProjection A V q n) := by
      ext k a x
      change rowProjection B V q n
        (gradedTensorMap f V n (DirectSum.lof R ℤ _ k (a ⊗ₜ[R] x))) =
          f n (rowProjection A V q n (DirectSum.lof R ℤ _ k (a ⊗ₜ[R] x)))
      rw [gradedTensorMap_lof_tmul]
      by_cases hkn : k = n
      · subst k
        rw [rowProjection_lof_self, rowProjection_lof_self, map_smul]
      · rw [rowProjection_lof_ne _ _ _ _ _ hkn, rowProjection_lof_ne _ _ _ _ _ hkn,
          map_zero]

    let actualRow {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (X : C) (q : mod2HomologyF2 H R 0 X →ₗ[ZMod 2] ZMod 2) (n : ℤ) :
        mod2HomologyF2 H R n X →ₗ[ZMod 2] mod2HomologyF2 H R n H.HF2 :=
      (rowProjection (fun i => mod2HomologyF2 H R i H.HF2) (fun i => mod2HomologyF2 H R i X) q n).comp
        (mod2TensorCoaction H R K X n)

    have row_comultiply {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (q : V 0 →ₗ[ZMod 2] ZMod 2) (n : ℤ) (z : cooperationTensor H R V n) :
        cooperationTensorMap H R (cooperationTensor H R V)
          (rowProjection (fun i => mod2HomologyF2 H R i H.HF2) V q) n
          (cooperationTensorComultiply H R K V n z) =
        cooperationTensorDiagonal H R K n (rowProjection (fun i => mod2HomologyF2 H R i H.HF2) V q n z) := by
      change (gradedTensorMapRight (fun i => mod2HomologyF2 H R i H.HF2) (rowProjection (fun i => mod2HomologyF2 H R i H.HF2) V q) n)
        (gradedTensorAssoc (fun i => mod2HomologyF2 H R i H.HF2) (fun i => mod2HomologyF2 H R i H.HF2) V n
          (gradedTensorMap (cooperationTensorDiagonal H R K) V n z)) = _
      rw [← LinearMap.comp_apply, rowProjection_assoc]
      exact LinearMap.congr_fun
        (rowProjection_map (fun i => mod2HomologyF2 H R i H.HF2)
          (gradedTensor (ZMod 2) (fun i => mod2HomologyF2 H R i H.HF2)
            (fun i => mod2HomologyF2 H R i H.HF2)) V q
          (cooperationTensorDiagonal H R K) n) z


    have actualRow_coaction {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (hD : Mod2KunnethDiagonalCompatible H R K)
        (X : C) (q : mod2HomologyF2 H R 0 X →ₗ[ZMod 2] ZMod 2)
        (n : ℤ) (x : mod2HomologyF2 H R n X) :
        cooperationTensorDiagonal H R K n (actualRow H R K X q n x) =
          cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X)
            (actualRow H R K X q) n (mod2TensorCoaction H R K X n x) := by
      have h := congrArg
        (cooperationTensorMap H R (cooperationTensor H R (fun i => mod2HomologyF2 H R i X))
          (rowProjection (fun i => mod2HomologyF2 H R i H.HF2) (fun i => mod2HomologyF2 H R i X) q) n)
        (tensorCoaction_coassoc H R K hD X n x)
      rw [row_comultiply] at h
      have hc := LinearMap.congr_fun
        (cooperationTensorMap_comp H R (fun i => mod2HomologyF2 H R i X)
          (mod2TensorCoaction H R K X)
          (rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
            (fun i => mod2HomologyF2 H R i X) q) n)
        (mod2TensorCoaction H R K X n x)
      exact h.trans hc

    have zeroTensor_unit_factor {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
        (z : mod2HomologyF2 H R 0 H.HF2 ⊗[ZMod 2] V) :
        letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
          fun i => mod2HomologyModule H R i H.HF2
        ∃ w : V, z = (cooperationUnit H : mod2HomologyF2 H R 0 H.HF2) ⊗ₜ[ZMod 2] w := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      let q := cooperationZeroEquiv H R B
      have hq : q.symm 1 = cooperationUnit H := by
        apply q.injective
        rw [q.apply_symm_apply]
        exact (cooperationZeroEquiv_unit H R B).symm
      obtain ⟨w, hw⟩ := tensor_rank_one q
        (TensorProduct.comm (ZMod 2) (mod2HomologyF2 H R 0 H.HF2) V z)
      refine ⟨w, ?_⟩
      apply (TensorProduct.comm (ZMod 2) (mod2HomologyF2 H R 0 H.HF2) V).injective
      rw [hw, hq, TensorProduct.comm_tmul]


    have negative_cooperation_subsingleton {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  (n : ℤ) (hn : n < 0) :
        Subsingleton (mod2HomologyF2 H R n H.HF2) := by
      letI := mod2HomologyModule H R n H.HF2
      letI := mod2HF2HomotopyModule H R n
      letI := H.homotopy_vanishes n (ne_of_lt hn)
      letI : IsEmpty (PositiveMonomial n) :=
        ⟨fun d => (not_lt_of_ge (le_of_lt hn)) (positiveMonomial_degree_pos d)⟩
      have hs : Subsingleton (LinearMap.ker (cooperationCounitF2 H R n)) :=
        (B.basis n).repr.injective.subsingleton
      have hz (a : mod2HomologyF2 H R n H.HF2) : a = 0 := by
        have ha : cooperationCounitF2 H R n a = 0 := Subsingleton.elim _ _
        exact congrArg Subtype.val (hs.elim (⟨a, ha⟩ : LinearMap.ker (cooperationCounitF2 H R n)) 0)
      exact ⟨fun a b => (hz a).trans (hz b).symm⟩

    have fourCell_coaction_expansion {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  (K : Mod2CooperationKunneth H R)
        (X : C)
        (hX : ∀ i, i ≠ 0 → i ≠ 1 → i ≠ 3 → i ≠ 4 → Subsingleton (Mod2Homology H i X))
        (q0 : mod2HomologyF2 H R 0 X ≃ₗ[ZMod 2] ZMod 2)
        (q1 : mod2HomologyF2 H R 1 X ≃ₗ[ZMod 2] ZMod 2)
        (q3 : mod2HomologyF2 H R 3 X ≃ₗ[ZMod 2] ZMod 2)
        (e4 : mod2HomologyF2 H R 4 X) :
        ∃ (c1 : mod2HomologyF2 H R 1 H.HF2) (c3 : mod2HomologyF2 H R 3 H.HF2)
          (c4 : mod2HomologyF2 H R 4 H.HF2),
          mod2TensorCoaction H R K X 4 e4 =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 4 e4 +
            DirectSum.lof (ZMod 2) ℤ _ 1 (c1 ⊗ₜ[ZMod 2] q3.symm 1) +
            DirectSum.lof (ZMod 2) ℤ _ 3 (c3 ⊗ₜ[ZMod 2] q1.symm 1) +
            DirectSum.lof (ZMod 2) ℤ _ 4 (c4 ⊗ₜ[ZMod 2] q0.symm 1) := by
      classical
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      let z := mod2TensorCoaction H R K X 4 e4
      obtain ⟨w, hw⟩ := zeroTensor_unit_factor H R B (z 0)
      obtain ⟨c1, hc1⟩ := tensor_rank_one q3 (z 1)
      obtain ⟨c3, hc3⟩ := tensor_rank_one q1 (z 3)
      obtain ⟨c4, hc4⟩ := tensor_rank_one q0 (z 4)
      have hd := directSum_supported_decomposition
        (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (4-i) X)
        {0, 1, 3, 4} (fun i hi => by
          have his : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 3 ∧ i ≠ 4 := by simpa using hi
          letI : Subsingleton (mod2HomologyF2 H R (4-i) X) := hX (4-i) (by omega) (by omega) (by omega) (by omega)
          infer_instance) z
      simp only [Finset.sum_insert (show (0 : ℤ) ∉ {1, 3, 4} by decide),
        Finset.sum_insert (show (1 : ℤ) ∉ {3, 4} by decide),
        Finset.sum_insert (show (3 : ℤ) ∉ {4} by decide), Finset.sum_singleton] at hd
      rw [hw, hc1, hc3, hc4] at hd
      have he := congrArg (cooperationTensorAugmentation H R
        (fun i => mod2HomologyF2 H R i X) 4) hd
      rw [map_add, map_add, map_add,
        positiveTensor_augmentation_zero H R _ 4 1 (by decide),
        positiveTensor_augmentation_zero H R _ 4 3 (by decide),
        positiveTensor_augmentation_zero H R _ 4 4 (by decide), add_zero, add_zero, add_zero] at he
      change cooperationTensorAugmentation H R _ 4 z =
        cooperationTensorAugmentation H R _ 4
          (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 4 w) at he
      rw [cooperationTensorUnit_augmentation] at he
      have he4 : e4 = w := by
        rw [← he]
        exact (tensorCoaction_counit H R K X 4 e4).symm
      refine ⟨c1, c3, c4, ?_⟩
      have hu : cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 4 e4 =
          DirectSum.lof (ZMod 2) ℤ _ 0 (cooperationUnit H ⊗ₜ[ZMod 2] e4) := rfl
      rw [hu]
      simpa only [← he4, add_assoc] using hd

    let tensorTerm {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (n k : ℤ) (a : mod2HomologyF2 H R k H.HF2) (x : V (n-k)) :
        cooperationTensor H R V n :=
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x)

    have tensorMap_term {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V W : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 2) (W i)]
        (f : ∀ i, V i →ₗ[ZMod 2] W i) (n k : ℤ)
        (a : mod2HomologyF2 H R k H.HF2) (x : V (n-k)) :
        cooperationTensorMap H R V f n (tensorTerm H R V n k a x) =
          tensorTerm H R W n k a (f (n-k) x) := by
      simp [tensorTerm, cooperationTensorMap, gradedTensorMapRight]

    have rowProjection_term_self {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (q : V 0 →ₗ[ZMod 2] ZMod 2) (n : ℤ)
        (a : mod2HomologyF2 H R n H.HF2) (x : V (n-n)) :
        rowProjection (fun i => mod2HomologyF2 H R i H.HF2) V q n
          (tensorTerm H R V n n a x) =
          q ((LinearEquiv.cast (R := ZMod 2) (M := V) (sub_self n)) x) • a :=
      rowProjection_lof_self (fun i => mod2HomologyF2 H R i H.HF2) V q n a x

    have rowProjection_term_ne {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (q : V 0 →ₗ[ZMod 2] ZMod 2) (n k : ℤ) (hkn : k ≠ n)
        (a : mod2HomologyF2 H R k H.HF2) (x : V (n-k)) :
        rowProjection (fun i => mod2HomologyF2 H R i H.HF2) V q n
          (tensorTerm H R V n k a x) = 0 :=
      rowProjection_lof_ne (fun i => mod2HomologyF2 H R i H.HF2) V q n k hkn a x

    have rowProjection_unit_pos {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (q : V 0 →ₗ[ZMod 2] ZMod 2) (n : ℤ) (hn : n ≠ 0) (x : V n) :
        rowProjection (fun i => mod2HomologyF2 H R i H.HF2) V q n
          (cooperationTensorUnit H R V n x) = 0 :=
      rowProjection_lof_ne (fun i => mod2HomologyF2 H R i H.HF2) V q n 0 (Ne.symm hn) _ _


    have threeCell_matrix_023 {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (hD : Mod2KunnethDiagonalCompatible H R K)
        (X : C) (q : mod2HomologyF2 H R 0 X →ₗ[ZMod 2] ZMod 2)
        (e0 : mod2HomologyF2 H R 0 X) (hq : q e0 = 1)
        (e2 : mod2HomologyF2 H R 2 X) (e4 : mod2HomologyF2 H R 3 X)
        (u : mod2HomologyF2 H R 2 H.HF2) (x1 : mod2HomologyF2 H R 1 H.HF2)
        (a : mod2HomologyF2 H R 3 H.HF2)
        (h0 : mod2TensorCoaction H R K X 0 e0 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 0 e0)
        (h2 : mod2TensorCoaction H R K X 2 e2 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 2 e2 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 2 2 u e0)
        (h4 : mod2TensorCoaction H R K X 3 e4 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 e4 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 3 1 x1 e2 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 3 3 a e0) :
        cooperationTensorDiagonal H R K 3 a =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3 a +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 1 x1 u +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a (cooperationUnit H) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      have hr0 : actualRow H R K X q 0 e0 = cooperationUnit H := by
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 0 (mod2TensorCoaction H R K X 0 e0) = _
        rw [h0]
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 0
          (tensorTerm H R (fun i => mod2HomologyF2 H R i X) 0 0 (cooperationUnit H) e0) = _
        have hp := rowProjection_term_self H R (fun j => mod2HomologyF2 H R j X) q 0 (cooperationUnit H) e0
        change _ = q e0 • cooperationUnit H at hp
        exact hp.trans (by rw [hq, one_smul])
      have hr2 : actualRow H R K X q 2 e2 = u := by
        have hu := rowProjection_unit_pos H R (fun i => mod2HomologyF2 H R i X) q 2 (by decide) e2
        have hp := rowProjection_term_self H R (fun i => mod2HomologyF2 H R i X) q 2 u e0
        change _ = q e0 • u at hp
        rw [hq, one_smul] at hp
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2) (fun i => mod2HomologyF2 H R i X) q 2 (mod2TensorCoaction H R K X 2 e2) = _
        rw [h2, map_add]
        exact (congrArg₂ (· + ·) hu hp).trans (zero_add u)
      have hr3 : actualRow H R K X q 3 e4 = a := by
        have hu := rowProjection_unit_pos H R (fun i => mod2HomologyF2 H R i X) q 3 (by decide) e4
        have hm0 := rowProjection_term_ne H R (fun i => mod2HomologyF2 H R i X) q 3 1 (by decide) x1 e2
        have ht := rowProjection_term_self H R (fun i => mod2HomologyF2 H R i X) q 3 a e0
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 3
          (tensorTerm H R (fun i => mod2HomologyF2 H R i X) 3 3 a e0) = q e0 • a at ht
        rw [hq, one_smul] at ht
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 3 (mod2TensorCoaction H R K X 3 e4) = _
        rw [h4, map_add, map_add]
        exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu hm0) ht).trans (by simp only [zero_add])
      have hmap : cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 3
          (mod2TensorCoaction H R K X 3 e4) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3 a +
            tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 1 x1 u +
            tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a (cooperationUnit H) := by
        have hu := tensorUnit_naturality H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 3 e4
        have hu' := hu.trans (congrArg (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3) hr3)
        have hm0 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 3 1 x1 e2
        change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 1 x1 (actualRow H R K X q 2 e2) at hm0
        have hm0' := hm0.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 1 x1) hr2)
        have hm1 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 3 3 a e0
        change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a (actualRow H R K X q 0 e0) at hm1
        have hm1' := hm1.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a) hr0)
        rw [h4, map_add, map_add]
        exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu' hm0') hm1')
      have h := actualRow_coaction H R K hD X q 3 e4
      rw [hr3] at h
      exact h.trans hmap


    have toda_homology_geometry {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)
        (η : Sphere (C := C) 1 ⟶ SphereSpectrum)
        (hToda : Toda.Relation (0 : (Sphere (C := C) 1)⟦(1 : ℤ)⟧ ⟶ SphereSpectrum)
          (2 • 𝟙 (Sphere (C := C) 1)) η (2 • 𝟙 SphereSpectrum)) :
        ∃ (Q : C) (i : Sphere (C := C) 1 ⟶ Q)
          (p : Q ⟶ (Sphere (C := C) 1)⟦(1 : ℤ)⟧)
          (_ : Triangle.mk (2 • 𝟙 (Sphere (C := C) 1)) i p ∈ distTriang C)
          (b : Q ⟶ SphereSpectrum) (t : HasFunctorialCofiber.cofib b ⟶ SphereSpectrum),
          i ≫ b = η ∧ b ≫ (2 • 𝟙 SphereSpectrum) = 0 ∧
          HasFunctorialCofiber.cofibι b ≫ t = 2 • 𝟙 SphereSpectrum ∧
          (∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Mod2Homology H n Q)) ∧
          (∀ n, Mod2Homology.pushforward H b n = 0) ∧
          (∀ n, n ≠ 0 → n ≠ 2 → n ≠ 3 →
            Subsingleton (Mod2Homology H n (HasFunctorialCofiber.cofib b))) ∧
          (∀ n, Mod2Homology.pushforward H t n = 0) ∧
          (∀ n, n ≠ 0 → n ≠ 1 → n ≠ 3 → n ≠ 4 →
            Subsingleton (Mod2Homology H n (HasFunctorialCofiber.cofib t))) := by
      obtain ⟨Q, i, p, hT, b, t, hib, hb2, ht, hcompareη, hcompare2⟩ :=
        triple_cone_geometry (2 • 𝟙 (Sphere (C := C) 1)) η
          (2 • 𝟙 SphereSpectrum) hToda
      let TQ : HoCofiberSequence (C := C) :=
        ⟨Sphere 1, Sphere 1, Q, 2 • 𝟙 _, i, p, hT⟩
      have hQ (n : ℤ) (hn1 : n ≠ 1) (hn2 : n ≠ 2) :
          Subsingleton (Mod2Homology H n Q) :=
        homology_middle_subsingleton H TQ n
          (sphereHomologyShiftSubsingleton H n 1 hn1)
          (sphereHomologyShiftSubsingleton H (n-1) 1 (by omega))
      have hbzero (n : ℤ) : Mod2Homology.pushforward H b n = 0 := by
        apply pushforward_zero_of_disjoint_support H b n
        by_cases hn : n = 0
        · subst n
          exact Or.inl (hQ 0 (by decide) (by decide))
        · exact Or.inr (sphereHomologySubsingleton H n hn)
      let TX := HoCofiberSequence.ofMorphism b
      have hX (n : ℤ) (hn0 : n ≠ 0) (hn2 : n ≠ 2) (hn3 : n ≠ 3) :
          Subsingleton (Mod2Homology H n (HasFunctorialCofiber.cofib b)) :=
        homology_middle_subsingleton H TX n (sphereHomologySubsingleton H n hn0)
          (hQ (n-1) (by omega) (by omega))
      have htzero (n : ℤ) : Mod2Homology.pushforward H t n = 0 := by
        by_cases hn : n = 0
        · subst n
          exact pushforward_zero_of_surjective_precomposition H
            (HasFunctorialCofiber.cofibι b) t 0
            (bottomEquiv_of_homology_zero H R TX 0 (hbzero 0)
              (by exact hQ (-1) (by decide) (by decide))).surjective
            (by
              rw [ht]
              exact twice_map_zero H R (𝟙 SphereSpectrum) 0)
        · exact pushforward_zero_of_disjoint_support H t n
            (Or.inr (sphereHomologySubsingleton H n hn))
      let TE := HoCofiberSequence.ofMorphism t
      have hE (n : ℤ) (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hn3 : n ≠ 3) (hn4 : n ≠ 4) :
          Subsingleton (Mod2Homology H n (HasFunctorialCofiber.cofib t)) :=
        homology_middle_subsingleton H TE n (sphereHomologySubsingleton H n hn0)
          (hX (n-1) (by omega) (by omega) (by omega))
      exact ⟨Q, i, p, hT, b, t, hib, hb2, ht, hQ, hbzero, hX, htzero, hE⟩

    have threeCell_023_coaction_expansion {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  (K : Mod2CooperationKunneth H R)
        (X : C)
        (hX : ∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → Subsingleton (Mod2Homology H i X))
        (q0 : mod2HomologyF2 H R 0 X ≃ₗ[ZMod 2] ZMod 2)
        (q2 : mod2HomologyF2 H R 2 X ≃ₗ[ZMod 2] ZMod 2)
        (e4 : mod2HomologyF2 H R 3 X) :
        ∃ (c2 : mod2HomologyF2 H R 1 H.HF2) (c4 : mod2HomologyF2 H R 3 H.HF2),
          mod2TensorCoaction H R K X 3 e4 =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 e4 +
            DirectSum.lof (ZMod 2) ℤ _ 1 (c2 ⊗ₜ[ZMod 2] q2.symm 1) +
            DirectSum.lof (ZMod 2) ℤ _ 3 (c4 ⊗ₜ[ZMod 2] q0.symm 1) := by
      classical
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      let z := mod2TensorCoaction H R K X 3 e4
      obtain ⟨w, hw⟩ := zeroTensor_unit_factor H R B (z 0)
      obtain ⟨c2, hc2⟩ := tensor_rank_one q2 (z 1)
      obtain ⟨c4, hc4⟩ := tensor_rank_one q0 (z 3)
      have hd := directSum_supported_decomposition
        (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (3-i) X)
        {0, 1, 3} (fun i hi => by
          letI : Subsingleton (mod2HomologyF2 H R (3-i) X) := hX (3-i) (by simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega)
            (by simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega)
            (by simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega)
          infer_instance) z
      simp only [Finset.sum_insert (show (0 : ℤ) ∉ {1, 3} by decide),
        Finset.sum_insert (show (1 : ℤ) ∉ {3} by decide), Finset.sum_singleton] at hd
      rw [hw, hc2, hc4] at hd
      have he := congrArg (cooperationTensorAugmentation H R
        (fun i => mod2HomologyF2 H R i X) 3) hd
      change cooperationTensorAugmentation H R _ 3 z = _ at he
      rw [map_add, map_add,
        positiveTensor_augmentation_zero H R _ 3 1 (by decide),
        positiveTensor_augmentation_zero H R _ 3 3 (by decide), add_zero, add_zero] at he
      change cooperationTensorAugmentation H R _ 3 z =
        cooperationTensorAugmentation H R _ 3
          (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 w) at he
      rw [cooperationTensorUnit_augmentation] at he
      have he4 : e4 = w := by
        rw [← he]
        exact (tensorCoaction_counit H R K X 3 e4).symm
      refine ⟨c2, c4, ?_⟩
      have hu : cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 e4 =
          DirectSum.lof (ZMod 2) ℤ _ 0 (cooperationUnit H ⊗ₜ[ZMod 2] e4) := rfl
      rw [hu]
      simpa only [← he4, add_assoc] using hd

    have coaction_of_unit_image {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (hU : Mod2KunnethUnitCompatible H R K)
        (X : C) (n : ℤ) (a : HomotopyGroup n X) :
        mod2TensorCoaction H R K X n (a ≫ adamsUnit H.unit X) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) n
            (a ≫ adamsUnit H.unit X) := by
      rw [tensorCoaction_apply]
      have hu : mod2CoactionMap H X n (a ≫ adamsUnit H.unit X) =
          mod2OuterUnitMap H X n (a ≫ adamsUnit H.unit X) := by
        change (a ≫ adamsUnit H.unit X) ≫ H.HF2 ◁ adamsUnit H.unit X =
          (a ≫ adamsUnit H.unit X) ≫ adamsUnit H.unit (H.HF2 ⊗ X)
        rw [Category.assoc, mod2AdamsUnit_naturality, Category.assoc]
      rw [hu, hU]

    have transfer_unit {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  {X Y : C} (f : X ⟶ Y) (n : ℤ)
        (x : mod2HomologyF2 H R n X)
        (hx : mod2TensorCoaction H R K X n x =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) n x) :
        mod2TensorCoaction H R K Y n (Mod2Homology.pushforward H f n x) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i Y) n
            (Mod2Homology.pushforward H f n x) := by
      have hn := tensorCoaction_naturality H R K f n x
      have hu := tensorUnit_naturality H R (fun i => mod2HomologyF2 H R i X) (fun i => (mod2HomologyF2Map H R f i).hom) n x
      have hm := congrArg (cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X) (fun i => (mod2HomologyF2Map H R f i).hom) n) hx
      exact hn.trans (hm.trans hu)

    have transfer_twoTerm {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  {X Y : C} (f : X ⟶ Y) (n k : ℤ)
        (x : mod2HomologyF2 H R n X) (a : mod2HomologyF2 H R k H.HF2)
        (y : mod2HomologyF2 H R (n-k) X)
        (hx : mod2TensorCoaction H R K X n x =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) n x +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) n k a y) :
        mod2TensorCoaction H R K Y n (Mod2Homology.pushforward H f n x) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i Y) n
            (Mod2Homology.pushforward H f n x) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i Y) n k a
            (Mod2Homology.pushforward H f (n-k) y) := by
      have hn := tensorCoaction_naturality H R K f n x
      have hu := tensorUnit_naturality H R (fun i => mod2HomologyF2 H R i X) (fun i => (mod2HomologyF2Map H R f i).hom) n x
      have ht := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i Y) (fun i => (mod2HomologyF2Map H R f i).hom) n k a y
      have hm := congrArg (cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X) (fun i => (mod2HomologyF2Map H R f i).hom) n) hx
      rw [map_add] at hm
      exact hn.trans (hm.trans (congrArg₂ (· + ·) hu ht))

    have tensorLowerMap_unit {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V W : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 2) (W i)]
        (g : ∀ i, V i →ₗ[ZMod 2] W (i-1)) (n : ℤ) (x : V n) :
        cooperationTensorLowerMap H R V W g n (cooperationTensorUnit H R V n x) =
          cooperationTensorUnit H R W (n-1) (g n x) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      have hc (i j : ℤ) (h : i = j) (z : V i) :
          g j ((LinearEquiv.cast (R := ZMod 2) (M := V) h) z) =
            (LinearEquiv.cast (R := ZMod 2) (M := W) (congrArg (fun k => k - 1) h))
              (g i z) := by subst j; rfl
      have ht (i j k : ℤ) (h : i = j) (h' : j = k) (h'' : i = k) (z : W i) :
          (LinearEquiv.cast (R := ZMod 2) (M := W) h')
            ((LinearEquiv.cast (R := ZMod 2) (M := W) h) z) =
          (LinearEquiv.cast (R := ZMod 2) (M := W) h'') z := by subst j; subst k; rfl
      simp only [cooperationTensorUnit_apply, cooperationTensorLowerMap,
        gradedTensorLowerMap_lof_tmul]
      rw [hc, ht]

    have tensorLowerMap_term {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V W : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 2) (W i)]
        (g : ∀ i, V i →ₗ[ZMod 2] W (i-1)) (n k : ℤ)
        (a : mod2HomologyF2 H R k H.HF2) (x : V (n-k)) :
        cooperationTensorLowerMap H R V W g n (tensorTerm H R V n k a x) =
          tensorTerm H R W (n-1) k a
            ((LinearEquiv.cast (R := ZMod 2) (M := W)
              (show n-k-1=n-1-k by omega)) (g (n-k) x)) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      exact gradedTensorLowerMap_lof_tmul (Mod2Cooperations H) g n k a x

    have fourCell_bottom_matrix {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (hD : Mod2KunnethDiagonalCompatible H R K)
        (X : C) (q : mod2HomologyF2 H R 0 X →ₗ[ZMod 2] ZMod 2)
        (e0 : mod2HomologyF2 H R 0 X) (hq : q e0 = 1)
        (e1 : mod2HomologyF2 H R 1 X) (e3 : mod2HomologyF2 H R 3 X)
        (e4 : mod2HomologyF2 H R 4 X)
        (x : mod2HomologyF2 H R 1 H.HF2) (u : mod2HomologyF2 H R 2 H.HF2)
        (a b : mod2HomologyF2 H R 3 H.HF2) (c : mod2HomologyF2 H R 4 H.HF2)
        (h0 : mod2TensorCoaction H R K X 0 e0 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 0 e0)
        (h1 : mod2TensorCoaction H R K X 1 e1 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 1 e1 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 1 1 x e0)
        (h3 : mod2TensorCoaction H R K X 3 e3 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 e3 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 3 2 u e1 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 3 3 a e0)
        (h4 : mod2TensorCoaction H R K X 4 e4 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 4 e4 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 4 1 x e3 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 4 3 b e1 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 4 4 c e0) :
        (cooperationTensorDiagonal H R K 3 a =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3 a +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 2 u x +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a (cooperationUnit H)) ∧
        (cooperationTensorDiagonal H R K 4 c =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 4 c +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 1 x a +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 3 b x +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 4 c (cooperationUnit H)) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      have hr0 : actualRow H R K X q 0 e0 = cooperationUnit H := by
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 0 (mod2TensorCoaction H R K X 0 e0) = _
        rw [h0]
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 0
          (tensorTerm H R (fun i => mod2HomologyF2 H R i X) 0 0 (cooperationUnit H) e0) = _
        have hp := rowProjection_term_self H R (fun j => mod2HomologyF2 H R j X) q 0 (cooperationUnit H) e0
        change _ = q e0 • cooperationUnit H at hp
        exact hp.trans (by rw [hq, one_smul])
      have hr1 : actualRow H R K X q 1 e1 = x := by
        have hu := rowProjection_unit_pos H R (fun i => mod2HomologyF2 H R i X) q 1 (by decide) e1
        have hp := rowProjection_term_self H R (fun i => mod2HomologyF2 H R i X) q 1 x e0
        change _ = q e0 • x at hp
        rw [hq, one_smul] at hp
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2) (fun i => mod2HomologyF2 H R i X) q 1 (mod2TensorCoaction H R K X 1 e1) = _
        rw [h1, map_add]
        exact (congrArg₂ (· + ·) hu hp).trans (zero_add x)
      have hr3 : actualRow H R K X q 3 e3 = a := by
        have hu := rowProjection_unit_pos H R (fun i => mod2HomologyF2 H R i X) q 3 (by decide) e3
        have hm0 := rowProjection_term_ne H R (fun i => mod2HomologyF2 H R i X) q 3 2 (by decide) u e1
        have ht := rowProjection_term_self H R (fun i => mod2HomologyF2 H R i X) q 3 a e0
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 3
          (tensorTerm H R (fun i => mod2HomologyF2 H R i X) 3 3 a e0) = q e0 • a at ht
        rw [hq, one_smul] at ht
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 3 (mod2TensorCoaction H R K X 3 e3) = _
        rw [h3, map_add, map_add]
        exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu hm0) ht).trans (by simp only [zero_add])
      have hr4 : actualRow H R K X q 4 e4 = c := by
        have hu := rowProjection_unit_pos H R (fun i => mod2HomologyF2 H R i X) q 4 (by decide) e4
        have hm0 := rowProjection_term_ne H R (fun i => mod2HomologyF2 H R i X) q 4 1 (by decide) x e3
        have hm1 := rowProjection_term_ne H R (fun i => mod2HomologyF2 H R i X) q 4 3 (by decide) b e1
        have ht := rowProjection_term_self H R (fun i => mod2HomologyF2 H R i X) q 4 c e0
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 4
          (tensorTerm H R (fun i => mod2HomologyF2 H R i X) 4 4 c e0) = q e0 • c at ht
        rw [hq, one_smul] at ht
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 4 (mod2TensorCoaction H R K X 4 e4) = _
        rw [h4, map_add, map_add, map_add]
        exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu hm0) hm1) ht).trans (by simp only [zero_add])
      constructor
      · have hmap : cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 3
            (mod2TensorCoaction H R K X 3 e3) =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3 a +
              tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 2 u x +
              tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a (cooperationUnit H) := by
          have hu := tensorUnit_naturality H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 3 e3
          have hu' := hu.trans (congrArg (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3) hr3)
          have hm0 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 3 2 u e1
          change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 2 u (actualRow H R K X q 1 e1) at hm0
          have hm0' := hm0.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 2 u) hr1)
          have hm1 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 3 3 a e0
          change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a (actualRow H R K X q 0 e0) at hm1
          have hm1' := hm1.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a) hr0)
          rw [h3, map_add, map_add]
          exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu' hm0') hm1')
        have h := actualRow_coaction H R K hD X q 3 e3
        rw [hr3] at h
        exact h.trans hmap
      · have hmap : cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 4
            (mod2TensorCoaction H R K X 4 e4) =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 4 c +
              tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 1 x a +
              tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 3 b x +
              tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 4 c (cooperationUnit H) := by
          have hu := tensorUnit_naturality H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 4 e4
          have hu' := hu.trans (congrArg (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 4) hr4)
          have hm0 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 4 1 x e3
          change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 1 x (actualRow H R K X q 3 e3) at hm0
          have hm0' := hm0.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 1 x) hr3)
          have hm1 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 4 3 b e1
          change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 3 b (actualRow H R K X q 1 e1) at hm1
          have hm1' := hm1.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 3 b) hr1)
          have hm2 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 4 4 c e0
          change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 4 c (actualRow H R K X q 0 e0) at hm2
          have hm2' := hm2.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 4 c) hr0)
          rw [h4, map_add, map_add, map_add]
          exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu' hm0') hm1') hm2')
        have h := actualRow_coaction H R K hD X q 4 e4
        rw [hr4] at h
        exact h.trans hmap


    have tensorTerm_coefficient_injective {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
        (V : ℤ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (n k : ℤ) (x : V (n-k)) (q : V (n-k) →ₗ[ZMod 2] ZMod 2) (hq : q x = 1) :
        Function.Injective (fun a : mod2HomologyF2 H R k H.HF2 => tensorTerm H R V n k a x) := by
      intro a b h
      apply pureTensorCoefficient_injective x q hq
      have hh := congrArg (fun z : cooperationTensor H R V n => z k) h
      simpa only [tensorTerm, DirectSum.lof_apply] using hh

    have tensorTerm_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (n k : ℤ) (a : mod2HomologyF2 H R k H.HF2) :
        tensorTerm H R V n k a 0 = 0 := by
      simp only [tensorTerm, TensorProduct.tmul_zero, map_zero]

    have tensorTerm_component_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (n i k : ℤ) (hik : i ≠ k) (a : mod2HomologyF2 H R k H.HF2) (x : V (n-k)) :
        (tensorTerm H R V n k a x) i = 0 := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      exact DirectSum.of_eq_of_ne
        (β := fun j => Mod2Cooperations H j ⊗[ZMod 2] V (n-j)) k i (a ⊗ₜ[ZMod 2] x) hik


    have tensorTerms_two_unique {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (n i j : ℤ) (hij : i ≠ j)
        (xi : V (n-i)) (qi : V (n-i) →ₗ[ZMod 2] ZMod 2) (hqi : qi xi = 1)
        (xj : V (n-j)) (qj : V (n-j) →ₗ[ZMod 2] ZMod 2) (hqj : qj xj = 1)
        (ai bi : mod2HomologyF2 H R i H.HF2)
        (aj bj : mod2HomologyF2 H R j H.HF2)
        (h : tensorTerm H R V n i ai xi + tensorTerm H R V n j aj xj =
          tensorTerm H R V n i bi xi + tensorTerm H R V n j bj xj) : ai = bi ∧ aj = bj := by
      constructor
      · apply pureTensorCoefficient_injective xi qi hqi
        have hh := congrArg (fun z : cooperationTensor H R V n => z i) h
        change (tensorTerm H R V n i ai xi) i + (tensorTerm H R V n j aj xj) i =
          (tensorTerm H R V n i bi xi) i + (tensorTerm H R V n j bj xj) i at hh
        rw [tensorTerm_component_zero H R V n i j hij,
          tensorTerm_component_zero H R V n i j hij, add_zero, add_zero] at hh
        simpa only [tensorTerm, DirectSum.lof_apply] using hh
      · apply pureTensorCoefficient_injective xj qj hqj
        have hh := congrArg (fun z : cooperationTensor H R V n => z j) h
        change (tensorTerm H R V n i ai xi) j + (tensorTerm H R V n j aj xj) j =
          (tensorTerm H R V n i bi xi) j + (tensorTerm H R V n j bj xj) j at hh
        rw [tensorTerm_component_zero H R V n j i (Ne.symm hij),
          tensorTerm_component_zero H R V n j i (Ne.symm hij), zero_add, zero_add] at hh
        simpa only [tensorTerm, DirectSum.lof_apply] using hh

    have homologyBoundary_naturality {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T U : HoCofiberSequence (C := C))
        (a : T.X ⟶ U.X) (c : T.Z ⟶ U.Z)
        (hδ : T.h ≫ (shiftFunctor C (1 : ℤ)).map a = c ≫ U.h)
        (n : ℤ) (x : Mod2Homology H n T.Z) :
        mod2HomologyConnecting H U n (Mod2Homology.pushforward H c n x) =
          Mod2Homology.pushforward H a (n-1)
            (mod2HomologyConnecting H T n x) := by
      have hlast : (H.HF2 ◁ c) ≫ (U.map (tensorLeft H.HF2)).h =
          (T.map (tensorLeft H.HF2)).h ≫ (H.HF2 ◁ a)⟦(1 : ℤ)⟧' := by
        change (H.HF2 ◁ c) ≫ (H.HF2 ◁ U.h) ≫ _ =
          ((H.HF2 ◁ T.h) ≫ _) ≫ _
        rw [← Category.assoc, ← whiskerLeft_comp, ← hδ, whiskerLeft_comp, Category.assoc]
        have hn := ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.naturality a
        change (H.HF2 ◁ (shiftFunctor C (1 : ℤ)).map a) ≫
            ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app U.X =
          ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app T.X ≫
            (shiftFunctor C (1 : ℤ)).map (H.HF2 ◁ a) at hn
        simpa only [Category.assoc] using congrArg (fun f => (H.HF2 ◁ T.h) ≫ f) hn
      exact connectingHomomorphism_naturality (T.map (tensorLeft H.HF2))
        (U.map (tensorLeft H.HF2)) (H.HF2 ◁ a) (H.HF2 ◁ c) hlast n x

    have comparison_nonzero_of_boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T U : HoCofiberSequence (C := C))
        (a : T.X ⟶ U.X) (c : T.Z ⟶ U.Z)
        (hδ : T.h ≫ (shiftFunctor C (1 : ℤ)).map a = c ≫ U.h)
        (n : ℤ) (x : Mod2Homology H n T.Z) (hx : x ≠ 0)
        (hT : Function.Injective (mod2HomologyConnecting H T n))
        (ha : Function.Injective (Mod2Homology.pushforward H a (n-1))) :
        Mod2Homology.pushforward H c n x ≠ 0 := by
      intro hz
      have h := homologyBoundary_naturality H T U a c hδ n x
      rw [hz, map_zero] at h
      apply hx
      apply hT
      apply ha
      simpa only [map_zero] using h.symm


    have coordinate_nonzero_unique   {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
        (q : V ≃ₗ[ZMod 2] ZMod 2) (x : V) (hx : x ≠ 0) : x = q.symm 1 := by
      apply q.injective
      rw [q.apply_symm_apply]
      have htwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      apply (htwo (q x)).resolve_left
      intro h
      apply hx
      apply q.injective
      simpa only [map_zero] using h

    have pushforward_comp_apply {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
        (n : ℤ) (x : Mod2Homology H n X) :
        Mod2Homology.pushforward H g n (Mod2Homology.pushforward H f n x) =
          Mod2Homology.pushforward H (f ≫ g) n x := by
      change (x ≫ H.HF2 ◁ f) ≫ H.HF2 ◁ g = x ≫ H.HF2 ◁ (f ≫ g)
      rw [whiskerLeft_comp, Category.assoc]

    have comparison_bottom_injective {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T U : HoCofiberSequence (C := C))
        (b : T.Y ⟶ U.Y) (c : T.Z ⟶ U.Z) (hmid : T.g ≫ c = b ≫ U.g) (n : ℤ)
        (hT : Function.Surjective (Mod2Homology.pushforward H T.g n))
        (hb : Function.Injective (Mod2Homology.pushforward H b n))
        (hU : Function.Injective (Mod2Homology.pushforward H U.g n)) :
        Function.Injective (Mod2Homology.pushforward H c n) := by
      intro x y h
      obtain ⟨x', rfl⟩ := hT x
      obtain ⟨y', rfl⟩ := hT y
      rw [pushforward_comp_apply, pushforward_comp_apply, hmid,
        ← pushforward_comp_apply, ← pushforward_comp_apply] at h
      exact congrArg (Mod2Homology.pushforward H T.g n) (hb (hU h))


    have comparison_twoCell_transfer {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (K : Mod2CooperationKunneth H R)
        (T U : HoCofiberSequence (C := C))
        (a : T.X ⟶ U.X) (b : T.Y ⟶ U.Y) (c : T.Z ⟶ U.Z)
        (hmid : T.g ≫ c = b ≫ U.g)
        (hlast : T.h ≫ (shiftFunctor C (1 : ℤ)).map a = c ≫ U.h)
        (d : ℤ) (qT0 : mod2HomologyF2 H R 0 T.Z ≃ₗ[ZMod 2] ZMod 2)
        (qTd : mod2HomologyF2 H R d T.Z ≃ₗ[ZMod 2] ZMod 2)
        (qU0 : mod2HomologyF2 H R 0 U.Z ≃ₗ[ZMod 2] ZMod 2)
        (qUd : mod2HomologyF2 H R d U.Z ≃ₗ[ZMod 2] ZMod 2)
        (u : mod2HomologyF2 H R d H.HF2)
        (hTg : Function.Surjective (Mod2Homology.pushforward H T.g 0))
        (hbg : Function.Injective (Mod2Homology.pushforward H b 0))
        (hUg : Function.Injective (Mod2Homology.pushforward H U.g 0))
        (hTd : Function.Injective (mod2HomologyConnecting H T d))
        (had : Function.Injective (Mod2Homology.pushforward H a (d-1)))
        (hψ : mod2TensorCoaction H R K T.Z d (qTd.symm 1) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i T.Z) d (qTd.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i T.Z) d d u
            ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i T.Z)
              (sub_self d).symm) (qT0.symm 1))) :
        mod2TensorCoaction H R K U.Z d (qUd.symm 1) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i U.Z) d (qUd.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i U.Z) d d u
            ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i U.Z)
              (sub_self d).symm) (qU0.symm 1)) := by
      have hn0 : qT0.symm 1 ≠ 0 := by
        intro h
        have hh := congrArg qT0 h
        exact one_ne_zero (by simpa only [qT0.apply_symm_apply, map_zero] using hh)
      have hnd : qTd.symm 1 ≠ 0 := by
        intro h
        have hh := congrArg qTd h
        exact one_ne_zero (by simpa only [qTd.apply_symm_apply, map_zero] using hh)
      have hc0 : Mod2Homology.pushforward H c 0 (qT0.symm 1) = qU0.symm 1 := by
        apply coordinate_nonzero_unique qU0
        intro hz
        apply hn0
        apply comparison_bottom_injective H T U b c hmid 0 hTg hbg hUg
        simpa only [map_zero] using hz
      have hcd : Mod2Homology.pushforward H c d (qTd.symm 1) = qUd.symm 1 :=
        coordinate_nonzero_unique qUd _
          (comparison_nonzero_of_boundary H T U a c hlast d _ hnd hTd had)
      have h := transfer_twoTerm H R K c d d (qTd.symm 1) u
        ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i T.Z)
          (sub_self d).symm) (qT0.symm 1)) hψ
      rw [hcd, homologyPushforward_cast, hc0] at h
      exact h

    have inducedMap_iso_bijective {C : Type 1} [StableHomotopyCategory.{1,0} C]  {X Y : C} (e : X ≅ Y) (n : ℤ) :
        Function.Bijective (inducedMap e.hom n) := by
      constructor
      · intro x y h
        exact (cancel_mono e.hom).mp h
      · intro y
        refine ⟨y ≫ e.inv, ?_⟩
        simp only [inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          Category.assoc, Iso.inv_hom_id, Category.comp_id]

    let desuspendEquiv {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [MonoidalPreadditive C] (R : Mod2RingStructure H)  (X : C) (n : ℤ) :
        mod2HomologyF2 H R n (X⟦(1 : ℤ)⟧) ≃ₗ[ZMod 2] mod2HomologyF2 H R (n - 1) X :=
      LinearEquiv.ofBijective (mod2HomologyDesuspendF2 H R X n)
        ((homotopyDesuspend_bijective (H.HF2 ⊗ X) n).comp
          (inducedMap_iso_bijective (((tensorLeft H.HF2).commShiftIso (1 : ℤ)).app X) n))

    have represented_desuspend_natTrans {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C]  (F G : C ⥤ C)
        [F.CommShift ℤ] [G.CommShift ℤ] (α : F ⟶ G) [α.CommShift ℤ]
        (X : C) (n : ℤ) (x : HomotopyGroup n (F.obj (X⟦(1 : ℤ)⟧))) :
        homotopyDesuspend (G.obj X) n
          ((x ≫ α.app (X⟦(1 : ℤ)⟧)) ≫ (G.commShiftIso (1 : ℤ)).hom.app X) =
          homotopyDesuspend (F.obj X) n (x ≫ (F.commShiftIso (1 : ℤ)).hom.app X) ≫
            α.app X := by
      rw [Category.assoc, ← NatTrans.shift_app_comm, ← Category.assoc,
        homotopyDesuspend_postcompose]

    have coaction_desuspend {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [MonoidalPreadditive C] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ]  (X : C) (n : ℤ) (x : Mod2Homology H n (X⟦(1 : ℤ)⟧)) :
        mod2DoubleHomologyDesuspend H X n (mod2CoactionMap H (X⟦(1 : ℤ)⟧) n x) =
          mod2CoactionMap H X (n - 1) (mod2HomologyDesuspend H X n x) := by
      let F := tensorLeft H.HF2
      let α : F ⟶ F ⋙ F := F.leftUnitor.inv ≫ Functor.whiskerRight (mod2UnitNatTrans H) F
      have h := represented_desuspend_natTrans F (F ⋙ F) α X n x
      change homotopyDesuspend (H.HF2 ⊗ (H.HF2 ⊗ X)) n
          (((x ≫ H.HF2 ◁ adamsUnit H.unit (X⟦(1 : ℤ)⟧)) ≫
            H.HF2 ◁ ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app X) ≫
              ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app (H.HF2 ⊗ X)) =
        homotopyDesuspend (H.HF2 ⊗ X) n
          (x ≫ ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app X) ≫
            H.HF2 ◁ adamsUnit H.unit X
      simp [α, F, mod2UnitNatTrans, Functor.commShiftIso_comp_hom_app,
        Category.assoc] at h
      simp only [Category.assoc]
      convert h using 1 <;> rfl

    have tensorCoaction_desuspend {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [MonoidalPreadditive C] (R : Mod2RingStructure H) [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        (X : C) (n : ℤ) (x : Mod2Homology H n (X⟦(1 : ℤ)⟧)) :
        mod2TensorCoaction H R K X (n - 1) (mod2HomologyDesuspend H X n x) =
          cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i (X⟦(1 : ℤ)⟧))
            (fun i => mod2HomologyF2 H R i X) (mod2HomologyDesuspendF2 H R X) n
            (mod2TensorCoaction H R K (X⟦(1 : ℤ)⟧) n x) := by
      rw [tensorCoaction_apply, ← coaction_desuspend, hK]
      rfl

    have tensorDesuspend_injective {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [MonoidalPreadditive C] (R : Mod2RingStructure H) [NatTrans.CommShift (mod2UnitNatTrans H) ℤ]  (X : C) (n : ℤ) :
        Function.Injective
          (cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i (X⟦(1 : ℤ)⟧))
            (fun i => mod2HomologyF2 H R i X) (mod2HomologyDesuspendF2 H R X) n) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      dsimp only [cooperationTensorLowerMap, KIP126.Algebra.gradedTensorLowerMap]
      apply (DirectSum.lmap_injective _).mpr
      intro i
      exact (TensorProduct.congr (LinearEquiv.refl (ZMod 2) (Mod2Cooperations H i))
        ((desuspendEquiv H R X (n - i)).trans
          (LinearEquiv.cast (R := ZMod 2) (M := fun j => mod2HomologyF2 H R j X)
            (show n - i - 1 = n - 1 - i by omega)))).injective

    let shiftedConeIso {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)]  {A B Q : C} (α : A ⟶ B)
        (i : B⟦(1 : ℤ)⟧ ⟶ Q) (p : Q ⟶ (A⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)
        (hT : Triangle.mk (α⟦(1 : ℤ)⟧') i p ∈ distTriang C) :
        Q ≅ (HasFunctorialCofiber.cofib α)⟦(1 : ℤ)⟧ := by
      let T := Triangle.mk α (HasFunctorialCofiber.cofibι α) (HasFunctorialCofiber.cofibδ α)
      let eA : A⟦(1 : ℤ)⟧ ≅ A⟦(1 : ℤ)⟧ :=
        ⟨-𝟙 _, -𝟙 _, by simp, by simp⟩
      exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂
        (Triangle.mk (α⟦(1 : ℤ)⟧') i p) ((Triangle.shiftFunctor C (1 : ℤ)).obj T)
        hT (Triangle.shift_distinguished T (HasFunctorialCofiber.cofib_distinguished α) 1)
        eA (Iso.refl _) (by
          simp [T, eA, Triangle.shiftFunctor]
          exact (Category.id_comp _).symm))

    let isoHomologyEquiv {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  {X Y : C} (e : X ≅ Y) (n : ℤ) :
        mod2HomologyF2 H R n X ≃ₗ[ZMod 2] mod2HomologyF2 H R n Y := {
      toFun := Mod2Homology.pushforward H e.hom n
      invFun := Mod2Homology.pushforward H e.inv n
      left_inv x := by
        change (x ≫ H.HF2 ◁ e.hom) ≫ H.HF2 ◁ e.inv = x
        rw [Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, Category.comp_id]
      right_inv x := by
        change (x ≫ H.HF2 ◁ e.inv) ≫ H.HF2 ◁ e.hom = x
        rw [Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id, Category.comp_id]
      map_add' := (mod2HomologyF2Map H R e.hom n).hom.map_add
      map_smul' := (mod2HomologyF2Map H R e.hom n).hom.map_smul }

    have cast_same   (V : ℤ → Type) [∀ i, AddCommGroup (V i)]
        [∀ i, Module (ZMod 2) (V i)] (i : ℤ) (h : i = i) (x : V i) :
        (LinearEquiv.cast (R := ZMod 2) (M := V) h) x = x := rfl

    let suspendClass {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ]  (X : C) (n : ℤ) (x : mod2HomologyF2 H R n X) :
        mod2HomologyF2 H R (n + 1) (X⟦(1 : ℤ)⟧) :=
      (desuspendEquiv H R X (n + 1)).symm
        ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i X)
          (by omega)) x)

    have nonzero_coordinate_one   {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
        (q : V ≃ₗ[ZMod 2] ZMod 2) (x : V) (hx : x ≠ 0) : q x = 1 := by
      have hn : q x ≠ 0 := fun h => hx (q.map_eq_zero_iff.mp h)
      have htwo (a : ZMod 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp
      exact (htwo _).resolve_left hn

    have nonzero_eq_basis   {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
        (q : V ≃ₗ[ZMod 2] ZMod 2) (x : V) (hx : x ≠ 0) : x = q.symm 1 := by
      apply q.injective
      rw [q.apply_symm_apply]
      exact nonzero_coordinate_one q x hx

    let shiftedCoordinate {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ]  {X Q : C} (e : Q ≅ X⟦(1 : ℤ)⟧)
        (n : ℤ) (q : mod2HomologyF2 H R n X ≃ₗ[ZMod 2] ZMod 2) :
        mod2HomologyF2 H R (n + 1) Q ≃ₗ[ZMod 2] ZMod 2 :=
      (((isoHomologyEquiv H R e (n + 1)).trans (desuspendEquiv H R X (n + 1))).trans
        (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i X)
          (by omega))).trans q

    have shiftedCoordinate_basis {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ]  {X Q : C} (e : Q ≅ X⟦(1 : ℤ)⟧)
        (n : ℤ) (q : mod2HomologyF2 H R n X ≃ₗ[ZMod 2] ZMod 2) :
        (shiftedCoordinate H R e n q).symm 1 =
          Mod2Homology.pushforward H e.inv (n + 1) (suspendClass H R X n (q.symm 1)) := by
      apply (shiftedCoordinate H R e n q).injective
      rw [LinearEquiv.apply_symm_apply]
      change 1 = q ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i X)
        (by omega)) ((desuspendEquiv H R X (n + 1))
          ((isoHomologyEquiv H R e (n + 1))
            ((isoHomologyEquiv H R e (n + 1)).symm (suspendClass H R X n (q.symm 1))))))
      rw [LinearEquiv.apply_symm_apply]
      simp only [suspendClass, LinearEquiv.apply_symm_apply]
      rw [cast_cast]
      simp only [cast_same, LinearEquiv.apply_symm_apply]

    have suspend_twoCell_coaction {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        (X : C) (d : ℤ) (hd : d = 1 ∨ d = 2)
        (e0 : mod2HomologyF2 H R 0 X) (ed : mod2HomologyF2 H R d X)
        (u : mod2HomologyF2 H R d H.HF2)
        (hψ : mod2TensorCoaction H R K X d ed =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) d ed +
          DirectSum.lof (ZMod 2) ℤ _ d (u ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i X)
              (sub_self d).symm) e0)) :
        mod2TensorCoaction H R K (X⟦(1 : ℤ)⟧) (d + 1) (suspendClass H R X d ed) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i (X⟦(1 : ℤ)⟧)) (d + 1)
            (suspendClass H R X d ed) +
          DirectSum.lof (ZMod 2) ℤ _ d (u ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i (X⟦(1 : ℤ)⟧))
              (by omega)) (suspendClass H R X 0 e0)) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      rcases hd with rfl | rfl
      · apply tensorDesuspend_injective H R X
        rw [← tensorCoaction_desuspend H R K hK, map_add, tensorLowerMap_unit]
        simp only [cooperationTensorLowerMap,
          KIP126.Algebra.gradedTensorLowerMap_lof_tmul]
        change mod2TensorCoaction H R K X 1
            ((desuspendEquiv H R X 2) ((desuspendEquiv H R X 2).symm ed)) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 1
            ((desuspendEquiv H R X 2) ((desuspendEquiv H R X 2).symm ed)) +
          DirectSum.lof (ZMod 2) ℤ
            (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (1 - i) X) 1
            (u ⊗ₜ[ZMod 2] (desuspendEquiv H R X 1) ((desuspendEquiv H R X 1).symm e0))
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact hψ
      · apply tensorDesuspend_injective H R X
        rw [← tensorCoaction_desuspend H R K hK, map_add, tensorLowerMap_unit]
        simp only [cooperationTensorLowerMap,
          KIP126.Algebra.gradedTensorLowerMap_lof_tmul]
        change mod2TensorCoaction H R K X 2
            ((desuspendEquiv H R X 3) ((desuspendEquiv H R X 3).symm ed)) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 2
            ((desuspendEquiv H R X 3) ((desuspendEquiv H R X 3).symm ed)) +
          DirectSum.lof (ZMod 2) ℤ
            (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (2 - i) X) 2
            (u ⊗ₜ[ZMod 2] (desuspendEquiv H R X 1) ((desuspendEquiv H R X 1).symm e0))
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact hψ


    have iso_suspended_twoCell_coaction {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        {X Q : C} (e : Q ≅ X⟦(1 : ℤ)⟧) (d : ℤ) (hd : d = 1 ∨ d = 2)
        (e0 : mod2HomologyF2 H R 0 X) (ed : mod2HomologyF2 H R d X)
        (u : mod2HomologyF2 H R d H.HF2)
        (hψ : mod2TensorCoaction H R K X d ed =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) d ed +
          DirectSum.lof (ZMod 2) ℤ _ d (u ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i X)
              (sub_self d).symm) e0)) :
        mod2TensorCoaction H R K Q (d + 1)
            (Mod2Homology.pushforward H e.inv (d + 1) (suspendClass H R X d ed)) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i Q) (d + 1)
            (Mod2Homology.pushforward H e.inv (d + 1) (suspendClass H R X d ed)) +
          DirectSum.lof (ZMod 2) ℤ _ d (u ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i Q)
              (by omega))
              (Mod2Homology.pushforward H e.inv 1 (suspendClass H R X 0 e0))) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      rw [tensorCoaction_naturality, suspend_twoCell_coaction H R K hK X d hd e0 ed u hψ,
        map_add, tensorUnit_naturality]
      congr 1
      simp [cooperationTensorMap, KIP126.Algebra.gradedTensorMapRight,
        homologyPushforward_cast]
      congr 2
      exact homologyPushforward_cast H R e.inv 1 (d + 1 - d)
        (by omega) (suspendClass H R X 0 e0)

    have shifted_coordinate_coaction {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        {X Q : C} (e : Q ≅ X⟦(1 : ℤ)⟧) (d : ℤ) (hd : d = 1 ∨ d = 2)
        (q0 : mod2HomologyF2 H R 0 X ≃ₗ[ZMod 2] ZMod 2)
        (qd : mod2HomologyF2 H R d X ≃ₗ[ZMod 2] ZMod 2)
        (u : mod2HomologyF2 H R d H.HF2)
        (hψ : mod2TensorCoaction H R K X d (qd.symm 1) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) d (qd.symm 1) +
          DirectSum.lof (ZMod 2) ℤ _ d (u ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i X)
              (sub_self d).symm) (q0.symm 1))) :
        mod2TensorCoaction H R K Q (d + 1) ((shiftedCoordinate H R e d qd).symm 1) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i Q) (d + 1)
            ((shiftedCoordinate H R e d qd).symm 1) +
          DirectSum.lof (ZMod 2) ℤ _ d (u ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i Q)
              (by omega)) ((shiftedCoordinate H R e 0 q0).symm 1)) := by
      rw [shiftedCoordinate_basis, shiftedCoordinate_basis]
      exact iso_suspended_twoCell_coaction H R K hK e d hd (q0.symm 1) (qd.symm 1) u hψ

    let zeroShiftConeIso {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)]  (f : (SphereSpectrum : C) ⟶ SphereSpectrum) :
        HasFunctorialCofiber.cofib ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ f) ≅
          HasFunctorialCofiber.cofib f := by
      let e : Sphere (C := C) 0 ≅ SphereSpectrum := (shiftFunctorZero C ℤ).app SphereSpectrum
      exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂
        (Triangle.mk (e.hom ≫ f) (HasFunctorialCofiber.cofibι (e.hom ≫ f))
          (HasFunctorialCofiber.cofibδ (e.hom ≫ f)))
        (Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f))
        (HasFunctorialCofiber.cofib_distinguished (e.hom ≫ f))
        (HasFunctorialCofiber.cofib_distinguished f) e (Iso.refl _) (by
          change (e.hom ≫ f) ≫ 𝟙 _ = e.hom ≫ f
          rw [Category.comp_id]))

    let twoCellOneTopCoordinate {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
        (f : Sphere (C := C) 0 ⟶ SphereSpectrum) (hf : H.HF2 ◁ f = 0) :
        mod2HomologyF2 H R 1 (HasFunctorialCofiber.cofib f) ≃ₗ[ZMod 2] ZMod 2 :=
      ((twoCell_top_equiv H R 1 (by decide) f hf).trans
        (isoHomologyEquiv H R ((shiftFunctorZero C ℤ).app SphereSpectrum) 0)).trans
          (sphereZeroCoordinate H R)

    have boundary_one_coefficient {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        (T : HoCofiberSequence (C := C)) (n k : ℤ)
        (zt : mod2HomologyF2 H R n T.Z)
        (zm : mod2HomologyF2 H R (n-k) T.Z)
        (zb : mod2HomologyF2 H R (n-n) T.Z)
        (xt : mod2HomologyF2 H R (n-1) T.X)
        (xm : mod2HomologyF2 H R (n-1-k) T.X)
        (q : mod2HomologyF2 H R (n-1-k) T.X →ₗ[ZMod 2] ZMod 2) (hqm : q xm = 1)
        (a c : mod2HomologyF2 H R k H.HF2) (b : mod2HomologyF2 H R n H.HF2)
        (hdt : boundaryF2 H R T n zt = xt)
        (hdm : (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i T.X)
          (show n-k-1=n-1-k by omega)) (boundaryF2 H R T (n-k) zm) = xm)
        (hdb : boundaryF2 H R T (n-n) zb = 0)
        (hX : mod2TensorCoaction H R K T.X (n-1) xt =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i T.X) (n-1) xt +
          tensorTerm H R (fun i => mod2HomologyF2 H R i T.X) (n-1) k a xm)
        (hZ : mod2TensorCoaction H R K T.Z n zt =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i T.Z) n zt +
          tensorTerm H R (fun i => mod2HomologyF2 H R i T.Z) n k c zm +
          tensorTerm H R (fun i => mod2HomologyF2 H R i T.Z) n n b zb) : c = a := by
      have hu := tensorLowerMap_unit H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n zt
      have hu' := hu.trans (congrArg (cooperationTensorUnit H R (fun d => mod2HomologyF2 H R d T.X) (n-1)) hdt)
      have hm := tensorLowerMap_term H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n k c zm
      have hm' := hm.trans (congrArg (tensorTerm H R (fun d => mod2HomologyF2 H R d T.X) (n-1) k c) hdm)
      have hb := tensorLowerMap_term H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n n b zb
      rw [hdb, map_zero] at hb
      have hb' := hb.trans (tensorTerm_zero H R (fun d => mod2HomologyF2 H R d T.X) (n-1) n b)
      have hmap := congrArg (cooperationTensorLowerMap H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n) hZ
      rw [map_add, map_add] at hmap
      have hmap' := hmap.trans (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu' hm') hb')
      have h := tensorCoaction_boundary H R K hK T n zt
      change mod2TensorCoaction H R K T.X (n-1) (boundaryF2 H R T n zt) = _ at h
      rw [hdt, hX] at h
      have he := h.trans (hmap'.trans (add_zero _))
      exact tensorTerm_coefficient_injective H R (fun d => mod2HomologyF2 H R d T.X)
        (n-1) k xm q hqm (add_left_cancel he).symm

    have boundary_two_coefficients {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        (T : HoCofiberSequence (C := C)) (n i j : ℤ) (hij : i ≠ j)
        (zt : mod2HomologyF2 H R n T.Z)
        (zi : mod2HomologyF2 H R (n-i) T.Z) (zj : mod2HomologyF2 H R (n-j) T.Z)
        (zb : mod2HomologyF2 H R (n-n) T.Z)
        (xt : mod2HomologyF2 H R (n-1) T.X)
        (xi : mod2HomologyF2 H R (n-1-i) T.X) (xj : mod2HomologyF2 H R (n-1-j) T.X)
        (qi : mod2HomologyF2 H R (n-1-i) T.X →ₗ[ZMod 2] ZMod 2) (hqi : qi xi = 1)
        (qj : mod2HomologyF2 H R (n-1-j) T.X →ₗ[ZMod 2] ZMod 2) (hqj : qj xj = 1)
        (ai ci : mod2HomologyF2 H R i H.HF2) (aj cj : mod2HomologyF2 H R j H.HF2)
        (b : mod2HomologyF2 H R n H.HF2)
        (hdt : boundaryF2 H R T n zt = xt)
        (hdi : (LinearEquiv.cast (R := ZMod 2) (M := fun d => mod2HomologyF2 H R d T.X)
          (show n-i-1=n-1-i by omega)) (boundaryF2 H R T (n-i) zi) = xi)
        (hdj : (LinearEquiv.cast (R := ZMod 2) (M := fun d => mod2HomologyF2 H R d T.X)
          (show n-j-1=n-1-j by omega)) (boundaryF2 H R T (n-j) zj) = xj)
        (hdb : boundaryF2 H R T (n-n) zb = 0)
        (hX : mod2TensorCoaction H R K T.X (n-1) xt =
          cooperationTensorUnit H R (fun d => mod2HomologyF2 H R d T.X) (n-1) xt +
          tensorTerm H R (fun d => mod2HomologyF2 H R d T.X) (n-1) i ai xi +
          tensorTerm H R (fun d => mod2HomologyF2 H R d T.X) (n-1) j aj xj)
        (hZ : mod2TensorCoaction H R K T.Z n zt =
          cooperationTensorUnit H R (fun d => mod2HomologyF2 H R d T.Z) n zt +
          tensorTerm H R (fun d => mod2HomologyF2 H R d T.Z) n i ci zi +
          tensorTerm H R (fun d => mod2HomologyF2 H R d T.Z) n j cj zj +
          tensorTerm H R (fun d => mod2HomologyF2 H R d T.Z) n n b zb) : ci = ai ∧ cj = aj := by
      have hu := tensorLowerMap_unit H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n zt
      have hu' := hu.trans (congrArg (cooperationTensorUnit H R (fun d => mod2HomologyF2 H R d T.X) (n-1)) hdt)
      have hi := tensorLowerMap_term H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n i ci zi
      have hi' := hi.trans (congrArg (tensorTerm H R (fun d => mod2HomologyF2 H R d T.X) (n-1) i ci) hdi)
      have hj := tensorLowerMap_term H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n j cj zj
      have hj' := hj.trans (congrArg (tensorTerm H R (fun d => mod2HomologyF2 H R d T.X) (n-1) j cj) hdj)
      have hb := tensorLowerMap_term H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n n b zb
      rw [hdb, map_zero] at hb
      have hb' := hb.trans (tensorTerm_zero H R (fun d => mod2HomologyF2 H R d T.X) (n-1) n b)
      have hmap := congrArg (cooperationTensorLowerMap H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n) hZ
      rw [map_add, map_add, map_add] at hmap
      have hmap' := hmap.trans
        (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu' hi') hj') hb')
      have h := tensorCoaction_boundary H R K hK T n zt
      change mod2TensorCoaction H R K T.X (n-1) (boundaryF2 H R T n zt) = _ at h
      rw [hdt, hX] at h
      have he := h.trans (hmap'.trans (add_zero _))
      rw [add_assoc, add_assoc] at he
      exact tensorTerms_two_unique H R (fun d => mod2HomologyF2 H R d T.X)
        (n-1) i j hij xi qi hqi xj qj hqj ci ai cj aj (add_left_cancel he).symm

    have fourCell_degree3_expansion {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  (K : Mod2CooperationKunneth H R)
        (X : C)
        (hX : ∀ i, i ≠ 0 → i ≠ 1 → i ≠ 3 → i ≠ 4 → Subsingleton (Mod2Homology H i X))
        (q0 : mod2HomologyF2 H R 0 X ≃ₗ[ZMod 2] ZMod 2)
        (q2 : mod2HomologyF2 H R 1 X ≃ₗ[ZMod 2] ZMod 2)
        (e4 : mod2HomologyF2 H R 3 X) :
        ∃ (c2 : mod2HomologyF2 H R 2 H.HF2) (c4 : mod2HomologyF2 H R 3 H.HF2),
          mod2TensorCoaction H R K X 3 e4 =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 e4 +
            DirectSum.lof (ZMod 2) ℤ _ 2 (c2 ⊗ₜ[ZMod 2] q2.symm 1) +
            DirectSum.lof (ZMod 2) ℤ _ 3 (c4 ⊗ₜ[ZMod 2] q0.symm 1) := by
      classical
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      let z := mod2TensorCoaction H R K X 3 e4
      obtain ⟨w, hw⟩ := zeroTensor_unit_factor H R B (z 0)
      obtain ⟨c2, hc2⟩ := tensor_rank_one q2 (z 2)
      obtain ⟨c4, hc4⟩ := tensor_rank_one q0 (z 3)
      have hd := directSum_supported_decomposition
        (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (3-i) X)
        {0, 2, 3} (fun i hi => by
          have his : i ≠ 0 ∧ i ≠ 2 ∧ i ≠ 3 := by simpa using hi
          by_cases hin : i = -1
          · subst i
            letI : Subsingleton (Mod2Cooperations H (-1)) :=
              negative_cooperation_subsingleton H R B (-1) (by decide)
            infer_instance
          · letI : Subsingleton (mod2HomologyF2 H R (3-i) X) :=
              hX (3-i) (by omega) (by omega) (by omega) (by omega)
            infer_instance) z
      simp only [Finset.sum_insert (show (0 : ℤ) ∉ {2, 3} by decide),
        Finset.sum_insert (show (2 : ℤ) ∉ {3} by decide), Finset.sum_singleton] at hd
      rw [hw, hc2, hc4] at hd
      have he := congrArg (cooperationTensorAugmentation H R
        (fun i => mod2HomologyF2 H R i X) 3) hd
      change cooperationTensorAugmentation H R _ 3 z = _ at he
      rw [map_add, map_add,
        positiveTensor_augmentation_zero H R _ 3 2 (by decide),
        positiveTensor_augmentation_zero H R _ 3 3 (by decide), add_zero, add_zero] at he
      change cooperationTensorAugmentation H R _ 3 z =
        cooperationTensorAugmentation H R _ 3
          (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 w) at he
      rw [cooperationTensorUnit_augmentation] at he
      have he4 : e4 = w := by
        rw [← he]
        exact (tensorCoaction_counit H R K X 3 e4).symm
      refine ⟨c2, c4, ?_⟩
      have hu : cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 e4 =
          DirectSum.lof (ZMod 2) ℤ _ 0 (cooperationUnit H ⊗ₜ[ZMod 2] e4) := rfl
      rw [hu]
      simpa only [← he4, add_assoc] using hd

    let coneBottomCoordinate {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  {Q : C} (b : Q ⟶ SphereSpectrum)
        (hb : Mod2Homology.pushforward H b 0 = 0)
        (hQ : Subsingleton (Mod2Homology H (-1) Q)) :
        mod2HomologyF2 H R 0 (HasFunctorialCofiber.cofib b) ≃ₗ[ZMod 2] ZMod 2 :=
      (bottomEquiv_of_homology_zero H R (HoCofiberSequence.ofMorphism b) 0 hb
        (by exact hQ)).symm.trans (sphereZeroCoordinate H R)

    let coneAboveCoordinate {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  {Q : C} (b : Q ⟶ SphereSpectrum)
        (n : ℤ) (hn : n ≠ 0)
        (hb : Mod2Homology.pushforward H b (n-1) = 0)
        (q : mod2HomologyF2 H R (n-1) Q ≃ₗ[ZMod 2] ZMod 2) :
        mod2HomologyF2 H R n (HasFunctorialCofiber.cofib b) ≃ₗ[ZMod 2] ZMod 2 :=
      (boundaryEquiv_of_homology_zero H R (HoCofiberSequence.ofMorphism b) n hb
        (sphereHomologySubsingleton H n hn)).trans q

    have coneAboveCoordinate_boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  {Q : C} (b : Q ⟶ SphereSpectrum)
        (n : ℤ) (hn : n ≠ 0)
        (hb : Mod2Homology.pushforward H b (n-1) = 0)
        (q : mod2HomologyF2 H R (n-1) Q ≃ₗ[ZMod 2] ZMod 2) :
        boundaryF2 H R (HoCofiberSequence.ofMorphism b) n
          ((coneAboveCoordinate H R b n hn hb q).symm 1) = q.symm 1 := by
      change (boundaryEquiv_of_homology_zero H R (HoCofiberSequence.ofMorphism b) n hb
        (sphereHomologySubsingleton H n hn))
          ((boundaryEquiv_of_homology_zero H R (HoCofiberSequence.ofMorphism b) n hb
            (sphereHomologySubsingleton H n hn)).symm (q.symm 1)) = q.symm 1
      exact LinearEquiv.apply_symm_apply _ _

    have coneBottomCoordinate_generator {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  {Q : C} (b : Q ⟶ SphereSpectrum)
        (hb : Mod2Homology.pushforward H b 0 = 0)
        (hQ : Subsingleton (Mod2Homology H (-1) Q)) :
        (coneBottomCoordinate H R b hb hQ).symm 1 =
          Mod2Homology.pushforward H (HasFunctorialCofiber.cofibι b) 0
            ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ adamsUnit H.unit SphereSpectrum) := by
      apply (coneBottomCoordinate H R b hb hQ).injective
      rw [LinearEquiv.apply_symm_apply]
      change 1 = sphereZeroCoordinate H R
        ((bottomEquiv_of_homology_zero H R (HoCofiberSequence.ofMorphism b) 0 hb
          (by exact hQ)).symm
          ((bottomEquiv_of_homology_zero H R (HoCofiberSequence.ofMorphism b) 0 hb
            (by exact hQ)) _))
      rw [LinearEquiv.symm_apply_apply]
      exact (sphereZeroCoordinate_unit H R).symm

    have coneBottomCoordinate_coaction {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (K : Mod2CooperationKunneth H R)
        (hU : Mod2KunnethUnitCompatible H R K)
        {Q : C} (b : Q ⟶ SphereSpectrum)
        (hb : Mod2Homology.pushforward H b 0 = 0)
        (hQ : Subsingleton (Mod2Homology H (-1) Q)) :
        mod2TensorCoaction H R K (HasFunctorialCofiber.cofib b) 0
          ((coneBottomCoordinate H R b hb hQ).symm 1) =
        cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib b)) 0
          ((coneBottomCoordinate H R b hb hQ).symm 1) := by
      rw [coneBottomCoordinate_generator H R b hb hQ]
      exact transfer_unit H R K (HasFunctorialCofiber.cofibι b) 0 _
        (coaction_of_unit_image H R K hU SphereSpectrum 0
          ((shiftFunctorZero C ℤ).hom.app SphereSpectrum))

    have toda_matrix_exists {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (B : Mod2ReducedMilnorBasis H R) (K : Mod2CooperationKunneth H R)
        (hK : Mod2KunnethSuspensionCompatible H R K)
        (hD : Mod2KunnethDiagonalCompatible H R K)
        (hU : Mod2KunnethUnitCompatible H R K)
        (η : Sphere (C := C) 1 ⟶ SphereSpectrum)
        (x : mod2HomologyF2 H R 1 H.HF2) (u : mod2HomologyF2 H R 2 H.HF2)
        (q20 : mod2HomologyF2 H R 0 (HasFunctorialCofiber.cofib (2 • 𝟙 (SphereSpectrum : C))) ≃ₗ[ZMod 2] ZMod 2)
        (q21 : mod2HomologyF2 H R 1 (HasFunctorialCofiber.cofib (2 • 𝟙 (SphereSpectrum : C))) ≃ₗ[ZMod 2] ZMod 2)
        (qη0 : mod2HomologyF2 H R 0 (HasFunctorialCofiber.cofib η) ≃ₗ[ZMod 2] ZMod 2)
        (qη2 : mod2HomologyF2 H R 2 (HasFunctorialCofiber.cofib η) ≃ₗ[ZMod 2] ZMod 2)
        (hψ2 : mod2TensorCoaction H R K (HasFunctorialCofiber.cofib (2 • 𝟙 (SphereSpectrum : C))) 1 (q21.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n (HasFunctorialCofiber.cofib (2 • 𝟙 (SphereSpectrum : C)))) 1 (q21.symm 1) +
          tensorTerm H R (fun n => mod2HomologyF2 H R n (HasFunctorialCofiber.cofib (2 • 𝟙 (SphereSpectrum : C)))) 1 1 x (q20.symm 1))
        (hψη : mod2TensorCoaction H R K (HasFunctorialCofiber.cofib η) 2 (qη2.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n (HasFunctorialCofiber.cofib η)) 2 (qη2.symm 1) +
          tensorTerm H R (fun n => mod2HomologyF2 H R n (HasFunctorialCofiber.cofib η)) 2 2 u (qη0.symm 1))
        (hToda : Toda.Relation (0 : (Sphere (C := C) 1)⟦(1 : ℤ)⟧ ⟶ SphereSpectrum)
          (2 • 𝟙 (Sphere (C := C) 1)) η (2 • 𝟙 SphereSpectrum)) :
        ∃ (a b : mod2HomologyF2 H R 3 H.HF2) (c : mod2HomologyF2 H R 4 H.HF2),
          (cooperationTensorDiagonal H R K 3 a =
            cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n H.HF2) 3 a +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 3 2 u x +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 3 3 a (cooperationUnit H)) ∧
          (cooperationTensorDiagonal H R K 3 b =
            cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n H.HF2) 3 b +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 3 1 x u +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 3 3 b (cooperationUnit H)) ∧
          (cooperationTensorDiagonal H R K 4 c =
            cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n H.HF2) 4 c +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 4 1 x a +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 4 3 b x +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 4 4 c (cooperationUnit H)) := by
      classical
      obtain ⟨Q, i, p, hT, b, t, hib, hb2, ht, hQ, hbzero, hX, htzero, hE⟩ :=
        toda_homology_geometry H R η hToda
      let TQ : HoCofiberSequence (C := C) :=
        ⟨Sphere 1, Sphere 1, Q, 2 • 𝟙 _, i, p, hT⟩
      let TX := HoCofiberSequence.ofMorphism b
      let TE := HoCofiberSequence.ofMorphism t
      let Tη := HoCofiberSequence.ofMorphism η
      let T2 := HoCofiberSequence.ofMorphism (2 • 𝟙 (SphereSpectrum : C))
      have hTshift : Triangle.mk ((2 • 𝟙 (SphereSpectrum : C))⟦(1 : ℤ)⟧') i p ∈ distTriang C := by
        have hmap : ((2 • 𝟙 (SphereSpectrum : C))⟦(1 : ℤ)⟧') = 2 • 𝟙 (Sphere (C := C) 1) := by
          calc
            _ = 2 • (shiftFunctor C (1 : ℤ)).map (𝟙 (SphereSpectrum : C)) := Functor.map_nsmul _
            _ = 2 • 𝟙 (Sphere (C := C) 1) :=
              congrArg (fun f : Sphere (C := C) 1 ⟶ Sphere (C := C) 1 => (2 : ℕ) • f)
                ((shiftFunctor C (1 : ℤ)).map_id SphereSpectrum)
        rw [hmap]
        exact hT
      let eQ := shiftedConeIso (2 • 𝟙 (SphereSpectrum : C)) i p hTshift
      let qQ1 : mod2HomologyF2 H R 1 Q ≃ₗ[ZMod 2] ZMod 2 :=
        shiftedCoordinate H R eQ 0 q20
      let qQ2 : mod2HomologyF2 H R 2 Q ≃ₗ[ZMod 2] ZMod 2 :=
        shiftedCoordinate H R eQ 1 q21
      have hψQ : mod2TensorCoaction H R K Q 2 (qQ2.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n Q) 2 (qQ2.symm 1) +
          tensorTerm H R (fun n => mod2HomologyF2 H R n Q) 2 1 x (qQ1.symm 1) := by
        exact shifted_coordinate_coaction H R K hK eQ 1 (Or.inl rfl) q20 q21 x hψ2
      let qX0 : mod2HomologyF2 H R 0 TX.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneBottomCoordinate H R b (hbzero 0) (hQ (-1) (by decide) (by decide))
      let qX2 : mod2HomologyF2 H R 2 TX.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneAboveCoordinate H R b 2 (by decide) (hbzero 1) qQ1
      let qX3 : mod2HomologyF2 H R 3 TX.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneAboveCoordinate H R b 3 (by decide) (hbzero 2) qQ2
      let qE0 : mod2HomologyF2 H R 0 TE.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneBottomCoordinate H R t (htzero 0) (hX (-1) (by decide) (by decide) (by decide))
      let qE1 : mod2HomologyF2 H R 1 TE.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneAboveCoordinate H R t 1 (by decide) (htzero 0) qX0
      let qE3 : mod2HomologyF2 H R 3 TE.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneAboveCoordinate H R t 3 (by decide) (htzero 2) qX2
      let qE4 : mod2HomologyF2 H R 4 TE.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneAboveCoordinate H R t 4 (by decide) (htzero 3) qX3
      have hid (n : ℤ) : Function.Injective
          (Mod2Homology.pushforward H (𝟙 (SphereSpectrum : C)) n) := by
        intro a b h
        change a ≫ H.HF2 ◁ 𝟙 _ = b ≫ H.HF2 ◁ 𝟙 _ at h
        simpa only [whiskerLeft_id, Category.comp_id] using h
      have hi1 : Function.Injective (Mod2Homology.pushforward H i 1) := by
        apply bottom_injective_of_homology_zero H TQ 1
        exact twice_map_zero H R (𝟙 (Sphere (C := C) 1)) 1
      obtain ⟨cη, hcη, hδη⟩ := compare_cones_of_factorization η b i hib
      have hψX2 : mod2TensorCoaction H R K TX.Z 2 (qX2.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n TX.Z) 2 (qX2.symm 1) +
          tensorTerm H R (fun n => mod2HomologyF2 H R n TX.Z) 2 2 u (qX0.symm 1) := by
        exact comparison_twoCell_transfer H R K Tη TX i (𝟙 SphereSpectrum) cη
          (by
            change HasFunctorialCofiber.cofibι η ≫ cη = 𝟙 SphereSpectrum ≫ HasFunctorialCofiber.cofibι b
            simpa only [Category.id_comp] using hcη) hδη 2 qη0 qη2 qX0 qX2 u
          (homology_bottom_surjective H Tη 0 (by
            change Subsingleton (Mod2Homology H (-1) (Sphere (C := C) 1))
            exact sphereHomologyShiftSubsingleton H (-1) 1 (by decide)))
          (hid 0) (bottom_injective_of_homology_zero H TX 0 (hbzero 0))
          (homology_connecting_injective H Tη 2 (sphereHomologySubsingleton H 2 (by decide)))
          hi1 hψη
      obtain ⟨c2, hc2, hδ2⟩ := compare_cones_of_factorization (2 • 𝟙 (SphereSpectrum : C)) t
        (HasFunctorialCofiber.cofibι b) ht
      have hψE1 : mod2TensorCoaction H R K TE.Z 1 (qE1.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n TE.Z) 1 (qE1.symm 1) +
          tensorTerm H R (fun n => mod2HomologyF2 H R n TE.Z) 1 1 x (qE0.symm 1) := by
        exact comparison_twoCell_transfer H R K T2 TE (HasFunctorialCofiber.cofibι b)
          (𝟙 SphereSpectrum) c2 (by
            change HasFunctorialCofiber.cofibι (2 • 𝟙 (SphereSpectrum : C)) ≫ c2 =
              𝟙 SphereSpectrum ≫ HasFunctorialCofiber.cofibι t
            simpa only [Category.id_comp] using hc2) hδ2
          1 q20 q21 qE0 qE1 x
          (homology_bottom_surjective H T2 0 (by
            change Subsingleton (Mod2Homology H (-1) (SphereSpectrum : C))
            exact sphereHomologySubsingleton H (-1) (by decide)))
          (hid 0) (bottom_injective_of_homology_zero H TE 0 (htzero 0))
          (homology_connecting_injective H T2 1 (sphereHomologySubsingleton H 1 (by decide)))
          (bottom_injective_of_homology_zero H TX 0 (hbzero 0)) hψ2
      have hδX2 : boundaryF2 H R TX 2 (qX2.symm 1) = qQ1.symm 1 :=
        coneAboveCoordinate_boundary H R b 2 (by decide) (hbzero 1) qQ1
      have hδX3 : boundaryF2 H R TX 3 (qX3.symm 1) = qQ2.symm 1 :=
        coneAboveCoordinate_boundary H R b 3 (by decide) (hbzero 2) qQ2
      have hδX0 : boundaryF2 H R TX 0 (qX0.symm 1) = 0 := by
        exact @Subsingleton.elim (mod2HomologyF2 H R (-1) Q)
          (hQ (-1) (by decide) (by decide)) _ _
      have hδE1 : boundaryF2 H R TE 1 (qE1.symm 1) = qX0.symm 1 :=
        coneAboveCoordinate_boundary H R t 1 (by decide) (htzero 0) qX0
      have hδE3 : boundaryF2 H R TE 3 (qE3.symm 1) = qX2.symm 1 :=
        coneAboveCoordinate_boundary H R t 3 (by decide) (htzero 2) qX2
      have hδE4 : boundaryF2 H R TE 4 (qE4.symm 1) = qX3.symm 1 :=
        coneAboveCoordinate_boundary H R t 4 (by decide) (htzero 3) qX3
      have hδE0 : boundaryF2 H R TE 0 (qE0.symm 1) = 0 := by
        exact @Subsingleton.elim (mod2HomologyF2 H R (-1) TX.Z)
          (hX (-1) (by decide) (by decide) (by decide)) _ _
      obtain ⟨cX1, b3, hψX3⟩ := threeCell_023_coaction_expansion H R B K TX.Z hX qX0 qX2 (qX3.symm 1)
      have hcX1 : cX1 = x := boundary_one_coefficient H R K hK TX 3 1
        (qX3.symm 1) (qX2.symm 1) (qX0.symm 1) (qQ2.symm 1) (qQ1.symm 1)
        qQ1.toLinearMap (qQ1.apply_symm_apply 1) x cX1 b3 hδX3 hδX2 hδX0 hψQ hψX3
      subst cX1
      obtain ⟨cE2, a3, hψE3⟩ := fourCell_degree3_expansion H R B K TE.Z hE qE0 qE1 (qE3.symm 1)
      have hcE2 : cE2 = u := boundary_one_coefficient H R K hK TE 3 2
        (qE3.symm 1) (qE1.symm 1) (qE0.symm 1) (qX2.symm 1) (qX0.symm 1)
        qX0.toLinearMap (qX0.apply_symm_apply 1) u cE2 a3 hδE3 hδE1 hδE0 hψX2 hψE3
      subst cE2
      obtain ⟨cE1, cE3, c4, hψE4⟩ := fourCell_coaction_expansion H R B K TE.Z hE qE0 qE1 qE3 (qE4.symm 1)
      obtain ⟨hcE1, hcE3⟩ := boundary_two_coefficients H R K hK TE 4 1 3 (by decide)
        (qE4.symm 1) (qE3.symm 1) (qE1.symm 1) (qE0.symm 1)
        (qX3.symm 1) (qX2.symm 1) (qX0.symm 1)
        qX2.toLinearMap (qX2.apply_symm_apply 1) qX0.toLinearMap (qX0.apply_symm_apply 1)
        x cE1 b3 cE3 c4 hδE4 hδE3 hδE1 hδE0 hψX3 hψE4
      subst cE1
      subst cE3
      have hψX0 : mod2TensorCoaction H R K TX.Z 0 (qX0.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n TX.Z) 0 (qX0.symm 1) :=
        coneBottomCoordinate_coaction H R K hU b (hbzero 0) (hQ (-1) (by decide) (by decide))
      have hψE0 : mod2TensorCoaction H R K TE.Z 0 (qE0.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n TE.Z) 0 (qE0.symm 1) :=
        coneBottomCoordinate_coaction H R K hU t (htzero 0) (hX (-1) (by decide) (by decide) (by decide))
      have hbdiag := threeCell_matrix_023 H R K hD TX.Z qX0.toLinearMap (qX0.symm 1)
        (qX0.apply_symm_apply 1) (qX2.symm 1) (qX3.symm 1) u x b3 hψX0 hψX2 hψX3
      obtain ⟨hadiag, hcdiag⟩ := fourCell_bottom_matrix H R K hD TE.Z qE0.toLinearMap
        (qE0.symm 1) (qE0.apply_symm_apply 1) (qE1.symm 1) (qE3.symm 1) (qE4.symm 1)
        x u a3 b3 c4 hψE0 hψE1 hψE3 hψE4
      exact ⟨a3, b3, c4, hadiag, hbdiag, hcdiag⟩

    open scoped TensorProduct DirectSum in
    have two_cell_coordinates :
        let R := KIP126.Def.standardHF2AdamsContext.cooperationStructure.ring
        let B := KIP126.Def.standardHF2AdamsContext.cooperationStructure.basis
        let K := KIP126.Def.standardHF2AdamsContext.cooperationStructure.kunneth
        let η := literature.sources.sourceComparisons.classicalSource.eta
        ∃ (x1 : mod2HomologyF2 H R 1 H.HF2) (u2 : mod2HomologyF2 H R 2 H.HF2)
          (q20 : mod2HomologyF2 H R 0
            (HasFunctorialCofiber.cofib ((2 : ℕ) • 𝟙 (SphereSpectrum : C))) ≃ₗ[ZMod 2] ZMod 2)
          (q21 : mod2HomologyF2 H R 1
            (HasFunctorialCofiber.cofib ((2 : ℕ) • 𝟙 (SphereSpectrum : C))) ≃ₗ[ZMod 2] ZMod 2)
          (qη0 : mod2HomologyF2 H R 0 (HasFunctorialCofiber.cofib η) ≃ₗ[ZMod 2] ZMod 2)
          (qη2 : mod2HomologyF2 H R 2 (HasFunctorialCofiber.cofib η) ≃ₗ[ZMod 2] ZMod 2),
          cooperationMilnorPolynomial H R B 1 x1 = MvPolynomial.X ((0 : Fin 1), 0) ∧
          cooperationMilnorPolynomial H R B 2 u2 = MvPolynomial.X ((0 : Fin 1), 0) ^ 2 ∧
          mod2TensorCoaction H R K
            (HasFunctorialCofiber.cofib ((2 : ℕ) • 𝟙 (SphereSpectrum : C))) 1 (q21.symm 1) =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i
              (HasFunctorialCofiber.cofib ((2 : ℕ) • 𝟙 (SphereSpectrum : C)))) 1 (q21.symm 1) +
            tensorTerm H R (fun i => mod2HomologyF2 H R i
              (HasFunctorialCofiber.cofib ((2 : ℕ) • 𝟙 (SphereSpectrum : C)))) 1 1 x1 (q20.symm 1) ∧
          mod2TensorCoaction H R K (HasFunctorialCofiber.cofib η) 2 (qη2.symm 1) =
            cooperationTensorUnit H R
              (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η)) 2 (qη2.symm 1) +
            tensorTerm H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η))
              2 2 u2 (qη0.symm 1) := by
      classical
      let R := KIP126.Def.standardHF2AdamsContext.cooperationStructure.ring
      let B := KIP126.Def.standardHF2AdamsContext.cooperationStructure.basis
      let K := KIP126.Def.standardHF2AdamsContext.cooperationStructure.kunneth
      let η := literature.sources.sourceComparisons.classicalSource.eta
      have h2 := two_filtration
      have hη := eta_filtration
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
        fun i => mod2HF2HomotopyModule H R i
      have low_support (d : ℕ →₀ ℕ) (hd : slotWeight d ≤ 2) :
          d = Finsupp.single 0 (d 0) := by
        have hz (j : ℕ) (hj : 1 ≤ j) : d j = 0 := by
          by_contra hn
          have hw := Finsupp.le_weight_of_ne_zero'
            (fun j : ℕ => 2 ^ (j + 1) - 1) hn
          have hp : 2 ^ 2 ≤ 2 ^ (j + 1) :=
            Nat.pow_le_pow_right (by decide) (by omega)
          change 2 ^ (j + 1) - 1 ≤ slotWeight d at hw
          norm_num at hp
          omega
        ext j
        rcases j with _ | j
        · simp
        · simp [hz (j + 1) (by omega)]
      have low_weight (d : ℕ →₀ ℕ) (hd : slotWeight d ≤ 2) : slotWeight d = d 0 := by
        conv_lhs => rw [low_support d hd]
        simp [slotWeight, Finsupp.weight_single]
      let p1 : PositiveMonomial 1 :=
        ⟨Finsupp.single 0 1, by norm_num [slotWeight, Finsupp.weight_single], by simp⟩
      let p2 : PositiveMonomial 2 :=
        ⟨Finsupp.single 0 2, by norm_num [slotWeight, Finsupp.weight_single], by simp⟩
      have hp1 (q : PositiveMonomial 1) : q = p1 := by
        apply Subtype.ext
        have hw : slotWeight q.val = 1 := by exact_mod_cast q.property.1
        rw [low_support q.val (by omega), ← low_weight q.val (by omega), hw]
      have hp2 (q : PositiveMonomial 2) : q = p2 := by
        apply Subtype.ext
        have hw : slotWeight q.val = 2 := by exact_mod_cast q.property.1
        rw [low_support q.val (by omega), ← low_weight q.val (by omega), hw]
      have basis_polynomial (n : ℤ) (p : PositiveMonomial n) :
          cooperationMilnorPolynomial H R B n (B.basis n p).val =
            milnorMonomialPolynomial (⟨p.val, p.property.1⟩ : MilnorMonomial n) := by
        change Finsupp.linearCombination (ZMod 2) milnorMonomialPolynomial
          (cooperationMilnorEquiv H R B n (B.basis n p).val) = _
        erw [cooperationMilnorEquiv_reduced_basis H R B n p]
        simp only [Finsupp.linearCombination_single, one_smul]
      let x1 : mod2HomologyF2 H R 1 H.HF2 := (B.basis 1 p1).val
      let u2 : mod2HomologyF2 H R 2 H.HF2 := (B.basis 2 p2).val
      have hx : cooperationMilnorPolynomial H R B 1 x1 = MvPolynomial.X ((0 : Fin 1), 0) := by
        change cooperationMilnorPolynomial H R B 1 (B.basis 1 p1).val = _
        rw [basis_polynomial 1 p1]
        simp [milnorMonomialPolynomial, p1, Finsupp.mapDomain_single, MvPolynomial.X]
      have hu : cooperationMilnorPolynomial H R B 2 u2 = MvPolynomial.X ((0 : Fin 1), 0) ^ 2 := by
        change cooperationMilnorPolynomial H R B 2 (B.basis 2 p2).val = _
        rw [basis_polynomial 2 p2]
        simp [milnorMonomialPolynomial, p2, Finsupp.mapDomain_single,
          MvPolynomial.X_pow_eq_monomial]
      let f2 : (SphereSpectrum : C) ⟶ SphereSpectrum := (2 : ℕ) • 𝟙 _
      let α2 : Sphere (C := C) 0 ⟶ SphereSpectrum :=
        (shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ f2
      have hf2 : H.HF2 ◁ α2 = 0 := tensor_zero_of_first_filtration H R α2 h2.1
      have hfη : H.HF2 ◁ η = 0 := tensor_zero_of_first_filtration H R η hη.1
      obtain ⟨e21, q20old, he21, _, _, hψ2⟩ :=
        twoCell_actual_coaction H R B K 1 (by decide) p1 hp1 α2 h2.1 h2.2
          (low_basis_primitive 1 p1 1 (Or.inl rfl) rfl)
      obtain ⟨eη2, qη0, heη2, _, _, hψη⟩ :=
        twoCell_actual_coaction H R B K 2 (by decide) p2 hp2 η hη.1 hη.2
          (low_basis_primitive 2 p2 2 (Or.inr rfl) rfl)
      let q21old := twoCellOneTopCoordinate H R α2 hf2
      let qη2 : mod2HomologyF2 H R 2 (HasFunctorialCofiber.cofib η) ≃ₗ[ZMod 2] ZMod 2 :=
        ((twoCell_top_equiv H R 2 (by decide) η hfη).trans
          (desuspendEquiv H R (SphereSpectrum : C) 1)).trans (sphereZeroCoordinate H R)
      have he21' : e21 = q21old.symm 1 := nonzero_eq_basis q21old e21 he21
      have heη2' : eη2 = qη2.symm 1 := nonzero_eq_basis qη2 eη2 heη2
      have hψ2' : mod2TensorCoaction H R K (HasFunctorialCofiber.cofib α2) 1 (q21old.symm 1) =
          cooperationTensorUnit H R
            (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α2)) 1 (q21old.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α2))
            1 1 x1 (q20old.symm 1) := by
        rw [he21'] at hψ2
        change mod2TensorCoaction H R K (HasFunctorialCofiber.cofib α2) 1 (q21old.symm 1) =
          cooperationTensorUnit H R
            (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α2)) 1 (q21old.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α2))
            1 1 x1 (q20old.symm 1) at hψ2
        exact hψ2
      have hψη' : mod2TensorCoaction H R K (HasFunctorialCofiber.cofib η) 2 (qη2.symm 1) =
          cooperationTensorUnit H R
            (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η)) 2 (qη2.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η))
            2 2 u2 (qη0.symm 1) := by
        rw [heη2'] at hψη
        change mod2TensorCoaction H R K (HasFunctorialCofiber.cofib η) 2 (qη2.symm 1) =
          cooperationTensorUnit H R
            (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η)) 2 (qη2.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η))
            2 2 u2 (qη0.symm 1) at hψη
        exact hψη
      let e := zeroShiftConeIso f2
      let E0 := isoHomologyEquiv H R e 0
      let E1 := isoHomologyEquiv H R e 1
      let q20 := E0.symm.trans q20old
      let q21 := E1.symm.trans q21old
      have hc0 : Mod2Homology.pushforward H e.hom 0 (q20old.symm 1) = q20.symm 1 := by
        apply q20.injective
        change q20old (E0.symm (E0 (q20old.symm 1))) = q20 (q20.symm 1)
        rw [E0.symm_apply_apply, q20old.apply_symm_apply, q20.apply_symm_apply]
      have hc1 : Mod2Homology.pushforward H e.hom 1 (q21old.symm 1) = q21.symm 1 := by
        apply q21.injective
        change q21old (E1.symm (E1 (q21old.symm 1))) = q21 (q21.symm 1)
        rw [E1.symm_apply_apply, q21old.apply_symm_apply, q21.apply_symm_apply]
      refine ⟨x1, u2, q20, q21, qη0, qη2, hx, hu, ?_, hψη'⟩
      have ht := transfer_twoTerm H R K e.hom 1 1 (q21old.symm 1) x1 (q20old.symm 1) hψ2'
      erw [hc1, hc0] at ht
      exact ht

    let Rlow := KIP126.Def.standardHF2AdamsContext.cooperationStructure.ring
    let Blow := KIP126.Def.standardHF2AdamsContext.cooperationStructure.basis
    let Klow := KIP126.Def.standardHF2AdamsContext.cooperationStructure.kunneth
    let ηlow := literature.sources.sourceComparisons.classicalSource.eta
    have hKlow := KIP126.Def.standardHF2AdamsContext.cooperationStructure.suspension
    have hUlow := KIP126.Def.standardHF2AdamsContext.cooperationStructure.unit
    have hDlow := KIP126.Def.standardHF2AdamsContext.cooperationStructure.diagonal
    obtain ⟨xlow, ulow, q20, q21, qη0, qη2, hxlow, hulow, hψ2, hψη⟩ :=
      two_cell_coordinates
    intro ht
    obtain ⟨a, b, c, ha, hb, hc⟩ := toda_matrix_exists H Rlow Blow Klow
      hKlow hDlow hUlow ηlow xlow ulow q20 q21 qη0 qη2 hψ2 hψη ht
    apply low_cooperation_obstructions xlow ulow hxlow hulow a b c ha hb
    change cooperationTensorDiagonal H Rlow Klow 4 c =
      cooperationTensorUnit H Rlow (fun n => mod2HomologyF2 H Rlow n H.HF2) 4 c +
        (tensorTerm H Rlow (fun n => mod2HomologyF2 H Rlow n H.HF2) 4 1 xlow a +
          tensorTerm H Rlow (fun n => mod2HomologyF2 H Rlow n H.HF2) 4 3 b xlow) +
        tensorTerm H Rlow (fun n => mod2HomologyF2 H Rlow n H.HF2) 4 4 c (cooperationUnit H)
    simpa only [add_assoc] using hc

  have moore_factor (S : Syn)
      (htf : ∀ a : S ⟶ S, a + a = 0 → a = 0) :
      ∃ (M : Syn) (i : S ⟶ M) (p : M ⟶ S⟦(1 : ℤ)⟧)
        (ε : S⟦(1 : ℤ)⟧ ⟶ S),
        Triangle.mk ((2 : ℕ) • 𝟙 S) i p ∈ distTriang Syn ∧
          (2 : ℕ) • 𝟙 M = p ≫ ε ≫ i := by
    obtain ⟨M, i, p, hT⟩ := distinguished_cocone_triangle ((2 : ℕ) • 𝟙 S)
    let T := Triangle.mk ((2 : ℕ) • 𝟙 S) i p
    have hp : (2 : ℕ) • p = 0 := by
      have h := comp_distTriang_mor_zero₃₁ T hT
      change p ≫ ((2 : ℕ) • 𝟙 S)⟦(1 : ℤ)⟧' = 0 at h
      simpa only [Syn, C, Functor.map_nsmul, CategoryTheory.Functor.map_id,
        Preadditive.comp_nsmul, Category.comp_id] using h
    have hp' : ((2 : ℕ) • 𝟙 M) ≫ p = 0 := by
      simpa only [Syn, C, Preadditive.nsmul_comp, Category.id_comp] using hp
    obtain ⟨a, ha⟩ := T.coyoneda_exact₃ hT ((2 : ℕ) • 𝟙 M) hp'
    change (2 : ℕ) • 𝟙 M = a ≫ i at ha
    have hi : (2 : ℕ) • i = 0 := by
      have h := comp_distTriang_mor_zero₁₂ T hT
      change ((2 : ℕ) • 𝟙 S) ≫ i = 0 at h
      simpa only [Syn, C, Preadditive.nsmul_comp, Category.id_comp] using h
    have hai : i ≫ a = 0 := by
      apply htf
      have h : (2 : ℕ) • (i ≫ a) = 0 := by
        rw [← Preadditive.nsmul_comp, hi, zero_comp]
      simpa only [Syn, C, two_nsmul] using h
    obtain ⟨ε, hε⟩ := T.yoneda_exact₃ hT a hai
    change a = p ≫ ε at hε
    refine ⟨M, i, p, ε, hT, ?_⟩
    rw [ha, hε, Category.assoc]

  have classical_moore_two_ne_zero
      (Scl N : C) (j : Scl ⟶ N) (v : N ⟶ Scl⟦(1 : ℤ)⟧)
      (hT : Triangle.mk ((2 : ℕ) • 𝟙 Scl) j v ∈ distTriang C)
      (η : Scl⟦(1 : ℤ)⟧ ⟶ Scl) (hη : η + η = 0)
      (hnotoda : ¬ Toda.Relation
        (0 : Scl⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ ⟶ Scl)
        ((2 : ℕ) • 𝟙 (Scl⟦(1 : ℤ)⟧)) η ((2 : ℕ) • 𝟙 Scl)) :
      (2 : ℕ) • 𝟙 N ≠ 0 := by
    intro hN
    let T := Triangle.mk ((2 : ℕ) • 𝟙 Scl) j v
    let J := Triangle.mk ((2 : ℕ) • 𝟙 (Scl⟦(1 : ℤ)⟧))
      (-j⟦(1 : ℤ)⟧') (v⟦(1 : ℤ)⟧')
    let e : Scl⟦(1 : ℤ)⟧ ≅ Scl⟦(1 : ℤ)⟧ :=
      { hom := -𝟙 _
        inv := -𝟙 _
        hom_inv_id := by simp [C]
        inv_hom_id := by simp [C] }
    have hJ : J ∈ distTriang C := by
      have hr := rot_of_distTriang T.rotate.rotate
        (rot_of_distTriang T.rotate (rot_of_distTriang T hT))
      apply isomorphic_distinguished _ hr
      refine Triangle.isoMk J T.rotate.rotate.rotate e (Iso.refl _) (Iso.refl _)
        ?_ ?_ ?_
      · simp [Syn, C, J, T, Triangle.rotate, e, Functor.map_nsmul,
          (shiftFunctor C (1 : ℤ)).map_id Scl]
        erw [CategoryTheory.Category.comp_id]
      · simp [Syn, C, J, T, Triangle.rotate, e]
      · simp [Syn, C, J, T, Triangle.rotate, e,
          (shiftFunctor C (1 : ℤ)).map_id (Scl⟦(1 : ℤ)⟧)]
        erw [CategoryTheory.Category.comp_id]
    have hcomp : ((2 : ℕ) • 𝟙 (Scl⟦(1 : ℤ)⟧)) ≫ η = 0 := by
      simpa only [Syn, C, Preadditive.nsmul_comp, Category.id_comp, two_nsmul, Preadditive.add_comp] using hη
    obtain ⟨b, hb⟩ := J.yoneda_exact₂ hJ η hcomp
    change η = (-j⟦(1 : ℤ)⟧') ≫ b at hb
    have hNshift : (2 : ℕ) • 𝟙 (N⟦(1 : ℤ)⟧) = 0 := by
      have h := congrArg (fun f : N ⟶ N => f⟦(1 : ℤ)⟧') hN
      simpa only [Syn, C, Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using h
    have hb2 : b ≫ ((2 : ℕ) • 𝟙 Scl) = 0 := by
      calc
        b ≫ ((2 : ℕ) • 𝟙 Scl) = ((2 : ℕ) • 𝟙 (N⟦(1 : ℤ)⟧)) ≫ b := by
          simp only [Syn, C, Preadditive.comp_nsmul, Preadditive.nsmul_comp,
            Category.comp_id, Category.id_comp]
        _ = 0 := by rw [hNshift, zero_comp]
    apply hnotoda
    refine ⟨N⟦(1 : ℤ)⟧, -j⟦(1 : ℤ)⟧', v⟦(1 : ℤ)⟧', hJ, b, hb.symm, ?_⟩
    simpa only [Syn, C, comp_zero] using hb2.symm

  have realized_moore_two_ne_zero
      (F : Syn ⥤ C) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
      (S : Syn) (Scl : C) (U : F.obj S ≅ Scl)
      (M : Syn) (i : S ⟶ M) (p : M ⟶ S⟦(1 : ℤ)⟧)
      (hT : Triangle.mk ((2 : ℕ) • 𝟙 S) i p ∈ distTriang Syn)
      (η : Scl⟦(1 : ℤ)⟧ ⟶ Scl) (hη : η + η = 0)
      (hnotoda : ¬ Toda.Relation
        (0 : Scl⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ ⟶ Scl)
        ((2 : ℕ) • 𝟙 (Scl⟦(1 : ℤ)⟧)) η ((2 : ℕ) • 𝟙 Scl)) :
      (2 : ℕ) • 𝟙 M ≠ 0 := by
    let T := Triangle.mk ((2 : ℕ) • 𝟙 S) i p
    let j := U.inv ≫ F.map i
    let v := F.map p ≫ (F.commShiftIso (1 : ℤ)).hom.app S ≫ U.hom⟦(1 : ℤ)⟧'
    let N := Triangle.mk ((2 : ℕ) • 𝟙 Scl) j v
    have hN : N ∈ distTriang C := by
      apply isomorphic_distinguished _ (F.map_distinguished T hT)
      refine Triangle.isoMk N (F.mapTriangle.obj T) U.symm U.symm (Iso.refl _)
        ?_ ?_ ?_
      · simp [Syn, C, N, T, Functor.mapTriangle, Functor.map_nsmul,
          F.map_id S, Category.id_comp U.inv,
          Preadditive.comp_nsmul, Preadditive.nsmul_comp]
        erw [CategoryTheory.Category.comp_id]
      · simp [Syn, C, N, T, Functor.mapTriangle, j]
      · simp [Syn, C, N, T, Functor.mapTriangle, v, Category.assoc,
          ← Functor.map_comp, Triangle.mk_obj₁,
          Category.comp_id ((F.commShiftIso (1 : ℤ)).hom.app S)]
        erw [CategoryTheory.Category.comp_id]
        rfl
    have hn := classical_moore_two_ne_zero Scl (F.obj M) j v hN η hη hnotoda
    intro hM
    apply hn
    have h := congrArg F.map hM
    simpa only [Syn, C, Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using h


  have toda_finish
      (hs1 : ∀ a b : BiHom 1 0 (S_0_0 : Syn), a ≠ 0 → b ≠ 0 → a = b)
      (he : lambdaMultiply 2 etaClass ≠ 0)
      (M : Syn) (i : (S_0_0 : Syn) ⟶ M)
      (p : M ⟶ (S_0_0 : Syn)⟦(1 : ℤ)⟧)
      (ε : (S_0_0 : Syn)⟦(1 : ℤ)⟧ ⟶ (S_0_0 : Syn))
      (hT : Triangle.mk ((2 : ℕ) • 𝟙 (S_0_0 : Syn)) i p ∈ distTriang Syn)
      (hMoore : (2 : ℕ) • 𝟙 M = p ≫ ε ≫ i)
      (hM : (2 : ℕ) • 𝟙 M ≠ 0)
      (hproduct : ∀ θ : BiHom 62 64 (S_0_0 : Syn),
        sphereProduct (lambdaMultiply 2 etaClass) θ =
          lambdaMultiply 2 (sphereProduct etaClass θ)) :
      ∀ θ : BiHom 62 64 (S_0_0 : Syn), θ + θ = 0 →
        TripleToda syntheticTwo θ syntheticTwo
          (lambdaMultiply 2 (sphereProduct etaClass θ)) := by
    let S := (S_0_0 : Syn)
    let F := SyntheticCategory.biShift (Syn := Syn) (62,64)
    let F0 := SyntheticCategory.biShift (Syn := Syn) (0,0)
    let Fs := SyntheticCategory.biShift (Syn := Syn) (1,0)
    let FF := SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (62,64)
    letI : F.Additive := D.shiftAdditive (62,64)
    letI : F.CommShift ℤ := D.shiftCommShift (62,64)
    letI : F.IsTriangulated := D.shiftExact (62,64)
    let X := F.obj (F0.obj S)
    let A := F.obj S
    let Q := F.obj M
    let e0 : F0.obj S ≅ S := SyntheticCategory.biShift_zero.app S
    let j : X ≅ A := F.mapIso e0
    let js : X⟦(1 : ℤ)⟧ ≅ A⟦(1 : ℤ)⟧ :=
      (shiftFunctor Syn (1 : ℤ)).mapIso j
    let γ : F.obj (S⟦(1 : ℤ)⟧) ≅ A⟦(1 : ℤ)⟧ :=
      (F.commShiftIso (1 : ℤ)).app S
    let f : X ⟶ A := F.map syntheticTwo
    let ir : A ⟶ Q := F.map i
    let px : Q ⟶ X⟦(1 : ℤ)⟧ := F.map p ≫ γ.hom ≫ js.inv
    let b : X⟦(1 : ℤ)⟧ ⟶ A := js.hom ≫ γ.inv ≫ F.map ε
    let T := Triangle.mk ((2 : ℕ) • 𝟙 S) i p
    let TX := Triangle.mk f ir px
    have hTX : TX ∈ distTriang Syn := by
      apply isomorphic_distinguished _ (F.map_distinguished T hT)
      refine Triangle.isoMk TX (F.mapTriangle.obj T) j (Iso.refl _) (Iso.refl _)
        ?_ ?_ ?_
      · simp [Syn, S, TX, T, f, j, e0, syntheticTwo, Functor.mapTriangle,
          Functor.map_comp, F.map_id S]
        erw [CategoryTheory.Category.comp_id]
      · simp [Syn, S, TX, T, ir, Functor.mapTriangle]
      · change (F.map p ≫ γ.hom ≫ js.inv) ≫ js.hom =
          𝟙 Q ≫ (F.map p ≫ γ.hom)
        simp only [Syn, S, Category.assoc, Iso.inv_hom_id,
          Category.comp_id, Category.id_comp]
    have hQ : (2 : ℕ) • 𝟙 Q = px ≫ b ≫ ir := by
      have h := congrArg F.map hMoore
      simpa only [Syn, S, Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_comp,
        Q, px, b, ir, Category.assoc, Iso.inv_hom_id_assoc,
        Iso.hom_inv_id_assoc] using h

    have hε : ε ≠ 0 := by
      intro hz
      apply hM
      simpa only [Syn, S, hz, zero_comp, comp_zero] using hMoore
    have hFε : F.map ε ≠ 0 := by
      intro hz
      apply hε
      exact FF.map_injective (by simpa only [Syn, S, Functor.map_zero] using hz)
    have hbne : b ≠ 0 := by
      intro hz
      apply hFε
      apply (cancel_epi γ.inv).mp
      apply (cancel_epi js.hom).mp
      simpa only [Syn, S, b, Category.assoc, comp_zero] using hz

    let t : Smn (Syn := Syn) 63 64 ≅ X⟦(1 : ℤ)⟧ :=
      tripleTodaSource 0 0 62 64 0 0
    let μ : F.obj (Fs.obj S) ≅ Smn (Syn := Syn) 63 64 :=
      (SyntheticCategory.biShift_comp (1,0) (62,64)).app S
    let κ : F.obj (Fs.obj S) ≅ X⟦(1 : ℤ)⟧ := μ ≪≫ t
    let e : BiHom 1 0 S := lambdaMultiply 2 etaClass
    let σ : Smn (Syn := Syn) 63 64 ⟶ A := μ.inv ≫ F.map e
    let b0 : BiHom 1 0 S := FF.preimage (κ.hom ≫ b)
    have hb0map : F.map b0 = κ.hom ≫ b := FF.map_preimage _
    have hb0ne : b0 ≠ 0 := by
      intro hz
      apply hbne
      apply (cancel_epi κ.hom).mp
      have hh := hb0map.symm
      simpa only [Syn, S, hz, Functor.map_zero, comp_zero] using hh
    have hb0 : b0 = e := hs1 b0 e hb0ne he
    have hb : b = t.inv ≫ σ := by
      apply (cancel_epi κ.hom).mp
      rw [← hb0map, hb0]
      simp only [Syn, S, κ, σ, Iso.trans_hom, Category.assoc,
        Iso.hom_inv_id_assoc]

    intro θ hθ
    let Z := F0.obj S
    let u : Z ⟶ S := e0.hom
    let g : A ⟶ Z :=
      (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫ F0.map θ
    have hright :
        (SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app S =
          SyntheticCategory.biShift_zero.hom.app A := by
      have hh := D.shiftCoherence.right_unit (62,64) S
      simp only [biShiftAddIso, Iso.trans_hom, NatTrans.comp_app,
        eqToIso.hom, eqToHom_app, eqToHom_refl, Category.comp_id] at hh
      exact hh
    have hgu : g ≫ u = θ := by
      calc
        g ≫ u = (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫
            (F0.map θ ≫ SyntheticCategory.biShift_zero.hom.app S) :=
          Category.assoc _ _ _
        _ = (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫
            (SyntheticCategory.biShift_zero.hom.app A ≫ θ) :=
          congrArg (fun a : F0.obj A ⟶ S =>
            (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫ a)
            (SyntheticCategory.biShift_zero.hom.naturality θ)
        _ = (SyntheticCategory.biShift_comp (62,64) (0,0)).inv.app S ≫
            ((SyntheticCategory.biShift_comp (62,64) (0,0)).hom.app S ≫ θ) := by
          rw [hright]
        _ = θ := ((SyntheticCategory.biShift_comp (62,64) (0,0)).app S).inv_hom_id_assoc θ
    have hg2 : (2 : ℕ) • g = 0 := by
      apply (cancel_mono u).mp
      simpa only [Syn, S, Preadditive.nsmul_comp, hgu, two_nsmul, Preadditive.add_comp, zero_comp] using hθ
    have hf : f = (2 : ℕ) • j.hom := by
      simp only [Syn, S, f, syntheticTwo, Functor.map_comp, Functor.map_nsmul,
        CategoryTheory.Functor.map_id, Preadditive.comp_nsmul, Category.comp_id,
        j, Functor.mapIso_hom, e0, Iso.app_hom]
    have hfg : f ≫ g = 0 := by
      rw [hf, Preadditive.nsmul_comp, ← Preadditive.comp_nsmul, hg2, comp_zero]
    obtain ⟨gbar, hgbar⟩ := TX.yoneda_exact₂ hTX g hfg
    change g = ir ≫ gbar at hgbar
    have hgbar' : ir ≫ gbar = g := hgbar.symm
    have hbar : gbar ≫ syntheticTwo = px ≫ t.inv ≫ sphereProduct e θ := by
      calc
        gbar ≫ syntheticTwo = ((2 : ℕ) • 𝟙 Q) ≫ gbar ≫ u := by
          simp only [Syn, S, syntheticTwo, u, e0, Iso.app_hom, Category.assoc,
            Preadditive.comp_nsmul, Preadditive.nsmul_comp,
            Category.id_comp, Category.comp_id]
        _ = px ≫ b ≫ ir ≫ gbar ≫ u := by
          rw [hQ]
          simp only [Syn, S, Category.assoc]
        _ = px ≫ b ≫ θ := by
          rw [← Category.assoc ir gbar u, hgbar', hgu]
        _ = px ≫ t.inv ≫ sphereProduct e θ := by
          simp only [Syn, S, F, hb, σ, sphereProduct, μ, Iso.app_inv, Category.assoc]
    have hv : sphereProduct e θ = lambdaMultiply 2 (sphereProduct etaClass θ) :=
      hproduct θ
    rw [hv] at hbar
    change Toda.Relation
      (t.inv ≫ lambdaMultiply 2 (sphereProduct etaClass θ)) f g syntheticTwo
    refine ⟨Q, ir, px, hTX, gbar, hgbar', ?_⟩
    simpa only [Syn, S, Category.assoc] using hbar.symm


  obtain ⟨Moore, mooreIncl, mooreProj, epsilon, hMooreTriangle, hMooreFactor⟩ :=
    moore_factor (S_0_0 : Syn) sphere_end_no_two_torsion
  let R := D.recovery.realization
  letI : R.CommShift ℤ := D.realizationShift
  letI : R.IsTriangulated := D.realizationExact
  letI := D.recovery.adjunction.isLeftAdjoint
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts R
  letI := Functor.additive_of_preservesBinaryBiproducts R
  let U : R.obj (S_0_0 : Syn) ≅ (SphereSpectrum : C) :=
    (R.mapIso D.nu.unitIso).symm ≪≫
      D.recovery.nuRealizationIso.app SphereSpectrum
  have hMooreNonzero : (2 : ℕ) • 𝟙 Moore ≠ 0 :=
    realized_moore_two_ne_zero R (S_0_0 : Syn) (SphereSpectrum : C) U
      Moore mooreIncl mooreProj hMooreTriangle
      literature.sources.sourceComparisons.classicalSource.eta classical_eta_double_zero
      classical_toda_nonzero
  exact toda_finish (small_synthetic 0 (by decide)) lambda_eta_nonzero
    Moore mooreIncl mooreProj epsilon hMooreTriangle hMooreFactor hMooreNonzero hstar


end KIP126.Main.AdamsSynthetic.Toda
