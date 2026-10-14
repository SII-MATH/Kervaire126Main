module

public import KIP126.Def.ProofTools.Laws
public import KIP126.Def.ProofTools.Representatives

/-! AimPaper Theorem 6.1. The original GL1 and GL2 geometric proof debts
are retained in place; the representative and Bockstein assembly is proved.
Upstream comparisons are used directly from the fixed Literature interface. -/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Classical.Adams KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem lambda_target_class (Y : ClassicalObject) (s t : ℤ) (k j : ℕ)
    (x : Ambient model Y (s,t)) (hx : IsPermanent model Y (s,t) x)
    (e : ((model.family.nu model.nu (Y.obj model.auxiliary)).sequence.ssData (s,t,t-k)).eInfty)
    (he : HasInfinityRepresentative _ 2 (s,t,t-k) (targetNuLabel model Y s t k x) e) :
    KIP126.Literature.Standard.infinityNuWindow Y (s,t) (t-k-j) (by omega)
      (KIP126.Literature.Standard.infinityLambda (.nu Y) j (s,t) (t-k) e) =
      KIP126.Literature.subquotientClass (KIP126.Literature.permanentCycles model Y (s,t))
        (KIP126.Literature.boundaries model Y (1+t-(t-k-j)) (s,t)) ⟨x,hx⟩ := by
  have hlabel : nuWeightLabel model Y s t (t-k) (by omega) x =
      targetNuLabel model Y s t k x := by
    have hk : (t-(t-k)).toNat = k := by omega
    have transport (a b : ℕ) (hab : a = b)
        (h : (s,t,t-a) = (s,t,t-b)) :
        regradeE2 h (targetNuLabel model Y s t a x) = targetNuLabel model Y s t b x := by
      subst b
      rfl
    exact transport _ k hk _
  have heq := (KIP126.Literature.Standard.eInfinity_nu_labels Y s t (t-k)
    (by omega) x e).mp (by rwa [hlabel])
  have hm := KIP126.Literature.Standard.eInfinity_lambda_nu Y j (s,t) (t-k) (by omega) e
  rw [heq.2] at hm
  exact hm

/-- MainPaper Theorem 6.1. The applied comparison input supplies the synthetic
δ/λ/ρ comparisons; all differential, extension, and no-crossing premises
remain explicit in the conclusion's predicate. -/
public theorem generalizedLeibniz
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) :
    GeneralizedLeibnizLaw model X Y f := by
  intro page r m l s t x y xInfinity yInfinity hpage hpr hm hmUpper hl
    hx hy hxInfinity hyInfinity hdx hf hfInfinity hsourceCrossing htargetCrossing
  have hR : 2 ≤ r + l - m := by omega
  have hy_later : IsCycle model Y (r + l - m - 1)
      (s + m, t + m) y := by
    by_cases hlmin : l = (normalizedExponent model.classicalTower f : ℤ)
    · convert hy using 1
      omega
    have hlstrict : (normalizedExponent model.classicalTower f : ℤ) < l := lt_of_le_of_ne hl (Ne.symm hlmin)
    -- Remaining geometric obligation (GL1), MainPaper 6.1, lines 1625–1650:
    -- synchronize the two source relations in the δ/f square using
    -- hsourceCrossing, then use htargetCrossing on its lower edge. The
    -- resulting δ-extension forces y to survive through d_(r+l-m-1).
    sorry
  let q : ℕ := (r + l - m - 1).toNat
  have hq : 0 < q := by dsimp only [q]; omega
  have hqZ : (q : ℤ) = r + l - m - 1 := Int.toNat_of_nonneg (by omega)
  have hyq : ReachesPage (model.classical.obj (Y.obj model.auxiliary)) (q+1) (s + m, t + m) y := by
    apply (isCycle_iff_reaches model Y (q+1) (by omega) (s+m,t+m) y).mp
    simpa only [add_sub_cancel_right, hqZ] using hy_later
  obtain ⟨a, ha, hda⟩ := KIP126.Literature.Standard.bhs_bockstein Y q hq (s + m) (t + m) y hyq
  have htarget : (s + r + l, t + r - 1 + l) =
      (s + m + (q : ℤ) + 1, t + m + (q : ℤ)) := by
    ext <;> omega
  let yExpected : Ambient model Y
      (s + m + (q : ℤ) + 1, t + m + (q : ℤ)) :=
    (eqToHom (congrArg (fun p => Ambient model Y p) htarget)) yInfinity
  have htarget_congruent : Congruent model Y q
      (s + m + (q : ℤ) + 1, t + m + (q : ℤ))
      yExpected (KIP126.Literature.bocksteinLabel model Y q hq (s + m) (t + m) a) := by
    refine ⟨by omega, ?_⟩
    let W := Classical.choice hfInfinity
    have undo_label {p₁ p₂ : ℤ × ℤ × ℤ} (hp : p₁ = p₂)
        (z : (model.family.nu model.nu (Y.obj model.auxiliary)).E₂ p₁)
        (e : ((model.family.nu model.nu (Y.obj model.auxiliary)).sequence.ssData p₂).eInfty)
        (he : HasInfinityRepresentative _ 2 p₂ (regradeE2 hp z) e) :
        HasInfinityRepresentative (model.family.nu model.nu (Y.obj model.auxiliary)) 2 p₁ z
          ((eqToHom (congrArg (fun p => ((model.family.nu model.nu
            (Y.obj model.auxiliary)).sequence.ssData p).eInfty) hp.symm)) e) := by
      subst p₂
      exact he
    have ht := W.target_rep
    dsimp only [infiniteTargetForExtension] at ht
    have h_ungraded := undo_label _ _ _ ht
    have h_propagated_target := lambda_target_class Y
      (s + r + l) (t + r - 1 + l) (l - normalizedExponent model.classicalTower f).toNat (r - page).toNat
      yInfinity hyInfinity _ h_ungraded
    have h_boundary_le :
        1 + (t + r - 1 + l) - ((t + r - 1 + l) -
          (l - normalizedExponent model.classicalTower f).toNat - (r - page).toNat) ≤ (q : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
      omega
    have h_propagated_target_q := congrArg
      (KIP126.Literature.permanentQuotientMap model Y h_boundary_le
        (s + r + l, t + r - 1 + l)) h_propagated_target
    -- Remaining geometric obligation (GL2), MainPaper 6.1, lines 1644–1652:
    -- h_propagated_target_q gives the λ^(r-page) target label in Z∞/B_q.
    -- Identify the propagated δ-extension target with this Bockstein lift's
    -- label modulo the actual B_q. This is the δ/classical differential
    -- comparison, with the λ exponents r-page and m-e(f) retained.
    -- GL1 supplies the Bockstein lift; GL2 and the proved representative
    -- congruence lemma then give the original differential equation.
    sorry
  have hchosen : DifferentialAt model Y ((q : ℤ) + 1)
      (s + m, t + m) (s + m + (q : ℤ) + 1, t + m + (q : ℤ))
      y (KIP126.Literature.bocksteinLabel model Y q hq (s + m) (t + m) a) := ⟨by omega, hda⟩
  have hfinal := differentialAt_of_congruent model Y hchosen
    (by simpa only [add_sub_cancel_right] using htarget_congruent)
  have hRq : (q : ℤ) + 1 = r + l - m := by omega
  rw [hRq] at hfinal
  have undo_transport {p₁ p₂ : ℤ × ℤ} (hp : p₁ = p₂)
      (z : Ambient model Y p₁)
      (h : DifferentialAt model Y (r + l - m) (s + m, t + m) p₂ y
        ((eqToHom (congrArg (fun p => Ambient model Y p) hp)) z)) :
      DifferentialAt model Y (r + l - m) (s + m, t + m) p₁ y z := by
    subst p₂
    exact h
  exact undo_transport htarget yInfinity hfinal


end
end KIP126.ProofTools.Standard
