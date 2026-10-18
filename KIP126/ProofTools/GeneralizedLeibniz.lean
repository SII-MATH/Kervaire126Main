module

public import KIP126.ProofTools.Laws
public import KIP126.ProofTools.Representatives
import all KIP126.ProofTools.GeneralizedLeibniz.Boundary
import all KIP126.ProofTools.GeneralizedLeibniz.Square
import all KIP126.ProofTools.GeneralizedLeibniz.WeightedReverse
import all KIP126.ProofTools.GeneralizedLeibniz.RightEdge
import all KIP126.ProofTools.GeneralizedLeibniz.Propagation
import all KIP126.ProofTools.GeneralizedLeibniz.WitnessSquare
import all KIP126.ProofTools.GeneralizedLeibniz.BottomTarget
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingShift
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingFinite
import all KIP126.ProofTools.GeneralizedLeibniz.LeftEdge
import all KIP126.ProofTools.GeneralizedLeibniz.MinimalBottom

/-! AimPaper Theorem 6.1. The original GL1 and GL2 crossing proof debts
are retained in place; the left edge, minimal bottom case, representative
and Bockstein assembly are proved.
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
  let WFinite := Classical.choice hf
  let WInfinity := Classical.choice hfInfinity
  let LeftEdge : Prop := TowerExtensionEquation
    (model.convergentMap (.quotient (page-1) (extensionSourceObject model X Y f))
      (.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
      (Internal.Leibniz.absoluteBoundary
        ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) (page-1)))
    (t-s,t+normalizedExponent model.classicalTower f) s r WFinite.source
    (Internal.Leibniz.glBottomSource X Y f page r l s t hpage hpr WInfinity)
  let SourceNoCrossing : Prop :=
    Internal.Leibniz.TowerNoCrossing (model.convergentMap
      (.quotient (page-1) (extensionSourceObject model X Y f))
      (.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
      (Internal.Leibniz.absoluteBoundary
        ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) (page-1)))
      (t-s,t+normalizedExponent model.classicalTower f) s r ∨
    Internal.Leibniz.TowerNoCrossing (model.convergentMap
      (.quotient (page-1) (extensionSourceObject model X Y f))
      (.quotient (page-1) (.nu Y)) (finiteExtensionMap model X Y f (page-1)))
      (t-s,t+normalizedExponent model.classicalTower f) s m
  let BottomNoCrossing : Prop := Internal.Leibniz.TowerNoCrossing
    (model.convergentMap
      (.shift (1,-((page-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
      (.shift (1,-((page-1:ℕ):ℤ)) (.nu Y))
      ((SyntheticCategory.biShift (1,-((page-1:ℕ):ℤ))).map (model.normalizedMap X Y f).map))
    (t-s,t+normalizedExponent model.classicalTower f) (s+r) l
  have hleftReady : LeftEdge :=
    Internal.Leibniz.gl_left_edge X Y f page r m l s t
      hpage hpr hdx.2 hxInfinity WFinite WInfinity
  have hgeometryMinimal
      (hs : NoCrossingOn model X r page (s,t) ∨
        m ≤ normalizedExponent model.classicalTower f)
      (hl0 : l ≤ normalizedExponent model.classicalTower f) :
      LeftEdge ∧ SourceNoCrossing ∧ BottomNoCrossing := by
    refine ⟨hleftReady, ?_,
      Internal.Leibniz.minimal_length_bottom_tower_no_crossing
        X Y f page r l s t hl0⟩
    rcases hs with hδ | hm0
    · exact Or.inl
        (Internal.Leibniz.classical_noCrossing_shifted_absolute_boundary X page
          (normalizedExponent model.classicalTower f) r s t hδ)
    · exact Or.inr
        (Internal.Leibniz.minimal_length_finite_tower_no_crossing X Y f
          (page-1) (by omega) s t m hm0)
  have hsourceReady : SourceNoCrossing ∨ FiniteNoCrossing model X Y f page m s t := by
    rcases hsourceCrossing with hδcross | hfcross
    · exact Or.inl (Or.inl
        (Internal.Leibniz.classical_noCrossing_shifted_absolute_boundary X page
          (normalizedExponent model.classicalTower f) r s t hδcross))
    · by_cases hmmin : m ≤ normalizedExponent model.classicalTower f
      · exact Or.inl (Or.inr
          (Internal.Leibniz.minimal_length_finite_tower_no_crossing X Y f
            (page-1) (by omega) s t m hmmin))
      · exact Or.inr hfcross
  have boundary_regrade (m0 m1 w0 w1 : ℤ) (hm0 : m0=m1) (hw0 : w0=w1)
      (a0 : BiHom m0 w0 (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) (page-1))) :
      Internal.Mahowald.biSuspensionHomEquiv m1 w1 (page-1:ℕ) _
        (homotopyRegrade hm0 hw0 a0 ≫ XModLambdaN.proj _ (page-1)) =
      homotopyRegrade (congrArg (fun z => z-1) hm0) (congrArg (fun z : ℤ => z+((page-1:ℕ):ℤ)) hw0)
        (Internal.Mahowald.biSuspensionHomEquiv m0 w0 (page-1:ℕ) _
          (a0 ≫ XModLambdaN.proj _ (page-1))) := by
    subst m1; subst w1; rfl
  obtain ⟨hbottom,hbottomSource,hbottomTarget⟩ :=
    Internal.Leibniz.infinite_extension_lambda_boundary_shift X Y f
      (r-page).toNat (page-1) l (s+r) (t+r-1) xInfinity yInfinity WInfinity
  have hbottomPoint := Internal.Leibniz.gl_bottom_point page r s t
    (normalizedExponent model.classicalTower f) hpage hpr
  have hR : 2 ≤ r + l - m := by omega
  have hy_later : IsCycle model Y (r + l - m - 1)
      (s + m, t + m) y := by
    by_cases hlmin : l = (normalizedExponent model.classicalTower f : ℤ)
    · convert hy using 1
      omega
    have hlstrict : (normalizedExponent model.classicalTower f : ℤ) < l := lt_of_le_of_ne hl (Ne.symm hlmin)
    let k : ℕ := (r - 1).toNat
    have hkZ : (k : ℤ) = r - 1 := Int.toNat_of_nonneg (by omega)
    have hindex : (s + r, t + r - 1) = (s + k + 1, t + k) := by
      ext <;> omega
    let xInfinity' : Ambient model X (s + k + 1, t + k) :=
      (eqToHom (congrArg (fun p => Ambient model X p) hindex)) xInfinity
    have transport {p p' : ℤ × ℤ} (hp : p = p') (z : Ambient model X p)
        (hz : IsPermanent model X p z)
        (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary)) r (s,t) p x z) :
        IsPermanent model X p' ((eqToHom (congrArg (fun q => Ambient model X q) hp)) z) ∧
          HasDifferential (model.classical.obj (X.obj model.auxiliary)) r (s,t) p' x
            ((eqToHom (congrArg (fun q => Ambient model X q) hp)) z) := by
      subst p'
      exact ⟨hz,hd⟩
    obtain ⟨hInfinity',hd'⟩ := transport hindex xInfinity hxInfinity hdx.2
    have hdNat : HasDifferential (model.classical.obj (X.obj model.auxiliary))
        (k+1) (s,t) (s+k+1,t+k) x xInfinity' := by
      convert hd' using 1
      omega
    obtain ⟨aδ,haδ,hδ⟩ := Internal.Leibniz.differential_absolute_boundary X
      (page-1) k (by omega) (by omega) s t x xInfinity' hdNat hInfinity'
    have hδsquare := Internal.Leibniz.absoluteBoundary_natural
      (model.normalizedMap X Y f).map (page-1)
    suffices hright : ∃ a : BiHom ((t+m)-(s+m))
        (t+normalizedExponent model.classicalTower f)
        (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) (page-1)),
        Detects (model.convergence (.quotient (page-1) (.nu Y)))
          (s+m,t+m,t+normalizedExponent model.classicalTower f)
          (regradeE2 (by exact Prod.ext rfl (Prod.ext (by change (t-s)+(s+m)=t+m; omega) rfl))
            (finiteTargetForExtension model X Y f (page-1) m s t hm y)) a ∧
        FiltrationAtLeast model.syntheticTower (s+r+l)
          (Internal.Mahowald.biSuspensionHomEquiv ((t+m)-(s+m))
            (t+normalizedExponent model.classicalTower f) ((page-1:ℕ):ℤ)
            (model.nu.functor.obj (Y.obj model.auxiliary))
            (a ≫ XModLambdaN.proj _ (page-1))) by
      obtain ⟨a,ha,hfil⟩ := hright
      exact Internal.Leibniz.gl1_right_edge_survival X Y f page r m l s t
        hpage hpr hm hmUpper hlstrict y a ha hfil
    suffices hgeometry : LeftEdge ∧ SourceNoCrossing ∧ BottomNoCrossing by
      obtain ⟨hleft,hsource,hbottomCrossing⟩ := hgeometry
      obtain ⟨aRight,haRight,hboundary⟩ := Internal.Leibniz.gl_witness_square_high_filtration
        X Y f page r m l s t hpage hpr WFinite WInfinity hleft hsource hbottomCrossing
      let hmStem : t-s=(t+m)-(s+m) := by omega
      refine ⟨homotopyRegrade hmStem rfl aRight,?_,?_⟩
      · have hp : (s+m,(t-s)+(s+m),t+normalizedExponent model.classicalTower f) =
            (s+m,t+m,t+normalizedExponent model.classicalTower f) := by exact Prod.ext rfl (Prod.ext (by change (t-s)+(s+m)=t+m; omega) rfl)
        have hh := Internal.Mahowald.detects_transport hp _ _ haRight
        convert hh using 1
        simp only [Internal.Mahowald.regrade_precomp, ←Category.assoc, eqToHom_trans]
      · rw [boundary_regrade]
        exact (Internal.Leibniz.regrade_filtration_iff _ _ _ _).mpr hboundary
    -- GL1: the specified left edge is proved. The remaining obligation is
    -- the two no-crossing inputs in the strict bottom-length case.
    -- hsourceReady already handles the classical-delta and minimal-f cases.
    -- The witness square now constructs the common right representative;
    -- its high boundary feeds the proved survival argument above.
    refine ⟨hleftReady, ?_⟩
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
    let W := WInfinity
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
    let d : ℕ := (m - normalizedExponent model.classicalTower f).toNat
    have hdpage : d < page-1 := by dsimp only [d]; omega
    have hiq : page-1-d ≤ q := by dsimp only [d]; omega
    suffices hδ : ∃ aRight : BiHom ((t+m)-(s+m)) (t+m-d)
        (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) (page-1)),
        Detects (model.convergence (.quotient (page-1) (.nu Y)))
          (s+m,t+m,t+m-d)
          ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary))
            (page-1)).pageMap 2 (s+m,t+m,t+m-d)
            (nuWeightLabel model Y (s+m) (t+m) (t+m-d) (by omega) y)) aRight ∧
        Detects (model.convergence (.nu Y))
          (s+m+(q:ℤ)+1,t+m+(q:ℤ),t+m-d+((page-1:ℕ):ℤ))
          (nuWeightLabel model Y (s+m+(q:ℤ)+1) (t+m+(q:ℤ))
            (t+m-d+((page-1:ℕ):ℤ)) (by omega) yExpected)
          (homotopyRegrade (by dsimp; omega) rfl
            (Internal.Mahowald.biSuspensionHomEquiv ((t+m)-(s+m)) (t+m-d) (page-1:ℕ)
              (model.nu.functor.obj (Y.obj model.auxiliary))
              (aRight ≫ XModLambdaN.proj _ (page-1)))) by
      obtain ⟨aRight,haRight,hδRight⟩ := hδ
      have hdTarget := Internal.Leibniz.finite_detected_boundary_differential_weighted
        Y (page-1) q d hdpage hiq (s+m) (t+m) y yExpected aRight haRight hδRight
      have hc := Internal.Mahowald.differential_targets_sub_mem_boundary model Y
        ((q:ℤ)+1) (s+m,t+m) (s+m+(q:ℤ)+1,t+m+(q:ℤ)) y yExpected
        (KIP126.Literature.bocksteinLabel model Y q hq (s+m) (t+m) a) hdTarget hda
      simpa only [add_sub_cancel_right] using hc
    have hwSource : t+normalizedExponent model.classicalTower f = t+m-d := by
      dsimp only [d]
      omega
    have hpTarget :
        (s+m+(q:ℤ)+1,t+m+(q:ℤ),t+m-d+((page-1:ℕ):ℤ)) =
        (s+r+l,(t-s)-1+(s+r+l),t+normalizedExponent model.classicalTower f+((page-1:ℕ):ℤ)) := by
      ext <;> dsimp <;> omega
    let bottomLabel := regradeE2 hpTarget
      (nuWeightLabel model Y (s+m+(q:ℤ)+1) (t+m+(q:ℤ))
        (t+m-d+((page-1:ℕ):ℤ)) (by omega) yExpected)
    let BottomLabel : Prop := HasInfinityRepresentative _ 2
      (s+r+l,(t-s)+(s+r+l),t+normalizedExponent model.classicalTower f)
      (regradeE2 (by ext <;> dsimp <;> omega)
        (((essShift (1,-((page-1:ℕ):ℤ))).page (.nu Y) 2 (by decide)
          ((t-s)-1,t+normalizedExponent model.classicalTower f+((page-1:ℕ):ℤ)) (s+r+l)).hom bottomLabel))
      (Internal.Leibniz.glBottomTarget X Y f page r l s t hpage hpr WInfinity)
    have hbottomLabel : BottomLabel := by
      apply Internal.Leibniz.gl_bottom_target_representative
        X Y f page r l s t hpage hpr WInfinity bottomLabel
      apply (Internal.Leibniz.regradeE2_heq hpTarget _).trans
      exact Internal.Leibniz.nuWeight_label_heq Y
        (s+m+(q:ℤ)+1) (t+m+(q:ℤ)) (t+m-d+((page-1:ℕ):ℤ))
        (s+r+l) (t+r-1+l)
        (t+normalizedExponent model.classicalTower f+((page-1:ℕ):ℤ))
        (by omega) (by omega) (by omega) (by omega) (by omega)
        yExpected yInfinity (Internal.Leibniz.eqToHom_apply_heq _ yInfinity)
    suffices hgeometry : LeftEdge ∧ SourceNoCrossing ∧ BottomNoCrossing by
      obtain ⟨hleft,hsource,hbottomCrossing⟩ := hgeometry
      obtain ⟨aRight,haRight,hboundary⟩ := Internal.Leibniz.gl_witness_square_detects
        X Y f page r m l s t hpage hpr WFinite WInfinity hleft hsource hbottomCrossing
        bottomLabel hbottomLabel
      have hmStem : t-s=(t+m)-(s+m) := by omega
      refine ⟨homotopyRegrade hmStem hwSource aRight,?_,?_⟩
      · have hpSource : (s+m,(t-s)+(s+m),t+normalizedExponent model.classicalTower f) =
            (s+m,t+m,t+normalizedExponent model.classicalTower f) := by exact Prod.ext rfl (Prod.ext (by change (t-s)+(s+m)=t+m; omega) rfl)
        have hh := Internal.Mahowald.detects_transport hpSource _ _ haRight
        rw [Internal.Leibniz.finite_extension_target_weight_label] at hh
        have weight_transport (w w' : ℤ) (hw : w=w') (hwt : w≤t+m) (hwt' : w'≤t+m)
            (a0 : BiHom ((t+m)-(s+m)) w
              (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) (page-1)))
            (ha0 : Detects (model.convergence (.quotient (page-1) (.nu Y))) (s+m,t+m,w)
              ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary))
                (page-1)).pageMap 2 (s+m,t+m,w)
                (nuWeightLabel model Y (s+m) (t+m) w hwt y)) a0) :
            Detects (model.convergence (.quotient (page-1) (.nu Y))) (s+m,t+m,w')
              ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary))
                (page-1)).pageMap 2 (s+m,t+m,w')
                (nuWeightLabel model Y (s+m) (t+m) w' hwt' y))
              (homotopyRegrade rfl hw a0) := by
          subst w'
          exact ha0
        have hh' := weight_transport _ _ hwSource (by omega) (by omega) _ hh
        convert hh' using 1
        simp only [Internal.Mahowald.regrade_precomp, ←Category.assoc, eqToHom_trans]
      · have hh := Internal.Mahowald.detects_transport hpTarget.symm _ _ hboundary
        convert hh using 1
        · have cancel {i j : Tridegree} (h : i=j)
              (z : (model.family.nu model.nu (Y.obj model.auxiliary)).E₂ i) :
              regradeE2 h.symm (regradeE2 h z)=z := by subst j; rfl
          exact (cancel hpTarget _).symm
        · rw [boundary_regrade]
          simp only [Internal.Mahowald.regrade_precomp, ←Category.assoc, eqToHom_trans]
    -- GL2: the minimal bottom case closes with either a classical boundary
    -- no-crossing input or a minimal finite length. The remaining branch
    -- needs the original crossing conditions converted to the actual edges.
    -- The propagated bottom target already has the prescribed classical label.
    -- The witness square now produces one aRight with both detections;
    -- weighted reverse performs rho lifting, lambda division and B_q readout.
    by_cases hminimal : (NoCrossingOn model X r page (s,t) ∨
        m ≤ normalizedExponent model.classicalTower f) ∧
        l ≤ normalizedExponent model.classicalTower f
    · exact hgeometryMinimal hminimal.1 hminimal.2
    · refine ⟨hleftReady, ?_⟩
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
