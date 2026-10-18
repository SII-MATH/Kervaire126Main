module
import all KIP126.ProofTools.GeneralizedLeibniz.LevelLanguage
import all KIP126.ProofTools.GeneralizedLeibniz.LevelLeftEdge
import all KIP126.ProofTools.GeneralizedLeibniz.BottomTarget
import all KIP126.ProofTools.GeneralizedLeibniz.WeightedReverse

/-! The generalized Leibniz square at an explicit lambda level.
The quotient exponent and all four edge weights retain the chosen level.
Only actual ESS no-crossing conditions on this square are used. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 2400000
set_option Elab.async false

private theorem level_gl_bottom_target_representative (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r l s t : ℤ) (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    {xInfinity : Ambient model X (s+r,t+r-1)}
    {yInfinity : Ambient model Y (s+r+l,t+r-1+l)}
    (W : InfiniteExtensionWitness model X Y f l (s+r) (t+r-1) xInfinity yInfinity)
    (target : (model.family.nu model.nu (Y.obj model.auxiliary)).E₂
      (s+r+l,(t-s)-1+(s+r+l),t+normalizedExponent model.classicalTower f-level+(page+level-1:ℕ)))
    (htarget : HEq target (nuWeightLabel model Y (s+r+l) (t+r-1+l)
      (t+normalizedExponent model.classicalTower f-level+(page+level-1:ℕ))
      (by have := W.length_lower; omega) yInfinity)) :
    HasInfinityRepresentative _ 2
      (s+r+l,(t-s)+(s+r+l),t+normalizedExponent model.classicalTower f-level)
      (regradeE2 (by ext <;> dsimp <;> omega)
        (((essShift (1,-((page+level-1:ℕ):ℤ))).page (.nu Y) 2 (by decide)
          ((t-s)-1,t+normalizedExponent model.classicalTower f-level+(page+level-1:ℕ)) (s+r+l)).hom target))
      (levelGLBottomTarget X Y f page level r l s t hpage hpr W) := by
  let e := normalizedExponent model.classicalTower f
  let k := (r-page).toNat
  let q := page+level-1
  let p : ℤ×ℤ := ((t+r-1)-(s+r),(t+r-1)+e)
  let p' : ℤ×ℤ := ((t-s)-1,t+e-level+(q:ℤ))
  have hk : (k:ℤ)=r-page := Int.toNat_of_nonneg (by omega)
  have hq : (q:ℤ)=(page:ℤ)+level-1 := by dsimp [q]; omega
  have hp : p+(0,-(k:ℤ))=p' := by ext <;> dsimp [p,p'] <;> omega
  let targetRaw : (model.family.obj (model.nu.functor.obj (Y.obj model.auxiliary))).E₂
      (s+r+l,(p+(0,-(k:ℤ))).1+(s+r+l),(p+(0,-(k:ℤ))).2) :=
    regradeE2 (by ext <;> dsimp [p,e,q] <;> omega) target
  have htargetRaw : HEq targetRaw
      (nuWeightLabel model Y (s+r+l) (t+r-1+l) (p.2-k) (by have := W.length_lower; dsimp [p,e]; omega) yInfinity) := by
    apply (regradeE2_heq _ target).trans
    apply htarget.trans
    exact nuWeight_label_heq Y _ _ _ _ _ _ rfl rfl (by dsimp [p,e,q]; omega) _ _ _ _ (HEq.rfl)
  have hsource := infinite_target_nuWeight_heq X Y f l (s+r) (t+r-1) W.length_lower yInfinity
  let iRaw : Tridegree := (s+r+l,(p+(0,-(k:ℤ))).1+(s+r+l),(p+(0,-(k:ℤ))).2)
  let eRaw : ((model.family.obj ((SyntheticObject.nu Y).obj model.nu model.auxiliary)).sequence.ssData iRaw).eInfty :=
    lambdaRawInfinity (.nu Y) k p (s+r+l) W.target
  have hRaw : HEq eRaw (lambdaRawInfinity (.nu Y) k p (s+r+l) W.target) := HEq.rfl
  have hiRaw : iRaw=(s+r+l,t+r-1+l,p.2-k) := by ext <;> dsimp [iRaw,p] <;> omega
  have hraw : HasInfinityRepresentative
      (model.family.obj ((SyntheticObject.nu Y).obj model.nu model.auxiliary)) 2 iRaw targetRaw eRaw := by
    exact lambdaRawInfinity_nu_representative_regraded Y k p (s+r+l) (t+r-1+l)
      (by dsimp [p]; omega) (by dsimp [p,e]; have := W.length_lower; omega) yInfinity
      (infiniteTargetForExtension model X Y f l (s+r) (t+r-1) W.length_lower yInfinity)
      hsource W.target W.target_rep iRaw hiRaw targetRaw htargetRaw eRaw hRaw
  have hbound := ((essShift (1,-(q:ℤ))).representative_iff (.nu Y) 2 (by decide)
    (p+(0,-(k:ℤ))) (s+r+l) targetRaw (lambdaRawInfinity (.nu Y) k p (s+r+l) W.target)).mp hraw
  have hpoint : (s+r+l,(lambdaBoundaryPoint k q p).1+(s+r+l),(lambdaBoundaryPoint k q p).2) =
      (s+r+l,(t-s)+(s+r+l),t+e-level) := by
    have h := level_gl_bottom_point page level r s t e hpage hpr
    exact congrArg (fun v : ℤ×ℤ => (s+r+l,v.1+(s+r+l),v.2)) h
  have hbound := representative_transport hpoint _ _ hbound
  have hshift (a b : ℤ×ℤ) (hab : a=b)
      (x : (model.family.nu model.nu (Y.obj model.auxiliary)).E₂ (s+r+l,a.1+(s+r+l),a.2))
      (y : (model.family.nu model.nu (Y.obj model.auxiliary)).E₂ (s+r+l,b.1+(s+r+l),b.2)) (hxy : HEq x y) :
      HEq (((essShift (1,-(q:ℤ))).page (.nu Y) 2 (by decide) a (s+r+l)).hom x)
        (((essShift (1,-(q:ℤ))).page (.nu Y) 2 (by decide) b (s+r+l)).hom y) := by
    subst b
    cases hxy
    rfl
  let labelA := ((essShift (1,-(q:ℤ))).page (.nu Y) 2 (by decide) (p+(0,-(k:ℤ))) (s+r+l)).hom targetRaw
  let labelB := ((essShift (1,-(q:ℤ))).page (.nu Y) 2 (by decide) p' (s+r+l)).hom target
  have hshiftxy := hshift (p+(0,-(k:ℤ))) p' hp targetRaw target (regradeE2_heq _ target)
  have hlabel := (regradeE2_heq hpoint labelA).trans hshiftxy
  have hcan : (s+r+l,(p'+(1,-(q:ℤ))).1+(s+r+l),(p'+(1,-(q:ℤ))).2) =
      (s+r+l,(t-s)+(s+r+l),t+e-level) := by ext <;> dsimp [p'] <;> omega
  let finalLabel : (model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) (.nu Y)).obj
      model.nu model.auxiliary)).E₂ (s+r+l,(t-s)+(s+r+l),t+e-level) :=
    regradeE2 hcan labelB
  have hfinal : HEq finalLabel labelB := regradeE2_heq hcan labelB
  have hlabel' := hlabel.trans hfinal.symm
  have hlabelEq := eq_of_heq hlabel'
  rw [hlabelEq] at hbound
  exact hbound

/-- AimPaper's four-edge argument with every lambda level retained.
The top edge lies in `Q_(page+level-1)` at weight `t+e(f)-level`;
the bottom edge is the actual propagated infinite extension in that square.
The hypotheses are no-crossing conditions on these exact maps and weights. -/
private theorem generalizedLeibniz_at_level
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r m l s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (xInfinity : Ambient model X (s+r,t+r-1))
    (yInfinity : Ambient model Y (s+r+l,t+r-1+l))
    (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    (hm : (normalizedExponent model.classicalTower f:ℤ)≤m)
    (hmUpper : m≤(page:ℤ)-2+normalizedExponent model.classicalTower f)
    (hl : (normalizedExponent model.classicalTower f:ℤ)≤l)
    (hxInfinity : IsPermanent model X (s+r,t+r-1) xInfinity)
    (hyInfinity : IsPermanent model Y (s+r+l,t+r-1+l) yInfinity)
    (hdx : DifferentialAt model X r (s,t) (s+r,t+r-1) x xInfinity)
    (WFinite : LevelFiniteExtensionWitness X Y f page level m s t x y)
    (WInfinity : InfiniteExtensionWitness model X Y f l (s+r) (t+r-1) xInfinity yInfinity)
    (hsourceCrossing : LevelBoundaryNoCrossing X Y f page level r s t ∨
      LevelFiniteNoCrossing X Y f page level m s t)
    (hbottomCrossing : LevelBottomNoCrossing X Y f page level r l s t) :
    DifferentialAt model Y (r+l-m) (s+m,t+m) (s+r+l,t+r-1+l) y yInfinity := by
  let q : ℕ := page+level-1
  let K : ℕ := (r+l-m-1).toNat
  let d : ℕ := (m-normalizedExponent model.classicalTower f).toNat+level
  have hq : (q:ℤ)=(page:ℤ)+level-1 := by dsimp [q]; omega
  have hK : (K:ℤ)=r+l-m-1 := by dsimp [K]; omega
  have hd : (d:ℤ)=m-normalizedExponent model.classicalTower f+level := by
    dsimp [d]; omega
  have hdq : d<q := by omega
  have hqK : q-d≤K := by omega
  have hindex : (s+r+l,t+r-1+l)=(s+m+(K:ℤ)+1,t+m+(K:ℤ)) := by
    ext <;> omega
  let yExpected : Ambient model Y (s+m+(K:ℤ)+1,t+m+(K:ℤ)) :=
    (eqToHom (congrArg (fun p => Ambient model Y p) hindex)) yInfinity
  have hweight : t+normalizedExponent model.classicalTower f-level=t+m-d := by omega
  have htargetPoint :
      (s+m+(K:ℤ)+1,t+m+(K:ℤ),t+m-d+(q:ℤ)) =
      (s+r+l,(t-s)-1+(s+r+l),t+normalizedExponent model.classicalTower f-level+(q:ℤ)) := by
    ext <;> dsimp <;> omega
  let bottomLabel := regradeE2 htargetPoint
    (nuWeightLabel model Y (s+m+(K:ℤ)+1) (t+m+(K:ℤ))
      (t+m-d+(q:ℤ)) (by omega) yExpected)
  have hbottomLabel := level_gl_bottom_target_representative X Y f page level r l s t
    hpage hpr WInfinity bottomLabel (by
      apply (regradeE2_heq htargetPoint _).trans
      exact nuWeight_label_heq Y
        (s+m+(K:ℤ)+1) (t+m+(K:ℤ)) (t+m-d+(q:ℤ))
        (s+r+l) (t+r-1+l)
        (t+normalizedExponent model.classicalTower f-level+(page+level-1:ℕ))
        (by omega) (by omega) (by omega) (by omega) (by omega)
        yExpected yInfinity (eqToHom_apply_heq _ yInfinity))
  have hleft := level_gl_left_edge X Y f page level r m l s t
    hpage hpr hdx.2 hxInfinity WFinite WInfinity
  obtain ⟨aRight,haRight,hboundary⟩ := absolute_boundary_square_detects_unshifted
    (extensionSourceObject model X Y f) (.nu Y) (model.normalizedMap X Y f).map
    q (t-s,t+normalizedExponent model.classicalTower f-level) s m r l
    WFinite.source WFinite.target
    (levelGLBottomSource X Y f page level r l s t hpage hpr WInfinity)
    (levelGLBottomTarget X Y f page level r l s t hpage hpr WInfinity)
    hleft WFinite.equation
    (level_gl_bottom_extension X Y f page level r l s t hpage hpr WInfinity)
    hsourceCrossing hbottomCrossing _ WFinite.target_rep bottomLabel hbottomLabel
  have hstem : t-s=(t+m)-(s+m) := by omega
  let a := homotopyRegrade hstem hweight aRight
  have ha : Detects (model.convergence (.quotient q (.nu Y))) (s+m,t+m,t+m-d)
      ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) q).pageMap
        2 (s+m,t+m,t+m-d)
        (nuWeightLabel model Y (s+m) (t+m) (t+m-d) (by omega) y)) a := by
    have hp : (s+m,(t-s)+(s+m),t+normalizedExponent model.classicalTower f-level) =
        (s+m,t+m,t+normalizedExponent model.classicalTower f-level) := by
      ext <;> dsimp <;> omega
    have hh := detects_transport hp _ _ haRight
    have weight_transport (w w' : ℤ) (hw : w=w') (hwt : w≤t+m) (hwt' : w'≤t+m)
        (a0 : BiHom ((t+m)-(s+m)) w
          (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q))
        (ha0 : Detects (model.convergence (.quotient q (.nu Y))) (s+m,t+m,w)
          ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) q).pageMap
            2 (s+m,t+m,w) (nuWeightLabel model Y (s+m) (t+m) w hwt y)) a0) :
        Detects (model.convergence (.quotient q (.nu Y))) (s+m,t+m,w')
          ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) q).pageMap
            2 (s+m,t+m,w') (nuWeightLabel model Y (s+m) (t+m) w' hwt' y))
          (homotopyRegrade rfl hw a0) := by
      subst w'
      exact ha0
    have hh' : Detects (model.convergence (.quotient q (.nu Y)))
        (s+m,t+m,t+normalizedExponent model.classicalTower f-level)
        ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) q).pageMap
          2 (s+m,t+m,t+normalizedExponent model.classicalTower f-level)
          (nuWeightLabel model Y (s+m) (t+m)
            (t+normalizedExponent model.classicalTower f-level) (by omega) y))
        (homotopyRegrade hstem rfl aRight) := by
      convert hh using 1
      · simp only [levelFiniteTargetLabel,normalized_regrade_trans]
        rfl
      · simp only [regrade_precomp,←Category.assoc,eqToHom_trans]
    have hfinal := weight_transport _ _ hweight (by omega) (by omega) _ hh'
    convert hfinal using 1
    simp only [a,regrade_precomp,←Category.assoc,eqToHom_trans]
  have hboundary' : Detects (model.convergence (.nu Y))
      (s+m+(K:ℤ)+1,t+m+(K:ℤ),t+m-d+(q:ℤ))
      (nuWeightLabel model Y (s+m+(K:ℤ)+1) (t+m+(K:ℤ))
        (t+m-d+(q:ℤ)) (by omega) yExpected)
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv ((t+m)-(s+m)) (t+m-d) q
          (model.nu.functor.obj (Y.obj model.auxiliary))
          (a ≫ XModLambdaN.proj _ q))) := by
    have hh := detects_transport htargetPoint.symm _ _ hboundary
    have boundary_regrade (m0 m1 w0 w1 : ℤ) (hm0 : m0=m1) (hw0 : w0=w1)
        (a0 : BiHom m0 w0 (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q)) :
        biSuspensionHomEquiv m1 w1 (q:ℤ) _
          (homotopyRegrade hm0 hw0 a0 ≫ XModLambdaN.proj _ q) =
        homotopyRegrade (congrArg (fun z => z-1) hm0)
          (congrArg (fun z : ℤ => z+(q:ℤ)) hw0)
          (biSuspensionHomEquiv m0 w0 (q:ℤ) _ (a0 ≫ XModLambdaN.proj _ q)) := by
      subst m1; subst w1; rfl
    convert hh using 1
    · simp only [bottomLabel,normalized_regrade_trans]
      rfl
    · dsimp only [a]
      dsimp only [SyntheticObject.obj]
      rw [boundary_regrade]
      simp only [regrade_precomp,←Category.assoc,eqToHom_trans]
  have hresult : DifferentialAt model Y ((K:ℤ)+1)
      (s+m,t+m) (s+m+(K:ℤ)+1,t+m+(K:ℤ)) y yExpected :=
    ⟨by omega, finite_detected_boundary_differential_weighted Y q K d hdq hqK
      (s+m) (t+m) y yExpected a ha hboundary'⟩
  have hpageResult : (K:ℤ)+1=r+l-m := by omega
  rw [hpageResult] at hresult
  have undo_transport {p₁ p₂ : ℤ×ℤ} (hp : p₁=p₂)
      (z : Ambient model Y p₁)
      (h : DifferentialAt model Y (r+l-m) (s+m,t+m) p₂ y
        ((eqToHom (congrArg (fun p => Ambient model Y p) hp)) z)) :
      DifferentialAt model Y (r+l-m) (s+m,t+m) p₁ y z := by
    subst p₂
    exact h
  exact undo_transport hindex yInfinity hresult

end
end KIP126.ProofTools.Internal.Leibniz
