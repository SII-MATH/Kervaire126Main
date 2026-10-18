module
import all KIP126.ProofTools.GeneralizedLeibniz.WitnessSquare
import all KIP126.ProofTools.GeneralizedLeibniz.Boundary

/-! AimPaper Theorem 6.1, bottom edge after multiplication by lambda.
The actual filtered shift and lambda maps preserve the prescribed nu target
label, including exponent zero. The final wrapper transports that same
infinity class to the GL square's coordinates; its remaining HEq parameter
is only arithmetic reindexing of the given classical target label. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 600000
set_option Elab.async false

private theorem nu_lambda_representative (Y : ClassicalObject) (k : ℕ)
    (s t w : ℤ) (hw : w ≤ t) (y : Ambient model Y (s,t))
    (e : ((model.family.obj (model.nu.functor.obj (Y.obj model.auxiliary))).sequence.ssData (s,t,w)).eInfty)
    (he : HasInfinityRepresentative _ 2 (s,t,w) (nuWeightLabel model Y s t w hw y) e) :
    HasInfinityRepresentative _ 2 (s,t,w-k) (nuWeightLabel model Y s t (w-k) (by omega) y)
      (KIP126.Literature.Standard.infinityLambda (.nu Y) k (s,t) w e) := by
  obtain ⟨hy,heq⟩ := (KIP126.Literature.Standard.eInfinity_nu_labels Y s t w hw y e).mp he
  apply (KIP126.Literature.Standard.eInfinity_nu_labels Y s t (w-k) (by omega) y _).mpr
  refine ⟨hy,?_⟩
  rw [KIP126.Literature.Standard.eInfinity_lambda_nu Y k (s,t) w hw,heq]
  rfl

private def lambdaRawInfinity (A : SyntheticObject) (k : ℕ)
    (p : ℤ × ℤ) (s : ℤ)
    (x : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty) :
    ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,(p+(0,-(k:ℤ))).1+s,(p+(0,-(k:ℤ))).2)).eInfty := by
  let p' : ℤ×ℤ := p+(0,-(k:ℤ))
  let I : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty ≅
      ((model.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) A).obj model.nu model.auxiliary)).sequence.ssData
      (s,p'.1+s,p'.2)).eInfty :=
    towerInfinityIso (model.convergence A) (model.convergence (.shift (0,-(k:ℤ)) A))
      ((essShift (0,-(k:ℤ))).filtered A p) s
  let L : ((model.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) A).obj model.nu model.auxiliary)).sequence.ssData
      (s,p'.1+s,p'.2)).eInfty ⟶
      ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p'.1+s,p'.2)).eInfty :=
    (model.family.map (lambdaPow k (A.obj model.nu model.auxiliary))).eInftyMap
      (s,p'.1+s,p'.2)
  exact L (I.hom x)

private theorem eqToHom_apply_heq {U V : ModuleCat ℤ} (h : U=V) (x : U) :
    HEq ((eqToHom h) x) x := by
  subst V
  rfl

private theorem infinityShift_stem_heq (A : SyntheticObject) (k : ℕ) (m w s : ℤ)
    (x : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,m+s,w)).eInfty) :
    HEq ((KIP126.Literature.infinityShift model
      KIP126.Literature.Standard.infinityShift_comparison A k (s,m+s) w).hom x)
      ((towerInfinityIso (model.convergence A) (model.convergence (.shift (0,-(k:ℤ)) A))
        ((essShift (0,-(k:ℤ))).filtered A (m,w)) s).hom x) := by
  have hiso (p p' : ℤ×ℤ) (hp : p=p')
      (a : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
      (b : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,p'.1+s,p'.2)).eInfty)
      (hab : HEq a b) :
      HEq ((towerInfinityIso (model.convergence A) (model.convergence (.shift (0,-(k:ℤ)) A))
        ((essShift (0,-(k:ℤ))).filtered A p) s).hom a)
      ((towerInfinityIso (model.convergence A) (model.convergence (.shift (0,-(k:ℤ)) A))
        ((essShift (0,-(k:ℤ))).filtered A p') s).hom b) := by
    subst p'
    cases hab
    rfl
  let p : ℤ×ℤ := (m+s-s,w)
  let U (i : Tridegree) := ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData i).eInfty
  let V (i : Tridegree) := ((model.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) A).obj model.nu model.auxiliary)).sequence.ssData i).eInfty
  have hi : (s,m+s,w)=(s,p.1+s,p.2) := by simp [p]
  have hj : (s,(p+(0,-(k:ℤ))).1+s,(p+(0,-(k:ℤ))).2)=(s,m+s,w-k) := by simp [p,sub_eq_add_neg]
  let a := (eqToHom (congrArg U hi)) x
  let I := towerInfinityIso (model.convergence A) (model.convergence (.shift (0,-(k:ℤ)) A))
    ((essShift (0,-(k:ℤ))).filtered A p) s
  change HEq ((eqToHom (congrArg V hj)) (I.hom a)) _
  exact (eqToHom_apply_heq (congrArg V hj) (I.hom a)).trans
    (hiso p (m,w) (by simp [p]) a x (eqToHom_apply_heq (congrArg U hi) x))

private theorem lambdaRawInfinity_pos (A : SyntheticObject) (k : ℕ) (hk : 0<k)
    (p : ℤ×ℤ) (s : ℤ)
    (e : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty) :
    HEq (lambdaRawInfinity A k p s e)
      (KIP126.Literature.Standard.infinityLambda A k (s,p.1+s) p.2 e) := by
  have hmap {U V : SyntheticSpectrum} (f : U⟶V) (i j : Tridegree) (hij : i=j)
      (a : ((model.family.obj U).sequence.ssData i).eInfty)
      (b : ((model.family.obj U).sequence.ssData j).eInfty) (hab : HEq a b) :
      HEq ((model.family.functor.map f).eInftyMap i a)
        ((model.family.functor.map f).eInftyMap j b) := by
    subst j
    cases hab
    rfl
  rcases p with ⟨m,w⟩
  simp only [lambdaRawInfinity,KIP126.Literature.Standard.infinityLambda,
    KIP126.Literature.InfinityShiftCoordinates.lambdaMap,show k ≠ 0 by omega,↓reduceDIte,ModuleCat.comp_apply]
  exact hmap _ _ _ (by ext <;> dsimp <;> omega) _ _ (infinityShift_stem_heq A k m w s e).symm
private theorem shift_zero_lambda (A : SyntheticSpectrum) (p : ℤ×ℤ)
    (a : BiHom p.1 p.2 A) :
    homotopyRegrade (by simp) (by simp) (shiftHomotopyClass (0,0) p a) ≫ lambdaPow 0 A = a := by
  rw [regrade_precomp]
  simp only [shiftHomotopyClass,lambdaPow,Category.assoc]
  rw [←Category.assoc,←Category.assoc]
  have hu := model.quotients.coherence.right_unit p (S_0_0 : SyntheticSpectrum)
  simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,NatTrans.comp_app] at hu
  have hn := SyntheticCategory.biShift_zero.hom.naturality a
  dsimp only [Functor.id_map,Functor.id_obj] at hn
  rw [Category.assoc,Category.assoc,hn,←Category.assoc]
  erw [←hu]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  simp only [eqToHom_app,←Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp]

private theorem lambdaRawInfinity_zero (A : SyntheticObject) (p : ℤ×ℤ) (s : ℤ)
    (e : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty) :
    HEq (lambdaRawInfinity A 0 p s e) e := by
  let F := model.syntheticTower.filtration (A.obj model.nu model.auxiliary)
  haveI : Epi (F.toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s p)).mp
    inferInstance ((infinityGradedIso (model.convergence A) p s).hom e)
  obtain ⟨br,hbr,hgbr⟩ := shift_frame A (0,0) p s e ar har
  obtain ⟨cr,hcr,hgcr⟩ := tower_map_frame
    (model.convergentMap (.shift (0,0) A) A (lambdaPow 0 (A.obj model.nu model.auxiliary)))
    (p+(0,0)) s _ br hgbr
  have hactual := shift_zero_lambda (A.obj model.nu model.auxiliary) p ((F.F s p).arrow ar)
  rw [hbr] at hcr
  have hh : homotopyRegrade (by simp) (by simp)
      (((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s (p+(0,0))).arrow cr) =
      (F.F s p).arrow ar := by
    rw [←hcr,regrade_comp]
    exact hactual
  have transport_frame (p q : ℤ×ℤ) (h : p=q)
      (a : (Subobject.underlying.obj (F.F s p) : ModuleCat ℤ))
      (b : (Subobject.underlying.obj (F.F s q) : ModuleCat ℤ))
      (ha : homotopyRegrade (congrArg Prod.fst h.symm) (congrArg Prod.snd h.symm)
        ((F.F s q).arrow b) = (F.F s p).arrow a) :
      HEq (F.toAssociatedGraded s q b) (F.toAssociatedGraded s p a) := by
    subst q
    have hb : b=a := (ModuleCat.mono_iff_injective (F.F s p).arrow).mp inferInstance ha
    subst b
    rfl
  have hgr := transport_frame p (p+(0,0)) (by simp) ar cr hh
  rw [har,hgcr] at hgr
  have transport_grade (p q : ℤ×ℤ) (h : p=q)
      (z : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
      (z' : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,q.1+s,q.2)).eInfty)
      (hz : HEq ((infinityGradedIso (model.convergence A) q s).hom z')
        ((infinityGradedIso (model.convergence A) p s).hom z)) : HEq z' z := by
    subst q
    exact heq_of_eq ((infinityGradedIso (model.convergence A) p s).toLinearEquiv.injective (eq_of_heq hz))
  exact transport_grade p (p+(0,0)) (by simp) e _ hgr

private theorem representative_heq_transport (A : SyntheticAdamsSS)
    (i j : Tridegree) (hij : i=j) (x : A.E₂ i) (y : A.E₂ j)
    (e : (A.sequence.ssData i).eInfty) (e' : (A.sequence.ssData j).eInfty)
    (hxy : HEq x y) (hee : HEq e e')
    (he : HasInfinityRepresentative A 2 i x e) :
    HasInfinityRepresentative A 2 j y e' := by
  subst j
  cases hxy
  cases hee
  exact he

private theorem regradeE2_heq {A : SyntheticAdamsSS} {i j : Tridegree} (h : i=j) (x : A.E₂ i) :
    HEq (regradeE2 h x) x := by
  subst j
  rfl

private theorem infinite_target_nuWeight_heq (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (n s t : ℤ) (hn : normalizedExponent model.classicalTower f ≤ n)
    (y : Ambient model Y (s+n,t+n)) :
    HEq (infiniteTargetForExtension model X Y f n s t hn y)
      (nuWeightLabel model Y (s+n) (t+n) (t+normalizedExponent model.classicalTower f) (by omega) y) := by
  unfold infiniteTargetForExtension nuWeightLabel
  apply (regradeE2_heq _ _).trans
  apply HEq.trans _ (regradeE2_heq _ _).symm
  have h : (t+n-(t+normalizedExponent model.classicalTower f)).toNat =
      (n-normalizedExponent model.classicalTower f).toNat := by congr 1; omega
  rw [h]

private theorem lambdaRawInfinity_nu_representative (Y : ClassicalObject) (k : ℕ)
    (p : ℤ×ℤ) (s : ℤ) (hw : p.2≤p.1+s) (y : Ambient model Y (s,p.1+s))
    (e : ((model.family.obj ((SyntheticObject.nu Y).obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (he : HasInfinityRepresentative (model.family.obj ((SyntheticObject.nu Y).obj model.nu model.auxiliary)) 2 (s,p.1+s,p.2) (nuWeightLabel model Y s (p.1+s) p.2 hw y) e)
    (i : Tridegree) (hi : i=(s,p.1+s,p.2-k))
    (target : (model.family.obj ((SyntheticObject.nu Y).obj model.nu model.auxiliary)).E₂ i)
    (htarget : HEq target (nuWeightLabel model Y s (p.1+s) (p.2-k) (by omega) y))
    (eRaw : ((model.family.obj ((SyntheticObject.nu Y).obj model.nu model.auxiliary)).sequence.ssData i).eInfty)
    (hRaw : HEq eRaw (lambdaRawInfinity (.nu Y) k p s e)) :
    HasInfinityRepresentative (model.family.obj ((SyntheticObject.nu Y).obj model.nu model.auxiliary)) 2 i target eRaw := by
  have h := nu_lambda_representative Y k s (p.1+s) p.2 hw y e he
  apply representative_heq_transport _ _ _ hi.symm _ _ _ _ htarget.symm _ h
  apply HEq.trans _ hRaw.symm
  by_cases hk : k=0
  · subst k
    have hz : HEq (KIP126.Literature.Standard.infinityLambda (.nu Y) 0 (s,p.1+s) p.2 e) e := by
      simpa only [KIP126.Literature.Standard.infinityLambda,
        InfinityShiftCoordinates.lambdaMap, ↓reduceDIte] using
        (eqToHom_apply_heq (by simp) e)
    exact hz.trans (lambdaRawInfinity_zero (.nu Y) p s e).symm
  · exact (lambdaRawInfinity_pos (.nu Y) k (by omega) p s e).symm

private theorem nuWeight_label_heq (Y : ClassicalObject) (s t w s' t' w' : ℤ)
    (hs : s=s') (ht : t=t') (hw : w=w') (hwt : w≤t) (hwt' : w'≤t')
    (x : Ambient model Y (s,t)) (x' : Ambient model Y (s',t')) (hx : HEq x x') :
    HEq (nuWeightLabel model Y s t w hwt x) (nuWeightLabel model Y s' t' w' hwt' x') := by
  subst s'; subst t'; subst w'
  cases hx
  rfl

private theorem lambdaRawInfinity_nu_representative_regraded (Y : ClassicalObject) (k : ℕ)
    (p : ℤ×ℤ) (s t : ℤ) (ht : p.1+s=t) (hw : p.2≤t) (y : Ambient model Y (s,t))
    (source : (model.family.obj ((SyntheticObject.nu Y).obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2))
    (hsource : HEq source (nuWeightLabel model Y s t p.2 hw y))
    (e : ((model.family.obj ((SyntheticObject.nu Y).obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (he : HasInfinityRepresentative (model.family.obj ((SyntheticObject.nu Y).obj model.nu model.auxiliary)) 2 (s,p.1+s,p.2) source e)
    (i : Tridegree) (hi : i=(s,t,p.2-k))
    (target : (model.family.obj ((SyntheticObject.nu Y).obj model.nu model.auxiliary)).E₂ i)
    (htarget : HEq target (nuWeightLabel model Y s t (p.2-k) (by omega) y))
    (eRaw : ((model.family.obj ((SyntheticObject.nu Y).obj model.nu model.auxiliary)).sequence.ssData i).eInfty)
    (hRaw : HEq eRaw (lambdaRawInfinity (.nu Y) k p s e)) :
    HasInfinityRepresentative (model.family.obj ((SyntheticObject.nu Y).obj model.nu model.auxiliary)) 2 i target eRaw := by
  subst t
  have hs := eq_of_heq hsource
  rw [hs] at he
  exact lambdaRawInfinity_nu_representative Y k p s hw y e he i hi target htarget eRaw hRaw

private theorem gl_bottom_target_representative (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (r l s t : ℤ) (hpage : 2≤page) (hpr : (page:ℤ)≤r)
    {xInfinity : Ambient model X (s+r,t+r-1)}
    {yInfinity : Ambient model Y (s+r+l,t+r-1+l)}
    (W : InfiniteExtensionWitness model X Y f l (s+r) (t+r-1) xInfinity yInfinity)
    (target : (model.family.nu model.nu (Y.obj model.auxiliary)).E₂
      (s+r+l,(t-s)-1+(s+r+l),t+normalizedExponent model.classicalTower f+(page-1:ℕ)))
    (htarget : HEq target (nuWeightLabel model Y (s+r+l) (t+r-1+l)
      (t+normalizedExponent model.classicalTower f+(page-1:ℕ))
      (by have := W.length_lower; omega) yInfinity)) :
    HasInfinityRepresentative _ 2
      (s+r+l,(t-s)+(s+r+l),t+normalizedExponent model.classicalTower f)
      (regradeE2 (by ext <;> dsimp <;> omega)
        (((essShift (1,-((page-1:ℕ):ℤ))).page (.nu Y) 2 (by decide)
          ((t-s)-1,t+normalizedExponent model.classicalTower f+(page-1:ℕ)) (s+r+l)).hom target))
      (glBottomTarget X Y f page r l s t hpage hpr W) := by
  let e := normalizedExponent model.classicalTower f
  let k := (r-page).toNat
  let q := page-1
  let p : ℤ×ℤ := ((t+r-1)-(s+r),(t+r-1)+e)
  let p' : ℤ×ℤ := ((t-s)-1,t+e+(q:ℤ))
  have hk : (k:ℤ)=r-page := Int.toNat_of_nonneg (by omega)
  have hq : (q:ℤ)=(page:ℤ)-1 := by dsimp [q]; omega
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
      (s+r+l,(t-s)+(s+r+l),t+e) := by
    have h := gl_bottom_point page r s t e hpage hpr
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
      (s+r+l,(t-s)+(s+r+l),t+e) := by ext <;> dsimp [p'] <;> omega
  let finalLabel : (model.family.obj ((SyntheticObject.shift (1,-(q:ℤ)) (.nu Y)).obj
      model.nu model.auxiliary)).E₂ (s+r+l,(t-s)+(s+r+l),t+e) :=
    regradeE2 hcan labelB
  have hfinal : HEq finalLabel labelB := regradeE2_heq hcan labelB
  have hlabel' := hlabel.trans hfinal.symm
  have hlabelEq := eq_of_heq hlabel'
  rw [hlabelEq] at hbound
  exact hbound

end
end KIP126.ProofTools.Internal.Leibniz
