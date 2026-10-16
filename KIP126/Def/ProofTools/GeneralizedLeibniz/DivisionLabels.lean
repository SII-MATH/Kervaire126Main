module
import all KIP126.Def.ProofTools.GeneralizedLeibniz.Reverse
import all KIP126.Def.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.Def.ProofTools.GeneralizedLeibniz.CrossingDelta

/-! AimPaper's boundary indeterminacy after finite lambda division.
The actual lambda map carries the first label of a chosen smaller-quotient
representative to its finite target label. Equal detected representatives
therefore identify the original label modulo B_(d+1). This comparison concerns
the source label. Detection supplies an actual lambda preimage, including
the zero-exponent case; its first label is chosen internally, and source
boundary ambiguity preserves the classical differential. Compatibility of
the divided absolute-boundary target remains a separate reverse GL step. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.Core.SpectralSequence.FinitePageCalculus
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

private def finiteLambdaClass (X : ClassicalObject) (q d : ℕ) (hd : 0 < d) (hdq : d < q)
    (s t : ℤ)
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d))) :
    BiHom (t-s) (t-d) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) :=
  homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
    (shiftHomotopyClass (0,-(d:ℤ)) (t-s,t) b) ≫
    ((model.quotients.tower _).triangle hd hdq).lambdaMap

private theorem finite_quotient_lambda_detects (X : ClassicalObject)
    (q d : ℕ) (hd : 0 < d) (hdq : d < q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)))
    (hb : b ≫ (model.quotients.tower _).rho 1 (q-d) (by omega) =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-d)
      (finiteTargetLabel model X q s t d x) (finiteLambdaClass X q d hd hdq s t b) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let n := q-d
  have hn : 0 < n := by dsimp [n]; omega
  have ha := first_label_detects_unshifted X n hn s t x b hb
  have hx := first_label_lift_cycles X n hn s t x b hb
  have hsource : (s,t,t)=(s,(t-s)+s,t) := by simp
  have hstem := detects_transport hsource _ _ ha
  let L : ((SyntheticObject.shift (0,-(d:ℤ)) (.quotient n (.nu X))).obj model.nu model.auxiliary) ⟶
      ((SyntheticObject.quotient q (.nu X)).obj model.nu model.auxiliary) :=
    ((model.quotients.tower A).triangle hd hdq).lambdaMap
  have hmap := shifted_map_detects (.quotient n (.nu X)) (.quotient q (.nu X))
    (0,-(d:ℤ)) (t-s,t) s L
    (regradeE2 hsource (regradeE2 (by simp) (finiteTargetLabel model X n s t 0 x))) b hstem
  have hindex : (s,((t-s,t)+(0,-(d:ℤ))).1+s,((t-s,t)+(0,-(d:ℤ))).2) =
      (s,t,t-d) := by ext <;> simp [sub_eq_add_neg]
  have hmap := detects_transport hindex _ _ hmap
  obtain ⟨e,he,ar,har,hgar⟩ := hmap
  obtain ⟨e0,he0,_⟩ := ha
  have heStem := representative_transport hsource _ _ he0
  have heMap := shifted_representative_map (.quotient n (.nu X)) (.quotient q (.nu X))
    (0,-(d:ℤ)) (t-s,t) s L _ _ heStem
  have heMap := representative_transport hindex _ _ heMap
  have heq := he.unique heMap
  have heq' : e = KIP126.Literature.Standard.infinityFiniteLambda X q d hdq (s,t) t e0 := by
    convert heq using 1
    simp only [KIP126.Literature.Standard.infinityFiniteLambda,
      InfinityShiftCoordinates.finiteLambdaMap, show d ≠ 0 by omega, ↓reduceDIte,
      InfinityShiftCoordinates.shift, infinityShift, Iso.trans_hom, ModuleCat.comp_apply,
      eqToIso.hom, KIP126.Literature.Standard.infinityShiftData,
      KIP126.Literature.Standard.infinityShift_comparison]
    rw [infinity_map_regrade L hindex]
    rfl
  have hlabel : HasInfinityRepresentative _ 2 (s,t,t-d)
      (finiteTargetLabel model X q s t d x)
      (KIP126.Literature.Standard.infinityFiniteLambda X q d hdq (s,t) t e0) := by
    apply (finite_target_label_iff X q (by omega) s t d hdq
      ⟨x,by convert hx using 1; congr 1; dsimp [n]; omega⟩ _).mpr
    rw [KIP126.Literature.Standard.eInfinity_lambda_finite X q d hdq (s,t) t (by dsimp [n] at hn; omega)]
    have he0' := (KIP126.Literature.Standard.eInfinity_finite_labels X n hn s t t
      (by constructor <;> dsimp [n] at * <;> omega) x e0).mp
      ((congrArg (fun z => HasInfinityRepresentative _ 2 (s,t,t) z e0)
        (zero_weight_label X n s t x)).mpr he0)
    rw [he0'.2]
    rfl
  have heFinal : HasInfinityRepresentative _ 2 (s,t,t-d)
      (finiteTargetLabel model X q s t d x) e := by
    simpa only [heq'] using hlabel
  refine ⟨e,heFinal,ar,?_,hgar⟩
  convert har using 1
  simp only [finiteLambdaClass,regrade_precomp,Category.assoc]
  simp only [←Category.assoc,eqToHom_trans]
  rfl

private theorem finite_detected_labels_congruent (X : ClassicalObject)
    (q : ℕ) (hq : 0 < q) (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < q)
    (x y : Ambient model X (s,t))
    (a : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hx : Detects (model.convergence (.quotient q (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) x)) a)
    (hy : Detects (model.convergence (.quotient q (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) y)) a) :
    x-y ∈ boundaries model X (1+t-w) (s,t) := by
  obtain ⟨ex,hex,ax,hax,hgx⟩ := hx
  obtain ⟨ey,hey,ay,hay,hgy⟩ := hy
  have hab : ax=ay := (ModuleCat.mono_iff_injective
    ((model.syntheticTower.filtration (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)).F s (t-s,w)).arrow).mp
      inferInstance (hax.trans hay.symm)
  have heq : ex=ey := ((model.convergence (.quotient q (.nu X))).identification (s,t,w)).toLinearEquiv.injective (by
    change ((model.convergence (.quotient q (.nu X))).identification (s,t,w)).hom ex =
      ((model.convergence (.quotient q (.nu X))).identification (s,t,w)).hom ey
    rw [hgx,hgy,hab])
  obtain ⟨hxc,hxl⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels X q hq s t w hw x ex).mp hex
  obtain ⟨hyc,hyl⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels X q hq s t w hw y ey).mp hey
  have hequal : subquotientClass (cycles model X (q-t+w) (s,t)) (boundaries model X (1+t-w) (s,t)) ⟨x,hxc⟩ =
      subquotientClass (cycles model X (q-t+w) (s,t)) (boundaries model X (1+t-w) (s,t)) ⟨y,hyc⟩ := by
    rw [←hxl,←hyl,heq]
  have hzero : subquotientClass (cycles model X (q-t+w) (s,t)) (boundaries model X (1+t-w) (s,t))
      (⟨x,hxc⟩-⟨y,hyc⟩) = 0 := by rw [map_sub,hequal,sub_self]
  exact (CrossingLabels.subquotient_zero_iff _ _ _).mp hzero

private theorem finite_lambda_first_label_congruent (X : ClassicalObject)
    (q d : ℕ) (hd : 0 < d) (hdq : d < q) (s t : ℤ)
    (x x0 : Ambient model X (s,t))
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)))
    (hb : b ≫ (model.quotients.tower _).rho 1 (q-d) (by omega) =
      firstLabel model X s t x0 ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (a : BiHom (t-s) (t-d) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-d)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,t-d)
        (nuWeightLabel model X s t (t-d) (by omega) x)) a)
    (hlam : finiteLambdaClass X q d hd hdq s t b = a) :
    x-x0 ∈ boundaries model X (d+1) (s,t) := by
  have hbdet := finite_quotient_lambda_detects X q d hd hdq s t x0 b hb
  rw [hlam] at hbdet
  have hlabel : nuWeightLabel model X s t (t-d) (by omega) x0 =
      targetNuLabel model X s t d x0 := by
    have hd' : (t-(t-d)).toNat = d := by omega
    have transport (a b : ℕ) (hab : a=b)
        (h : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 h (targetNuLabel model X s t a x0) = targetNuLabel model X s t b x0 := by
      subst b
      rfl
    exact transport _ d hd' _
  have hbdet' : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-d)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,t-d)
        (nuWeightLabel model X s t (t-d) (by omega) x0)) a := by
    rw [hlabel]
    exact hbdet
  have h := finite_detected_labels_congruent X q (by omega) s t (t-d)
    (by omega) x x0 a ha hbdet'
  convert h using 1
  congr 1
  omega

private theorem finiteLambdaClass_vertical (X : ClassicalObject)
    (q d : ℕ) (hd : 0 < d) (hdq : d < q) (s t : ℤ)
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d))) :
    finiteLambdaClass X q d hd hdq s t b =
      verticalShiftEquiv _ d (t-s) (t-d) (homotopyRegrade rfl (by omega) b) ≫
        ((model.quotients.tower _).triangle hd hdq).lambdaMap := by
  have transport (A : SyntheticSpectrum) (m t w : ℤ) (h : t=w+d)
      (b : BiHom m t A) :
      homotopyRegrade (by simp) (by simp [h])
        (shiftHomotopyClass (0,-(d:ℤ)) (m,t) b) =
        verticalShiftEquiv A d m w (homotopyRegrade rfl h b) := by
    subst t
    simp [verticalShiftEquiv, AddEquiv.trans_apply, regradeAddEquiv,
      suspInvarianceAddEquiv, susp_invariance, shiftHomotopyClass, Iso.homCongr,
      homotopyRegrade]
  exact congrArg (fun f => f ≫ ((model.quotients.tower _).triangle hd hdq).lambdaMap)
    (transport _ (t-s) t (t-d) (by omega) b)

private theorem finite_lambda_division_first_label_congruent (X : ClassicalObject)
    (q d : ℕ) (hd : 0 < d) (hdq : d < q) (s t : ℤ)
    (x x0 : Ambient model X (s,t))
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)))
    (hb : b ≫ (model.quotients.tower _).rho 1 (q-d) (by omega) =
      firstLabel model X s t x0 ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (a : BiHom (t-s) (t-d) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-d)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,t-d)
        (nuWeightLabel model X s t (t-d) (by omega) x)) a)
    (hlam : verticalShiftEquiv _ d (t-s) (t-d) (homotopyRegrade rfl (by omega) b) ≫
        ((model.quotients.tower _).triangle hd hdq).lambdaMap = a) :
    x-x0 ∈ boundaries model X (d+1) (s,t) := by
  apply finite_lambda_first_label_congruent X q d hd hdq s t x x0 b hb a ha
  exact (finiteLambdaClass_vertical X q d hd hdq s t b).trans hlam

private theorem differential_of_source_boundary_congruent (X : ClassicalObject)
    (r b : ℤ) (p q : Bidegree)
    (x x0 : Ambient model X p) (y : Ambient model X q)
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary)) r p q x0 y)
    (hx : x-x0 ∈ boundaries model X b p) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary)) r p q x y := by
  let E := model.classical.obj (X.obj model.auxiliary)
  obtain ⟨hdeg,xr,yr,hxr,hyr,hdr⟩ := hd
  have hr : 2 ≤ r := hxr.1
  have hnext : ReachesPage E (r+1) p (x-x0) :=
    (isCycle_iff_reaches model X (r+1) (by omega) p (x-x0)).mp
      ⟨by omega, by
        simpa only [add_sub_cancel_right] using boundaries_le_cycles model X p b r hx⟩
  obtain ⟨zr,hzr⟩ := reaches_earlier hr (by omega : r≤r+1) hnext
  have hdz : E.d r p zr = 0 := represents_d_zero_of_later
    (by change (model.classical.obj (X.obj model.auxiliary)).r₀ ≤ r
        rw [model.classical.firstPage]
        exact hr) (by omega : r<r+1) hzr hnext
  refine ⟨hdeg,xr+zr,yr,?_,hyr,?_⟩
  · have hh := middle_add hxr hzr
    have he : x0+(x-x0)=x := by abel
    simpa only [he] using hh
  · rw [map_add,hdr]
    change yr + (eqToHom (congrArg (E.Page r) hdeg)) (E.d r p zr) = yr
    rw [hdz,map_zero,add_zero]

private theorem boundary_detects_differential_of_source_congruent (X : ClassicalObject)
    (i k : ℕ) (hi : 0 < i) (hik : i ≤ k) (s t b : ℤ)
    (x x0 : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : a ≫ (model.quotients.tower _).rho 1 i hi =
      firstLabel model X s t x0 ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (hx : x-x0 ∈ boundaries model X b (s,t))
    (hy : Detects (model.convergence (.nu X)) (s+k+1,t+k,t+i)
      (nuWeightLabel model X (s+k+1) (t+k) (t+i) (by omega) y)
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv (t-s) t i (model.nu.functor.obj (X.obj model.auxiliary))
          (a ≫ XModLambdaN.proj _ i)))) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  exact differential_of_source_boundary_congruent X (k+1) b (s,t) (s+k+1,t+k) x x0 y
    (boundary_detects_differential X i k hi hik s t x0 y a ha hy) hx


private theorem finite_lambda_division_detects_differential (X : ClassicalObject)
    (q d k : ℕ) (hd : 0 < d) (hdq : d < q) (hqdk : q-d ≤ k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (a : BiHom (t-s) (t-d) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-d)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,t-d)
        (nuWeightLabel model X s t (t-d) (by omega) x)) a)
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)))
    (hlam : verticalShiftEquiv _ d (t-s) (t-d) (homotopyRegrade rfl (by omega) b) ≫
        ((model.quotients.tower _).triangle hd hdq).lambdaMap = a)
    (hy : Detects (model.convergence (.nu X)) (s+k+1,t+k,t+(q-d:ℕ))
      (nuWeightLabel model X (s+k+1) (t+k) (t+(q-d:ℕ)) (by omega) y)
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv (t-s) t (q-d:ℕ) (model.nu.functor.obj (X.obj model.auxiliary))
          (b ≫ XModLambdaN.proj _ (q-d))))) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  obtain ⟨x0,hx0⟩ := quotient_first_label_exists X (q-d) (by omega) s t b
  have hcong := finite_lambda_division_first_label_congruent X q d hd hdq s t x x0 b hx0 a ha hlam
  exact boundary_detects_differential_of_source_congruent X (q-d) k (by omega) hqdk
    s t (d+1) x x0 y b hx0 hcong hy

private theorem finite_detected_boundary_differential (X : ClassicalObject)
    (i k : ℕ) (hi : 0 < i) (hik : i ≤ k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : Detects (model.convergence (.quotient i (.nu X))) (s,t,t)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) i).pageMap 2 (s,t,t)
        (nuWeightLabel model X s t t (by omega) x)) a)
    (hy : Detects (model.convergence (.nu X)) (s+k+1,t+k,t+i)
      (nuWeightLabel model X (s+k+1) (t+k) (t+i) (by omega) y)
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv (t-s) t i (model.nu.functor.obj (X.obj model.auxiliary))
          (a ≫ XModLambdaN.proj _ i)))) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  obtain ⟨x0,hx0⟩ := quotient_first_label_exists X i hi s t a
  have hdet0 := first_label_detects_unshifted X i hi s t x0 a hx0
  rw [←zero_weight_label X i s t x0] at hdet0
  have hcong := finite_detected_labels_congruent X i hi s t t (by omega) x x0 a ha hdet0
  exact boundary_detects_differential_of_source_congruent X i k hi hik s t (1+t-t)
    x x0 y a hx0 hcong hy

private theorem finite_detected_source_division (X : ClassicalObject)
    (q d : ℕ) (hd : 0 < d) (hdq : d < q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t-d) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-d)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,t-d)
        (nuWeightLabel model X s t (t-d) (by omega) x)) a) :
    ∃ b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)),
      verticalShiftEquiv _ d (t-s) (t-d) (homotopyRegrade rfl (by omega) b) ≫
        ((model.quotients.tower _).triangle hd hdq).lambdaMap = a := by
  have hfil := detects_filtration (.quotient q (.nu X)) (s,t,t-d) _ _ ha
  obtain ⟨bS,hbS⟩ := finite_source_division X d q hd hdq (t-s) (t-d) s (by omega) a hfil
  let e := verticalShiftEquiv (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)) d (t-s) (t-d)
  let b := homotopyRegrade rfl (by omega : t-d+d=t) (e.symm bS)
  refine ⟨b,?_⟩
  have hback : homotopyRegrade rfl (by omega : t=t-d+d) b = e.symm bS := by
    have cancel (A : SyntheticSpectrum) (m w w' : ℤ) (hw : w=w') (hw' : w'=w)
        (c : BiHom m w A) :
        homotopyRegrade rfl hw' (homotopyRegrade rfl hw c)=c := by subst w'; rfl
    exact cancel _ _ _ _ _ _ (e.symm bS)
  rw [hback]
  exact (congrArg (fun z => z ≫ ((model.quotients.tower _).triangle hd hdq).lambdaMap)
    (e.apply_symm_apply bS)).trans hbS

private def finiteLambdaDivisionClass (X : ClassicalObject) (q d : ℕ) (hdq : d < q)
    (s t : ℤ)
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d))) :
    BiHom (t-s) (t-d) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) := by
  by_cases hd : d=0
  · subst d
    exact homotopyRegrade rfl (by simp) b
  · exact finiteLambdaClass X q d (by omega) hdq s t b

private theorem finite_detected_source_division_uniform (X : ClassicalObject)
    (q d : ℕ) (hdq : d < q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t-d) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-d)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,t-d)
        (nuWeightLabel model X s t (t-d) (by omega) x)) a) :
    ∃ b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)),
      finiteLambdaDivisionClass X q d hdq s t b = a := by
  by_cases hd : d=0
  · subst d
    refine ⟨homotopyRegrade rfl (by simp) a,?_⟩
    simp only [finiteLambdaDivisionClass, ↓reduceDIte]
    have cancel (A : SyntheticSpectrum) (m w w' : ℤ) (hw : w=w') (hw' : w'=w)
        (c : BiHom m w A) :
        homotopyRegrade rfl hw' (homotopyRegrade rfl hw c)=c := by subst w'; rfl
    exact cancel _ _ _ _ _ _ a
  · have hd' : 0<d := by omega
    obtain ⟨b,hb⟩ := finite_detected_source_division X q d hd' hdq s t x a ha
    refine ⟨b,?_⟩
    simp only [finiteLambdaDivisionClass,dif_neg hd]
    exact (finiteLambdaClass_vertical X q d hd' hdq s t b).trans hb

private theorem finite_lambda_division_differential (X : ClassicalObject)
    (q d k : ℕ) (hdq : d < q) (hqdk : q-d ≤ k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (a : BiHom (t-s) (t-d) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-d)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,t-d)
        (nuWeightLabel model X s t (t-d) (by omega) x)) a)
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-d)))
    (hlam : finiteLambdaDivisionClass X q d hdq s t b = a)
    (hy : Detects (model.convergence (.nu X)) (s+k+1,t+k,t+(q-d:ℕ))
      (nuWeightLabel model X (s+k+1) (t+k) (t+(q-d:ℕ)) (by omega) y)
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv (t-s) t (q-d:ℕ) (model.nu.functor.obj (X.obj model.auxiliary))
          (b ≫ XModLambdaN.proj _ (q-d))))) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  by_cases hd : d=0
  · subst d
    rw [←hlam] at ha
    have hp : (s,t,t-(0:ℕ))=(s,t,t) := by simp
    have hdet := detects_transport hp _ _ ha
    apply finite_detected_boundary_differential X q k hdq hqdk s t x y b ?_ hy
    convert hdet using 1
    · have transport (w w' : ℤ) (hw : w=w') (hw₁ : w≤t) (hw₂ : w'≤t)
          (h : (s,t,w)=(s,t,w')) :
          regradeE2 h
            ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w)
              (nuWeightLabel model X s t w hw₁ x)) =
            ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w')
              (nuWeightLabel model X s t w' hw₂ x)) := by subst w'; rfl
      exact (transport _ _ (by simp) _ _ hp).symm
    · simp only [finiteLambdaDivisionClass, ↓reduceDIte]
      have cancel (A : SyntheticSpectrum) (m w w' : ℤ) (hw : w=w') (hw' : w'=w)
          (c : BiHom m w A) :
          homotopyRegrade rfl hw' (homotopyRegrade rfl hw c)=c := by subst w'; rfl
      exact (cancel _ _ _ _ _ _ b).symm
  · have hd' : 0<d := by omega
    have hclass : finiteLambdaClass X q d hd' hdq s t b = a := by
      simpa only [finiteLambdaDivisionClass, dif_neg hd] using hlam
    exact finite_lambda_division_detects_differential X q d k hd' hdq hqdk s t x y a ha b
      ((finiteLambdaClass_vertical X q d hd' hdq s t b).symm.trans hclass) hy


end
end KIP126.ProofTools.Internal.Leibniz
