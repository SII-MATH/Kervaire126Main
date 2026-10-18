module
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDivision
import all KIP126.ProofTools.GeneralizedLeibniz.Reverse
import all KIP126.ProofTools.GeneralizedLeibniz.Filtration

/-! The absolute-boundary crossing comparison of AimPaper Proposition
`prop:cross-dr-En`. The source is divided in the actual finite quotient,
then the fixed BHS comparison reads the resulting classical differential.
Absence of a nonzero differential supplies a representative whose boundary
has higher filtration. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000

private theorem regrade_filtration_iff {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (s : ℤ) (a : BiHom m w A) :
    FiltrationAtLeast model.syntheticTower s (homotopyRegrade hm hw a) ↔
      FiltrationAtLeast model.syntheticTower s a := by
  subst m'; subst w'; rfl

private theorem absolute_boundary_filtration_iff (X : ClassicalObject)
    (q : ℕ) (m w v : ℤ)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    FiltrationAtLeast model.syntheticTower v
        (a ≫ absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) q) ↔
      FiltrationAtLeast model.syntheticTower v
        (biSuspensionHomEquiv m w q (model.nu.functor.obj (X.obj model.auxiliary))
          (a ≫ XModLambdaN.proj _ q)) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let α := biSuspensionHomEquiv m w q A (a ≫ XModLambdaN.proj A q)
  have he : a ≫ absoluteBoundary A q =
      homotopyRegrade (sub_add_cancel m 1) (add_neg_cancel_right w (q:ℤ))
        (shiftHomotopyClass (1,-(q:ℤ)) (m-1,w+q) α) := by
    have h := congrArg (fun z => z ≫ (biSuspensionIso q A).inv)
      (bi_susp_symm_eq m w q A α)
    simpa [α, absoluteBoundary, shiftHomotopyClass, susp_invariance,
      Iso.homCongr] using h
  rw [he,regrade_filtration_iff]
  exact shift_filtration_iff (.nu X) (1,-(q:ℤ)) (m-1,w+q) v α

private theorem quotient_first_label_exists (X : ClassicalObject)
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    ∃ x : Ambient model X (s,t),
      a ≫ (model.quotients.tower _).rho 1 q hq =
        firstLabel model X s t x ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  obtain ⟨x,hx⟩ := firstLabel_surjective X s t
    (a ≫ (model.quotients.tower A).rho 1 q hq ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app A) 1)
  refine ⟨x,?_⟩
  rw [hx,Category.assoc,Category.assoc,←model.quotients.functoriality.map_comp,
    Iso.inv_hom_id_app,model.quotients.functoriality.map_id]
  simp only [Functor.id_obj,Category.comp_id]
  rfl

private theorem no_crossing_differential_zero (X : ClassicalObject)
    (r page s t u v : ℤ) (hnc : NoCrossingOn model X r page (s,t))
    (hu : s < u) (hu' : u-s ≤ page-2) (hv : s+page ≤ v) (hv' : v ≤ s+r)
    (x : Ambient model X (u,t+(u-s)))
    (y : Ambient model X (v,t+(v-s)-1))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (v-u) (u,t+(u-s)) (v,t+(v-s)-1) x y) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (v-u) (u,t+(u-s)) (v,t+(v-s)-1) x 0 := by
  obtain ⟨hdeg,xr,yr,hx,hy,hd⟩ := hd
  have hz : yr = 0 := by
    by_contra hz
    apply hnc.2.2
    refine ⟨u-s,s+r-v,by omega,hu',by omega,by omega,?_⟩
    have he : HasNonzeroDifferential (model.classical.obj (X.obj model.auxiliary))
        (v-u) (u,t+(u-s)) (v,t+(v-s)-1) x y := ⟨hdeg,xr,yr,hx,hy,hd,hz⟩
    have h₁ : s+(u-s)=u := by omega
    have h₂ : s+r-(s+r-v)=v := by omega
    have h₃ : t+r-(s+r-v)-1=t+(v-s)-1 := by omega
    have h₄ : r-(u-s)-(s+r-v)=v-u := by omega
    change ∃ (x : Ambient model X (s+(u-s),t+(u-s)))
      (y : Ambient model X (s+r-(s+r-v),t+r-(s+r-v)-1)),
      HasNonzeroDifferential (model.classical.obj (X.obj model.auxiliary))
        (r-(u-s)-(s+r-v)) (s+(u-s),t+(u-s))
        (s+r-(s+r-v),t+r-(s+r-v)-1) x y
    rw [h₁,h₂,h₃,h₄]
    exact ⟨x,y,he⟩
  exact ⟨hdeg,xr,0,hx,RepresentsOnPage.zero (by omega),hd.trans hz⟩

private theorem divided_boundary_correction (X : ClassicalObject)
    (r page s t u v : ℤ) (hnc : NoCrossingOn model X r page (s,t))
    (hu : s < u) (hu' : u-s ≤ page-2) (hv : s+page ≤ v) (hv' : v ≤ s+r)
    (d : ℕ) (hd : 0 < d) (hdv : (d:ℤ) ≤ v-u-1)
    (a : BiHom ((t+(u-s))-u) (t+(u-s))
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) d))
    (hfil : FiltrationAtLeast model.syntheticTower v
      (a ≫ absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) d)) :
    ∃ a0 : BiHom ((t+(u-s))-u) (t+(u-s))
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) d),
      FiltrationAtLeast model.syntheticTower (u+1) (a-a0) ∧
      FiltrationAtLeast model.syntheticTower (v+1)
        (a0 ≫ absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) d) := by
  let w := t+(u-s)
  let k : ℕ := (v-u-1).toNat
  have hk : (k:ℤ)=v-u-1 := by dsimp [k]; omega
  obtain ⟨x,hx⟩ := quotient_first_label_exists X d hd u w a
  have hsurv := absolute_boundary_filtration_cycles X d k hd (by omega) u w x a hx
    (by simpa only [show u+(k:ℤ)+1=v by omega] using
      (absolute_boundary_filtration_iff X d _ _ v a).mp hfil)
  have hreach := (isCycle_iff_reaches model X (k+1) (by omega) (u,w) x).mp
    ⟨by omega,by simpa only [add_sub_cancel_right] using hsurv⟩
  obtain ⟨b,hb,hdb⟩ := KIP126.Literature.Standard.bhs_bockstein X k (by omega) u w x hreach
  have hzero : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (u,w) (u+k+1,w+k) x 0 := by
    have H := no_crossing_differential_zero X r page s t u (u+k+1) hnc
      hu hu' (by omega) (by omega) x
    have hweight : t+(u+(k:ℤ)+1-s)-1=w+k := by dsimp [w]; omega
    have hlength : u+(k:ℤ)+1-u=k+1 := by omega
    rw [hweight,hlength] at H
    exact H _ hdb
  obtain ⟨a0,ha0,hδ⟩ := differential_absolute_boundary X d k hd (by omega) u w x 0
    hzero (Submodule.zero_mem _)
  refine ⟨a0,?_,?_⟩
  · exact detects_sub_filtration (model.convergence (.quotient d (.nu X))) (u,w,w)
      (first_label_detects_unshifted X d hd u w x a hx)
      (first_label_detects_unshifted X d hd u w x a0 ha0)
  · apply (absolute_boundary_filtration_iff X d _ _ (v+1) a0).mpr
    have hz : nuWeightLabel model X (u+k+1) (w+k) (w+d) (by omega) 0 = 0 := by
      have cast_zero (E : SyntheticAdamsSS.{0}) (s t w w' : ℤ) (hw : w=w')
          (he : (E.E₂ (s,t,w) : Type) = (E.E₂ (s,t,w') : Type)) :
          he.mp (0 : E.E₂ (s,t,w)) = 0 := by subst w'; rfl
      simp only [nuWeightLabel,regradeE2,targetNuLabel,map_zero]
      rw [cast_zero _ _ _ _ _ (by omega)]
      simp only [map_zero]
    rw [hz] at hδ
    have H := detects_zero_filtration (model.convergence (.nu X)) (u+k+1,w+k,w+d) hδ
    have H := (regrade_filtration_iff _ _ _ _).mp H
    simpa only [show u+(k:ℤ)+1+1=v+1 by omega] using H

private def regradeAddEquiv {A : SyntheticSpectrum} {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') : BiHom m w A ≃+ BiHom m' w' A where
  toFun := homotopyRegrade hm hw
  invFun := homotopyRegrade hm.symm hw.symm
  left_inv := by subst m'; subst w'; intro a; rfl
  right_inv := by subst m'; subst w'; intro a; rfl
  map_add' := by subst m'; subst w'; intro a b; rfl

private def verticalShiftEquiv (A : SyntheticSpectrum) (i : ℕ) (m w : ℤ) :
    BiHom m (w+i) A ≃+
      BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj A) :=
  (suspInvarianceAddEquiv m (w+i) 0 (-(i:ℤ)) A).trans
    (regradeAddEquiv (add_zero m) (add_neg_cancel_right w (i:ℤ)))

private theorem vertical_shift_filtration_iff (A : SyntheticObject)
    (i : ℕ) (m w v : ℤ) (a : BiHom m (w+i) (A.obj model.nu model.auxiliary)) :
    FiltrationAtLeast model.syntheticTower v (verticalShiftEquiv _ i m w a) ↔
      FiltrationAtLeast model.syntheticTower v a := by
  change FiltrationAtLeast model.syntheticTower v
    (homotopyRegrade _ _ (susp_invariance m (w+i) 0 (-(i:ℤ)) _ a)) ↔ _
  rw [regrade_filtration_iff]
  have he : susp_invariance m (w+i) 0 (-(i:ℤ)) _ a =
      shiftHomotopyClass (0,-(i:ℤ)) (m,w+i) a := by
    simp [susp_invariance,shiftHomotopyClass,Iso.homCongr]
  rw [he]
  exact shift_filtration_iff A (0,-(i:ℤ)) (m,w+i) v a

private theorem vertical_shift_comp (A B : SyntheticSpectrum) (f : A ⟶ B)
    (i : ℕ) (m w : ℤ) (a : BiHom m (w+i) A) :
    verticalShiftEquiv A i m w a ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map f =
      verticalShiftEquiv B i m w (a ≫ f) := by
  simp [verticalShiftEquiv,AddEquiv.trans_apply,regradeAddEquiv,
    suspInvarianceAddEquiv,susp_invariance,Iso.homCongr,regrade_precomp,Functor.map_comp]

private theorem boundary_crossing_correction (X : ClassicalObject)
    (q : ℕ) (r s t u v : ℤ) (hnc : NoCrossingOn model X r (q+1) (s,t))
    (hu : s < u) (hv' : v ≤ s+r)
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : FiltrationAtLeast model.syntheticTower u a)
    (hδ : FiltrationAtLeast model.syntheticTower v
      (a ≫ absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    ∃ a0 : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
      FiltrationAtLeast model.syntheticTower u a0 ∧
      FiltrationAtLeast model.syntheticTower (u+1) (a-a0) ∧
      FiltrationAtLeast model.syntheticTower (v+1)
        (a0 ≫ absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) q) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  have hq : 0 < q := by have := hnc.1; omega
  by_cases hv : s+(q:ℤ)+1 ≤ v
  swap
  · refine ⟨a,ha,?_,?_⟩
    · simpa only [FiltrationAtLeast,sub_self] using
        (model.syntheticTower.filtrationSubmodule _ (u+1) (t-s,t)).zero_mem
    · apply (absolute_boundary_filtration_iff X q (t-s) t (v+1) a).mpr
      let α := biSuspensionHomEquiv (t-s) t q A (a ≫ XModLambdaN.proj A q)
      have hα := nu_bottom_filtration X (s+q+1) (t+q)
        (homotopyRegrade (by omega) rfl α)
      have hα := (regrade_filtration_iff _ _ _ _).mp hα
      exact model.syntheticTower.filtrationSubmodule_antitone _ _ (by omega) hα
  by_cases hui : (q:ℤ) ≤ u-s
  · have haz := finite_high_filtration_zero X q hq (t-s) t u (by omega) a ha
    subst a
    refine ⟨0,?_,?_,?_⟩ <;>
      simp only [FiltrationAtLeast,sub_self,zero_comp] <;> exact Submodule.zero_mem _
  let i : ℕ := (u-s).toNat
  have hiZ : (i:ℤ)=u-s := by dsimp [i]; omega
  have hi : 0 < i := by omega
  have hiq : i < q := by omega
  let T := (model.quotients.tower A).triangle hi hiq
  obtain ⟨bS,hbS⟩ := finite_source_division X i q hi hiq (t-s) t u (by omega) a ha
  let e := verticalShiftEquiv (XModLambdaN A (q-i)) i (t-s) t
  let b := e.symm bS
  have hb : e b = bS := e.apply_symm_apply bS
  have hfilb : FiltrationAtLeast model.syntheticTower v (b ≫ absoluteBoundary A (q-i)) := by
    have h := (divided_boundary_filtration_iff X i q hi hiq (t-s) t v bS).mp (by
      rw [←Category.assoc,hbS]
      exact hδ)
    rw [←hb,vertical_shift_comp] at h
    exact (vertical_shift_filtration_iff (.shift (1,-((q-i:ℕ):ℤ)) (.nu X))
      i (t-s) t v (b ≫ absoluteBoundary A (q-i))).mp h
  have H := divided_boundary_correction X r (q+1) s t u v hnc hu (by omega)
    (by omega) hv' (q-i) (by omega) (by omega)
  have hw : t+(i:ℤ)=t+(u-s) := by omega
  have hm : t-s=(t+(i:ℤ))-u := by omega
  rw [←hw,←hm] at H
  obtain ⟨b0,hb0,hδ0⟩ := H b hfilb
  let a0 := e b0 ≫ T.lambdaMap
  have hdiff : FiltrationAtLeast model.syntheticTower (u+1) (a-a0) := by
    have hshift := (vertical_shift_filtration_iff (.quotient (q-i) (.nu X))
      i (t-s) t (u+1) (b-b0)).mpr hb0
    have hmap := map_preserves_filtration (model.convergentMap
      (.shift (0,-(i:ℤ)) (.quotient (q-i) (.nu X))) (.quotient q (.nu X)) T.lambdaMap)
      (t-s,t) (u+1) _ hshift
    change FiltrationAtLeast model.syntheticTower (u+1) (e (b-b0) ≫ T.lambdaMap) at hmap
    rw [map_sub,Preadditive.sub_comp,hb] at hmap
    change FiltrationAtLeast model.syntheticTower (u+1) (bS ≫ T.lambdaMap - a0) at hmap
    rwa [hbS] at hmap
  refine ⟨a0,?_,hdiff,?_⟩
  · have hdiff' := model.syntheticTower.filtrationSubmodule_antitone _ (t-s,t)
      (show u ≤ u+1 by omega) hdiff
    have H := (model.syntheticTower.filtrationSubmodule _ u (t-s,t)).sub_mem ha hdiff'
    simpa only [FiltrationAtLeast,sub_sub_cancel] using H
  · dsimp only [a0]
    rw [Category.assoc]
    apply (divided_boundary_filtration_iff X i q hi hiq (t-s) t (v+1) (e b0)).mpr
    rw [vertical_shift_comp]
    exact (vertical_shift_filtration_iff (.shift (1,-((q-i:ℕ):ℤ)) (.nu X))
      i (t-s) t (v+1) (b0 ≫ absoluteBoundary A (q-i))).mpr hδ0

private theorem classical_noCrossing_absolute_boundary (X : ClassicalObject)
    (page : ℕ) (r s t : ℤ) (hnc : NoCrossingOn model X r page (s,t)) :
    TowerNoCrossing (model.convergentMap
      (.quotient (page-1) (.nu X))
      (.shift (1,-((page-1:ℕ):ℤ)) (.nu X))
      (absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) (page-1)))
      (t-s,t) s r := by
  apply tower_no_crossing_of_correction
  intro u v hu _ hv a ha hδ
  have hnc' : NoCrossingOn model X r ((page-1:ℕ)+1) (s,t) := by
    convert hnc using 1
    have h := hnc.1
    omega
  exact boundary_crossing_correction X (page-1) r s t u v hnc' hu hv a ha hδ

end
end KIP126.ProofTools.Internal.Leibniz
