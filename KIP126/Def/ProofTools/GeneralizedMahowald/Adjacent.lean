module

import all KIP126.Def.ProofTools.GeneralizedMahowald.Coherence
import all KIP126.Def.ProofTools.GeneralizedMahowald.PageCalculus
import all KIP126.Def.ProofTools.GeneralizedMahowald.KernelCorrection
import all KIP126.Def.ProofTools.GeneralizedMahowald.Detection

/-! The proved adjacent Bockstein and zero-target cases of generalized Mahowald.
Source: bbac1fc05843 GeneralizedMahowald/Proofs.lean, lines 1481–1992
(MIT; retained source LICENSE). All upstream facts are called on the fixed model. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FinitePageCalculus KIP126.Kervaire.Route
open KIP126.Literature
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
local notation "Syn" => SyntheticSpectrum

private theorem adjacent_bockstein_coordinates
    (X : ClassicalObject)
    (i : ℕ) (hi : 0 < i) (s t : ℤ) (x : Ambient model X (s,t))
    (hx : x ∈ KIP126.Literature.cycles model X i (s,t)) :
    ∃ (aZero : BiHom (t-s) t (XModLambdaN (nuZero model X) i))
      (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i)),
      a = aZero ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) i ∧
      a ≫ (model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho 1 i hi =
        firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      KIP126.Core.SpectralSequence.HasDifferential
        (model.classical.obj (X.obj model.auxiliary)) (i+1)
        (s,t) (s+i+1,t+i) x (bocksteinLabel model X i hi s t aZero) ∧
      (homotopyRegrade (by omega) rfl
          (biSuspensionHomEquiv (t-s) t (i:ℤ)
            (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (i+1-i))
            (a ≫ ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).triangle hi
              (Nat.lt_succ_self i)).delta) ≫
            eqToHom (congrArg (fun n => XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n)
              (show i+1-i=1 by omega)))) =
        firstLabel model X (s+i+1) (t+i) (bocksteinLabel model X i hi s t aZero) ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  have bockstein_arrow_eq_biSuspensionIso_inv
      (X : ClassicalObject) (q : ℕ) (hq : 0 < q) :
      bocksteinArrow model X q hq =
        ((model.quotients.tower (nuZero model X)).triangle hq (Nat.lt_succ_self q)).delta ≫
          (biSuspensionIso (q : ℤ) (XModLambdaN (nuZero model X) (q+1-q))).inv ≫
            eqToHom (congrArg (fun n => (SyntheticCategory.biShift (1,-(q:ℤ))).obj
              (XModLambdaN (nuZero model X) n)) (show q+1-q=1 by omega)) := by
    have hcast {A A' B : Syn} (h : A=A') (e : A ≅ B)
        (he : (A ≅ B) = (A' ≅ B)) :
        (he.mp e).inv = e.inv ≫ eqToHom h := by
      subst A'
      change e.inv = e.inv ≫ 𝟙 A
      exact (Category.comp_id _).symm
    simp only [bocksteinArrow, biSuspensionIso]
    rw [hcast (congrArg (fun p : ℤ × ℤ => (SyntheticCategory.biShift p).obj
      (XModLambdaN (nuZero model X) (q+1-q))) (by ext <;> simp))]
    simp only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Category.assoc, eqToHom_trans]


  have biSuspensionHomEquiv_eq_inverse_susp (n w q : ℤ) (Q : Syn)
      (a : BiHom n w (((SyntheticCategory.biShift (0,-q)).obj Q)⟦(1:ℤ)⟧)) :
      biSuspensionHomEquiv n w q Q a =
        (susp_invariance (n-1) (w+q) 1 (-q) Q).symm
          (homotopyRegrade (by omega) (by omega) (a ≫ (biSuspensionIso q Q).inv)) := by
    have hc (n' w' : ℤ) (hn : n' = n) (hw : w' = w)
        (e : BiHom (n-1) (w+q) Q ≃
          BiHom n' w' (((SyntheticCategory.biShift (0,-q)).obj Q)⟦(1:ℤ)⟧))
        (he : (BiHom (n-1) (w+q) Q ≃
            BiHom n' w' (((SyntheticCategory.biShift (0,-q)).obj Q)⟦(1:ℤ)⟧)) =
          (BiHom (n-1) (w+q) Q ≃
            BiHom n w (((SyntheticCategory.biShift (0,-q)).obj Q)⟦(1:ℤ)⟧))) :
        (he.mp e).symm a = e.symm (homotopyRegrade hn.symm hw.symm a) := by
      subst n'
      subst w'
      rfl
    have regrade_comp {n' w' : ℤ} (hn : n=n') (hw : w=w') {A B : Syn}
        (a : BiHom n w A) (f : A ⟶ B) :
        homotopyRegrade hn hw (a ≫ f) = homotopyRegrade hn hw a ≫ f := by
      subst n'
      subst w'
      rfl
    change biSuspensionHomEquivRaw n w q Q a = _
    simp only [biSuspensionHomEquivRaw]
    rw [hc (n-1+1) (w+q+-q) (by omega) (by omega)]
    simp only [Equiv.symm_trans_apply, Iso.homCongr_symm, Iso.homCongr_apply,
      Iso.symm_hom, Iso.symm_inv, Iso.refl_hom, Category.id_comp, regrade_comp]


  have firstLabel_bocksteinLabel_eq
      (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
      (a : BiHom (t-s) t (XModLambdaN (nuZero model X) q)) :
      firstLabel model X (s+q+1) (t+q) (bocksteinLabel model X q hq s t a) =
        homotopyRegrade (by omega) rfl
          ((susp_invariance (t-s-1) (t+q) 1 (-(q:ℤ)) _).symm
            (homotopyRegrade (by omega) (by omega) (a ≫ bocksteinArrow model X q hq))) := by
    have regrade_cast {a b c d m n : ℤ} {Q : Syn}
        (h1 : a=m) (h2 : b=n) (h3 : a=c) (h4 : b=d)
        (he : BiHom m n Q = BiHom c d Q) (x : BiHom a b Q) :
        he.mp (homotopyRegrade h1 h2 x) = homotopyRegrade h3 h4 x := by
      subst m; subst n; subst c; subst d
      rfl
    simp only [firstLabel, bocksteinLabel, LinearEquiv.symm_apply_apply]
    exact regrade_cast _ _ _ _ _ _


  have firstLabel_bocksteinLabel_eq_actual_delta
      (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
      (a : BiHom (t-s) t (XModLambdaN (nuZero model X) q)) :
      firstLabel model X (s+q+1) (t+q) (bocksteinLabel model X q hq s t a) =
        homotopyRegrade (by omega) rfl
          (biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN (nuZero model X) (q+1-q))
            (a ≫ ((model.quotients.tower (nuZero model X)).triangle hq (Nat.lt_succ_self q)).delta) ≫
            eqToHom (congrArg (fun n => XModLambdaN (nuZero model X) n)
              (show q+1-q=1 by omega))) := by
    have regrade_comp {n w n' w' : ℤ} (hn : n=n') (hw : w=w') {A B : Syn}
        (a : BiHom n w A) (f : A ⟶ B) :
        homotopyRegrade hn hw (a ≫ f) = homotopyRegrade hn hw a ≫ f := by
      subst n'; subst w'
      rfl
    have inverse_susp_cast {A B : Syn} (h : A=B) (n w k l : ℤ)
        (b : BiHom (n+k) (w+l) ((SyntheticCategory.biShift (k,l)).obj A)) :
        (susp_invariance n w k l B).symm
          (b ≫ eqToHom (congrArg (SyntheticCategory.biShift (k,l)).obj h)) =
          (susp_invariance n w k l A).symm b ≫ eqToHom h := by
      subst B
      simp only [eqToHom_refl, Category.comp_id]
    rw [firstLabel_bocksteinLabel_eq, bockstein_arrow_eq_biSuspensionIso_inv,
      biSuspensionHomEquiv_eq_inverse_susp]
    simp only [regrade_comp, ←Category.assoc]
    rw [inverse_susp_cast (congrArg (fun n => XModLambdaN (nuZero model X) n)
      (show q+1-q=1 by omega))]
    rw [regrade_comp]


  have biSuspensionIso_natural (i : ℤ) {A B : Syn} (f : A ⟶ B) :
      (SyntheticCategory.biShift (1,-i)).map f ≫ (biSuspensionIso i B).hom =
        (biSuspensionIso i A).hom ≫
          (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-i)).map f) := by
    let e : (SyntheticCategory.biShift ((0,-i)+(1,0)) : Syn ⥤ Syn) ≅
        SyntheticCategory.biShift (0,-i) ⋙ shiftFunctor Syn (1:ℤ) :=
      (SyntheticCategory.biShift_comp (0,-i) (1,0)).symm ≪≫
        Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,-i)) (SyntheticCategory.biShift_compat 1)
    have cast_natural (p p' : ℤ×ℤ) (hp : p=p')
        (E : (SyntheticCategory.biShift p : Syn ⥤ Syn) ≅
          SyntheticCategory.biShift (0,-i) ⋙ shiftFunctor Syn (1:ℤ))
        (hA : ((SyntheticCategory.biShift p).obj A ≅
          (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj A)) =
          ((SyntheticCategory.biShift p').obj A ≅
          (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj A)))
        (hB : ((SyntheticCategory.biShift p).obj B ≅
          (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj B)) =
          ((SyntheticCategory.biShift p').obj B ≅
          (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj B))) :
        (SyntheticCategory.biShift p').map f ≫ (cast hB (E.app B)).hom =
          (cast hA (E.app A)).hom ≫
            (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-i)).map f) := by
      subst p'
      exact E.hom.naturality f
    unfold biSuspensionIso
    exact cast_natural ((0,-i)+(1,0)) (1,-i) (by ext <;> simp) e _ _


  have biSuspensionHomEquiv_natural (n w q : ℤ) {A B : Syn} (f : A ⟶ B)
      (a : BiHom n w (((SyntheticCategory.biShift (0,-q)).obj A)⟦(1:ℤ)⟧)) :
      biSuspensionHomEquiv n w q B
          (a ≫ (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-q)).map f)) =
        biSuspensionHomEquiv n w q A a ≫ f := by
    have susp_nat (n w k l : ℤ) (b : BiHom n w A) :
        susp_invariance n w k l A b ≫ (SyntheticCategory.biShift (k,l)).map f =
          susp_invariance n w k l B (b ≫ f) := by
      change ((SyntheticCategory.biShift_comp (n,w) (k,l)).inv.app S_0_0 ≫
        (SyntheticCategory.biShift (k,l)).map b ≫ 𝟙 _) ≫ _ =
        _ ≫ (SyntheticCategory.biShift (k,l)).map (b ≫ f) ≫ 𝟙 _
      simp only [Functor.map_comp, Category.comp_id, Category.assoc, Iso.app_inv]
    have inv_susp_nat (n w k l : ℤ)
        (b : BiHom (n+k) (w+l) ((SyntheticCategory.biShift (k,l)).obj A)) :
        (susp_invariance n w k l B).symm (b ≫ (SyntheticCategory.biShift (k,l)).map f) =
          (susp_invariance n w k l A).symm b ≫ f := by
      apply (susp_invariance n w k l B).injective
      rw [Equiv.apply_symm_apply, ←susp_nat, Equiv.apply_symm_apply]
    have hi : (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-q)).map f) ≫
        (biSuspensionIso q B).inv =
        (biSuspensionIso q A).inv ≫ (SyntheticCategory.biShift (1,-q)).map f := by
      apply (cancel_mono (biSuspensionIso q B).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [biSuspensionIso_natural]
      simp only [Iso.inv_hom_id_assoc]
    have regrade_comp {n w n' w' : ℤ} (hn : n=n') (hw : w=w') {A B : Syn}
        (a : BiHom n w A) (f : A ⟶ B) :
        homotopyRegrade hn hw (a ≫ f) = homotopyRegrade hn hw a ≫ f := by
      subst n'; subst w'
      rfl
    rw [biSuspensionHomEquiv_eq_inverse_susp, biSuspensionHomEquiv_eq_inverse_susp]
    simp only [Category.assoc]
    rw [hi, ←Category.assoc, regrade_comp, inv_susp_nat]
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let f : nuZero model X ⟶ A := SyntheticCategory.biShift_zero.hom.app A
  obtain ⟨aZero,haZero,hdiff⟩ := KIP126.Literature.Standard.bhs_bockstein X i hi s t x
    ((isCycle_iff_reaches model X ((i:ℤ)+1) (by omega) (s,t) x).mp ⟨by omega, by simpa using hx⟩)
  let a : BiHom (t-s) t (XModLambdaN A i) := aZero ≫ XModLambdaN.map f i
  have hfirst : a ≫ (model.quotients.tower A).rho 1 i hi =
      firstLabel model X s t x ≫ XModLambdaN.map f 1 := by
    dsimp only [a]
    have hn : (model.quotients.tower (nuZero model X)).rho 1 i hi ≫ XModLambdaN.map f 1 =
        XModLambdaN.map f i ≫ (model.quotients.tower A).rho 1 i hi :=
      (model.quotients.natural f).rho_naturality hi
    rw [Category.assoc, ←hn, ←Category.assoc, haZero]
  refine ⟨aZero,a,rfl,hfirst,hdiff,?_⟩
  let y := bocksteinLabel model X i hi s t aZero
  let b : BiHom ((t+i)-(s+i+1)) (t+i) (XModLambdaN A 1) :=
    homotopyRegrade (by omega) rfl
      (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A (i+1-i))
        (a ≫ ((model.quotients.tower A).triangle hi (Nat.lt_succ_self i)).delta) ≫
        eqToHom (congrArg (fun n => XModLambdaN A n) (show i+1-i=1 by omega)))
  have hb : b = firstLabel model X (s+i+1) (t+i) y ≫ XModLambdaN.map f 1 := by
    have hdelta : XModLambdaN.map f i ≫
        ((model.quotients.tower A).triangle hi (Nat.lt_succ_self i)).delta =
      ((model.quotients.tower (nuZero model X)).triangle hi (Nat.lt_succ_self i)).delta ≫
        (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-(i:ℤ))).map
          (XModLambdaN.map f (i+1-i))) :=
      (model.quotients.natural f).delta_naturality hi (Nat.lt_succ_self i)
    have map_cast (n m : ℕ) (h : n=m) :
        XModLambdaN.map f n ≫ eqToHom (congrArg (fun k => XModLambdaN A k) h) =
          eqToHom (congrArg (fun k => XModLambdaN (nuZero model X) k) h) ≫ XModLambdaN.map f m := by
      subst m
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    have regrade_comp {n w n' w' : ℤ} (hn : n=n') (hw : w=w') {A B : Syn}
        (a : BiHom n w A) (f : A ⟶ B) :
        homotopyRegrade hn hw (a ≫ f) = homotopyRegrade hn hw a ≫ f := by
      subst n'; subst w'
      rfl
    dsimp only [b,a,y]
    rw [firstLabel_bocksteinLabel_eq_actual_delta]
    rw [Category.assoc aZero,hdelta,←Category.assoc aZero,
      biSuspensionHomEquiv_natural]
    simp only [Category.assoc, regrade_comp]
    rw [map_cast (i+1-i) 1 (by omega)]
  exact hb

private theorem zero_target_actual_lift
    (X : ClassicalObject)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (hd : KIP126.Core.SpectralSequence.HasDifferential
      (model.classical.obj (X.obj model.auxiliary)) (i+q)
      (s,t) (s+i+q,t+i+q-1) x 0) :
    ∃ a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i),
      a ≫ (model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho 1 i hi =
        firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      a ≫ ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).triangle hi
        (show i < i+q by omega)).delta = 0 := by
  let E := model.classical.obj (X.obj model.auxiliary)
  let r : ℤ := i+q
  have hr : 2 ≤ r := by dsimp [r]; omega
  obtain ⟨hdeg,xr,yr,hxr,hyr,hdiff⟩ := hd
  have hy0 : yr=0 := represents_unique hyr (RepresentsOnPage.zero hr)
  have hz : E.d r (s,t) xr=0 := by
    apply (ModuleCat.mono_iff_injective (eqToHom (congrArg (E.Page r) hdeg))).mp inferInstance
    simpa only [ModuleCat.comp_apply,hy0,map_zero] using hdiff
  obtain ⟨_,z,hx,hzr⟩ := hxr
  let P := E.ssData (s,t)
  let n : ℕ := (r-E.r₀).toNat
  have hE : E.r₀ = 2 := model.classical.firstPage _
  have hnEq : n = (r-2).toNat := by dsimp only [n]; rw [hE]
  change (Subobject.underlying.obj (P.Z ↑n) : ModuleCat ℤ) at z
  change P.pageπ ↑n z=xr at hzr
  have hn : (↑n:WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  let down := Subobject.ofLE (P.Z ↑(n+1)) (P.Z ↑n) (P.Z_anti hn)
  have hk : xr ∈ LinearMap.ker (E.d r (s,t)).hom := hz
  rw [←subobjectModule_kernel,E.Z_succ r (s,t) (by rw [hE]; exact hr),subobjectModule_image] at hk
  obtain ⟨v,hv⟩ := hk
  change (Subobject.underlying.obj (P.Z ↑(n+1)) : ModuleCat ℤ) at v
  change P.pageπ ↑n (down v)=xr at hv
  have hb : (P.Z ↑n).arrow (z-down v) ∈ (ModuleCat.subobjectModule P.V) (P.B ↑n) := by
    apply (subobject_cokernel_π_eq_zero_iff (P.B ↑n) (P.Z ↑n) (P.B_le_Z _) _).mp
    change P.pageπ ↑n (z-down v)=0
    rw [map_sub,hzr,hv,sub_self]
  have hb' : (P.Z ↑n).arrow (z-down v) ∈
      (ModuleCat.subobjectModule P.V) (P.Z ↑(n+1)) :=
    (ModuleCat.subobjectModule P.V).monotone ((P.B_mono hn).trans (P.B_le_Z _)) hb
  have hv' : (P.Z ↑n).arrow (down v) ∈
      (ModuleCat.subobjectModule P.V) (P.Z ↑(n+1)) := by
    change (down ≫ (P.Z ↑n).arrow) v ∈ _
    dsimp only [down]
    rw [Subobject.ofLE_arrow]
    exact ⟨v,rfl⟩
  have hz' := ((ModuleCat.subobjectModule P.V) (P.Z ↑(n+1))).add_mem hb' hv'
  rw [map_sub,sub_add_cancel] at hz'
  obtain ⟨z',hz'⟩ := hz'
  have hxnext : x ∈ KIP126.Literature.cycles model X (i+q:ℕ) (s,t) := by
    have hn' : ((i+q:ℕ):ℤ)-1 = (n+1:ℕ) := by rw [hnEq]; dsimp only [r]; omega
    change ∃ v', (KIP126.Literature.cycleLabel model X ↑(((i+q:ℕ):ℤ)-1).toNat (s,t)) v'=x
    rw [hn',Int.toNat_natCast]
    refine ⟨z',?_⟩
    have heq : (Subobject.ofLE (P.Z ↑(n+1)) (P.Z 0) (P.Z_anti bot_le)) z' =
        (Subobject.ofLE (P.Z ↑n) (P.Z 0) (P.Z_anti bot_le)) z := by
      apply (ModuleCat.mono_iff_injective (P.Z 0).arrow).mp inferInstance
      simpa only [←ModuleCat.comp_apply,Subobject.ofLE_arrow] using hz'
    change KIP126.Literature.cycleLabel model X (↑(n+1)) (s,t) z' = x
    rw [initialProjection_eq_cycleLabel model X r hr (s,t)] at hx
    dsimp only [KIP126.Literature.cycleLabel]
    have heq' := congrArg (fun z => (P.pageπ 0 ≫ eqToHom
      (show P.page 0 = E.Page 2 (s,t) by simp [P,Page,hE])) z) heq
    exact heq'.trans hx
  obtain ⟨cZero,hcZero⟩ := (KIP126.Literature.Standard.bhs_finite_lift X (i+q) (by omega) s t x).mp
    ((isCycle_iff_reaches model X ((i+q:ℕ)+1) (by omega) (s,t) x).mp
      ⟨by omega,by simpa using hxnext⟩)
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let f : nuZero model X ⟶ A := SyntheticCategory.biShift_zero.hom.app A
  let c : BiHom (t-s) t (XModLambdaN A (i+q)) := cZero ≫ XModLambdaN.map f (i+q)
  refine ⟨c ≫ (model.quotients.tower A).rho i (i+q) (by omega),?_,?_⟩
  · rw [Category.assoc,(model.quotients.tower A).rho_comp hi (by omega)]
    dsimp only [c]
    have hnatur : (model.quotients.tower (nuZero model X)).rho 1 (i+q) (by omega) ≫
          XModLambdaN.map f 1 =
        XModLambdaN.map f (i+q) ≫ (model.quotients.tower A).rho 1 (i+q) (by omega) :=
      (model.quotients.natural f).rho_naturality (by omega)
    rw [Category.assoc,←hnatur,←Category.assoc,hcZero]
  · have hzero : (model.quotients.tower A).rho i (i+q) (by omega) ≫
        ((model.quotients.tower A).triangle hi (show i < i+q by omega)).delta = 0 := by
      rw [← (model.quotients.tower A).triangle_rho hi (show i < i+q by omega)]
      exact comp_distTriang_mor_zero₂₃ _ ((model.quotients.tower A).triangle hi (show i < i+q by omega)).distinguished
    rw [Category.assoc,hzero,comp_zero]

private theorem detects_sub (X : SyntheticObject) (i : Tridegree)
    {x y : (model.family.obj (X.obj model.nu model.auxiliary)).E₂ i}
    {a b : BiHom (i.2.1-i.1) i.2.2 (X.obj model.nu model.auxiliary)}
    (ha : Detects (model.convergence X) i x a)
    (hb : Detects (model.convergence X) i y b) :
    Detects (model.convergence X) i (x-y) (a-b) := by
  obtain ⟨e,⟨hr,z,hz,he⟩,a',ha',hga⟩ := ha
  obtain ⟨e',⟨_,z',hz',he'⟩,b',hb',hgb⟩ := hb
  refine ⟨e-e',⟨hr,z-z',?_,?_⟩,a'-b',?_,?_⟩
  · rw [map_sub,hz,hz']
  · rw [map_sub,he,he']
  · rw [map_sub,ha',hb']
  · rw [map_sub,map_sub,hga,hgb]

private theorem finiteTargetLabel_sub (X : ClassicalObject)
    (q : ℕ) (s t : ℤ) (k : ℕ) (x y : Ambient model X (s,t)) :
    finiteTargetLabel model X q s t k (x-y) =
      finiteTargetLabel model X q s t k x - finiteTargetLabel model X q s t k y := by
  have cast_sub (E : SyntheticAdamsSS) (s t w w' : ℤ) (h : w=w')
      (a b : E.E₂ (s,t,w)) :
      (congrArg (fun k => (E.E₂ (s,t,k) : Type)) h).mp (a-b) =
        (congrArg (fun k => (E.E₂ (s,t,k) : Type)) h).mp a -
          (congrArg (fun k => (E.E₂ (s,t,k) : Type)) h).mp b := by
    subst w'; rfl
  simp only [finiteTargetLabel,targetNuLabel,map_sub]
  rw [cast_sub] <;> simp only [map_sub,add_zero]

private theorem adjacent_mahowald_case
    (X : ClassicalObject)
    (i : ℕ) (hi : 0 < i) (s t : ℤ)
    (x : Ambient model X (s,t))
    (y : Ambient model X (s+i+1,t+i))
    (hd : KIP126.Core.SpectralSequence.HasDifferential
      (model.classical.obj (X.obj model.auxiliary)) (i+1)
        (s,t) (s+i+1,t+i) x y) :
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    let δ : XModLambdaN A i ⟶
        ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
      simpa only [show i.succ-i=1 by omega] using
        ((model.quotients.tower A).triangle hi (Nat.lt_succ_self i)).delta
    ∃ a : BiHom (t-s) t (XModLambdaN A i),
      a ≫ (model.quotients.tower A).rho 1 i (by omega) =
        firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
      Detects (model.convergence (.quotient 1 (.nu X))) (s+i+1,t+i,t+i)
        (regradeE2 (by simp) (finiteTargetLabel model X 1 (s+i+1) (t+i) 0 y))
        (homotopyRegrade (by change t-s-1 = (t+i)-(s+i+1); omega) rfl
          (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A 1) (a ≫ δ))) := by
  dsimp only
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let δ : XModLambdaN A i ⟶
      ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
    simpa only [show i.succ-i=1 by omega] using
      ((model.quotients.tower A).triangle hi (Nat.lt_succ_self i)).delta
  let boundary (a : BiHom (t-s) t (XModLambdaN A i)) :
      BiHom ((t+i)-(s+i+1)) (t+i) (XModLambdaN A 1) :=
    homotopyRegrade (by omega) rfl
      (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A 1) (a ≫ δ))
  have hx : x ∈ KIP126.Literature.cycles model X i (s,t) := by
    obtain ⟨_,xr,yr,hxr,hyr,hdr⟩ := hd
    have h := (isCycle_iff_reaches model X ((i:ℤ)+1)
      (by omega) (s,t) x).mpr ⟨xr,hxr⟩
    simpa only [add_sub_cancel_right] using h.2
  obtain ⟨aZero,a0,ha0,hfirst,hd0,hcoord⟩ := adjacent_bockstein_coordinates X i hi s t x hx
  let y0 := bocksteinLabel model X i hi s t aZero
  have Ecast {A B U : Syn} (h : A=B) (n w q : ℤ)
      (g : U ⟶ ((SyntheticCategory.biShift (0,-q)).obj A)⟦(1:ℤ)⟧)
      (he : (U ⟶ ((SyntheticCategory.biShift (0,-q)).obj A)⟦(1:ℤ)⟧) =
        (U ⟶ ((SyntheticCategory.biShift (0,-q)).obj B)⟦(1:ℤ)⟧))
      (a : BiHom n w U) :
      biSuspensionHomEquiv n w q B (a ≫ he.mp g) =
        biSuspensionHomEquiv n w q A (a ≫ g) ≫ eqToHom h := by
    subst B
    change biSuspensionHomEquiv n w q A (a ≫ g) =
      biSuspensionHomEquiv n w q A (a ≫ g) ≫ 𝟙 A
    exact (Category.comp_id _).symm
  have hbound0 : Detects (model.convergence (.quotient 1 (.nu X))) (s+i+1,t+i,t+i)
      (regradeE2 (by simp) (finiteTargetLabel model X 1 (s+i+1) (t+i) 0 y0)) (boundary a0) := by
    dsimp only [boundary,δ]
    rw [Ecast (congrArg (fun j => XModLambdaN A j) (show i+1-i=1 by omega))]
    rw [hcoord]
    apply first_label_detects_unshifted X 1 (by omega) (s+i+1) (t+i) y0 _
    rw [(model.quotients.tower A).rho_id,Category.comp_id]
  let b : BiHom ((t+i)-(s+i+1)) (t+i) (XModLambdaN A 1) :=
    firstLabel model X (s+i+1) (t+i) y ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1
  have hdb : Detects (model.convergence (.quotient 1 (.nu X))) (s+i+1,t+i,t+i)
      (regradeE2 (by simp) (finiteTargetLabel model X 1 (s+i+1) (t+i) 0 y)) b := by
    apply first_label_detects_unshifted X 1 (by omega) (s+i+1) (t+i) y b
    change b ≫ (model.quotients.tower A).rho 1 1 _ = _
    rw [(model.quotients.tower A).rho_id,Category.comp_id]
  have hdiff : y-y0 ∈ KIP126.Literature.boundaries model X i (s+i+1,t+i) := by
    have h := differential_targets_sub_mem_boundary model X ((i:ℤ)+1) (s,t) (s+i+1,t+i) x y y0 hd hd0
    simpa only [add_sub_cancel_right] using h
  by_cases hi1 : i=1
  · have heq : y=y0 := by
      have hz : y-y0=0 := by simpa only [hi1,Nat.cast_one,boundaries_one,Submodule.mem_bot] using hdiff
      exact sub_eq_zero.mp hz
    refine ⟨a0,hfirst,?_⟩
    change Detects _ (s+i+1,t+i,t+i) _ (boundary a0)
    simpa only [heq] using hbound0
  · have hi2 : 1 < i := by omega
    have hsub : Detects (model.convergence (.quotient 1 (.nu X))) (s+i+1,t+i,t+i)
        (regradeE2 (by simp) (finiteTargetLabel model X 1 (s+i+1) (t+i) 0 (y-y0)))
        (b-boundary a0) := by
      have h := detects_sub (.quotient 1 (.nu X)) (s+i+1,t+i,t+i) hdb hbound0
      have regrade_sub {E : SyntheticAdamsSS} {j k : Tridegree} (hjk : j=k)
          (u v : E.E₂ j) : regradeE2 hjk (u-v) = regradeE2 hjk u - regradeE2 hjk v := by
        subst k
        rfl
      rwa [←regrade_sub,←finiteTargetLabel_sub] at h
    have hcorrection : ∃ z : BiHom (t-s) t (XModLambdaN A i),
        z ≫ (model.quotients.tower A).rho 1 i (by omega) = 0 ∧ boundary z = b-boundary a0 := by
      obtain ⟨d,rfl⟩ : ∃ d : ℕ, i=d+1 := ⟨i-1,by omega⟩
      let i : ℕ := d+1
      let yd : KIP126.Literature.cycles model X
          ((1:ℤ)-(t+i)+((t+i)-(1-1:ℕ))) (s+i+1,t+i) :=
        ⟨y-y0,by
          rw [show (1:ℤ)-(t+i)+((t+i)-(1-1:ℕ))=1 by omega]
          exact boundaries_le_cycles model X (s+i+1,t+i) (d+1:ℕ) 1 hdiff⟩
      have hyd : yd.val ∈ KIP126.Literature.boundaries model X (d+1:ℕ) (s+i+1,t+i) := hdiff
      let c : BiHom ((t+i)-(s+i+1)) ((t+i)-(1-1:ℕ)) (XModLambdaN A 1) :=
        homotopyRegrade rfl (by omega) (b-boundary a0)
      have hc : Detects (model.convergence (.quotient 1 (.nu X)))
          (s+i+1,t+i,(t+i)-(1-1:ℕ))
          (finiteTargetLabel model X 1 (s+i+1) (t+i) (1-1) yd.val) c := by
        have back (u v w w' : ℤ) (h : w=w')
            (x : (model.family.obj (XModLambdaN A 1)).E₂ (u,v,w))
            (a : BiHom (v-u) w' (XModLambdaN A 1))
            (ha : Detects (model.convergence (.quotient 1 (.nu X))) (u,v,w')
              (regradeE2 (by rw [h]) x) a) :
            Detects (model.convergence (.quotient 1 (.nu X))) (u,v,w) x
              (homotopyRegrade rfl h.symm a) := by
          subst w'
          simpa only [regradeE2,eqToHom_refl,ModuleCat.id_apply,homotopyRegrade] using ha
        change Detects (model.convergence (.quotient 1 (.nu X)))
          (s+i+1,t+i,(t+i)-(0:ℤ))
          (finiteTargetLabel model X 1 (s+i+1) (t+i) 0 (y-y0))
          (homotopyRegrade rfl (by change t+i = t+i-0; omega) (b-boundary a0))
        exact back _ _ _ _ (by omega) _ _ hsub
      have hpre := actual_rho_kernel_correction X
        d 1 (by omega) (by omega) (s+i+1) (t+i) yd hyd c hc
      dsimp only at hpre
      have reindex (n w v : ℤ) (hn : n=t-s) (hw : w=t) (hv : v=t+i)
          (hm : n-1=(t+i)-(s+i+1)) (he : w+i=v)
          (hp : ∃ a : BiHom n w (XModLambdaN A i),
            a ≫ (model.quotients.tower A).rho 1 i (by dsimp [i]; omega) = 0 ∧
            homotopyRegrade hm he
              (biSuspensionHomEquiv n w (i:ℤ) (XModLambdaN A 1) (a ≫ δ)) =
              homotopyRegrade rfl hv.symm (b-boundary a0)) :
          ∃ z : BiHom (t-s) t (XModLambdaN A i),
            z ≫ (model.quotients.tower A).rho 1 i (by dsimp [i]; omega) = 0 ∧
              boundary z=b-boundary a0 := by
        subst n; subst w; subst v
        exact hp
      exact reindex (((t+i)-(s+i+1))+1) (((t+i)-(1-1:ℕ))-((d+1:ℕ):ℤ))
        ((t+i)-(1-1:ℕ)) (by omega) (by dsimp [i]; omega) (by omega)
        (by omega) (by dsimp [i]; omega) hpre
    obtain ⟨z,hzfirst,hzboundary⟩ := hcorrection
    refine ⟨a0+z,?_,?_⟩
    · rw [Preadditive.add_comp,hfirst,hzfirst,add_zero]
    · have hadd (u v : BiHom (t-s) t (XModLambdaN A i)) :
          boundary (u+v)=boundary u+boundary v := by
        have regrade_add {m w m' w' : ℤ} (hm:m=m') (hw:w=w') {Q : Syn}
            (u v : BiHom m w Q) : homotopyRegrade hm hw (u+v) =
              homotopyRegrade hm hw u + homotopyRegrade hm hw v := by
          subst m'; subst w'; rfl
        simp only [boundary,Preadditive.add_comp,map_add,regrade_add]
      have hb : boundary (a0+z)=b := by rw [hadd,hzboundary]; abel
      change Detects _ (s+i+1,t+i,t+i) _ (boundary (a0+z))
      rw [hb]
      exact hdb

end
end KIP126.ProofTools.Internal.Mahowald
