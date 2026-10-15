module
public import KIP126.Def.ProofTools.Operations
import all KIP126.Main.Internal.Theta.NoCrossing
import all KIP126.Main.Internal.Choice.LambdaInjectivity

/-! Original filtered realization-kernel descent,
Main/Solution/Computation/Lambda.lean:1080–1420, bbac1fc05843 (MIT).
The low stem staircase is proved in NoCrossing; convergence and shift
coordinates are those of the fixed public upstream system. -/
@[expose] section
namespace KIP126.Main.Internal.Theta
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Literature KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum Spectrum)
open KIP126.ProofTools.Operations
noncomputable section
local instance shiftAdditive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := SyntheticSpectrum) p).Additive :=
  KIP126.AdamsSynthetic.Standard.graded_shiftAdditive p
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
private theorem actual_stem63_no_late (q : ℤ) (hq : q≤6) (r : ℤ) (hr : 3≤r) :
    ∀ a : model.classical.sphere.Page r (q,q+63), model.classical.sphere.d r (q,q+63) a=0 := by
  rw [←Selected.Normalized.sphere_eq]
  exact stem63_no_late_differentials q hq r hr

private theorem high_lambda_eMap_injective (wt : ℤ) (hwt : wt≤70) (s : ℤ) (hs : 9≤s) :
    Function.Injective (((model.family.functor.map (lambdaPow 1 (model.nu.functor.obj SphereSpectrum))).eInftyMap (s,62+s,wt-1)).hom) := by
  have bhs_lambdaMap_injective (s : ℤ) (hs : 9≤s) :
      Function.Injective (KIP126.Literature.Standard.infinityLambda (.nu .sphere) 1 (s,62+s) wt) := by
    let E := model.classical.sphere
    by_cases hw : wt ≤ 62+s
    · have hr : 2 ≤ 2+(62+s)-wt := by omega
      have hidx : (s,62+s)-E.diffDeg (2+(62+s)-wt) = (wt-62-2,wt-1) := by
        rw [show E.diffDeg (2+(62+s)-wt) = (2+(62+s)-wt,2+(62+s)-wt-1) from model.classical.differentialDegree _ _]
        ext <;> dsimp <;> omega
      have hd : E.d (2+(62+s)-wt) ((s,62+s)-E.diffDeg (2+(62+s)-wt)) = 0 := by
        rw [hidx]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        have hout := actual_stem63_no_late (wt-62-2) (by omega) (2+(62+s)-wt) (by omega)
        have hpair : (wt-62-2,wt-62-2+63)=(wt-62-2,wt-1) := by ext <;> dsimp; omega
        rw [hpair] at hout
        exact hout y
      have hB := Choice.paper_boundaries_step .sphere (2+(62+s)-wt) hr (s,62+s) hd
      have hB' : boundaries model .sphere (1+(62+s)-wt) (s,62+s) =
          boundaries model .sphere (1+(62+s)-(wt-1)) (s,62+s) := by
        convert hB.symm using 1 <;> congr 1 <;> omega
      have hq := Choice.subquotient_map_injective_of_boundary_eq
        (permanentCycles model .sphere (s,62+s)) _ _
        (boundaries_monotone model .sphere (s,62+s) (show 1+(62+s)-wt ≤ 1+(62+s)-(wt-1) by omega)) hB'
      intro x y hxy
      apply (KIP126.Literature.Standard.infinityNuWindow .sphere (s,62+s) wt hw).injective
      apply hq
      have hx := KIP126.Literature.Standard.eInfinity_lambda_nu .sphere 1 (s,62+s) wt hw x
      have hy := KIP126.Literature.Standard.eInfinity_lambda_nu .sphere 1 (s,62+s) wt hw y
      exact hx.symm.trans ((congrArg (KIP126.Literature.Standard.infinityNuWindow
        .sphere (s,62+s) (wt-1) (by omega)) hxy).trans hy)
    · have hz : Subsingleton (nuEInftyModel model .sphere (s,62+s) wt) := by
        simp only [nuEInftyModel,hw,ite_false]
        infer_instance
      intro x y _
      apply (KIP126.Literature.Standard.eInfinity_nu .sphere (s,62+s) wt).injective
      exact hz.elim _ _
  have actual_lambda_eMap_injective (s : ℤ) (hs : 9≤s) :
      Function.Injective (((model.family.functor.map
        (lambdaPow 1 (model.nu.functor.obj (SphereSpectrum)))).eInftyMap
          (s,62+s,wt-1)).hom) := by
    let e := KIP126.Literature.Standard.infinityShiftData.shift model (.nu .sphere) 1 (s,62+s) wt
    have hl : KIP126.Literature.Standard.infinityLambda (.nu .sphere) 1 (s,62+s) wt =
        e.hom ≫ (model.family.map (lambdaPow 1 (model.nu.functor.obj (SphereSpectrum)))).eInftyMap (s,62+s,wt-1) := by
      simp only [KIP126.Literature.Standard.infinityLambda,InfinityShiftCoordinates.lambdaMap,
        Nat.one_ne_zero, ↓reduceDIte]
      rfl
    intro x y hxy
    apply e.symm.toLinearEquiv.injective
    apply bhs_lambdaMap_injective s hs
    rw [hl]
    simp only [ModuleCat.comp_apply]
    have hx := e.toLinearEquiv.apply_symm_apply x
    have hy := e.toLinearEquiv.apply_symm_apply y
    change e.hom (e.inv x) = x at hx
    change e.hom (e.inv y) = y at hy
    change (model.family.map (lambdaPow 1 (model.nu.functor.obj (SphereSpectrum)))).eInftyMap
      (s,62+s,wt-1) (e.hom (e.inv x)) =
      (model.family.map (lambdaPow 1 (model.nu.functor.obj (SphereSpectrum)))).eInftyMap
      (s,62+s,wt-1) (e.hom (e.inv y))
    rw [hx,hy]
    exact hxy
  exact actual_lambda_eMap_injective s hs

private theorem shifted_weight71_filtration9 (j : ℤ)
    (a : BiHom 62 (71+j) ((SyntheticCategory.biShift (0,j)).obj (model.nu.functor.obj SphereSpectrum))) :
    FiltrationAtLeast model.syntheticTower 9 a := by
  let X : SyntheticObject := .shift (0,j) (.nu .sphere)
  have hz (s : ℤ) (hs : 0≤s) (hs9 : s<9) :
      IsZero (((model.family.obj (X.obj model.nu model.auxiliary)).sequence.ssData (s,62+s,71+j)).eInfty) := by
    haveI : Subsingleton (nuEInftyModel model .sphere (s,62+s) 71) := by
      simp only [nuEInftyModel,show ¬(71:ℤ)≤(s,62+s).2 by dsimp; omega,ite_false]
      infer_instance
    haveI : Subsingleton (((model.family.obj (model.nu.functor.obj SphereSpectrum)).sequence.ssData (s,62+s,71)).eInfty) :=
      (KIP126.Literature.Standard.eInfinity_nu .sphere (s,62+s) 71).injective.subsingleton
    let e := towerInfinityIso (model.convergence (.nu .sphere))
      (model.convergence X) ((KIP126.AdamsSynthetic.Standard.essShift (0,j)).filtered (.nu .sphere) (62,71)) s
    haveI : Subsingleton (((model.family.obj ((.nu .sphere : SyntheticObject).obj model.nu model.auxiliary)).sequence.ssData (s,(62,71).1+s,(62,71).2)).eInfty) := by
      change Subsingleton (((model.family.obj (model.nu.functor.obj SphereSpectrum)).sequence.ssData (s,62+s,71)).eInfty)
      infer_instance
    exact ModuleCat.isZero_iff_subsingleton.mpr e.symm.toLinearEquiv.injective.subsingleton
  apply (filtration_iff_of_infinity_zero (model.convergence X) 0 9 62 (71+j) (by norm_num) hz a).mp
  refine ⟨a≫(model.syntheticTower.tower _).zeroIso.inv,?_⟩
  change (a≫(model.syntheticTower.tower _).zeroIso.inv)≫(model.syntheticTower.tower _).projection 0=a
  simp only [AbstractAdamsTower.projection,Int.toNat_zero,(model.syntheticTower.tower _).map_self]
  erw [Category.assoc,Category.id_comp,Iso.inv_hom_id,Category.comp_id]

private theorem selected_homotopyMap_kernel_zero_from_f9
    (X Y : SyntheticObject) (f : X.obj model.nu model.auxiliary ⟶ Y.obj model.nu model.auxiliary)
    (m w : ℤ)
    (hinj : ∀ s : ℕ, 9≤s → Function.Injective ((model.family.functor.map f).eInftyMap (s,m+s,w)))
    (a : BiHom m w (X.obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower 9 a) (haf : a≫f=0) : a=0 := by
  apply KIP126.AdamsSynthetic.Standard.synthetic_homotopy_separated X m w a
  intro s
  induction s with
  | zero => exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega : (0:ℤ)≤9) ha
  | succ s ih =>
    by_cases hs : s<9
    · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega : ((s+1:ℕ):ℤ)≤9) ha
    · have h := next_filtration_of_infinity_injective (model.convergentMap X Y f)
        (m,w) s (hinj s (by omega)) a ih (by rw [haf]; exact Submodule.zero_mem _)
      simpa only [Nat.cast_add,Nat.cast_one,FiltrationAtLeast] using h

private theorem actual_postcomp_filtration
    (X Y : SyntheticObject) (f : X.obj model.nu model.auxiliary ⟶ Y.obj model.nu model.auxiliary)
    (s m w : ℤ) (a : BiHom m w (X.obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    FiltrationAtLeast model.syntheticTower s (a≫f) :=
  map_preserves_filtration (model.convergentMap X Y f) (m,w) s a ha

private theorem lambda_kills_realization_kernel_62_71
    (a : BiHom 62 71 (S_0_0 : SyntheticSpectrum))
    (ha : model.recovery.realization.map a=0) : lambdaMultiply 1 a=0 := by
  have restriction_lift_zero
      (n : ℕ) {Y X : SyntheticSpectrum} (a : Y ⟶ X)
      (h : (SyntheticCategory.biShift (lambdaDegree (n+1))).map a ≫
        lambdaRestrictionSourceMap 1 (n+1) (by omega) X = 0) :
      lambdaPow n Y ≫ a = 0 := by
    rw [lambdaRestrictionSourceMap_naturality] at h
    simp only [lambdaRestrictionSourceMap, Category.assoc] at h
    have hp := (Limits.comp_eq_zero_iff_of_epi
      ((lambdaShiftAddIso n 1 (n+1) (by omega)).inv.app Y)).mp h
    rw [← Functor.map_comp] at hp
    have hz : lambdaPow (n+1-1) Y ≫ a = 0 := by
      apply (SyntheticCategory.biShift_fullyFaithful (Syn := SyntheticSpectrum) (lambdaDegree 1)).map_injective
      simpa only [Functor.map_zero] using hp
    rw [show n+1-1=n by omega] at hz
    exact hz
  have restriction_lift_lambda
      (coh : BiShiftCoherence SyntheticSpectrum) (n : ℕ) {Y X : SyntheticSpectrum} (a : Y ⟶ X) :
      ((SyntheticCategory.biShift (lambdaDegree (n+1))).map a ≫
        lambdaRestrictionSourceMap 1 (n+1) (by omega) X) ≫
          SyntheticCategory.lam.app X = lambdaPow (n+1) Y ≫ a := by
    calc
      _ = (SyntheticCategory.biShift (lambdaDegree (n+1))).map a ≫ lambdaPow (n+1) X := by
        simpa only [lambdaPow_one coh, Category.assoc] using
          congrArg (fun g => (SyntheticCategory.biShift (lambdaDegree (n+1))).map a ≫ g)
            (lambdaRestrictionSourceMap_commutes coh 1 (n+1) (by omega) X)
      _ = _ := lambdaPow_naturality (n+1) a
  have lambda_power_descent_step
      (f9 : ∀ k : ℤ, ∀ a : BiHom 62 (71+k)
        ((SyntheticCategory.biShift (0,k)).obj (model.nu.functor.obj SphereSpectrum)),
          FiltrationAtLeast model.syntheticTower 9 a)
      (ker : ∀ w : ℤ, w ≤ 69 →
        ∀ b : BiHom 62 w ((SyntheticCategory.biShift (0,-1)).obj
          (model.nu.functor.obj SphereSpectrum)),
        FiltrationAtLeast model.syntheticTower 9 b →
        b ≫ SyntheticCategory.lam.app _ = 0 → b = 0)
      (n : ℕ) (hn : 1≤n)
      (a : BiHom 62 71 (model.nu.functor.obj SphereSpectrum))
      (ha : lambdaMultiply (n+1) a=0) : lambdaMultiply n a=0 := by
    let X := model.nu.functor.obj SphereSpectrum
    let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum) (lambdaDegree (n+1))
    let e : Smn (Syn := SyntheticSpectrum) 62 (71-((n+1:ℕ):ℤ)) ≅ F.obj (Smn 62 71) :=
      eqToIso (by dsimp only [Smn]; congr 1) ≪≫
        ((SyntheticCategory.biShift_comp (62,71) (0,-((n+1 : ℕ):ℤ))).app S_0_0).symm
    let z : BiHom 62 (71-((n+1:ℕ):ℤ)) (F.obj X) := e.hom ≫ F.map a
    let R := lambdaRestrictionSourceMap 1 (n+1) (by omega) X
    let b : BiHom 62 (71-((n+1:ℕ):ℤ)) ((SyntheticCategory.biShift (0,-1)).obj X) := z ≫ R
    have hz9 : FiltrationAtLeast model.syntheticTower 9 z := by
      have hh := f9 (-((n+1:ℕ):ℤ))
      rw [← sub_eq_add_neg] at hh
      exact hh z
    have hb9 : FiltrationAtLeast model.syntheticTower 9 b :=
      actual_postcomp_filtration (.shift (lambdaDegree (n+1)) (.nu .sphere))
        (.shift (0,-1) (.nu .sphere)) R 9 62 (71-((n+1:ℕ):ℤ)) z hz9
    have hblam : b ≫ SyntheticCategory.lam.app X=0 := by
      have hh := congrArg (fun g => e.hom ≫ g)
        (restriction_lift_lambda model.quotients.coherence n a)
      have heq : b ≫ SyntheticCategory.lam.app X = lambdaMultiply (n+1) a := by
        simpa only [b,z,e,F,R,X,lambdaMultiply,Iso.trans_hom,Iso.symm_hom,Iso.app_inv,eqToIso.hom,Category.assoc] using hh
      exact heq.trans ha
    have hb0 : b=0 := ker (71-((n+1:ℕ):ℤ)) (by omega) b hb9 hblam
    have hR : F.map a ≫ R=0 := by
      apply (Limits.comp_eq_zero_iff_of_epi e.hom).mp
      simpa only [b,z,Category.assoc] using hb0
    have hn0 := restriction_lift_zero n a hR
    change _ ≫ _ ≫ (lambdaPow n (Smn 62 71) ≫ a) = 0
    rw [hn0]
    simp only [Limits.comp_zero]
  have hker (w : ℤ) (hw : w≤69)
      (b : BiHom 62 w ((SyntheticCategory.biShift (0,-1)).obj (model.nu.functor.obj SphereSpectrum)))
      (hb : FiltrationAtLeast model.syntheticTower 9 b)
      (hf : b ≫ SyntheticCategory.lam.app _=0) : b=0 := by
    apply selected_homotopyMap_kernel_zero_from_f9 (.shift (0,-1) (.nu .sphere))
      (.nu .sphere) (lambdaPow 1 (model.nu.functor.obj SphereSpectrum)) 62 w _ b hb
    · rw [lambdaPow_one model.quotients.coherence]
      exact hf
    · intro s hs
      have hh := high_lambda_eMap_injective (w+1) (by omega) s (by omega)
      rw [show w+1-1=w by omega] at hh
      exact hh
  let aNu : BiHom 62 71 (model.nu.functor.obj SphereSpectrum) := a ≫ model.nu.unitIso.inv
  obtain ⟨k,hk⟩ := (KIP126.Literature.Standard.selected_realization_kernel (.nu .sphere) 62 71 aNu).mp (by
    change model.recovery.realization.map (a ≫ model.nu.unitIso.inv)=0
    rw [Functor.map_comp,ha,Limits.zero_comp])
  have hdesc : ∀ k : ℕ, lambdaMultiply k aNu=0 → lambdaMultiply 1 aNu=0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      cases k with
      | zero =>
        have ha0 : aNu=0 := by
          simpa only [lambdaMultiply,lambdaPow,Category.assoc,
            Limits.comp_eq_zero_iff_of_epi] using hk
        simp only [ha0,lambdaMultiply,Limits.comp_zero]
      | succ k =>
        cases k with
        | zero => exact hk
        | succ k =>
          apply ih (k+1) (by omega)
          exact lambda_power_descent_step
            (shifted_weight71_filtration9) hker (k+1) (by omega) aNu hk
  have hnu := hdesc k hk
  apply (cancel_mono model.nu.unitIso.inv).mp
  rw [Limits.zero_comp]
  simpa only [aNu,lambdaMultiply,Category.assoc] using hnu

end
end KIP126.Main.Internal.Theta
