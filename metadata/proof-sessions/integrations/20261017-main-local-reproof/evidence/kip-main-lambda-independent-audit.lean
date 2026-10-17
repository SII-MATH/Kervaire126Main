module
public import KIP126.ProofTools.Operations
import Lean
import all KIP126.ProofTools.Operations
import all KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.Literature.Standard
import all KIP126.AdamsSynthetic.Standard.Separation
import all KIP126.Main.Internal.Theta.NoCrossing
import all KIP126.Main.Internal.Choice.LambdaInjectivity

/-! Original filtered realization-kernel descent,
Main/Solution/Computation/Lambda.lean:1080–1420, bbac1fc05843 (MIT).
The low stem staircase is proved in NoCrossing. The actual λ-kernel is
reconstructed from its cofiber first-quotient class; finite-quotient
filtration, Bockstein d₂, and the selected permanent lift close the kernel.
Convergence and shifts use the same fixed public upstream system. -/
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

private theorem route_regrade_zero {m m' w w' : ℤ} {Y : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') :
    homotopyRegrade hm hw (0 : BiHom m w Y) = 0 := by
  subst m'; subst w'; rfl

private theorem route_susp_inverse_zero (m n k l : ℤ) (Y : SyntheticSpectrum) :
    (susp_invariance m n k l Y).symm 0 = 0 := by
  letI := model.exactness.shiftAdditive (k,l)
  apply (susp_invariance m n k l Y).injective
  rw [Equiv.apply_symm_apply]
  simp [susp_invariance]

-- Exact specialization required at the integration point: X=.sphere,
-- s=w-63,t=w. Then t-s=63, d2 target=(w-61,w+1),
-- its actual first-quotient element has stem62, weight w+1.
private theorem route_actual_boundary_d2_zero
    (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (b : BiHom (t-s) t (XModLambdaN (nuZero model X) 1))
    (hb : b = firstLabel model X s t x)
    (hδ :
      b ≫ ((model.quotients.tower (nuZero model X)).triangle
        (by decide : 0<1) (by decide : 1<2)).delta =
      b ≫ XModLambdaN.proj (nuZero model X) 1 ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(1:ℤ))).map
            (XModLambdaN.incl (nuZero model X) (2-1))))
    (hprojection :
      b ≫ XModLambdaN.proj (nuZero model X) 1 ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(1:ℤ))).map
            (XModLambdaN.incl (nuZero model X) (2-1))) = 0) :
    (model.classical.obj (X.obj model.auxiliary)).d 2 (s,t) x = 0 := by
  have hArrow : b ≫ bocksteinArrow model X 1 (by decide) = 0 := by
    dsimp only [bocksteinArrow]
    rw [← Category.assoc b]
    change (b ≫ ((model.quotients.tower (nuZero model X)).triangle
      (by decide : 0<1) (by decide : 1<2)).delta) ≫ _ ≫ _ ≫ _ = 0
    rw [hδ, hprojection]
    simp only [zero_comp]
  have hLabel : bocksteinLabel model X 1 (by decide) s t b = 0 := by
    dsimp only [bocksteinLabel]
    rw [hArrow]
    simp only [route_regrade_zero, route_susp_inverse_zero, map_zero]
  obtain ⟨a,ha,hd⟩ := KIP126.Literature.Standard.bhs_bockstein X 1
    (by decide) s t x ⟨x,RepresentsOnPage.self_two x⟩
  have hab : a = b := by
    simpa only [(model.quotients.tower (nuZero model X)).rho_id,
      Category.comp_id, hb] using ha
  subst a
  rw [hLabel] at hd
  have hd2 : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      2 (s,t) (s+2,t+1) x 0 := by
    have hcast : ((1:ℕ):ℤ)=1 := by norm_num
    rw [hcast] at hd
    have ht : (s+1+1,t+1) = (s+2,t+1) := by
      ext <;> dsimp <;> omega
    rw [ht] at hd
    exact hd
  obtain ⟨hdeg,heq⟩ := hd2.eq_on_page_two
  let f := eqToHom (congrArg
    ((model.classical.obj (X.obj model.auxiliary)).Page 2) hdeg)
  have hinj := (ModuleCat.mono_iff_injective f).mp (inferInstance : Mono f)
  apply hinj
  simpa only [f, ModuleCat.comp_apply, map_zero] using heq

private theorem route_permanent_of_d2_and_no_late
    (E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (hstart : E.r₀=2)
    (p : ℤ×ℤ) (x : E.Page 2 p) (hd2 : E.d 2 p x=0)
    (hout : ∀ r : ℤ, 3≤r → E.d r p=0) :
    IsPermanentCycle E p x := by
  exact isPermanentCycle_of_reachesPage E 3 (by omega) p x
    ((PageThree.reachesPage_iff_d2_eq_zero (by omega) p x).mpr hd2) hout

private theorem lambda_kernel_zero_from_permanent_d2
    (X : ClassicalObject) (s t : ℤ)
    (hperm : ∀ x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t),
      (model.classical.obj (X.obj model.auxiliary)).d 2 (s,t) x = 0 →
      IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) (s,t) x)
    (a : BiHom (t-s-1) t ((SyntheticCategory.biShift (0,-1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))))
    (halambda : a ≫ SyntheticCategory.lam.app _ = 0)
    (haQ : a ≫ (SyntheticCategory.biShift (0,-1)).map
      (XModLambdaN.incl (model.nu.functor.obj (X.obj model.auxiliary)) 1) = 0) : a=0 := by
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  let F := shiftFunctor SyntheticSpectrum (1:ℤ)
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  have hshift : F.map a ≫ F.map (lambdaPow 1 V) = 0 := by
    rw [←Functor.map_comp,lambdaPow_one model.quotients.coherence,halambda,Functor.map_zero]
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle V 1).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished V 1) (F.map a) hshift
  let eS : Smn (Syn:=SyntheticSpectrum) (t-s) t ≅ F.obj (Smn (t-s-1) t) :=
    ((biShiftAddIso (t-s-1,t) (1,0) (t-s,t) (by ext <;> dsimp <;> omega)).app S_0_0).symm ≪≫
      (SyntheticCategory.biShift_compat 1).app (Smn (t-s-1) t)
  let b' : BiHom (t-s) t (XModLambdaN V 1) := eS.hom ≫ b
  have hboundary : b' ≫ XModLambdaN.proj V 1 = eS.hom ≫ F.map a := by
    simpa [b',F,XModLambdaN.cofiberTriangle,Category.assoc] using
      congrArg (fun f => eS.hom ≫ f) hb.symm
  have hprojection : b' ≫ XModLambdaN.proj V 1 ≫ F.map (G.map (XModLambdaN.incl V 1)) = 0 := by
    rw [←Category.assoc,hboundary,Category.assoc,←Functor.map_comp,haQ,Functor.map_zero,comp_zero]
  let e : nuZero model X ≅ V := SyntheticCategory.biShift_zero.app V
  let b₀ : BiHom (t-s) t (XModLambdaN (nuZero model X) 1) := b' ≫ XModLambdaN.map e.inv 1
  have hprojection₀ : b₀ ≫ XModLambdaN.proj (nuZero model X) 1 ≫
      F.map (G.map (XModLambdaN.incl (nuZero model X) 1)) = 0 := by
    calc
      b₀ ≫ XModLambdaN.proj (nuZero model X) 1 ≫
          F.map (G.map (XModLambdaN.incl (nuZero model X) 1)) =
          b' ≫ XModLambdaN.proj V 1 ≫ F.map (G.map
            (e.inv ≫ XModLambdaN.incl (nuZero model X) 1)) := by
        dsimp only [b₀]
        rw [Category.assoc,←Category.assoc (XModLambdaN.map e.inv 1),XModLambdaN.proj_naturality]
        simp [F,G,Functor.map_comp,Category.assoc]
      _ = (b' ≫ XModLambdaN.proj V 1 ≫ F.map (G.map (XModLambdaN.incl V 1))) ≫
          F.map (G.map (XModLambdaN.map e.inv 1)) := by
        rw [XModLambdaN.incl_naturality]
        simp only [Functor.map_comp,Category.assoc]
      _ = 0 := by rw [hprojection,zero_comp]
  obtain ⟨x,hx⟩ := Choice.nu_first_quotient_label_surjective X s t b₀
  have hd : (model.classical.obj (X.obj model.auxiliary)).d 2 (s,t) x = 0 := by
    apply route_actual_boundary_d2_zero X s t x b₀ hx.symm
    · exact Choice.lambda_zero_shift_delta_evaluation X 1 2 (by decide) (by decide) (t-s) t b₀
    · simpa only [Nat.reduceSub, Nat.cast_one] using hprojection₀
  obtain ⟨c,hc⟩ := (KIP126.Literature.Standard.selected_permanent_lift X s t x).mp (hperm x hd)
  have hzero₀ : b₀ ≫ XModLambdaN.proj (nuZero model X) 1 = 0 := by
    change c ≫ XModLambdaN.incl _ 1 = firstLabel model X s t x at hc
    rw [←hx,←hc,Category.assoc,XModLambdaN.incl_comp_proj,comp_zero]
  have hzero : b' ≫ XModLambdaN.proj V 1 = 0 := by
    apply (cancel_mono (F.map (G.map e.inv))).mp
    simpa [b₀,Category.assoc,XModLambdaN.proj_naturality,F,G] using hzero₀
  have ha : F.map a = 0 := by
    apply (cancel_epi eS.hom).mp
    rw [←hboundary,hzero,comp_zero]
  exact F.map_injective (by simpa only [Functor.map_zero] using ha)

private theorem lambda_kernel_zero_from_filtration9
    (w : ℤ) (hw : w≤69)
    (a : BiHom 62 w ((SyntheticCategory.biShift (0,-1)).obj
      (model.nu.functor.obj (SphereSpectrum : KIP126.AdamsSynthetic.Standard.Spectrum))))
    (ha : FiltrationAtLeast model.syntheticTower 9 a)
    (halambda : a ≫ SyntheticCategory.lam.app _ = 0) : a=0 := by
  let V := model.nu.functor.obj (SphereSpectrum : KIP126.AdamsSynthetic.Standard.Spectrum)
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  have hfil : FiltrationAtLeast model.syntheticTower 9
      (a ≫ G.map (XModLambdaN.incl V 1)) :=
    KIP126.ProofTools.Operations.map_preserves_filtration
      (model.convergentMap (.shift (0,-1) (.nu .sphere))
        (.shift (0,-1) (.quotient 1 (.nu .sphere))) (G.map (XModLambdaN.incl V 1)))
      (62,w) 9 a ha
  have hQ : a ≫ G.map (XModLambdaN.incl V 1) = 0 :=
    Choice.lambda_shifted_finite_high_filtration_zero .sphere 1 (by decide) (0,-1)
      62 w 9 (by dsimp; omega) _ hfil
  have hperm (x : model.classical.sphere.Page 2 (w-63,w))
      (hx : model.classical.sphere.d 2 (w-63,w) x = 0) :
      IsPermanentCycle model.classical.sphere (w-63,w) x := by
    apply route_permanent_of_d2_and_no_late model.classical.sphere
      (model.classical.firstPage _) (w-63,w) x hx
    intro r hr
    ext y
    have h := actual_stem63_no_late (w-63) (by omega) r hr
    rw [show w-63+63=w by omega] at h
    exact h y
  have hker := lambda_kernel_zero_from_permanent_d2 .sphere (w-63) w hperm
  rw [show w-(w-63)-1=62 by omega] at hker
  exact hker a halambda hQ


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
    exact lambda_kernel_zero_from_filtration9 w hw b hb hf
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

open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
run_cmd do
  let env ← getEnv
  let roots := #[`KIP126.Main.Internal.Choice.nu_lambda_injective_from_source,
    `KIP126.Main.Internal.Choice.lambda_first_quotient_delta_evaluation,
    `KIP126.Main.Internal.Theta.lambda_kills_realization_kernel_62_71]
  let mut rows : Array Json := #[]
  for root in roots do
    let found := env.constants.toList.filter fun (name, _) =>
      ((privateToUserName? name).getD name) == root
    unless found.length == 1 do throwError "Missing unique root: {root}"
    let mut todo := #[found.head!.1]
    let mut visited : NameSet := {}
    let mut pending : Array String := #[]
    let mut localPending : Array String := #[]
    let mut used : Array String := #[]
    while let some name := todo.back? do
      todo := todo.pop
      if visited.contains name then continue
      visited := visited.insert name
      let some info := env.find? name | throwError "Missing {name}"
      let sourceName := ((privateToUserName? name).getD name)
      unless (`KIP126).isPrefixOf sourceName do continue
      used := used.push sourceName.toString
      let body := info.value? (allowOpaque := true)
      if info.type.hasSorry || body.any (·.hasSorry) then
        pending := pending.push sourceName.toString
        if (`KIP126.Main).isPrefixOf sourceName then
          localPending := localPending.push sourceName.toString
      todo := todo ++ info.type.getUsedConstants
      if let some value := body then todo := todo ++ value.getUsedConstants
    rows := rows.push <| Json.mkObj [
      ("root",toJson root.toString),
      ("reachable_project_count",toJson used.size),
      ("project_constants",toJson (used.qsort (· < ·))),
      ("pending_direct_project",toJson (pending.qsort (· < ·))),
      ("pending_direct_main",toJson (localPending.qsort (· < ·)))]
  liftIO <| IO.FS.writeFile "/tmp/kip-main-lambda-independent-deps.json" (Json.arr rows).pretty
  logInfo "Independent lambda dependency capture completed"
