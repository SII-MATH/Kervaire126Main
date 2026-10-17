module
import all KIP126.Main.Internal.Theta.RealizationKernel
import all KIP126.Main.Internal.Choice.OrderTwo
/-! Select an order-two representative in weight 70 by removing the odd-primary
part with an odd multiple. The final realization-kernel descent is adapted from
Lambda.lean:116–140 and 1426–1460, bbac1fc05843 (MIT). No exponent-two
assertion is made for arbitrary integral representatives. -/
@[expose] section
namespace KIP126.Main.Internal.Theta
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic KIP126.Literature KIP126.Kervaire.Route
open KIP126.Classical.Adams
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum Spectrum)
noncomputable section
local instance shiftAdditive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := SyntheticSpectrum) p).Additive :=
  KIP126.AdamsSynthetic.Standard.graded_shiftAdditive p
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem classical_infinity_double (p : ℤ × ℤ)
    (x : (model.classical.sphere.ssData p).eInfty) : x+x=0 := by
  let D := model.classical.sphere.ssData p
  let n : WithTop ℕ := ↑(2-model.classical.sphere.r₀).toNat
  have hpage (y : D.page n) : y+y=0 := by
    change model.classical.sphere.Page 2 p at y
    letI := model.sphereAlgebra.scalar p
    change y+y=0
    calc
      y+y = (1 : ZMod 2) • y + (1 : ZMod 2) • y := by simp only [one_smul]
      _ = ((1 : ZMod 2)+1) • y := (add_smul _ _ _).symm
      _ = 0 := by rw [show (1 : ZMod 2)+1=0 from rfl,zero_smul]
  haveI : Epi (D.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (D.pageπ ⊤)).mp inferInstance x
  have h := D.infinity_projection_eq_of_page_projection_eq n (z+z) 0 (by
    simp only [map_add, map_zero]
    exact hpage _)
  simpa only [map_add,map_zero] using h

private theorem classical_doubling_filtration (s : ℤ)
    (a : HomotopyGroup (C := Spectrum) 62 SphereSpectrum)
    (ha : a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s 62) :
    a+a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule (s+1) 62 := by
  let F := (model.classicalTower.tower SphereSpectrum).filtration
  let e : (model.classical.sphere.ssData (s,62+s)).eInfty ≅ F.associatedGraded s 62 := by
    simpa only [add_sub_cancel_right,F,ClassicalObject.obj,ClassicalAdamsFamily.sphere]
      using (model.classicalConvergence .sphere).identification (s,62+s)
  have hdouble (x : F.associatedGraded s 62) : x+x=0 := by
    apply (ModuleCat.mono_iff_injective e.inv).mp inferInstance
    simpa only [map_add,map_zero] using classical_infinity_double (s,62+s) (e.inv x)
  have hm : a ∈ ModuleCat.subobjectModule _ (F.F s 62) := by
    simpa only [F,AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using ha
  obtain ⟨b,hb⟩ := hm
  have hg : F.toAssociatedGraded s 62 (b+b)=0 := by
    rw [map_add]
    exact hdouble _
  have hn := (F.toAssociatedGraded_eq_zero_iff s 62 (b+b)).mp hg
  rw [map_add,hb] at hn
  simpa only [F,AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using hn

private theorem classical_stem62_tail_step (s : ℤ) (hs : 34≤s)
    (a : HomotopyGroup (C := Spectrum) 62 SphereSpectrum)
    (ha : a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s 62) :
    a ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule (s+1) 62 := by
  let D := model.classical.sphere.ssData (s,62+s)
  let n : WithTop ℕ := ↑(2-model.classical.sphere.r₀).toNat
  have hp : Subsingleton (D.page n) :=
    KIP126.Literature.Standard.sphereVanishing s (62+s) (by omega) (by omega)
  have hinf : Subsingleton D.eInfty := by
    have hall (e : D.eInfty) : e=0 := by
      haveI : Epi (D.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
      obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (D.pageπ ⊤)).mp inferInstance e
      have h := D.infinity_projection_eq_of_page_projection_eq n z 0 (hp.elim _ _)
      simpa only [map_zero] using h
    exact ⟨fun x y => (hall x).trans (hall y).symm⟩
  let F := (model.classicalTower.tower SphereSpectrum).filtration
  let e : D.eInfty ≅ F.associatedGraded s 62 := by
    simpa only [D,add_sub_cancel_right,F,ClassicalObject.obj,ClassicalAdamsFamily.sphere]
      using (model.classicalConvergence .sphere).identification (s,62+s)
  letI : Subsingleton (F.associatedGraded s 62) :=
    (ModuleCat.mono_iff_injective e.inv).mp inferInstance |>.subsingleton
  have hm : a ∈ ModuleCat.subobjectModule _ (F.F s 62) := by
    simpa only [F,AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using ha
  obtain ⟨b,hb⟩ := hm
  have hg : F.toAssociatedGraded s 62 b=0 := Subsingleton.elim _ _
  have hn := (F.toAssociatedGraded_eq_zero_iff s 62 b).mp hg
  rw [hb] at hn
  simpa only [F,AbstractAdamsTower.filtration,OrderIso.apply_symm_apply] using hn

/-- Remove the odd-primary part by an odd multiple, preserving every mod-two
label. Only a finite filtration argument is used, not integral separation. -/
private theorem classical_stem62_odd_multiple_primary
    (a : HomotopyGroup (C := Spectrum) 62 SphereSpectrum) :
    ∃ n : ℕ, Odd n ∧ ∃ k : ℕ, (2^k : ℕ) • (n • a)=0 := by
  have hpower (k : ℕ) : (2^k : ℕ) • a ∈
      (model.classicalTower.tower SphereSpectrum).filtrationSubmodule k 62 := by
    induction k with
    | zero =>
      simp only [pow_zero,one_nsmul,Nat.cast_zero]
      refine ⟨a ≫ (model.classicalTower.tower SphereSpectrum).zeroIso.inv,?_⟩
      change (a ≫ (model.classicalTower.tower SphereSpectrum).zeroIso.inv) ≫
        (model.classicalTower.tower SphereSpectrum).projection 0=a
      simp only [AbstractAdamsTower.projection,Int.toNat_zero,
        (model.classicalTower.tower SphereSpectrum).map_self]
      erw [Category.assoc,Category.id_comp,Iso.inv_hom_id,Category.comp_id]
    | succ k ih =>
      have h := classical_doubling_filtration k ((2^k : ℕ) • a) ih
      simpa only [pow_succ,mul_nsmul,two_nsmul,Nat.cast_add,Nat.cast_one] using h
  let b := (2^34 : ℕ) • a
  have hall (s : ℕ) (hs : 34≤s) :
      b ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule s 62 := by
    induction s,hs using Nat.le_induction with
    | base => exact hpower 34
    | succ s hs ih =>
      simpa only [Nat.cast_add,Nat.cast_one] using classical_stem62_tail_step s (by omega) b ih
  obtain ⟨n,hn,_,hz⟩ := KIP126.AdamsSynthetic.Standard.classical_sphere_separated 62 b (by
    intro s
    by_cases hs : 34≤s
    · exact hall s hs
    · exact (model.classicalTower.tower SphereSpectrum).filtrationSubmodule_antitone 62
        (by omega : (s:ℤ)≤34) (hpower 34))
  refine ⟨n,hn,34,?_⟩
  simpa only [b,smul_comm n (2^34 : ℕ) a] using hz

private theorem lambda_h0_map_zero_iff
    {T : Type*} [Category T] [Preadditive T] (R : SyntheticSpectrum ⥤ T) [R.Additive]
    (coh : BiShiftCoherence SyntheticSpectrum) (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum))
    (hlambda : lambdaMultiply 1 h0 = KIP126.Literature.Route.syntheticTwo)
    (b : BiHom 62 70 (S_0_0 : SyntheticSpectrum)) :
    R.map (lambdaMultiply 1 (sphereProduct h0 b)) = 0 ↔ R.map (b+b) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
    let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum) (62,70)
    have ht : R.map (F.map (lambdaMultiply 1 h0) ≫ b) = 0 ↔
        R.map (F.map (SyntheticCategory.lam.app (Smn 0 1))) ≫ R.map (F.map h0) ≫ R.map b = 0 := by
      simp only [lambdaMultiply, lambdaPow_one coh, F, eqToHom_refl,
        Functor.map_comp, Category.id_comp, Category.assoc, Limits.comp_eq_zero_iff_of_epi]
    simp only [lambdaMultiply, lambdaPow_one coh, eqToHom_refl,
      Functor.map_comp, Category.id_comp, Limits.comp_eq_zero_iff_of_epi]
    dsimp only [sphereProduct]
    have hn := SyntheticCategory.lam.naturality
      ((SyntheticCategory.biShift_comp (0,1) (62,70)).inv.app (S_0_0 : SyntheticSpectrum))
    simp only [Prod.mk_add_mk, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
    erw [← hn]
    simp only [Functor.map_comp, Category.assoc, Limits.comp_eq_zero_iff_of_epi]
    erw [coh.lambda_comm (62,70) (Smn 0 1)]
    simp only [Functor.map_comp, Category.assoc, Limits.comp_eq_zero_iff_of_epi]
    change R.map (F.map (SyntheticCategory.lam.app (Smn 0 1))) ≫
      R.map (F.map h0) ≫ R.map b = 0 ↔ _
    rw [← ht, hlambda]
    simp only [KIP126.Literature.Route.syntheticTwo, Functor.id_obj, Functor.map_comp, two_smul, Functor.map_add,
      Category.assoc, Preadditive.add_comp,
      ← Preadditive.comp_add, Limits.comp_eq_zero_iff_of_epi]

private theorem two_torsion_62_70_of_realization_primary
    (b : BiHom 62 70 (S_0_0 : SyntheticSpectrum))
    (hprimary : ∃ n : ℕ, (2^n : ℕ) •
      KIP126.Literature.Standard.realizeSphere 62 70 b=0) : b + b = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
    letI := Choice.realization_additive
    have hb : model.recovery.realization.map (b+b) = 0 := by
      rw [Functor.map_add]
      let α : HomotopyGroup (C := Spectrum) 62 SphereSpectrum :=
        (KIP126.Literature.Standard.realization_sphere 62 70).hom ≫ model.recovery.realization.map b ≫
          model.recovery.realization.map model.nu.unitIso.inv ≫ model.recovery.nuRealizationIso.hom.app SphereSpectrum
      have h := KIP126.Literature.Standard.stem62_exponent_two α hprimary
      apply (cancel_epi (KIP126.Literature.Standard.realization_sphere 62 70).hom).mp
      apply (cancel_mono (model.recovery.realization.map model.nu.unitIso.inv)).mp
      apply (cancel_mono ((model.recovery.nuRealizationIso.app SphereSpectrum).hom)).mp
      erw [Preadditive.comp_add, Preadditive.add_comp, Preadditive.add_comp,
        Limits.comp_zero, Limits.zero_comp, Limits.zero_comp]
      repeat erw [Category.assoc]
      exact h
    have hl := (lambda_h0_map_zero_iff model.recovery.realization model.quotients.coherence
      KIP126.Literature.Standard.syntheticH0 KIP126.Literature.Standard.toda_lambda_h0 b).mpr hb
    have hp : model.recovery.realization.map (sphereProduct KIP126.Literature.Standard.syntheticH0 b) = 0 := by
      have hm : lambdaMultiply 1 (sphereProduct KIP126.Literature.Standard.syntheticH0 b) =
          lambdaMultiply 1 (𝟙 (Smn (Syn := SyntheticSpectrum) 62 71)) ≫ sphereProduct KIP126.Literature.Standard.syntheticH0 b := by
        simp only [lambdaMultiply, Category.assoc, Category.id_comp]
        rfl
      have hc := congrArg (fun z => (KIP126.Literature.Standard.realization_sphere 62 70).hom ≫ z) hl
      rw [hm, Functor.map_comp, ← Category.assoc] at hc
      erw [KIP126.Literature.Standard.realization_lambda 62 71 1] at hc
      exact (Limits.comp_eq_zero_iff_of_epi (KIP126.Literature.Standard.realization_sphere 62 71).hom).mp
        (by simpa only [Limits.comp_zero] using hc)
    have hk := lambda_kills_realization_kernel_62_71 (sphereProduct KIP126.Literature.Standard.syntheticH0 b) hp
    exact (lambda_h0_map_zero_iff (𝟭 SyntheticSpectrum) model.quotients.coherence KIP126.Literature.Standard.syntheticH0 KIP126.Literature.Standard.toda_lambda_h0 b).mp hk

/-- Select an order-two representative of the same first-quotient class.
An odd multiple removes the integral odd-primary component. -/
private theorem first_quotient_order_two_lift
    (x : model.classical.sphere.Page 2 (8,70))
    (b₀ : BiHom 62 70 (S_0_0 : SyntheticSpectrum))
    (hb₀ : KIP126.Literature.sphereFirstQuotient model 8 70 (quotientClass 1 b₀)=x) :
    ∃ b : BiHom 62 70 (S_0_0 : SyntheticSpectrum),
      KIP126.Literature.sphereFirstQuotient model 8 70 (quotientClass 1 b)=x ∧ b+b=0 := by
  obtain ⟨n,hn,hprimary⟩ := classical_stem62_odd_multiple_primary
    (KIP126.Literature.Standard.realizeSphere 62 70 b₀)
  refine ⟨n • b₀,?_,?_⟩
  · have hx : x+x=0 := by
      letI := model.sphereAlgebra.scalar (8,70)
      calc
        x+x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := by simp only [one_smul]
        _ = ((1 : ZMod 2)+1) • x := (add_smul _ _ _).symm
        _ = 0 := by rw [show (1 : ZMod 2)+1=0 from rfl,zero_smul]
    have hq : quotientClass 1 (n • b₀)=n • quotientClass 1 b₀ := by
      simp only [quotientClass,Preadditive.nsmul_comp]
    rw [hq,map_nsmul,hb₀]
    obtain ⟨k,rfl⟩ := hn
    rw [add_nsmul,one_nsmul,mul_nsmul,two_nsmul,hx,nsmul_zero,zero_add]
  · apply two_torsion_62_70_of_realization_primary
    simpa only [map_nsmul] using hprimary

end
end KIP126.Main.Internal.Theta
