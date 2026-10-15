module

public import KIP126.Def.ProofTools.Laws
import all KIP126.Def.ProofTools.GeneralizedMahowald.Coherence
import all KIP126.Def.ProofTools.DetectionOperations
import all KIP126.Def.ProofTools.StretchingRepresentatives

/-! The proved sphere cases of generalized Mahowald, retained from
GeneralizedMahowald/Proofs.lean:1996–2940 at bbac1fc05843 (MIT).
Shared detection, filtration and coherence arguments use the same fixed system. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 6000000
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
noncomputable section

private theorem sphere_first_quotient_label  (s t : ℤ)
    (y : Ambient model .sphere (s,t)) :
    (sphereFirstQuotient model.nu model.quotients.functoriality model.firstQuotient) s t
      (firstLabel model .sphere s t y ≫ XModLambdaN.map
        ((SyntheticCategory.biShift_zero.hom.app _) ≫ model.nu.unitIso.hom) 1) = y := by
  let e := SyntheticCategory.biShift_zero.app (model.nu.functor.obj SphereSpectrum) ≪≫ model.nu.unitIso
  let Q := (model.quotients.functoriality.functor 1).mapIso e
  let c : BiHom (t-s) t (XModLambdaN (nuZero model .sphere) 1) ≃ₗ[ℤ] Ambient model .sphere (s,t) :=
    Eq.mp (congrArg (fun z : ℤ => BiHom (t-s) z
      (XModLambdaN (nuZero model .sphere) 1) ≃ₗ[ℤ] Ambient model .sphere (s,t))
      (Int.add_zero t)) (model.firstQuotient .sphere 0 s t)
  change c ((firstLabel model .sphere s t y ≫ Q.hom) ≫ Q.inv) = y
  rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have cast_symm (n m : ℤ) (h : n = m)
      (e : BiHom (t-s) n (XModLambdaN (nuZero model .sphere) 1) ≃ₗ[ℤ]
        Ambient model .sphere (s,t)) (z : Ambient model .sphere (s,t)) :
      (congrArg (fun w => BiHom (t-s) w (XModLambdaN (nuZero model .sphere) 1)) h).mp
          (e.symm z) =
        ((congrArg (fun w => BiHom (t-s) w (XModLambdaN (nuZero model .sphere) 1) ≃ₗ[ℤ]
          Ambient model .sphere (s,t)) h).mp e).symm z := by
    subst m
    rfl
  have hc : firstLabel model .sphere s t y = c.symm y := by
    exact cast_symm (t+0) t (Int.add_zero t) (model.firstQuotient .sphere 0 s t) y
  rw [hc,LinearEquiv.apply_symm_apply]

private theorem sphere_finite_lambda_detects 
    (q : ℕ) (_hq : 0 < q) (s t : ℤ) (k : ℕ)
    (y : Ambient model .sphere (s,t))
    (α : BiHom (t-s) t (model.nu.functor.obj SphereSpectrum))
    (hα : α ≫ XModLambdaN.incl _ 1 =
      firstLabel model .sphere s t y ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (model.convergence (.quotient q (.nu .sphere))) (s,t,t-k)
      (finiteTargetLabel model .sphere q s t k y)
      (lambdaMultiply k α ≫ XModLambdaN.incl _ q) := by
  have family_page_id (X : SyntheticSpectrum) (r : ℤ) (i : Tridegree) :
      familyPageMap model.family (𝟙 X) r i = 𝟙 _ := by
    change (model.family.map (𝟙 X)).pageMap r i = 𝟙 _
    rw [SyntheticAdamsFamily.map_id,SpectralSequenceMorphism.pageMap_id]
  let a : BiHom (t-s) t (S_0_0 : SyntheticSpectrum) := α ≫ model.nu.unitIso.hom
  have hfirst : quotientClass 1 a =
      firstLabel model .sphere s t y ≫ XModLambdaN.map
        (SyntheticCategory.biShift_zero.hom.app _ ≫ model.nu.unitIso.hom) 1 := by
    dsimp only [quotientClass,a]
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hα,
      Category.assoc,←model.quotients.functoriality.map_comp]
    rfl
  have hl : (sphereFirstQuotient model.nu model.quotients.functoriality model.firstQuotient) s t (quotientClass 1 a) = y := by
    rw [hfirst]
    exact sphere_first_quotient_label s t y
  have hs := model.sphereDetectionCompatible.homotopy_lambda s t k a
  rw [hl] at hs
  have hforw : familyPageMap model.family model.nu.unitIso.hom 2 (s,t,t-k)
      (targetNuLabel model .sphere s t k y) = model.comparison.sphereE2 s t k y := by
    let z : (model.family.obj (nuZero model .sphere)).E₂ (s,t,t-k) := by
      simpa [SyntheticAdamsSS.E₂] using model.comparison.nuE2 .sphere 0 s t k y
    exact (ConcreteCategory.congr_hom (family_page_comp
      (SyntheticCategory.biShift_zero.hom.app _) model.nu.unitIso.hom 2 (s,t,t-k)) z).trans
        (model.comparison.sphere_nu s t k y)
  have hback : familyPageMap model.family model.nu.unitIso.inv 2 (s,t,t-k)
      (model.comparison.sphereE2 s t k y) = targetNuLabel model .sphere s t k y := by
    rw [←hforw,←ModuleCat.comp_apply,family_page_comp,Iso.hom_inv_id,family_page_id]
    rfl
  have hc : lambdaMultiply k a ≫ model.nu.unitIso.inv = lambdaMultiply k α := by
    dsimp only [lambdaMultiply,a]
    simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have hn := detects_map .sphere (.nu .sphere) model.nu.unitIso.inv
    (s,t,t-k) _ _ hs
  have hn' : Detects (model.convergence (.nu .sphere)) (s,t,t-k)
      (targetNuLabel model .sphere s t k y) (lambdaMultiply k α) := by
    exact (congrArg₂ (Detects (model.convergence (.nu .sphere)) (s,t,t-k)) hback hc).mp hn
  exact detects_map (.nu .sphere) (.quotient q (.nu .sphere))
    (XModLambdaN.incl _ q) (s,t,t-k) _ _ hn'

end
end KIP126.ProofTools.Internal.Mahowald
