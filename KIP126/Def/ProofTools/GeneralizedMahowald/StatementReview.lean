module
import all KIP126.Def.ProofTools.GeneralizedMahowald.RotatedNuPremises
import all KIP126.Def.ProofTools.GeneralizedMahowald.BottomNuInjection
import KIP126.Def.Literature.Standard

/-! A concrete refutation of the locked exact-source MH2 law. All inputs
are supplied by the actual rotated nu triangle, its proved premise vector,
and the actual bottom-map leading image of d2(h4). This file does not call
the theorem generalizedMahowald. -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
set_option Elab.async false

private theorem zero_normalized_leading_nonzero (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (he : normalizedExponent model.classicalTower f=0)
    (x : Ambient model X (3,17))
    (hnu : familyPageMap model.family (model.nu.functor.map f) 2 (3,17,17)
      (nuWeightLabel model X 3 17 17 (by omega) x)≠0) :
    familyPageMap model.family (model.normalizedMap X Y f).map 2
      (3,(17-3)+3,17+normalizedExponent model.classicalTower f)
      (infiniteSourceForExtension model X Y f 3 17 x)≠0 := by
  have core (k : ℕ) (hk : k=0)
      (M : (SyntheticCategory.biShift (0,(k:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
          model.nu.functor.obj (Y.obj model.auxiliary))
      (hM : lambdaToPositivePow k _≫M=model.nu.functor.map f) :
      familyPageMap model.family M 2 (3,(17-3)+3,17+k)
        (regradeE2 (by simp) (model.comparison.nuE2 X k 3 17 0 x))≠0 := by
    subst k
    rw [normalized_zero_map_form rfl M _ hM]
    simp only [eqToHom_refl,Category.id_comp]
    rw [←family_page_comp,ModuleCat.comp_apply]
    exact hnu
  exact core _ he _ (model.normalizedMap X Y f).factorization


private theorem candidate_zero_differential :
    DifferentialAt model rotatedNuRouteTriangle.Z 3 (1,16) (4,18) 0 0 := by
  refine ⟨by decide,?_,0,0,RepresentsOnPage.zero (by decide),RepresentsOnPage.zero (by decide),?_⟩
  · rw [model.classical.differentialDegree]
    rfl
  · simp

/-- All geometric inputs and original hypotheses are now supplied by the
proved rotated-triangle modules. Only leading-image nonvanishing is explicit. -/
private theorem mh2_candidate_refutation_of_bottom_nonzero
    (hbottom : familyPageMap model.family
      (model.normalizedMap .sphere .nuCofiber rotatedNuRouteTriangle.f).map 2
      (3,(17-3)+3,17+normalizedExponent model.classicalTower rotatedNuRouteTriangle.f)
      (infiniteSourceForExtension model .sphere .nuCofiber rotatedNuRouteTriangle.f 3 17
        mh2BoundaryClass) ≠ 0) :
    GeneralizedMahowaldLaw model rotatedNuRouteTriangle → False := by
  intro hLaw
  have he := rotated_nu_exponent_sum
  have htriangle : NormalizedTriangleCompatible model rotatedNuRouteTriangle he :=
    rotated_nu_normalized_distinguished
  obtain ⟨sx,hsusp,hh,hcross,hg⟩ := rotated_nu_remaining_premises
  have hef := rotated_nu_f_exponent
  have heg := rotated_nu_g_exponent
  have heh : normalizedExponent model.classicalTower rotatedNuRouteTriangle.h=1 := by
    rw [hef,heg] at he
    omega
  have hx : IsCycle model .sphere 1 (3,17) mh2BoundaryClass :=
    ⟨by decide,boundaries_le_cycles model .sphere (3,17) 2 1 mh2BoundaryClass_boundary⟩
  have hy : IsCycle model .nuCofiber 1 (4,18) 0 := ⟨by decide,Submodule.zero_mem _⟩
  have hxBar : IsCycle model rotatedNuRouteTriangle.Z 2 (1,16) 0 :=
    ⟨by decide,Submodule.zero_mem _⟩
  have hyBar : IsPermanent model rotatedNuRouteTriangle.Z (4,18) 0 := Submodule.zero_mem _
  have H := hLaw he htriangle 1 0 2 1 16
  dsimp only at H
  norm_num only [hef,heg,heh] at H
  obtain ⟨_,y',hy',_⟩ := H mh2BoundaryClass 0 0 0 sx
    (by decide) (by decide) (by decide) hx hy hxBar hyBar hsusp hh
    candidate_zero_differential (Or.inr hcross) hg
  exact nonzero_leading_image_no_positive_extension .sphere .nuCofiber
    rotatedNuRouteTriangle.f 3 1 3 17 (by decide) mh2BoundaryClass hbottom ⟨y',hy'⟩

/-- The actual rotated nu triangle and the actual boundary d2(h4) refute
this exact-source version of the generalized Mahowald law. No invocation
of the theorem generalizedMahowald occurs in this proof or its new helpers. -/
private theorem rotated_nu_generalized_mahowald_law_false :
    ¬GeneralizedMahowaldLaw model rotatedNuRouteTriangle := by
  apply mh2_candidate_refutation_of_bottom_nonzero
  apply zero_normalized_leading_nonzero .sphere .nuCofiber rotatedNuRouteTriangle.f
    rotated_nu_f_exponent mh2BoundaryClass
  exact nu_bottom_boundary_leading_nonzero

end
end KIP126.ProofTools.Internal.Mahowald
