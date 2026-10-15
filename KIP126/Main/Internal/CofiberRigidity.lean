module

public import KIP126.Main.SectionSeven.NormalizedNu
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.QuotientCalculus
import all KIP126.Main.Internal.Selected.DetectionOperations
public import KIP126.Def.ProofTools.Operations

/-! Proof port of CnuRigidity.lean:199–211, 318–440 at bbac1fc05843 (MIT).
The original bottom-cell argument uses the actual E₆ survival and the BHS
quotient by B₅. All lemmas here are proved; upstream data are called directly. -/
@[expose] section
namespace KIP126.Main.Internal.Rigidity
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.ProofTools.Operations
open KIP126.Main.Internal KIP126.Main.Internal.Selected
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem sphere_zero_weight_label_14_139
    (x : model.classical.sphere.Page 2 (14,139))
    (a : BiHom 125 139 (S_0_0 : SyntheticSpectrum))
    (ha : Detects (model.convergence .sphere) (14,139,139)
      (model.comparison.sphereE2 14 139 0 x) a) :
    sphereFirstQuotient model 14 139 (quotientClass 1 a)=x := by
  let y := sphereFirstQuotient model 14 139 (quotientClass 1 a)
  have hd := detects_map .sphere (.quotient 1 .sphere)
    (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 1) (14,139,139) _ a ha
  have hd' := model.sphereDetectionCompatible.first_quotient 14 139 y
  have hy : (sphereFirstQuotient model 14 139).symm y=quotientClass 1 a :=
    (sphereFirstQuotient model 14 139).symm_apply_apply _
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hy
  rw [hy] at hd'
  obtain ⟨e,he,hf⟩ := detects_infinity_equal (.quotient 1 .sphere) (14,139,139)
    (quotientClass 1 a) _ _ hd hd'
  let g := XModLambdaN.map model.nu.unitIso.inv 1
  have he' := family_infinity_representative_map g (14,139,139) _ _ he
  have hf' := family_infinity_representative_map g (14,139,139) _ _ hf
  change HasInfinityRepresentative _ 2 (14,139,139)
    (familyPageMap model.family g 2 (14,139,139) (quotientLabel 1 14 139 0 x)) _ at he'
  change HasInfinityRepresentative _ 2 (14,139,139)
    (familyPageMap model.family g 2 (14,139,139) (quotientLabel 1 14 139 0 y)) _ at hf'
  have hlx := sphere_quotient_label_to_nu 1 0 14 139 x
  have hly := sphere_quotient_label_to_nu 1 0 14 139 y
  change familyPageMap model.family g 2 (14,139,139) (quotientLabel 1 14 139 0 x)=_ at hlx
  change familyPageMap model.family g 2 (14,139,139) (quotientLabel 1 14 139 0 y)=_ at hly
  rw [hlx] at he'
  rw [hly] at hf'
  have hi (v : model.classical.sphere.Page 2 (14,139)) :=
    KIP126.Literature.Standard.eInfinity_finite_labels .sphere 1 (by decide)
      14 139 139 (by decide) v ((model.family.map g).eInftyMap (14,139,139) e)
  obtain ⟨hx,hxq⟩ := (hi x).mp he'
  obtain ⟨hy,hyq⟩ := (hi y).mp hf'
  let xx : cycles model .sphere 1 (14,139) := ⟨x,hx⟩
  let yy : cycles model .sphere 1 (14,139) := ⟨y,hy⟩
  have heq : subquotientClass _ (boundaries model .sphere 1 (14,139)) xx =
      subquotientClass _ (boundaries model .sphere 1 (14,139)) yy := hxq.symm.trans hyq
  have hz : subquotientClass _ (boundaries model .sphere 1 (14,139)) (xx-yy)=0 := by
    rw [map_sub,heq,sub_self]
  have hm := (subquotientClass_eq_zero_iff _ _ (xx-yy)).mp hz
  change x-y ∈ boundaries model .sphere 1 (14,139) at hm
  rw [boundaries_one model .sphere (14,139),Submodule.mem_bot] at hm
  exact (sub_eq_zero.mp hm).symm

theorem sphere_to_nu_label (X : ClassicalObject)
    (f : SphereSpectrum ⟶ X.obj model.auxiliary)
    (x : model.classical.sphere.Page 2 (14,139)) :
    familyPageMap model.family (model.nu.unitIso.inv ≫ model.nu.functor.map f) 2 (14,139,139-(4:ℕ))
      (model.comparison.sphereE2 14 139 4 x) =
    targetNuLabel model X 14 139 4 ((model.classical.map f).pageMap 2 (14,139) x) := by
  let nx : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj SphereSpectrum))).E₂ (14,139,139-(4:ℕ)) := by
    simpa only [ClassicalObject.obj,add_zero] using model.comparison.nuE2 .sphere 0 14 139 4 x
  let ny : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))).E₂ (14,139,139-(4:ℕ)) := by
    simpa only [add_zero] using model.comparison.nuE2 X 0 14 139 4 ((model.classical.map f).pageMap 2 (14,139) x)
  have hs : familyPageMap model.family
      (SyntheticCategory.biShift_zero.hom.app _ ≫ model.nu.unitIso.hom) 2 (14,139,139-(4:ℕ)) nx =
      model.comparison.sphereE2 14 139 4 x := by
    exact model.comparison.sphere_nu 14 139 4 x
  have hn : familyPageMap model.family ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f))
      2 (14,139,139-(4:ℕ)) nx = ny := by
    exact model.comparison.nu_natural .sphere X f 0 14 139 4 x
  rw [← hs]
  have hc := ConcreteCategory.congr_hom
    (family_page_comp
      (SyntheticCategory.biShift_zero.hom.app _ ≫ model.nu.unitIso.hom)
      (model.nu.unitIso.inv ≫ model.nu.functor.map f) 2 (14,139,139-(4:ℕ))) nx
  erw [hc]
  have hm : (SyntheticCategory.biShift_zero.hom.app _ ≫ model.nu.unitIso.hom) ≫
      (model.nu.unitIso.inv ≫ model.nu.functor.map f) =
      (SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f) ≫
        SyntheticCategory.biShift_zero.hom.app _ := by
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    exact (SyntheticCategory.biShift_zero.hom.naturality (model.nu.functor.map f)).symm
  rw [hm]
  erw [← ConcreteCategory.congr_hom (family_page_comp
    ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f))
    (SyntheticCategory.biShift_zero.hom.app _) 2 (14,139,139-(4:ℕ))) nx]
  change familyPageMap model.family (SyntheticCategory.biShift_zero.hom.app _) 2 (14,139,139-(4:ℕ))
    (familyPageMap model.family ((SyntheticCategory.biShift (0,0)).map (model.nu.functor.map f))
      2 (14,139,139-(4:ℕ)) nx) = _
  rw [hn]
  rfl

theorem nu_lambda_four_infinity_nonzero (X : ClassicalObject)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (14,139))
    (hs : SurvivesTo (model.classical.obj (X.obj model.auxiliary)) 6 (14,139) x)
    (e : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (14,139,135)).eInfty)
    (he : HasInfinityRepresentative (model.family.nu model.nu (X.obj model.auxiliary)) 2
      (14,139,135) (targetNuLabel model X 14 139 4 x) e) : e ≠ 0 := by
  obtain ⟨hc,hp⟩ := (KIP126.Literature.Standard.eInfinity_nu_labels
    X 14 139 135 (by decide) x e).mp he
  intro hz
  rw [hz,map_zero] at hp
  have hb := (subquotientClass_eq_zero_iff _ _ ⟨x,hc⟩).mp hp.symm
  change x ∈ boundaries model X 5 (14,139) at hb
  obtain ⟨xr,hrep,hne⟩ := hs
  have hzero : RepresentsOnPage (model.classical.obj (X.obj model.auxiliary)) 6 (14,139) x 0 :=
    KIP126.ProofTools.representsOnPage_of_congruent model X (by decide)
      (RepresentsOnPage.zero (by decide))
      ⟨by decide, by simpa [KIP126.ProofTools.Ambient] using hb⟩
  exact hne (FinitePageCalculus.represents_unique hrep hzero)

end
end KIP126.Main.Internal.Rigidity
