module
import all KIP126.Def.ProofTools.GeneralizedMahowald.SourceBoundaryReview
import all KIP126.Def.ProofTools.GeneralizedMahowald.RotatedNuPremises
import all KIP126.Def.ProofTools.GeneralizedMahowald.RotatedNuTriangle
import all KIP126.Def.ProofTools.GeneralizedMahowald.NuCofiberMayCorrection
import all KIP126.Def.ProofTools.GeneralizedLeibniz.Reverse
import all KIP126.Def.ProofTools.GeneralizedMahowald.HMapCoherence

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature KIP126.Classical.Adams
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem specific_top_lambda_injective
    (a : Smn 14 17 ⟶ (SyntheticCategory.biShift (0,-1)).obj (Smn 4 4 : SyntheticSpectrum))
    (ha : a≫SyntheticCategory.lam.app (Smn 4 4)=0) : a=0 := by
  let F := shiftFunctor SyntheticSpectrum (1:ℤ)
  have hz : ∀ b : F.obj (Smn 14 17) ⟶ XModLambdaN (Smn 4 4) 1, b=0 := by
    intro b
    let e : F.obj (Smn 14 17) ≅ Smn 15 17 :=
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift_comp (14,17) (1,0)).app S_0_0
    apply (cancel_epi e.inv).mp
    simpa only [comp_zero] using balanced_four_first_quotient_15_17_zero (e.inv≫b)
  have hs : F.map a≫F.map (lambdaPow 1 (Smn 4 4))=0 := by
    rw [←Functor.map_comp,lambdaPow_one model.quotients.coherence,ha,Functor.map_zero]
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle (Smn 4 4) 1).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished (Smn 4 4) 1) (F.map a) hs
  have hf : F.map a=0 := by rw [hb,hz b,zero_comp]
  exact F.map_injective (by simpa only [Functor.map_zero] using hf)


private theorem sphere_ext_three_fourteen_zero (x : Ambient model .sphere (3,14)) : x=0 := by
  let e := KIP126.Computation.Standard.coordinates 3 14 (by decide)
  have hn : KIP126.Computation.Standard.archive.basisCount 3 14 = 0 :=
    (KIP126.Computation.Table.archive_dimension 3 14 (by decide)).trans (by decide)
  haveI : Subsingleton (Fin (KIP126.Computation.Standard.archive.basisCount 3 14) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  apply e.injective
  exact Subsingleton.elim _ _

private theorem sphere_nu_infinity_zero_of_ambient_zero (s t w : ℤ)
    (hz : ∀ x : Ambient model .sphere (s,t), x=0) :
    IsZero (((model.family.nu model.nu (ClassicalObject.sphere.obj model.auxiliary)).sequence.ssData
      (s,t,w)).eInfty) := by
  haveI : Subsingleton (Ambient model .sphere (s,t)) := ⟨fun x y => (hz x).trans (hz y).symm⟩
  haveI : Subsingleton (KIP126.Literature.nuEInftyModel model .sphere (s,t) w) := by
    unfold KIP126.Literature.nuEInftyModel
    split <;> infer_instance
  haveI : Subsingleton (((model.family.nu model.nu
      (ClassicalObject.sphere.obj model.auxiliary)).sequence.ssData (s,t,w)).eInfty) :=
    (KIP126.Literature.Standard.eInfinity_nu .sphere (s,t) w).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem nuSphere_pi_11_13_filtration_four
    (a : BiHom 11 13 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) :
    FiltrationAtLeast model.syntheticTower 4 a := by
  have ha2 := nu_bottom_filtration .sphere 2 13 a
  apply (filtration_iff_of_infinity_zero (model.convergence (.nu .sphere)) 2 4 11 13
    (by decide) ?_ a).mp ha2
  intro j hj2 hj4
  have hj : j=2 ∨ j=3 := by omega
  rcases hj with rfl | rfl
  · exact sphere_nu_infinity_zero_of_ambient_zero 2 13 13 sphere_ext_two_thirteen_zero
  · exact sphere_nu_infinity_zero_of_ambient_zero 3 14 13 sphere_ext_three_fourteen_zero

private theorem specific_source_to_first_quotient_zero
    (z : BiHom 14 17 (Smn 3 4 : SyntheticSpectrum))
    (d : (Smn 3 4 : SyntheticSpectrum) ⟶
      XModLambdaN (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) 1) : z≫d=0 := by
  let e := suspInvarianceAddEquiv 11 13 3 4 (S_0_0 : SyntheticSpectrum)
  let z₀ : BiHom 11 13 (S_0_0 : SyntheticSpectrum) := e.symm z
  let a := z₀≫model.nu.unitIso.inv
  have ha4 := nuSphere_pi_11_13_filtration_four a
  have hz4 : FiltrationAtLeast model.syntheticTower 4 z₀ := by
    have h := map_preserves_filtration (model.convergentMap (.nu .sphere) .sphere model.nu.unitIso.hom)
      (11,13) 4 a ha4
    simpa only [a,Category.assoc,Iso.inv_hom_id,Category.comp_id,FiltrationAtLeast,SyntheticObject.obj] using h
  have hzshift : FiltrationAtLeast model.syntheticTower 4 (e z₀) := by
    have h := (shift_filtration_iff .sphere (3,4) (11,13) 4 z₀).mpr hz4
    simpa [e,suspInvarianceAddEquiv,shiftHomotopyClass,susp_invariance,Iso.homCongr] using h
  have hz : FiltrationAtLeast model.syntheticTower 4 z := by
    simpa only [z₀,AddEquiv.apply_symm_apply] using hzshift
  have hd := map_preserves_filtration (model.convergentMap (.shift (3,4) .sphere)
    (.quotient 1 (.nu .sphere)) d) (14,17) 4 z hz
  exact finite_high_filtration_zero .sphere 1 (by decide) 14 17 4 (by decide) (z≫d) hd


private theorem specific_two_cell_first_quotient_injective
    (T : Triangle SyntheticSpectrum) (hT : T∈distTriang SyntheticSpectrum)
    (eA : T.obj₁ ≅ (Smn 3 4 : SyntheticSpectrum))
    (eB : T.obj₂ ≅ model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
    (α : BiHom 14 17 T.obj₂)
    (hα : α≫T.mor₂≫XModLambdaN.incl T.obj₃ 1=0) :
    α≫XModLambdaN.incl T.obj₂ 1=0 := by
  let L := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  letI := model.exactness.shiftCommShift (0,-1)
  letI := model.exactness.shiftExact (0,-1)
  let eTop : T.obj₁⟦(1:ℤ)⟧ ≅ (Smn 4 4 : SyntheticSpectrum) :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso eA ≪≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift_comp (3,4) (1,0)).app S_0_0
  obtain ⟨β,hβ⟩ := (XModLambdaN.cofiberTriangle T.obj₃ 1).coyoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished T.obj₃ 1) (α≫T.mor₂) (by
      change (α≫T.mor₂)≫XModLambdaN.incl T.obj₃ 1=0
      simpa only [Category.assoc] using hα)
  change BiHom 14 17 (L.obj T.obj₃) at β
  change α≫T.mor₂=β≫lambdaPow 1 T.obj₃ at hβ
  let γ := β≫L.map T.mor₃
  have hγ : γ≫lambdaPow 1 (T.obj₁⟦(1:ℤ)⟧)=0 := by
    have hnat : L.map T.mor₃≫lambdaPow 1 (T.obj₁⟦(1:ℤ)⟧)=lambdaPow 1 T.obj₃≫T.mor₃ :=
      lambdaPow_naturality 1 T.mor₃
    dsimp only [γ]
    rw [Category.assoc,hnat,←Category.assoc,←hβ,
      Category.assoc,comp_distTriang_mor_zero₂₃ T hT,comp_zero]
  have hγtop : (γ≫L.map eTop.hom)≫SyntheticCategory.lam.app (Smn 4 4)=0 := by
    have hnat : L.map eTop.hom≫lambdaPow 1 (Smn 4 4)=
        lambdaPow 1 (T.obj₁⟦(1:ℤ)⟧)≫eTop.hom := lambdaPow_naturality 1 eTop.hom
    rw [←lambdaPow_one model.quotients.coherence,Category.assoc,hnat,←Category.assoc,hγ,zero_comp]
  have hγ0 : γ=0 := by
    have hz := specific_top_lambda_injective (γ≫L.map eTop.hom) hγtop
    apply (cancel_mono (L.map eTop.hom)).mp
    simpa only [zero_comp] using hz
  let U := L.mapTriangle.obj T
  have hU : U∈distTriang SyntheticSpectrum := L.map_distinguished T hT
  have hβδ : β≫U.mor₃=0 := by
    change β≫(L.map T.mor₃≫(L.commShiftIso (1:ℤ)).hom.app _)=0
    rw [←Category.assoc]
    change γ≫_=0
    rw [hγ0,zero_comp]
  obtain ⟨η,hη⟩ := U.coyoneda_exact₃ hU β hβδ
  change BiHom 14 17 (L.obj T.obj₂) at η
  change β=η≫L.map T.mor₂ at hη
  have hdiff : (α-η≫lambdaPow 1 T.obj₂)≫T.mor₂=0 := by
    have hnat : lambdaPow 1 T.obj₂≫T.mor₂=L.map T.mor₂≫lambdaPow 1 T.obj₃ :=
      (lambdaPow_naturality 1 T.mor₂).symm
    rw [Preadditive.sub_comp,Category.assoc,hnat,
      ←Category.assoc]
    change α≫T.mor₂-(η≫L.map T.mor₂)≫lambdaPow 1 T.obj₃=0
    rw [←hη,←hβ,sub_self]
  obtain ⟨ζ,hζ⟩ := T.coyoneda_exact₂ hT (α-η≫lambdaPow 1 T.obj₂) hdiff
  have hzsource : ζ≫T.mor₁≫XModLambdaN.incl T.obj₂ 1≫XModLambdaN.map eB.hom 1=0 := by
    have hz := specific_source_to_first_quotient_zero (ζ≫eA.hom)
      (eA.inv≫T.mor₁≫XModLambdaN.incl T.obj₂ 1≫XModLambdaN.map eB.hom 1)
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using hz
  have hh := congrArg (fun f => f≫XModLambdaN.incl T.obj₂ 1≫XModLambdaN.map eB.hom 1) hζ
  have hηzero : η≫lambdaPow 1 T.obj₂≫XModLambdaN.incl T.obj₂ 1≫XModLambdaN.map eB.hom 1=0 := by
    simpa only [Category.assoc,comp_zero,zero_comp] using
      congrArg (fun f => η≫f≫XModLambdaN.map eB.hom 1)
        (XModLambdaN.lambdaPow_comp_incl T.obj₂ 1)
  have hmap : α≫XModLambdaN.incl T.obj₂ 1≫XModLambdaN.map eB.hom 1=0 := by
    simpa only [Preadditive.sub_comp,Category.assoc,hηzero,sub_zero,hzsource] using hh
  have hh' := congrArg (fun f => f≫XModLambdaN.map eB.inv 1) hmap
  simpa only [Category.assoc,←model.quotients.functoriality.map_comp,
    Iso.hom_inv_id,model.quotients.functoriality.map_id,Category.comp_id,zero_comp] using hh'


private theorem nu_triangle_bottom_boundary_image_nonzero
    (α : BiHom 14 17 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (hα : α≫XModLambdaN.incl _ 1=firstLabel model .sphere 3 17 mh2BoundaryClass≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    let T := normalizedTriangle model model.auxiliary.nuRouteTriangle
      KIP126.Literature.Standard.nuCofiber_exponent_sum
    α≫T.mor₂≫XModLambdaN.incl T.obj₃ 1≠0 := by
  dsimp only
  let T := normalizedTriangle model model.auxiliary.nuRouteTriangle
    KIP126.Literature.Standard.nuCofiber_exponent_sum
  have hT : T∈distTriang SyntheticSpectrum := KIP126.Literature.Standard.nuCofiber_distinguished
  let eA : T.obj₁ ≅ (Smn 3 4 : SyntheticSpectrum) := by
    change (SyntheticCategory.biShift
      (0,(normalizedExponent model.classicalTower model.auxiliary.nuMap:ℤ))).obj
      (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary)) ≅ _
    rw [KIP126.Literature.Standard.nuCofiber_nu_exponent]
    exact (SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree model) ≪≫
      (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0
  intro hzero
  have hz := specific_two_cell_first_quotient_injective T hT eA (Iso.refl _) α hzero
  apply mh2BoundaryClass_nonzero
  apply first_label_zero .sphere 3 17 mh2BoundaryClass
  rw [←hα]
  exact hz

private theorem nu_bottom_boundary_first_quotient_nonzero
    (α : BiHom 14 17 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (hα : α≫XModLambdaN.incl _ 1=firstLabel model .sphere 3 17 mh2BoundaryClass≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    α≫model.nu.functor.map model.auxiliary.nuRouteTriangle.g≫XModLambdaN.incl _ 1≠0 := by
  have hnonzero := nu_triangle_bottom_boundary_image_nonzero α hα
  let B := model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)
  let e := zero_negative_iso B
    (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g)
    KIP126.Literature.Standard.nuCofiber_bottom_exponent
  have he := negative_lift_zero_map_form
    (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g)
    KIP126.Literature.Standard.nuCofiber_bottom_exponent
    (model.normalizedMap .sphere .nuCofiber model.auxiliary.nuRouteTriangle.g).map
    (model.nu.functor.map model.auxiliary.nuRouteTriangle.g)
    (model.normalizedMap .sphere .nuCofiber model.auxiliary.nuRouteTriangle.g).factorization
  intro hz
  apply hnonzero
  let j := negativeLift
    (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g)
    (model.normalizedMap .sphere .nuCofiber model.auxiliary.nuRouteTriangle.g).map
  change α≫j≫XModLambdaN.incl _ 1=0
  have hm : α≫j≫XModLambdaN.incl _ 1≫XModLambdaN.map e.hom 1=0 := by
    rw [←XModLambdaN.incl_naturality]
    have hj : j≫e.hom=model.nu.functor.map model.auxiliary.nuRouteTriangle.g := he
    rw [←Category.assoc j e.hom,hj]
    convert hz using 1 <;> rfl
  have h := congrArg (fun z => z≫XModLambdaN.map e.inv 1) hm
  simpa only [B,Category.assoc,←model.quotients.functoriality.map_comp,
    Iso.hom_inv_id,model.quotients.functoriality.map_id,Category.comp_id,zero_comp] using h

private theorem nu_bottom_boundary_leading_nonzero :
    familyPageMap model.family (model.nu.functor.map model.auxiliary.nuRouteTriangle.g)
      2 (3,17,17) (nuWeightLabel model .sphere 3 17 17 (by omega) mh2BoundaryClass)≠0 := by
  obtain ⟨α,hα,_⟩ := cumulative_boundary_torsion_lift_unshifted .sphere 1 3 17
    mh2BoundaryClass mh2BoundaryClass_boundary
  have hp := first_label_lift_permanent .sphere 3 17 mh2BoundaryClass α hα
  have hd := nu_first_label_detects .sphere 3 17 mh2BoundaryClass hp α hα
  have hm := detects_map (.nu .sphere) (.nu .nuCofiber)
    (model.nu.functor.map model.auxiliary.nuRouteTriangle.g)
    (3,17,17) _ α hd
  intro hz
  have hm0 : Detects (model.convergence (.nu .nuCofiber)) (3,17,17) 0
      (α≫model.nu.functor.map model.auxiliary.nuRouteTriangle.g) := by
    convert hm using 1
    exact hz.symm
  have hf := detects_zero_filtration (model.convergence (.nu .nuCofiber)) (3,17,17) hm0
  have hq := map_preserves_filtration (model.convergentMap (.nu .nuCofiber)
    (.quotient 1 (.nu .nuCofiber)) (XModLambdaN.incl _ 1)) (14,17) 4 _ hf
  apply nu_bottom_boundary_first_quotient_nonzero α hα
  apply finite_high_filtration_zero .nuCofiber 1 (by decide) 14 17 4 (by decide)
  convert hq using 1
  simp only [Category.assoc,FiltrationAtLeast,SyntheticObject.obj]
  rfl

end
end KIP126.ProofTools.Internal.Mahowald
