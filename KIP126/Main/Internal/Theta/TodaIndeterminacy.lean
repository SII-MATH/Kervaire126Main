module
public import KIP126.Literature.Standard.Filtration
import all KIP126.Main.Internal.Theta.Products
import all KIP126.Main.Internal.Theta.Detection
import all KIP126.Main.Internal.Selected.NuErrorData
import all KIP126.Main.Internal.Selected.InfinityFrames
/-! Full first-quotient Toda indeterminacy, ThetaToda:782–1022,
bbac1fc05843 (MIT). Both indeterminacy summands are proved zero. -/
@[expose] section
namespace KIP126.Main.Internal.Theta
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.Main.Internal KIP126.Main.Internal.Selected KIP126.Main.Internal.Selected.NuError
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald KIP126.Main.SectionSeven KIP126.Literature.Route
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem sphere_first_quotient_63_64_permanent (a:BiHom 63 64 (S_0_0:SyntheticSpectrum)) :
    KIP126.Literature.sphereFirstQuotient model 1 64 (quotientClass 1 a) ∈ permanentCycles model .sphere (1,64) := by
  obtain ⟨e,he,_⟩ := model.sphereDetectionCompatible.homotopy_lambda 1 64 0 a
  have h := family_infinity_representative_map model.nu.unitIso.inv (1,64,64-(0:ℕ)) _ _ he
  change HasInfinityRepresentative (model.family.nu model.nu SphereSpectrum) 2 (1,64,64-(0:ℕ))
    (familyPageMap model.family model.nu.unitIso.inv 2 (1,64,64-(0:ℕ))
      (sphereLabel 1 64 0 (KIP126.Literature.sphereFirstQuotient model 1 64 (quotientClass 1 a)))) _ at h
  rw [sphere_label_to_nu 0 1 64] at h
  exact ((nu_target_label_iff 1 64 0 _ _).mp h).1

theorem sphere_first_quotient_63_64_zero (a:BiHom 63 64 (S_0_0:SyntheticSpectrum)) :
    KIP126.Literature.sphereFirstQuotient model 1 64 (quotientClass 1 a)=0 := by
  classical
  let E:=Normalized.sphere
  let x:=Normalized.label (1,64) (KIP126.Literature.sphereFirstQuotient model 1 64 (quotientClass 1 a))
  have hp := sphere_first_quotient_63_64_permanent a
  have hreaches := normalized_reaches 3 (1,64) _ (permanent_reaches .sphere 3 (by decide) (1,64) _ hp)
  obtain ⟨x3,hx3⟩ := hreaches
  have hd : E.d 2 (1,64) x=0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
    (by decide : (2:ℤ)<3) (represents_two_self x) ⟨x3,hx3⟩
  have h142 : HasDifferential E 2 (1,64) (3,65)
      (Normalized.basis .sphere 1 64 0) (Normalized.basis .sphere 3 65 0) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,1,64,[0],3,65,[0],"S0_AdamsE2_ss",401⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 142 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨a,ha,b,hb,hab⟩ := hrow
    change HasDifferential E 2 (1,64) (3,65) a b at hab
    have va : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 1 64 [0]=true := rfl
    have vb : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 3 65 [0]=true := rfl
    simp only [Normalized.decode,va,vb,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at hab
    exact hab
  obtain ⟨f,hf⟩ := Normalized.basis_correct ⟨.sphere,3,65,["0,1,18,2"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 102 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (3,65) ≃ₗ[ℤ] (Fin 1 →₀ ZMod 2) at f
  change ∀i:Fin 1,f.symm (Finsupp.single i 1)=Normalized.basis .sphere 3 65 i.val at hf
  have hn:Normalized.basis .sphere 3 65 0≠0 := by
    intro h
    have h0:=congrArg (fun z=>f z 0) ((hf 0).trans h)
    simp at h0
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,1,64,["69,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 85 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (1,64) ≃ₗ[ℤ] (Fin 1 →₀ ZMod 2) at e
  change ∀i:Fin 1,e.symm (Finsupp.single i 1)=Normalized.basis .sphere 1 64 i.val at he
  have heq:e x=Finsupp.single 0 (e x 0) := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp
  have hxe:x=e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc:e x 0=c at hxe
  have hx0 : x=0 := by
    fin_cases c
    · simp only [show (⟨0,by decide⟩:ZMod 2)=0 from rfl,Finsupp.single_zero,map_zero] at hxe
      exact hxe
    · change x=e.symm (Finsupp.single 0 1) at hxe
      rw [he] at hxe
      change x=Normalized.basis .sphere 1 64 0 at hxe
      obtain ⟨hdeg,hh⟩ := h142.eq_on_page_two
      apply False.elim
      apply hn
      rw [←hxe,ConcreteCategory.comp_apply,hd,map_zero] at hh
      exact hh.symm
  have h := congrArg (denormalize (1,64)) hx0
  simpa only [x,denormalize_label,map_zero] using h

theorem theta_b_right_indeterminacy_first_zero
    (c:BiHom 63 64 (S_0_0:SyntheticSpectrum)) (b:BiHom 62 70 (S_0_0:SyntheticSpectrum)) :
    KIP126.Literature.sphereFirstQuotient model 9 134 (quotientClass 1 (sphereProduct c b))=0 := by
  have hm:=KIP126.Literature.Standard.first_quotient_action 1 64 8 70 c (quotientClass 1 b)
  change KIP126.Literature.sphereFirstQuotient model 9 134 (sphereAction c (quotientClass 1 b)) =
    model.sphereAlgebra.product (1,64) (8,70)
      (KIP126.Literature.sphereFirstQuotient model 1 64 (quotientClass 1 c))
      (KIP126.Literature.sphereFirstQuotient model 8 70 (quotientClass 1 b)) at hm
  rw [sphere_first_quotient_63_64_zero c,map_zero,LinearMap.zero_apply] at hm
  simpa only [sphereAction,sphereProduct,quotientClass,Category.assoc] using hm

theorem theta_b_left_indeterminacy_first_zero
    (theta:BiHom 62 64 (S_0_0:SyntheticSpectrum)) (htheta:ThetaChoice theta)
    (a:BiHom 63 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) :
    KIP126.Literature.sphereFirstQuotient model 9 134 (sphereAction theta a)=0 := by
  have hm:=KIP126.Literature.Standard.first_quotient_action 2 64 7 70 theta a
  change KIP126.Literature.sphereFirstQuotient model 9 134 (sphereAction theta a) =
    model.sphereAlgebra.product (2,64) (7,70)
      (KIP126.Literature.sphereFirstQuotient model 2 64 (quotientClass 1 theta))
      (KIP126.Literature.sphereFirstQuotient model 7 70 a) at hm
  rw [show KIP126.Literature.sphereFirstQuotient model 2 64 (quotientClass 1 theta)=KIP126.Computation.Standard.h5Square from htheta] at hm
  exact hm.trans (h5_square_times_entire_770_zero _)
theorem theta_b_left_indeterminacy_normalize
    (coh:BiShiftCoherence SyntheticSpectrum) (theta:BiHom 62 64 (S_0_0:SyntheticSpectrum))
    {W:SyntheticSpectrum} (y:(Smn (Syn:=SyntheticSpectrum) 62 70)⟦(1:ℤ)⟧⟶W) :
    (tripleTodaSource (Syn:=SyntheticSpectrum) 62 64 0 0 62 70).hom≫
      ((SyntheticCategory.biShift (62,70)).map theta)⟦(1:ℤ)⟧'≫y =
    sphereAction theta
      ((SyntheticCategory.biShift_comp (62,70) (1,0)).inv.app (S_0_0:SyntheticSpectrum)≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app (Smn 62 70)≫y) := by
  have hc:=coh.associativity (62,64) (62,70) (1,0) (124,134) (63,70) (125,134)
    (by decide) (by decide) (by decide) (by decide) (S_0_0:SyntheticSpectrum)
  have hi :
      ((SyntheticCategory.biShift (1,0)).mapIso
        ((SyntheticCategory.biShift_comp (62,64) (62,70)).app (S_0_0:SyntheticSpectrum))) ≪≫
        (SyntheticCategory.biShift_comp (124,134) (1,0)).app (S_0_0:SyntheticSpectrum) =
      (SyntheticCategory.biShift_comp (62,70) (1,0)).app (Smn (Syn:=SyntheticSpectrum) 62 64) ≪≫
        (SyntheticCategory.biShift_comp (62,64) (63,70)).app (S_0_0:SyntheticSpectrum) := by
    apply Iso.ext
    simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,
      eqToHom_app,eqToHom_refl,Category.comp_id,Smn,Functor.mapIso_hom,Iso.app_hom] using hc
  have hinv:=congrArg (fun e=>e.inv) hi
  simp only [Iso.trans_inv,Functor.mapIso_inv,Iso.app_inv] at hinv
  have hn:=(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.naturality
    ((SyntheticCategory.biShift (62,70)).map theta)
  have hn':=(SyntheticCategory.biShift_comp (Syn:=SyntheticSpectrum) (62,70) (1,0)).inv.naturality theta
  change ((SyntheticCategory.biShift_comp (124,134) (1,0)).inv.app (S_0_0:SyntheticSpectrum) ≫
    (SyntheticCategory.biShift (1,0)).map
      ((SyntheticCategory.biShift_comp (62,64) (62,70)).inv.app (S_0_0:SyntheticSpectrum)) ≫
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app
      ((SyntheticCategory.biShift (62,70)).obj (Smn 62 64))) ≫
    ((SyntheticCategory.biShift (62,70)).map theta)⟦(1:ℤ)⟧'≫y =
    (SyntheticCategory.biShift_comp (62,64) (63,70)).inv.app (S_0_0:SyntheticSpectrum) ≫
      (SyntheticCategory.biShift (63,70)).map theta≫
      (SyntheticCategory.biShift_comp (62,70) (1,0)).inv.app (S_0_0:SyntheticSpectrum)≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app (Smn 62 70)≫y
  have hny:=congrArg (fun z=>z≫y) hn
  simp only [Category.assoc] at hny
  simp only [Category.assoc]
  rw [←hny]
  simp only [←Category.assoc]
  rw [hinv]
  simpa only [Category.assoc,Functor.comp_map,Prod.mk_add_mk,Int.reduceAdd,Smn] using congrArg (fun z =>
    (SyntheticCategory.biShift_comp (62,64) (63,70)).inv.app (S_0_0:SyntheticSpectrum) ≫ z ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app (Smn 62 70) ≫ y) hn'.symm
theorem theta_b_quotient_toda_unique
    (theta:BiHom 62 64 (S_0_0:SyntheticSpectrum)) (htheta:ThetaChoice theta)
    (b:BiHom 62 70 (S_0_0:SyntheticSpectrum))
    (qz qz' : ((SyntheticCategory.biShift (62,70)).obj (Smn (Syn:=SyntheticSpectrum) 62 64))⟦(1:ℤ)⟧⟶
      XModLambdaN (S_0_0:SyntheticSpectrum) 1)
    (hz:Toda.Relation qz ((SyntheticCategory.biShift (62,70)).map theta)
      (2 • 𝟙 (Smn 62 70)) (quotientClass 1 b))
    (hz':Toda.Relation qz' ((SyntheticCategory.biShift (62,70)).map theta)
      (2 • 𝟙 (Smn 62 70)) (quotientClass 1 b)) : qz=qz' := by
  let src:=tripleTodaSource (Syn:=SyntheticSpectrum) 62 64 0 0 62 70
  obtain ⟨y,z,he⟩ := (Toda.relation_iff_indeterminacy hz').mp hz
  apply (cancel_epi src.hom).mp
  apply (KIP126.Literature.sphereFirstQuotient model 9 134).injective
  apply sub_eq_zero.mp
  rw [←map_sub,←Preadditive.comp_sub,he,Preadditive.comp_add,map_add]
  have hy : KIP126.Literature.sphereFirstQuotient model 9 134
      (src.hom≫((SyntheticCategory.biShift (62,70)).map theta)⟦(1:ℤ)⟧'≫y)=0 := by
    rw [theta_b_left_indeterminacy_normalize model.quotients.coherence theta y]
    exact theta_b_left_indeterminacy_first_zero theta htheta _
  let c:BiHom 63 64 (S_0_0:SyntheticSpectrum) :=
    (susp_invariance 63 64 62 70 (S_0_0:SyntheticSpectrum)).symm (src.hom≫z)
  have hc : (SyntheticCategory.biShift_comp (63,64) (62,70)).inv.app (S_0_0:SyntheticSpectrum)≫
      (SyntheticCategory.biShift (62,70)).map c=src.hom≫z := by
    have hcc : susp_invariance 63 64 62 70 (S_0_0:SyntheticSpectrum) c=src.hom≫z :=
      (susp_invariance 63 64 62 70 (S_0_0:SyntheticSpectrum)).apply_symm_apply (src.hom≫z)
    dsimp only [susp_invariance] at hcc
    simp only [Equiv.trans_apply,Functor.FullyFaithful.homEquiv_apply,
      Iso.homCongr_apply,Iso.refl_hom,Category.comp_id] at hcc
    exact hcc
  have hright:src.hom≫(z≫quotientClass 1 b)=quotientClass 1 (sphereProduct c b) := by
    unfold sphereProduct quotientClass
    rw [←Category.assoc,←hc]
    simp only [Category.assoc]
  rw [hright,theta_b_right_indeterminacy_first_zero c b,add_zero]
  exact hy
end
end KIP126.Main.Internal.Theta
