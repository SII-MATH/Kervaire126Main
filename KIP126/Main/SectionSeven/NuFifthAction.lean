module
public import KIP126.Main.SectionSeven.Predicates
public import KIP126.Def.Literature.Standard.QuotientAlgebra
import all KIP126.Main.Internal.DetectionLabels
/-! The original Main Q3 action-versus-actual-map proof, NuFifth:1983–2294,
bbac1fc05843 (MIT). The quotient algebras are the same fixed upstream objects. -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Kervaire.Route KIP126.Literature
open KIP126.Main.Internal KIP126.ProofTools.Operations
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
private theorem filtration_zero {X : SyntheticSpectrum} {m w : ℤ} (a : BiHom m w X) :
    FiltrationAtLeast model.syntheticTower 0 a := by
  let T := model.syntheticTower.tower X
  refine ⟨a ≫ T.zeroIso.inv,?_⟩
  change (a ≫ T.zeroIso.inv) ≫ T.projection 0=a
  dsimp only [AbstractAdamsTower.projection]
  rw [T.map_self]
  change (a ≫ T.zeroIso.inv) ≫ (𝟙 (T.stage 0) ≫ T.zeroIso.hom)=a
  rw [Category.id_comp,Category.assoc,Iso.inv_hom_id,Category.comp_id]

private theorem q3_sphere_action_actual_map
    (unique:∀u v:BiHom 122 130 (XModLambdaN (S_0_0:SyntheticSpectrum) 3),u≠0→v≠0→u=v)
    (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 3 ≅
      (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 3))
    (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 3≫κ.hom=
      (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3))
    (ν:BiHom 3 4 (S_0_0:SyntheticSpectrum))
    (x:BiHom 122 130 (XModLambdaN (S_0_0:SyntheticSpectrum) 3)) (hx:x≠0) :
    sphereAction ν x=(susp_invariance 122 130 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 3) x)≫
      κ.inv≫XModLambdaN.map ν 3 := by
  classical
  have tensorLeft_sphere_faithful (m n:ℤ) : (tensorLeft (Smn (Syn:=SyntheticSpectrum) m n)).Faithful := by
    let e : Smn (Syn:=SyntheticSpectrum) (-m) (-n) ⊗ Smn m n ≅ (𝟙_ SyntheticSpectrum) :=
      (biShift_eq_tensor_Smn (-m) (-n) (Smn m n)).symm ≪≫
        (SyntheticCategory.biShift_comp (m,n) (-m,-n)).app (S_0_0:SyntheticSpectrum) ≪≫
          eqToIso (by simp [S_0_0]) ≪≫ SyntheticCategory.biShift_zero.app (S_0_0:SyntheticSpectrum)
    let f : tensorLeft (Smn (Syn:=SyntheticSpectrum) m n) ⋙ tensorLeft (Smn (-m) (-n)) ≅ 𝟭 SyntheticSpectrum :=
      (tensorLeftTensor _ _).symm ≪≫ (tensoringLeft SyntheticSpectrum).mapIso e ≪≫ leftUnitorNatIso SyntheticSpectrum
    exact Functor.Faithful.of_comp_iso f
  let tensorLeft_sphere_fullyFaithful (m n:ℤ) : (tensorLeft (Smn (Syn:=SyntheticSpectrum) m n)).FullyFaithful := by
    let e : Smn (Syn:=SyntheticSpectrum) (-m) (-n) ⊗ Smn m n ≅ (𝟙_ SyntheticSpectrum) :=
      (biShift_eq_tensor_Smn (-m) (-n) (Smn m n)).symm ≪≫
        (SyntheticCategory.biShift_comp (m,n) (-m,-n)).app (S_0_0:SyntheticSpectrum) ≪≫
          eqToIso (by simp [S_0_0]) ≪≫ SyntheticCategory.biShift_zero.app (S_0_0:SyntheticSpectrum)
    let f : tensorLeft (Smn (Syn:=SyntheticSpectrum) m n) ⋙ tensorLeft (Smn (-m) (-n)) ≅ 𝟭 SyntheticSpectrum :=
      (tensorLeftTensor _ _).symm ≪≫ (tensoringLeft SyntheticSpectrum).mapIso e ≪≫ leftUnitorNatIso SyntheticSpectrum
    letI := tensorLeft_sphere_faithful (-m) (-n)
    exact Functor.FullyFaithful.ofCompFaithful ((Functor.FullyFaithful.ofFullyFaithful (𝟭 SyntheticSpectrum)).ofIso f.symm)
  have lambda_cubed_kills_unit_hom
      (f:(S_0_0:SyntheticSpectrum)⟶XModLambdaN (S_0_0:SyntheticSpectrum) 3) :
      lambdaPow 3 (S_0_0:SyntheticSpectrum)≫f=0 := by
    letI:=Standard.quotientSyntheticSymmetric
    letI:=Standard.mayData.leftShift
    letI:=Standard.mayData.leftExact
    let l:BiHom 0 (-3) (S_0_0:SyntheticSpectrum):=lambdaPow 3 (S_0_0:SyntheticSpectrum)
    let z:BiHom 0 0 (XModLambdaN (S_0_0:SyntheticSpectrum) 3):=SyntheticCategory.biShift_zero.hom.app (S_0_0:SyntheticSpectrum)≫f
    have hl:quotientClass 3 l=0 := by
      change lambdaPow 3 (S_0_0:SyntheticSpectrum)≫XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3=0
      exact comp_distTriang_mor_zero₁₂ (XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 3) (HasFunctorialCofiber.cofib_distinguished _)
    have ha:=Standard.quotientAlgebra_sphere_action 3 (by decide) 0 (-3) 0 0 l z
    have hp:Standard.quotientAlgebraProduct (Standard.quotientAlgebra 3 (by decide)) (quotientClass 3 l) z=0 := by
      rw [hl]
      unfold Standard.quotientAlgebraProduct
      have hz:z ⊗ₘ (0:BiHom 0 (-3) (XModLambdaN (S_0_0:SyntheticSpectrum) 3))=0 := by
        rw [tensorHom_def]
        have hz':(XModLambdaN (S_0_0:SyntheticSpectrum) 3) ◁ (0:BiHom 0 (-3) (XModLambdaN (S_0_0:SyntheticSpectrum) 3))=0 :=
          (tensorLeft (XModLambdaN (S_0_0:SyntheticSpectrum) 3)).map_zero _ _
        rw [hz',comp_zero]
      simp only [hz,zero_comp,comp_zero]
    have haction:sphereAction l z=lambdaPow 3 (S_0_0:SyntheticSpectrum)≫f := by
      unfold sphereAction z l
      rw [←Category.assoc ((SyntheticCategory.biShift (0,0)).map (lambdaPow 3 (S_0_0:SyntheticSpectrum))),
        SyntheticCategory.biShift_zero.hom.naturality]
      have hc:(SyntheticCategory.biShift_comp (0,-3) (0,0)).hom.app (S_0_0:SyntheticSpectrum)=
        SyntheticCategory.biShift_zero.hom.app (Smn (Syn:=SyntheticSpectrum) 0 (-3)):= by
        have hc := model.quotients.coherence.right_unit (0,-3) (S_0_0:SyntheticSpectrum)
        change (biShiftAddIso (0,-3) (0,0) (0,-3) (by decide)).hom.app (S_0_0:SyntheticSpectrum)=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      change (SyntheticCategory.biShift_comp (0,-3) (0,0)).inv.app (S_0_0:SyntheticSpectrum)≫
        (SyntheticCategory.biShift_zero.hom.app (Smn (Syn:=SyntheticSpectrum) 0 (-3))≫lambdaPow 3 (S_0_0:SyntheticSpectrum))≫f=_
      rw [←hc]
      simp only [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    exact haction.symm.trans (ha.symm.trans hp)
  have unit_restriction_surjective
       :
      Function.Surjective (fun g:XModLambdaN (S_0_0:SyntheticSpectrum) 3⟶XModLambdaN (S_0_0:SyntheticSpectrum) 3 =>
        XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3≫g) := by
    intro f
    let T:=XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 3
    obtain ⟨g,hg⟩:=T.yoneda_exact₂ (HasFunctorialCofiber.cofib_distinguished _) f
      (lambda_cubed_kills_unit_hom  f)
    exact ⟨g,hg.symm⟩
  have unit_restriction_injective :
      Function.Injective (fun g:XModLambdaN (S_0_0:SyntheticSpectrum) 3⟶XModLambdaN (S_0_0:SyntheticSpectrum) 3 =>
        XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3≫g) := by
    intro f g hfg
    change XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3≫f=XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3≫g at hfg
    let T:=XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 3
    have hz:T.mor₂≫(f-g)=0 := by
      change XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3≫(f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩:=T.yoneda_exact₃ (HasFunctorialCofiber.cofib_distinguished _) (f-g) hz
    let e:T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 1 (-3):=(biSuspensionIso 3 (S_0_0:SyntheticSpectrum)).symm
    have he:e.inv≫δ=0 := by
      apply sphere_quotient_high_filtration_zero 3 (by decide) 1 (-3) 0 (by decide)
      exact filtration_zero (e.inv≫δ)
    have hd:δ=0 := by
      apply (cancel_epi e.inv).mp
      simpa only [comp_zero] using he
    apply sub_eq_zero.mp
    simpa only [hd,comp_zero] using hδ
  have extend_unit_iso
      {S A:SyntheticSpectrum} (i:S⟶A)
      (hi:Function.Bijective (fun g:A⟶A=>i≫g))
      (F T:SyntheticSpectrum⥤SyntheticSpectrum) (ff:F.FullyFaithful) (tt:T.FullyFaithful)
      (eS:F.obj S≅T.obj S) (eA:F.obj A≅T.obj A) :
      ∃E:F.obj A≅T.obj A,F.map i≫E.hom=eS.hom≫T.map i := by
    have lift (F T:SyntheticSpectrum⥤SyntheticSpectrum) (ff:F.FullyFaithful)
        (eA:F.obj A≅T.obj A) (f:F.obj S⟶T.obj A) :
        ∃g:F.obj A⟶T.obj A,F.map i≫g=f := by
      let z:=ff.preimage (f≫eA.inv)
      obtain ⟨g,hg⟩:=hi.2 z
      change i≫g=z at hg
      refine ⟨F.map g≫eA.hom,?_⟩
      rw [←Category.assoc,←F.map_comp,hg]
      have hz:F.map z=f≫eA.inv:=ff.map_preimage _
      rw [hz,Category.assoc,Iso.inv_hom_id,Category.comp_id]
    have inj (F:SyntheticSpectrum⥤SyntheticSpectrum) (ff:F.FullyFaithful)
        {a b:F.obj A⟶F.obj A} (h:F.map i≫a=F.map i≫b) :a=b := by
      obtain ⟨a',rfl⟩:=ff.map_surjective a
      obtain ⟨b',rfl⟩:=ff.map_surjective b
      rw [←F.map_comp,←F.map_comp] at h
      exact congrArg F.map (hi.1 (ff.map_injective h))
    obtain ⟨f,hf⟩:=lift F T ff eA (eS.hom≫T.map i)
    obtain ⟨g,hg⟩:=lift T F tt eA.symm (eS.inv≫F.map i)
    have hfg:f≫g=𝟙 _ := by
      apply inj F ff
      rw [←Category.assoc,hf,Category.assoc,hg,←Category.assoc,Iso.hom_inv_id,Category.id_comp,Category.comp_id]
    have hgf:g≫f=𝟙 _ := by
      apply inj T tt
      rw [←Category.assoc,hg,Category.assoc,hf,←Category.assoc,Iso.inv_hom_id,Category.id_comp,Category.comp_id]
    exact ⟨⟨f,g,hfg,hgf⟩,hf⟩
  have q3_unit_tensor_iso
       :
      ∃e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 3) ≅
          Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 3,
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3)≫e.hom=
          (ρ_ (Smn (Syn:=SyntheticSpectrum) 3 4)).inv≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3) := by
    obtain ⟨e,he⟩:=extend_unit_iso (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3)
      ⟨unit_restriction_injective,unit_restriction_surjective ⟩
      (SyntheticCategory.biShift (3,4)) (tensorLeft (Smn (Syn:=SyntheticSpectrum) 3 4))
      (SyntheticCategory.biShift_fullyFaithful (3,4)) (tensorLeft_sphere_fullyFaithful 3 4)
      (ρ_ (Smn (Syn:=SyntheticSpectrum) 3 4)).symm (biShift_eq_tensor_Smn 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 3))
    refine ⟨e,?_⟩
    simpa only [Iso.symm_hom,tensorLeft,curriedTensor_obj_map,id_tensorHom] using he
  have q3_pi_four_one_zero
      (z : BiHom 4 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 3)) : z=0 := by
    apply sphere_quotient_high_filtration_zero 3 (by decide) 4 1 0 (by decide) z
    exact filtration_zero z
  have q3_sphere_inclusion_hom_injective :
      Function.Injective (fun f : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 3 ⟶
        XModLambdaN (S_0_0:SyntheticSpectrum) 3 => XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 3 ≫ f) := by
    intro f g hfg
    change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 3 ≫ f =
      XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 3 ≫ g at hfg
    let T := XModLambdaN.cofiberTriangle (Smn (Syn:=SyntheticSpectrum) 3 4) 3
    have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
    have hz : T.mor₂ ≫ (f-g)=0 := by
      change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 3 ≫ (f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩ := T.yoneda_exact₃ hT (f-g) hz
    let e : T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 4 1 :=
      (biSuspensionIso 3 (Smn (Syn:=SyntheticSpectrum) 3 4)).symm ≪≫
        (SyntheticCategory.biShift_comp (3,4) (1,-3)).app (S_0_0:SyntheticSpectrum)
    have he := q3_pi_four_one_zero (e.inv ≫ δ)
    have hd : δ=0 := by
      apply (cancel_epi e.inv).mp
      simpa only [comp_zero] using he
    apply sub_eq_zero.mp
    simpa only [hd, comp_zero] using hδ
  have q3_tensor_source_square

      (unique:∀u v:BiHom 122 130 (XModLambdaN (S_0_0:SyntheticSpectrum) 3),u≠0→v≠0→u=v)
      (e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 3) ≅
        Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 3)
      (d:Smn (Syn:=SyntheticSpectrum) 125 134 ≅ Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ Smn (Syn:=SyntheticSpectrum) 122 130)
      (x:BiHom 122 130 (XModLambdaN (S_0_0:SyntheticSpectrum) 3)) (hx:x≠0) :
      d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)=
        (susp_invariance 122 130 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 3) x)≫e.hom := by
    let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (3,4)
    let T:=tensorLeft (Smn (Syn:=SyntheticSpectrum) 3 4)
    letI:=KIP126.AdamsSynthetic.Standard.graded_shiftAdditive (3,4)
    letI:=Standard.mayData.leftShift (Smn (Syn:=SyntheticSpectrum) 3 4)
    letI:=Standard.mayData.leftExact (Smn (Syn:=SyntheticSpectrum) 3 4)
    letI:T.Faithful:=tensorLeft_sphere_faithful 3 4
    let ff:=SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (3,4)
    let c: F.obj (Smn (Syn:=SyntheticSpectrum) 122 130) ≅ Smn (Syn:=SyntheticSpectrum) 125 134 :=
      (SyntheticCategory.biShift_comp (122,130) (3,4)).app (S_0_0:SyntheticSpectrum)
    let z:BiHom 122 130 (XModLambdaN (S_0_0:SyntheticSpectrum) 3):=
      ff.preimage (c.hom≫d.hom≫T.map x≫e.inv)
    have hz:F.map z=c.hom≫d.hom≫T.map x≫e.inv:=ff.map_preimage _
    have hzn:z≠0 := by
      intro h
      rw [h,Functor.map_zero] at hz
      have ht:T.map x=0 := by
        apply (cancel_epi (c.hom≫d.hom)).mp
        apply (cancel_mono e.inv).mp
        simpa only [Category.assoc,comp_zero,zero_comp] using hz.symm
      apply hx
      apply T.map_injective
      simpa only [Functor.map_zero] using ht
    have hzx:z=x:=unique z x hzn hx
    rw [hzx] at hz
    have heq:c.inv≫F.map x≫e.hom=d.hom≫T.map x := by
      rw [hz]
      simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]
    change d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)=_
    dsimp only [susp_invariance]
    simp only [Equiv.trans_apply,Functor.FullyFaithful.homEquiv_apply,
      Iso.homCongr_apply,Iso.refl_hom,Category.comp_id]
    simpa only [c,F,T,tensorLeft,curriedTensor_obj_map,id_tensorHom,Category.assoc] using heq.symm
  have q3_algebra_filler

      (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 3 ≅
        (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 3))
      (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 3≫κ.hom=
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3)) :
      ∃e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 3) ≅
          Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 3,
        letI:=Standard.quotientSyntheticSymmetric
        ∀ν:BiHom 3 4 (S_0_0:SyntheticSpectrum),
        κ.hom≫e.hom≫(quotientClass 3 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 3))≫
          (Standard.quotientAlgebra 3 (by decide)).mul=XModLambdaN.map ν 3 := by
    letI:=Standard.quotientSyntheticSymmetric
    letI:=Standard.quotientAlgebra 3 (by decide)
    obtain ⟨e,he⟩:=q3_unit_tensor_iso
    refine ⟨e,?_⟩
    intro ν
    apply q3_sphere_inclusion_hom_injective
    simp only [←Category.assoc]
    rw [hκ,he]
    simp only [Category.assoc]
    rw [←Category.assoc (𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3),
      tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
    rw [←Standard.quotientAlgebra_unit 3 (by decide)]
    have hm:=Mathlib.Tactic.MonTauto.rightUnitor_inv_tensor_one_mul (quotientClass 3 ν)
    change (ρ_ (Smn (Syn:=SyntheticSpectrum) 3 4)).inv≫(quotientClass 3 ν ⊗ₘ MonObj.one)≫MonObj.mul=quotientClass 3 ν at hm
    rw [hm]
    exact XModLambdaN.incl_naturality ν 3
  letI:=Standard.quotientSyntheticSymmetric
  let Q:=Standard.quotientAlgebra 3 (by decide)
  letI:=Q
  letI:=Standard.quotientAlgebra_commutative 3 (by decide)
  obtain ⟨e,he⟩:=q3_algebra_filler  κ hκ
  let d:Smn (Syn:=SyntheticSpectrum) 125 134 ≅ Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ Smn (Syn:=SyntheticSpectrum) 122 130 :=
    ((SyntheticCategory.biShift_comp (3,4) (122,130)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
      biShift_eq_tensor_Smn 122 130 (Smn (Syn:=SyntheticSpectrum) 3 4) ≪≫ β_ (Smn (Syn:=SyntheticSpectrum) 122 130) (Smn (Syn:=SyntheticSpectrum) 3 4)
  have ht:=q3_tensor_source_square  unique e d x hx
  have hc:=IsCommMonObj.mul_comm (XModLambdaN (S_0_0:SyntheticSpectrum) 3)
  change (β_ (XModLambdaN (S_0_0:SyntheticSpectrum) 3) (XModLambdaN (S_0_0:SyntheticSpectrum) 3)).hom≫Q.mul=Q.mul at hc
  have hb:(x ⊗ₘ quotientClass 3 ν)≫Q.mul=
      (β_ (Smn (Syn:=SyntheticSpectrum) 122 130) (Smn (Syn:=SyntheticSpectrum) 3 4)).hom≫
        (quotientClass 3 ν ⊗ₘ x)≫Q.mul := by
    rw [←hc,←Category.assoc,BraidedCategory.braiding_naturality,Category.assoc]
    simp only [hc]
  have hf:(quotientClass 3 ν ⊗ₘ x)=
      (𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)≫(quotientClass 3 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 3)) := by
    rw [tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
  rw [←Standard.quotientAlgebra_sphere_action 3 (by decide) 3 4 122 130 ν x]
  change Standard.quotientAlgebraProduct Q (quotientClass 3 ν) x=_
  calc
    _=d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)≫
        (quotientClass 3 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 3))≫Q.mul := by
      dsimp only [Standard.quotientAlgebraProduct,d,Iso.trans_hom,Iso.symm_hom]
      rw [hb,hf]
      simp only [Category.assoc]
      rfl
    _=(susp_invariance 122 130 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 3) x)≫e.hom≫
        (quotientClass 3 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 3))≫Q.mul := by
      simpa only [Category.assoc] using congrArg (fun z=>z≫
        (quotientClass 3 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 3))≫Q.mul) ht
    _=_ := by
      rw [←he ν]
      simp only [Iso.inv_hom_id_assoc]
end
end KIP126.Main.SectionSeven.Internal
