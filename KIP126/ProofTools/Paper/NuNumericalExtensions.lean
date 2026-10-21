module
import all KIP126.ProofTools.Paper.NumericalExamples
import all KIP126.ProofTools.Paper.Crossing
import all KIP126.ProofTools.GeneralizedLeibniz.Square
import all KIP126.ProofTools.Paper.ExtensionDescent
import all KIP126.ProofTools.MahowaldLeibniz.FixedModel
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionClassLabels
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionTarget
import all KIP126.ProofTools.GeneralizedMahowald.SphereAutomorphismDetection
import all KIP126.ProofTools.GeneralizedLeibniz.LevelBoundary
import all KIP126.ProofTools.GeneralizedLeibniz.SquareRepresentatives
import all KIP126.ProofTools.GeneralizedLeibniz.MinimalBottom
import KIP126.Literature.Standard.QuotientAlgebra
import KIP126.Literature.Standard.Filtration

/-! Fixed numerical nu extensions derived from independent sphere Adams
boundaries. All local declarations are private; no cofiber calculation or
finite/full extension conclusion is assumed. -/
@[expose] section
namespace KIP126.ProofTools.Paper.NuNumericalExtensions
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.AdamsSynthetic.Standard (model Spectrum SyntheticSpectrum)
open KIP126.ProofTools.Paper.NumericalExamples
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
private theorem sphere_quotient_high_filtration_zero (q : ℕ) (hq : 0 < q)
    (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
    (a : BiHom m w (XModLambdaN (S_0_0 : SyntheticSpectrum) q))
    (ha : FiltrationAtLeast model.syntheticTower s a) : a = 0 := by
  let g : XModLambdaN (S_0_0 : SyntheticSpectrum) q ⟶ XModLambdaN (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) q :=
    XModLambdaN.map model.nu.unitIso.inv q
  let f : XModLambdaN (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) q ⟶ XModLambdaN (S_0_0 : SyntheticSpectrum) q :=
    XModLambdaN.map model.nu.unitIso.hom q
  have hm := map_preserves_filtration
    (model.convergentMap (.quotient q .sphere) (.quotient q (.nu .sphere)) g)
    (m,w) s a ha
  have hz := finite_high_filtration_zero .sphere q hq m w s hs (a ≫ g) hm
  have hgf : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←model.quotients.functoriality.map_comp,Iso.inv_hom_id,model.quotients.functoriality.map_id]
    rfl
  have he := congrArg (fun z => z ≫ f) hz
  change (a ≫ g) ≫ f = 0 ≫ f at he
  rw [Category.assoc,hgf,Category.comp_id,zero_comp] at he
  exact he

private theorem filtration_zero {X : SyntheticSpectrum} {m w : ℤ} (a : BiHom m w X) :
    FiltrationAtLeast model.syntheticTower 0 a := by
  let T := model.syntheticTower.tower X
  refine ⟨a ≫ T.zeroIso.inv,?_⟩
  change (a ≫ T.zeroIso.inv) ≫ T.projection 0=a
  dsimp only [AbstractAdamsTower.projection]
  rw [T.map_self]
  change (a ≫ T.zeroIso.inv) ≫ (𝟙 (T.stage 0) ≫ T.zeroIso.hom)=a
  rw [Category.id_comp,Category.assoc,Iso.inv_hom_id,Category.comp_id]

private theorem q1_sphere_action_actual_map
    (unique:∀u v:BiHom 31 32 (XModLambdaN (S_0_0:SyntheticSpectrum) 1),u≠0→v≠0→u=v)
    (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≅
      (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1≫κ.hom=
      (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1))
    (ν:BiHom 3 4 (S_0_0:SyntheticSpectrum))
    (x:BiHom 31 32 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hx:x≠0) :
    sphereAction ν x=(susp_invariance 31 32 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫
      κ.inv≫XModLambdaN.map ν 1 := by
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
  have lambda_first_kills_unit_hom
      (f:(S_0_0:SyntheticSpectrum)⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1) :
      lambdaPow 1 (S_0_0:SyntheticSpectrum)≫f=0 := by
    letI:=Standard.quotientSyntheticSymmetric
    letI:=Standard.mayData.leftShift
    letI:=Standard.mayData.leftExact
    let l:BiHom 0 (-1) (S_0_0:SyntheticSpectrum):=lambdaPow 1 (S_0_0:SyntheticSpectrum)
    let z:BiHom 0 0 (XModLambdaN (S_0_0:SyntheticSpectrum) 1):=SyntheticCategory.biShift_zero.hom.app (S_0_0:SyntheticSpectrum)≫f
    have hl:quotientClass 1 l=0 := by
      change lambdaPow 1 (S_0_0:SyntheticSpectrum)≫XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1=0
      exact comp_distTriang_mor_zero₁₂ (XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 1) (HasFunctorialCofiber.cofib_distinguished _)
    have ha:=Standard.quotientAlgebra_sphere_action 1 (by decide) 0 (-1) 0 0 l z
    have hp:Standard.quotientAlgebraProduct (Standard.quotientAlgebra 1 (by decide)) (quotientClass 1 l) z=0 := by
      rw [hl]
      unfold Standard.quotientAlgebraProduct
      have hz:z ⊗ₘ (0:BiHom 0 (-1) (XModLambdaN (S_0_0:SyntheticSpectrum) 1))=0 := by
        rw [tensorHom_def]
        have hz':(XModLambdaN (S_0_0:SyntheticSpectrum) 1) ◁ (0:BiHom 0 (-1) (XModLambdaN (S_0_0:SyntheticSpectrum) 1))=0 :=
          (tensorLeft (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).map_zero _ _
        rw [hz',comp_zero]
      simp only [hz,zero_comp,comp_zero]
    have haction:sphereAction l z=lambdaPow 1 (S_0_0:SyntheticSpectrum)≫f := by
      unfold sphereAction z l
      rw [←Category.assoc ((SyntheticCategory.biShift (0,0)).map (lambdaPow 1 (S_0_0:SyntheticSpectrum))),
        SyntheticCategory.biShift_zero.hom.naturality]
      have hc:(SyntheticCategory.biShift_comp (0,-1) (0,0)).hom.app (S_0_0:SyntheticSpectrum)=
        SyntheticCategory.biShift_zero.hom.app (Smn (Syn:=SyntheticSpectrum) 0 (-1)):= by
        have hc := model.quotients.coherence.right_unit (0,-1) (S_0_0:SyntheticSpectrum)
        change (biShiftAddIso (0,-1) (0,0) (0,-1) (by decide)).hom.app (S_0_0:SyntheticSpectrum)=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      change (SyntheticCategory.biShift_comp (0,-1) (0,0)).inv.app (S_0_0:SyntheticSpectrum)≫
        (SyntheticCategory.biShift_zero.hom.app (Smn (Syn:=SyntheticSpectrum) 0 (-1))≫lambdaPow 1 (S_0_0:SyntheticSpectrum))≫f=_
      rw [←hc]
      simp only [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    exact haction.symm.trans (ha.symm.trans hp)
  have unit_restriction_surjective
       :
      Function.Surjective (fun g:XModLambdaN (S_0_0:SyntheticSpectrum) 1⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1 =>
        XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫g) := by
    intro f
    let T:=XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 1
    obtain ⟨g,hg⟩:=T.yoneda_exact₂ (HasFunctorialCofiber.cofib_distinguished _) f
      (lambda_first_kills_unit_hom  f)
    exact ⟨g,hg.symm⟩
  have unit_restriction_injective :
      Function.Injective (fun g:XModLambdaN (S_0_0:SyntheticSpectrum) 1⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1 =>
        XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫g) := by
    intro f g hfg
    change XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫f=XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫g at hfg
    let T:=XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 1
    have hz:T.mor₂≫(f-g)=0 := by
      change XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫(f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩:=T.yoneda_exact₃ (HasFunctorialCofiber.cofib_distinguished _) (f-g) hz
    let e:T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 1 (-1):=(biSuspensionIso 1 (S_0_0:SyntheticSpectrum)).symm
    have he:e.inv≫δ=0 := by
      apply sphere_quotient_high_filtration_zero 1 (by decide) 1 (-1) 0 (by decide)
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
  have q1_unit_tensor_iso
       :
      ∃e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
          Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1,
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)≫e.hom=
          (ρ_ (Smn (Syn:=SyntheticSpectrum) 3 4)).inv≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1) := by
    obtain ⟨e,he⟩:=extend_unit_iso (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)
      ⟨unit_restriction_injective,unit_restriction_surjective ⟩
      (SyntheticCategory.biShift (3,4)) (tensorLeft (Smn (Syn:=SyntheticSpectrum) 3 4))
      (SyntheticCategory.biShift_fullyFaithful (3,4)) (tensorLeft_sphere_fullyFaithful 3 4)
      (ρ_ (Smn (Syn:=SyntheticSpectrum) 3 4)).symm (biShift_eq_tensor_Smn 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    refine ⟨e,?_⟩
    simpa only [Iso.symm_hom,tensorLeft,curriedTensor_obj_map,id_tensorHom] using he
  have q1_pi_four_one_zero
      (z : BiHom 4 3 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) : z=0 := by
    apply sphere_quotient_high_filtration_zero 1 (by decide) 4 3 0 (by decide) z
    exact filtration_zero z
  have q1_sphere_inclusion_hom_injective :
      Function.Injective (fun f : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ⟶
        XModLambdaN (S_0_0:SyntheticSpectrum) 1 => XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≫ f) := by
    intro f g hfg
    change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≫ f =
      XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≫ g at hfg
    let T := XModLambdaN.cofiberTriangle (Smn (Syn:=SyntheticSpectrum) 3 4) 1
    have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
    have hz : T.mor₂ ≫ (f-g)=0 := by
      change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≫ (f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩ := T.yoneda_exact₃ hT (f-g) hz
    let e : T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 4 3 :=
      (biSuspensionIso 1 (Smn (Syn:=SyntheticSpectrum) 3 4)).symm ≪≫
        (SyntheticCategory.biShift_comp (3,4) (1,-1)).app (S_0_0:SyntheticSpectrum)
    have he := q1_pi_four_one_zero (e.inv ≫ δ)
    have hd : δ=0 := by
      apply (cancel_epi e.inv).mp
      simpa only [comp_zero] using he
    apply sub_eq_zero.mp
    simpa only [hd, comp_zero] using hδ
  have q1_tensor_source_square

      (unique:∀u v:BiHom 31 32 (XModLambdaN (S_0_0:SyntheticSpectrum) 1),u≠0→v≠0→u=v)
      (e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
        Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1)
      (d:Smn (Syn:=SyntheticSpectrum) 34 36 ≅ Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ Smn (Syn:=SyntheticSpectrum) 31 32)
      (x:BiHom 31 32 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hx:x≠0) :
      d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)=
        (susp_invariance 31 32 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫e.hom := by
    let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (3,4)
    let T:=tensorLeft (Smn (Syn:=SyntheticSpectrum) 3 4)
    letI:=KIP126.AdamsSynthetic.Standard.graded_shiftAdditive (3,4)
    letI:=Standard.mayData.leftShift (Smn (Syn:=SyntheticSpectrum) 3 4)
    letI:=Standard.mayData.leftExact (Smn (Syn:=SyntheticSpectrum) 3 4)
    letI:T.Faithful:=tensorLeft_sphere_faithful 3 4
    let ff:=SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (3,4)
    let c: F.obj (Smn (Syn:=SyntheticSpectrum) 31 32) ≅ Smn (Syn:=SyntheticSpectrum) 34 36 :=
      (SyntheticCategory.biShift_comp (31,32) (3,4)).app (S_0_0:SyntheticSpectrum)
    let z:BiHom 31 32 (XModLambdaN (S_0_0:SyntheticSpectrum) 1):=
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
  have q1_algebra_filler

      (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≅
        (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
      (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1≫κ.hom=
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)) :
      ∃e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
          Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1,
        letI:=Standard.quotientSyntheticSymmetric
        ∀ν:BiHom 3 4 (S_0_0:SyntheticSpectrum),
        κ.hom≫e.hom≫(quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫
          (Standard.quotientAlgebra 1 (by decide)).mul=XModLambdaN.map ν 1 := by
    letI:=Standard.quotientSyntheticSymmetric
    letI:=Standard.quotientAlgebra 1 (by decide)
    obtain ⟨e,he⟩:=q1_unit_tensor_iso
    refine ⟨e,?_⟩
    intro ν
    apply q1_sphere_inclusion_hom_injective
    simp only [←Category.assoc]
    rw [hκ,he]
    simp only [Category.assoc]
    rw [←Category.assoc (𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1),
      tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
    rw [←Standard.quotientAlgebra_unit 1 (by decide)]
    have hm:=Mathlib.Tactic.MonTauto.rightUnitor_inv_tensor_one_mul (quotientClass 1 ν)
    change (ρ_ (Smn (Syn:=SyntheticSpectrum) 3 4)).inv≫(quotientClass 1 ν ⊗ₘ MonObj.one)≫MonObj.mul=quotientClass 1 ν at hm
    rw [hm]
    exact XModLambdaN.incl_naturality ν 1
  letI:=Standard.quotientSyntheticSymmetric
  let Q:=Standard.quotientAlgebra 1 (by decide)
  letI:=Q
  letI:=Standard.quotientAlgebra_commutative 1 (by decide)
  obtain ⟨e,he⟩:=q1_algebra_filler  κ hκ
  let d:Smn (Syn:=SyntheticSpectrum) 34 36 ≅ Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ Smn (Syn:=SyntheticSpectrum) 31 32 :=
    ((SyntheticCategory.biShift_comp (3,4) (31,32)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
      biShift_eq_tensor_Smn 31 32 (Smn (Syn:=SyntheticSpectrum) 3 4) ≪≫ β_ (Smn (Syn:=SyntheticSpectrum) 31 32) (Smn (Syn:=SyntheticSpectrum) 3 4)
  have ht:=q1_tensor_source_square  unique e d x hx
  have hc:=IsCommMonObj.mul_comm (XModLambdaN (S_0_0:SyntheticSpectrum) 1)
  change (β_ (XModLambdaN (S_0_0:SyntheticSpectrum) 1) (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).hom≫Q.mul=Q.mul at hc
  have hb:(x ⊗ₘ quotientClass 1 ν)≫Q.mul=
      (β_ (Smn (Syn:=SyntheticSpectrum) 31 32) (Smn (Syn:=SyntheticSpectrum) 3 4)).hom≫
        (quotientClass 1 ν ⊗ₘ x)≫Q.mul := by
    rw [←hc,←Category.assoc,BraidedCategory.braiding_naturality,Category.assoc]
    simp only [hc]
  have hf:(quotientClass 1 ν ⊗ₘ x)=
      (𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)≫(quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) := by
    rw [tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
  rw [←Standard.quotientAlgebra_sphere_action 1 (by decide) 3 4 31 32 ν x]
  change Standard.quotientAlgebraProduct Q (quotientClass 1 ν) x=_
  calc
    _=d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul := by
      dsimp only [Standard.quotientAlgebraProduct,d,Iso.trans_hom,Iso.symm_hom]
      rw [hb,hf]
      simp only [Category.assoc]
      rfl
    _=(susp_invariance 31 32 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫e.hom≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul := by
      simpa only [Category.assoc] using congrArg (fun z=>z≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul) ht
    _=_ := by
      rw [←he ν]
      simp only [Iso.inv_hom_id_assoc]

private def h5Q1 : BiHom 31 32 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1) :=
  (KIP126.Literature.sphereFirstQuotient model 1 32).symm
    (model.standardClasses.standardHi 5)

private theorem h5Q1_ne_zero : h5Q1 ≠ 0 := by
  obtain ⟨x,hx,hne⟩ := (KIP126.Literature.Standard.adamsOneLine_d2 5 (by decide)).source_survives
  have h5ne : model.standardClasses.standardHi 5 ≠ 0 := by
    intro hz
    apply hne
    rw [←hx.eq_on_page_two,hz]
  intro hz
  apply h5ne
  have h := congrArg (KIP126.Literature.sphereFirstQuotient model 1 32) hz
  simpa only [h5Q1,LinearEquiv.apply_symm_apply,map_zero] using h

private theorem h5Q1_unique
    (u v : BiHom 31 32 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1))
    (hu : u≠0) (hv : v≠0) : u=v := by
  let d : model.classical.sphere.Page 2 (1,32) ≃ₗ[ℤ] (Fin 1 →₀ ZMod 2) := by
    have hdim : KIP126.Computation.Standard.archive.basisCount 1 32=1 := rfl
    exact hdim ▸ KIP126.Computation.Standard.coordinates 1 32 (by decide)
  let e := (KIP126.Literature.sphereFirstQuotient model 1 32).trans d
  have cases (z : Fin 1 →₀ ZMod 2) : z=0 ∨ z=Finsupp.single 0 1 :=
    NumericalExamples.one_coordinate_cases z
  have he (z : BiHom 31 32 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1))
      (hz : z≠0) : e z=Finsupp.single 0 1 := by
    rcases cases (e z) with h | h
    · exact False.elim (hz (e.injective (h.trans (map_zero e).symm)))
    · exact h
  exact e.injective ((he u hu).trans (he v hv).symm)

/-- Actual Q1 operation at the nonpermanent source h5. The normalization
label is combined with a genuine action/map comparison and Q1 source
uniqueness, rather than treated as an operation-level assertion by itself. -/
private theorem normalizedNuQ1_h5
    (κ : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≅
      (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (hκ : XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1≫κ.hom =
      (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)) :
    KIP126.Literature.sphereFirstQuotient model 2 36
      ((susp_invariance 31 32 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) h5Q1) ≫
        κ.inv ≫ XModLambdaN.map
          (normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent) 1) =
      KIP126.Literature.Standard.hiProduct 2 5 := by
  rw [←q1_sphere_action_actual_map h5Q1_unique κ hκ _ h5Q1 h5Q1_ne_zero]
  have h := KIP126.Literature.Standard.first_quotient_action 1 4 1 32
    (normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent) h5Q1
  change KIP126.Literature.sphereFirstQuotient model 2 36
      (sphereAction (normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent) h5Q1) =
    model.sphereAlgebra.product (1,4) (1,32)
      (KIP126.Literature.sphereFirstQuotient model 1 4
        (quotientClass 1 (normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent)))
      (KIP126.Literature.sphereFirstQuotient model 1 32 h5Q1) at h
  rw [KIP126.Literature.Standard.nuCofiber_normalized_label] at h
  change _ = model.sphereAlgebra.product (1,4) (1,32)
    (model.standardClasses.standardHi 2) (model.standardClasses.standardHi 5)
  simpa only [h5Q1,LinearEquiv.apply_symm_apply] using h

private def suspendNuClass (X : ClassicalObject) (s t : ℤ)
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary))) :
    BiHom ((t+1)-s) (t+1)
      (model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary)) :=
  homotopyRegrade (by dsimp;omega) rfl
    (shiftHomotopyClass (1,1) (t-s,t) a) ≫
      (model.nu.suspensionIso (X.obj model.auxiliary)).inv

private theorem suspend_nu_first_label
    (X : ClassicalObject) (s t : ℤ)
    (x : Ambient model X (s,t))
    (sx : Ambient model (.shift 1 X) (s,t+1))
    (hsx : (model.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x))
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1 = nativeFirstLabel X s t x) :
    suspendNuClass X s t a ≫ XModLambdaN.incl _ 1 =
      nativeFirstLabel (.shift 1 X) s (t+1) sx := by
  letI := model.exactness.shiftCommShift (1,1)
  letI := model.exactness.shiftExact (1,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists model.quotients.coherence (1,1) 1
    (model.nu.functor.obj (X.obj model.auxiliary))
  have hs := KIP126.AdamsSynthetic.Standard.firstQuotient_suspension X s t x sx ε hε hsx
  have hsf : nativeFirstLabel (.shift 1 X) s (t+1) sx ≫
      XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom 1 ≫ ε.hom =
      homotopyRegrade (by dsimp;omega) rfl
        (shiftHomotopyClass (1,1) (t-s,t) (nativeFirstLabel X s t x)) := by
    rw [←first_label_inline,←first_label_inline] at hs
    simpa only [nativeFirstLabel] using hs
  haveI : IsIso (XModLambdaN.map
      (model.nu.suspensionIso (X.obj model.auxiliary)).hom 1) := by
    change IsIso ((model.quotients.functoriality.functor 1).map
      (model.nu.suspensionIso (X.obj model.auxiliary)).hom)
    infer_instance
  apply (cancel_mono (XModLambdaN.map
    (model.nu.suspensionIso (X.obj model.auxiliary)).hom 1)).mp
  apply (cancel_mono ε.hom).mp
  simp only [Category.assoc]
  rw [hsf]
  dsimp only [suspendNuClass]
  have hinv : (model.nu.suspensionIso (X.obj model.auxiliary)).inv ≫
      XModLambdaN.incl _ 1 ≫
      XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom 1 =
      XModLambdaN.incl _ 1 := by
    rw [←XModLambdaN.incl_naturality,←Category.assoc,Iso.inv_hom_id,Category.id_comp]
  have hinvε := congrArg (fun z => z ≫ ε.hom) hinv
  simp only [Category.assoc] at hinvε
  rw [Category.assoc]
  erw [hinvε]
  rw [hε,←regrade_comp]
  rw [show shiftHomotopyClass (1,1) (t-s,t) a ≫
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1) =
      shiftHomotopyClass (1,1) (t-s,t) (a ≫ XModLambdaN.incl _ 1) by
    simp only [shiftHomotopyClass,Functor.map_comp,Category.assoc]]
  rw [ha]

private theorem exists_suspend_nu_first_label
    (X : ClassicalObject) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1 = nativeFirstLabel X s t x) :
    ∃ sx : Ambient model (.shift 1 X) (s,t+1),
      (model.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x) ∧
      suspendNuClass X s t a ≫ XModLambdaN.incl _ 1 =
        nativeFirstLabel (.shift 1 X) s (t+1) sx := by
  obtain ⟨sx,hsx⟩ := exists_suspendsClass X s (t+1) (by simpa using x)
  exact ⟨sx,hsx,suspend_nu_first_label X s t x sx hsx a ha⟩

private def tripleSuspendNuClass
    (a : BiHom 30 33 (model.nu.functor.obj
      (ClassicalObject.sphere.obj model.auxiliary))) :
    BiHom 33 36 (model.nu.functor.obj
      ((ClassicalObject.shift 3 .sphere).obj model.auxiliary)) :=
  let a1 := suspendNuClass .sphere 3 33 a
  let a2 := suspendNuClass (.shift 1 .sphere) 3 34 a1
  let a3 := suspendNuClass (.shift 1 (.shift 1 .sphere)) 3 35 a2
  a3 ≫ model.nu.functor.map tripleSphereShiftIso.hom

private theorem exists_triple_suspension_fixed_source
    (a : BiHom 30 33 (model.nu.functor.obj
      (ClassicalObject.sphere.obj model.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 3 33 h0h4Square) :
    ∃ x : Ambient model (.shift 3 .sphere) (3,36),
      IsSphereThreeH0H4Square x ∧
      tripleSuspendNuClass a ≫ XModLambdaN.incl _ 1 =
        nativeFirstLabel (.shift 3 .sphere) 3 36 x ∧
      IsPermanent model (.shift 3 .sphere) (3,36) x ∧
      Detects (model.convergence (.nu (.shift 3 .sphere))) (3,36,36)
        (nuWeightLabel model (.shift 3 .sphere) 3 36 36 (by decide) x)
        (tripleSuspendNuClass a) := by
  obtain ⟨x1,hx1,ha1⟩ := exists_suspend_nu_first_label .sphere 3 33 h0h4Square a ha
  let a1 := suspendNuClass .sphere 3 33 a
  obtain ⟨x2,hx2,ha2⟩ := exists_suspend_nu_first_label (.shift 1 .sphere) 3 34 x1 a1 ha1
  let a2 := suspendNuClass (.shift 1 .sphere) 3 34 a1
  obtain ⟨x3,hx3,ha3⟩ := exists_suspend_nu_first_label (.shift 1 (.shift 1 .sphere))
    3 35 x2 a2 ha2
  let a3 := suspendNuClass (.shift 1 (.shift 1 .sphere)) 3 35 a2
  let x := (model.classical.map tripleSphereShiftIso.hom).pageMap 2 (3,36) x3
  have hlabel : tripleSuspendNuClass a ≫ XModLambdaN.incl _ 1 =
      nativeFirstLabel (.shift 3 .sphere) 3 36 x := by
    change (a3 ≫ model.nu.functor.map tripleSphereShiftIso.hom) ≫
      XModLambdaN.incl _ 1 = _
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,ha3,
      native_first_label_natural]
    rfl
  have hp : x ∈ permanentCycles model (.shift 3 .sphere) (3,36) :=
    first_label_lift_permanent (.shift 3 .sphere) 3 36 x (tripleSuspendNuClass a) hlabel
  refine ⟨x,?_,hlabel,hp,?_⟩
  · exact ⟨x1,x2,x3,hx1,hx2,hx3,rfl⟩
  · exact nu_first_label_detects (.shift 3 .sphere) 3 36 x hp (tripleSuspendNuClass a) hlabel


private def tripleShiftFunctor : SyntheticSpectrum ⥤ SyntheticSpectrum :=
  (SyntheticCategory.biShift (1,1) ⋙ SyntheticCategory.biShift (1,1)) ⋙
    SyntheticCategory.biShift (1,1)

private def tripleShiftNatIso : tripleShiftFunctor ≅ SyntheticCategory.biShift (3,3) :=
  Functor.isoWhiskerRight (SyntheticCategory.biShift_comp (1,1) (1,1))
    (SyntheticCategory.biShift (1,1)) ≪≫
    SyntheticCategory.biShift_comp (2,2) (1,1)

private def tripleSourceIso : Smn (Syn:=SyntheticSpectrum) 33 36 ≅
    tripleShiftFunctor.obj (Smn 30 33) :=
  ((SyntheticCategory.biShift_comp (32,35) (1,1)).app S_0_0).symm ≪≫
    (SyntheticCategory.biShift (1,1)).mapIso
      (((SyntheticCategory.biShift_comp (31,34) (1,1)).app S_0_0).symm ≪≫
        (SyntheticCategory.biShift (1,1)).mapIso
          ((SyntheticCategory.biShift_comp (30,33) (1,1)).app S_0_0).symm)

private def tripleNuTargetIso :
    tripleShiftFunctor.obj (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) ≅
      model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary) :=
  (SyntheticCategory.biShift (1,1)).mapIso
    ((SyntheticCategory.biShift (1,1)).mapIso
      (model.nu.suspensionIso (ClassicalObject.sphere.obj model.auxiliary)).symm ≪≫
      (model.nu.suspensionIso ((ClassicalObject.shift 1 .sphere).obj model.auxiliary)).symm) ≪≫
    (model.nu.suspensionIso ((ClassicalObject.shift 1 (.shift 1 .sphere)).obj model.auxiliary)).symm ≪≫
    model.nu.functor.mapIso tripleSphereShiftIso

private def tripleFlatNuIso :
    (SyntheticCategory.biShift (3,3)).obj
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) ≅
      model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary) :=
  (tripleShiftNatIso.app _).symm ≪≫ tripleNuTargetIso

private def tripleSourceAuto : Smn (Syn:=SyntheticSpectrum) 33 36 ≅ Smn 33 36 :=
  tripleSourceIso ≪≫ tripleShiftNatIso.app (Smn 30 33) ≪≫
    (SyntheticCategory.biShift_comp (30,33) (3,3)).app S_0_0

private def tripleTargetAuto : Smn (Syn:=SyntheticSpectrum) 3 3 ≅ Smn 3 3 :=
  ((SyntheticCategory.biShift (3,3)).mapIso model.nu.unitIso).symm ≪≫
    tripleFlatNuIso ≪≫ nuSphereThree model

private theorem triple_suspend_expanded
    (a : BiHom 30 33 (model.nu.functor.obj
      (ClassicalObject.sphere.obj model.auxiliary))) :
    tripleSuspendNuClass a =
      tripleSourceIso.hom ≫ tripleShiftFunctor.map a ≫ tripleNuTargetIso.hom := by
  simp only [tripleSuspendNuClass,suspendNuClass,tripleSourceIso,tripleNuTargetIso,
    tripleShiftFunctor,shiftHomotopyClass,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_hom,Functor.map_comp,Functor.comp_map,Category.assoc,
    homotopyRegrade]
  rfl

private theorem triple_suspend_flat
    (a : BiHom 30 33 (model.nu.functor.obj
      (ClassicalObject.sphere.obj model.auxiliary))) :
    tripleSuspendNuClass a = tripleSourceAuto.hom ≫
      shiftHomotopyClass (3,3) (30,33) a ≫ tripleFlatNuIso.hom := by
  rw [triple_suspend_expanded]
  have hn := tripleShiftNatIso.hom.naturality a
  change tripleShiftFunctor.map a ≫ tripleShiftNatIso.hom.app _ =
    tripleShiftNatIso.hom.app _ ≫ (SyntheticCategory.biShift (3,3)).map a at hn
  simp only [tripleSourceAuto,tripleFlatNuIso,shiftHomotopyClass,Iso.trans_hom,
    Iso.symm_hom,Iso.app_hom,Iso.app_inv,Category.assoc,Iso.hom_inv_id_app_assoc]
  have hnf := congrArg (fun z => z ≫ tripleShiftNatIso.inv.app _ ≫
    tripleNuTargetIso.hom) hn
  simp only [Category.assoc,Iso.hom_inv_id_app_assoc] at hnf
  exact congrArg (fun z => tripleSourceIso.hom ≫ z) hnf

private theorem triple_suspend_sphere_coordinates
    (a : BiHom 30 33 (model.nu.functor.obj
      (ClassicalObject.sphere.obj model.auxiliary))) :
    tripleSuspendNuClass a ≫ (nuSphereThree model).hom =
      tripleSourceAuto.hom ≫
        shiftHomotopyClass (3,3) (30,33) (a ≫ model.nu.unitIso.hom) ≫
        tripleTargetAuto.hom := by
  rw [triple_suspend_flat]
  simp only [tripleTargetAuto,shiftHomotopyClass,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_inv,Functor.map_comp,Category.assoc,Iso.map_hom_inv_id_assoc]

private theorem triple_suspend_sphere_first_quotient
    (a : BiHom 30 33 (model.nu.functor.obj
      (ClassicalObject.sphere.obj model.auxiliary))) :
    tripleSuspendNuClass a ≫ (nuSphereThree model).hom ≫ XModLambdaN.incl _ 1 =
      shiftHomotopyClass (3,3) (30,33) (a ≫ model.nu.unitIso.hom) ≫
        XModLambdaN.incl _ 1 := by
  rw [←Category.assoc,triple_suspend_sphere_coordinates]
  simp only [Category.assoc,bigraded_sphere_automorphism_first_quotient]
  exact sphere_automorphism_quotient_projection 33 36 tripleSourceAuto _ _


/-- Any source and sphere-target coordinates for the same shift functor
give identical Q1 maps. The proof uses only naturality of the shift-functor
comparison and the two explicit sphere automorphisms. -/
private theorem shift_sphere_coordinates_first_quotient
    (δ p : ℤ × ℤ) (F : SyntheticSpectrum ⥤ SyntheticSpectrum)
    (E : F ≅ SyntheticCategory.biShift δ)
    (S : Smn (Syn:=SyntheticSpectrum) (p+δ).1 (p+δ).2 ≅ F.obj (Smn p.1 p.2))
    (T : F.obj (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) ≅
      Smn (Syn:=SyntheticSpectrum) δ.1 δ.2)
    (a : BiHom p.1 p.2 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) :
    S.hom ≫ F.map a ≫ T.hom ≫ XModLambdaN.incl _ 1 =
      shiftHomotopyClass δ p (a ≫ model.nu.unitIso.hom) ≫ XModLambdaN.incl _ 1 := by
  let U := S ≪≫ E.app (Smn p.1 p.2) ≪≫ (SyntheticCategory.biShift_comp p δ).app S_0_0
  let V := ((SyntheticCategory.biShift δ).mapIso model.nu.unitIso).symm ≪≫
    (E.app _).symm ≪≫ T
  have heq : S.hom ≫ F.map a ≫ T.hom =
      U.hom ≫ shiftHomotopyClass δ p (a ≫ model.nu.unitIso.hom) ≫ V.hom := by
    have hn := E.hom.naturality a
    have hnf := congrArg (fun z => z ≫ E.inv.app _ ≫ T.hom) hn
    simp only [Category.assoc,Iso.hom_inv_id_app_assoc] at hnf
    simp only [U,V,shiftHomotopyClass,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,
      Iso.app_inv,Functor.mapIso_inv,Functor.map_comp,Category.assoc,
      Iso.hom_inv_id_app_assoc,Iso.map_hom_inv_id_assoc]
    exact congrArg (fun z => S.hom ≫ z) hnf
  have heqQ := congrArg (fun z => z ≫ XModLambdaN.incl _ 1) heq
  simp only [Category.assoc] at heqQ
  rw [heqQ]
  simp only [bigraded_sphere_automorphism_first_quotient]
  exact sphere_automorphism_quotient_projection (p+δ).1 (p+δ).2 U _ _

private def positiveTripleShiftFunctor : SyntheticSpectrum ⥤ SyntheticSpectrum :=
  tripleShiftFunctor ⋙ SyntheticCategory.biShift (0,1)

private def positiveTripleShiftNatIso :
    positiveTripleShiftFunctor ≅ SyntheticCategory.biShift (3,4) :=
  Functor.isoWhiskerRight tripleShiftNatIso (SyntheticCategory.biShift (0,1)) ≪≫
    SyntheticCategory.biShift_comp (3,3) (0,1)

private def positiveTripleSourceIso : Smn (Syn:=SyntheticSpectrum) 33 37 ≅
    positiveTripleShiftFunctor.obj (Smn 30 33) :=
  ((SyntheticCategory.biShift_comp (33,36) (0,1)).app S_0_0).symm ≪≫
    (SyntheticCategory.biShift (0,1)).mapIso tripleSourceIso

private def positiveNuSphereThreeIso :
    (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary)) ≅
      Smn (Syn:=SyntheticSpectrum) 3 4 :=
  (SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree model) ≪≫
    (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0

private def positiveTripleTargetIso :
    positiveTripleShiftFunctor.obj
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) ≅
      Smn (Syn:=SyntheticSpectrum) 3 4 :=
  (SyntheticCategory.biShift (0,1)).mapIso tripleNuTargetIso ≪≫ positiveNuSphereThreeIso

/-- This is the actual full source of the normalized nu map, at the source
weight (36+e(nu))=37. -/
private def positiveTripleNuClass
    (a : BiHom 30 33 (model.nu.functor.obj
      (ClassicalObject.sphere.obj model.auxiliary))) :
    BiHom 33 37 ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary))) :=
  shiftHomotopyClass (0,1) (33,36) (tripleSuspendNuClass a)

private theorem positive_triple_suspend_sphere_first_quotient
    (a : BiHom 30 33 (model.nu.functor.obj
      (ClassicalObject.sphere.obj model.auxiliary))) :
    positiveTripleNuClass a ≫ positiveNuSphereThreeIso.hom ≫ XModLambdaN.incl _ 1 =
      shiftHomotopyClass (3,4) (30,33) (a ≫ model.nu.unitIso.hom) ≫
        XModLambdaN.incl _ 1 := by
  have h := shift_sphere_coordinates_first_quotient (3,4) (30,33)
    positiveTripleShiftFunctor positiveTripleShiftNatIso positiveTripleSourceIso
    positiveTripleTargetIso a
  calc
    positiveTripleNuClass a ≫ positiveNuSphereThreeIso.hom ≫ XModLambdaN.incl _ 1 =
        positiveTripleSourceIso.hom ≫ positiveTripleShiftFunctor.map a ≫
          positiveTripleTargetIso.hom ≫ XModLambdaN.incl _ 1 := by
      simp only [positiveTripleNuClass,shiftHomotopyClass,triple_suspend_expanded,
        positiveTripleSourceIso,positiveTripleTargetIso,positiveTripleShiftFunctor,
        Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,Functor.comp_map,
        Functor.map_comp,Category.assoc]
      rfl
    _ = _ := h


private theorem shift_precomp_sphere_automorphism_first_quotient
    (δ p : ℤ × ℤ) (V : SyntheticSpectrum)
    (σ : Smn (Syn:=SyntheticSpectrum) p.1 p.2 ≅ Smn p.1 p.2)
    (a : BiHom p.1 p.2 V) :
    shiftHomotopyClass δ p (σ.hom ≫ a) ≫ XModLambdaN.incl _ 1 =
      shiftHomotopyClass δ p a ≫ XModLambdaN.incl _ 1 := by
  let τ : Smn (Syn:=SyntheticSpectrum) (p+δ).1 (p+δ).2 ≅ Smn (p+δ).1 (p+δ).2 :=
    ((SyntheticCategory.biShift_comp p δ).app S_0_0).symm ≪≫
      (SyntheticCategory.biShift δ).mapIso σ ≪≫
      (SyntheticCategory.biShift_comp p δ).app S_0_0
  have heq : shiftHomotopyClass δ p (σ.hom ≫ a) =
      τ.hom ≫ shiftHomotopyClass δ p a := by
    simp only [τ,shiftHomotopyClass,Functor.map_comp,Iso.trans_hom,Iso.symm_hom,
      Functor.mapIso_hom,Iso.app_hom,Iso.app_inv,Category.assoc,Iso.hom_inv_id_app_assoc]
  rw [heq]
  simpa only [Category.assoc] using
    sphere_automorphism_quotient_projection (p+δ).1 (p+δ).2 τ _ (shiftHomotopyClass δ p a)

/-- The geometric boundary representative need only satisfy the actual
boundary-shift equality up to a source sphere automorphism. Its actual
normalized source first quotient equals that of the same fixed source
constructed by three suspensions; no full representative equality is used. -/
private theorem geometric_boundary_source_first_quotient
    (βν : BiHom 30 33 (model.nu.functor.obj
      (ClassicalObject.sphere.obj model.auxiliary)))
    (βunit : BiHom 30 33 (S_0_0 : SyntheticSpectrum))
    (hβunit : βunit = βν ≫ model.nu.unitIso.hom)
    (γ : BiHom 33 37 (Smn (Syn:=SyntheticSpectrum) 3 4))
    (σ : Smn (Syn:=SyntheticSpectrum) 30 33 ≅ Smn 30 33)
    (hγ : γ = shiftHomotopyClass (3,4) (30,33) (σ.hom ≫ βunit)) :
    (γ ≫ positiveNuSphereThreeIso.inv) ≫ XModLambdaN.incl _ 1 =
      positiveTripleNuClass βν ≫ XModLambdaN.incl _ 1 := by
  haveI : IsIso (XModLambdaN.map positiveNuSphereThreeIso.hom 1) := by
    change IsIso ((model.quotients.functoriality.functor 1).map positiveNuSphereThreeIso.hom)
    infer_instance
  apply (cancel_mono (XModLambdaN.map positiveNuSphereThreeIso.hom 1)).mp
  have hinv : positiveNuSphereThreeIso.inv ≫ XModLambdaN.incl _ 1 ≫
      XModLambdaN.map positiveNuSphereThreeIso.hom 1 = XModLambdaN.incl _ 1 := by
    rw [←XModLambdaN.incl_naturality,←Category.assoc,Iso.inv_hom_id,Category.id_comp]
  calc
    ((γ ≫ positiveNuSphereThreeIso.inv) ≫ XModLambdaN.incl _ 1) ≫
        XModLambdaN.map positiveNuSphereThreeIso.hom 1 = γ ≫ XModLambdaN.incl _ 1 := by
      simp only [Category.assoc]
      rw [hinv]
    _ = shiftHomotopyClass (3,4) (30,33) βunit ≫ XModLambdaN.incl _ 1 := by
      rw [hγ]
      exact shift_precomp_sphere_automorphism_first_quotient (3,4) (30,33) _ σ βunit
    _ = shiftHomotopyClass (3,4) (30,33) (βν ≫ model.nu.unitIso.hom) ≫
        XModLambdaN.incl _ 1 := by
      rw [hβunit]
      rfl
    _ = (positiveTripleNuClass βν ≫ XModLambdaN.incl _ 1) ≫
        XModLambdaN.map positiveNuSphereThreeIso.hom 1 := by
      rw [Category.assoc,←XModLambdaN.incl_naturality]
      exact (positive_triple_suspend_sphere_first_quotient βν).symm


private def boundaryShiftNatIsoAny (δ : ℤ×ℤ) (q : ℕ) :
    SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,-(q:ℤ)) ⋙
        SyntheticCategory.biShift δ ≅
      SyntheticCategory.biShift δ ⋙ SyntheticCategory.biShift (1,-(q:ℤ)) := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ
  let L := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let J := boundarySuspensionNatIso q
  let C := shiftCommIso δ (0,-(q:ℤ))
  letI := model.exactness.shiftCommShift δ
  exact Functor.isoWhiskerRight J F ≪≫ Functor.associator L S F ≪≫
    Functor.isoWhiskerLeft L (F.commShiftIso (1:ℤ)) ≪≫
    (Functor.associator L F S).symm ≪≫ Functor.isoWhiskerRight C.symm S ≪≫
    Functor.associator F L S ≪≫ Functor.isoWhiskerLeft F J.symm

private theorem boundaryShiftNatIsoAny_app (δ : ℤ×ℤ) (q : ℕ) (A : SyntheticSpectrum) :
    (boundaryShiftNatIsoAny δ q).app A =
      (SyntheticCategory.biShift δ).mapIso (biSuspensionIso q A) ≪≫
        (by letI := model.exactness.shiftCommShift δ
            exact ((SyntheticCategory.biShift δ).commShiftIso (1:ℤ)).app _) ≪≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
          ((shiftCommIso δ (0,-(q:ℤ))).symm.app A) ≪≫
        (biSuspensionIso q ((SyntheticCategory.biShift δ).obj A)).symm := by
  apply Iso.ext
  simp only [boundaryShiftNatIsoAny,boundarySuspensionNatIso,Iso.app_hom,
    Iso.trans_hom,Iso.symm_hom,NatTrans.comp_app,Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom,Functor.whiskerRight_app,Functor.whiskerLeft_app,
    Functor.associator_hom_app,Functor.associator_inv_app,NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app,Functor.mapIso_hom,Category.id_comp]

/-- A quotient comparison chosen from the canonical lambda square, retaining
the complete boundary square with the natural comparison above. -/
private theorem quotient_boundary_shift_any_exists
    (A : SyntheticSpectrum) (δ : ℤ×ℤ) (q : ℕ) :
    ∃ eQ : XModLambdaN ((SyntheticCategory.biShift δ).obj A) q ≅
        (SyntheticCategory.biShift δ).obj (XModLambdaN A q),
      XModLambdaN.incl ((SyntheticCategory.biShift δ).obj A) q ≫ eQ.hom =
        (SyntheticCategory.biShift δ).map (XModLambdaN.incl A q) ∧
      eQ.hom ≫ (SyntheticCategory.biShift δ).map (absoluteBoundary A q) ≫
          (boundaryShiftNatIsoAny δ q).hom.app A =
        absoluteBoundary ((SyntheticCategory.biShift δ).obj A) q := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ
  letI := model.exactness.shiftCommShift δ
  letI := model.exactness.shiftExact δ
  let C := (shiftCommIso δ (0,-(q:ℤ))).app A
  let T := Triangle.mk (lambdaPow q A) (XModLambdaN.incl A q) (XModLambdaN.proj A q)
  let T' := Triangle.mk (lambdaPow q (F.obj A))
    (XModLambdaN.incl (F.obj A) q) (XModLambdaN.proj (F.obj A) q)
  have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
  have hT' : T' ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
  let E := isoTriangleOfIso₁₂ T' (F.mapTriangle.obj T) hT'
    (F.map_distinguished T hT) C (Iso.refl _) (by
      change lambdaPow q (F.obj A) ≫ 𝟙 _ = C.hom ≫ F.map (lambdaPow q A)
      simpa only [Category.comp_id,C,F,lambdaDegree,Iso.app_hom] using
        lambdaPow_shift_comm δ q A)
  refine ⟨Triangle.π₃.mapIso E,?_,?_⟩
  · have h := E.hom.comm₂
    change XModLambdaN.incl (F.obj A) q ≫ E.hom.hom₃ =
      E.hom.hom₂ ≫ F.map (XModLambdaN.incl A q) at h
    change XModLambdaN.incl (F.obj A) q ≫ E.hom.hom₃ =
      F.map (XModLambdaN.incl A q)
    simpa only [E,isoTriangleOfIso₁₂_hom_hom₂,Iso.refl_hom,Category.id_comp] using h
  · have h := E.hom.comm₃
    have h₁ : E.hom.hom₁ = C.hom := by
      simp only [E,isoTriangleOfIso₁₂_hom_hom₁]
    rw [h₁] at h
    change XModLambdaN.proj (F.obj A) q ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map C.hom =
      E.hom.hom₃ ≫ (F.map (XModLambdaN.proj A q) ≫
        (F.commShiftIso (1:ℤ)).hom.app _) at h
    have hh := congrArg (fun z => z ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map C.inv ≫
      (biSuspensionIso q (F.obj A)).inv) h.symm
    simp only [Category.assoc,Iso.map_hom_inv_id_assoc] at hh
    change E.hom.hom₃ ≫ F.map (absoluteBoundary A q) ≫
      (boundaryShiftNatIsoAny δ q).hom.app A = absoluteBoundary (F.obj A) q
    change E.hom.hom₃ ≫ F.map (absoluteBoundary A q) ≫
      ((boundaryShiftNatIsoAny δ q).app A).hom = absoluteBoundary (F.obj A) q
    rw [boundaryShiftNatIsoAny_app]
    simpa only [absoluteBoundary,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,
      Functor.map_comp,Category.assoc,Iso.map_inv_hom_id_assoc,
      Iso.app_hom,Iso.app_inv,C,F] using hh


/-- Any natural interchange differs from the canonical commutator only by
an automorphism of the original representing sphere. -/
private theorem double_shift_comparison_sphere
    (D δ p : ℤ×ℤ)
    (N : SyntheticCategory.biShift (Syn:=SyntheticSpectrum) D ⋙ SyntheticCategory.biShift δ ≅
      SyntheticCategory.biShift δ ⋙ SyntheticCategory.biShift D)
    (A : SyntheticSpectrum) (a : BiHom p.1 p.2 A) :
    ∃ u : Smn (Syn:=SyntheticSpectrum) p.1 p.2 ≅ Smn p.1 p.2,
      shiftHomotopyClass δ (p+D) (shiftHomotopyClass D p a) ≫ N.hom.app A =
        homotopyRegrade
          (show ((p+δ)+D).1=((p+D)+δ).1 by dsimp; omega)
          (show ((p+δ)+D).2=((p+D)+δ).2 by dsimp; omega)
          (shiftHomotopyClass D (p+δ) (shiftHomotopyClass δ p (u.hom≫a))) := by
  obtain ⟨u,hu⟩ := natural_iso_comparison_sphere
    (SyntheticCategory.biShift D ⋙ SyntheticCategory.biShift δ)
    (SyntheticCategory.biShift δ ⋙ SyntheticCategory.biShift D)
    ((SyntheticCategory.biShift_fullyFaithful D).comp (SyntheticCategory.biShift_fullyFaithful δ))
    N (shiftCommIso D δ) p.1 p.2 A a
  refine ⟨u,?_⟩
  have hN : shiftHomotopyClass δ (p+D) (shiftHomotopyClass D p a) ≫ N.hom.app A =
      shiftHomotopyClass δ (p+D) (shiftHomotopyClass D p (u.hom≫a)) ≫
        (shiftCommIso D δ).hom.app A := by
    have hh := congrArg (fun v => (SyntheticCategory.biShift_comp (p+D) δ).inv.app S_0_0 ≫
      (SyntheticCategory.biShift δ).map ((SyntheticCategory.biShift_comp p D).inv.app S_0_0) ≫ v) hu
    simpa only [shiftHomotopyClass,Functor.map_comp,Functor.comp_map,Category.assoc] using hh
  rw [hN]
  rcases D with ⟨d₁,d₂⟩
  rw [shift_regrade]
  have hh := shift_hom_swap p (d₁,d₂) δ (p+(d₁,d₂)) (p+δ) ((p+(d₁,d₂))+δ)
    rfl rfl rfl (by ext <;> dsimp <;> omega) (u.hom≫a)
  simpa only [shiftHomotopyClass,biShiftAddIso,eqToIso_refl,Iso.trans_refl,Prod.eta,
    Category.assoc] using hh

/-- The exact degree instance needed by the numerical nu extension.
The comparison kappa is produced, not assumed. Its actual quotient boundary
is the shifted original boundary up to one source-sphere automorphism. -/
private theorem nu_degree_boundary_shift
    (A : SyntheticSpectrum)
    (x : BiHom 31 32 (XModLambdaN A 1)) :
    ∃ κ : XModLambdaN ((SyntheticCategory.biShift (3,4)).obj A) 1 ≅
        (SyntheticCategory.biShift (3,4)).obj (XModLambdaN A 1),
      XModLambdaN.incl _ 1≫κ.hom =
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl A 1) ∧
      ∃ u : Smn (Syn:=SyntheticSpectrum) 30 33 ≅ Smn 30 33,
        biSuspensionHomEquiv 34 36 1 ((SyntheticCategory.biShift (3,4)).obj A)
          ((shiftHomotopyClass (3,4) (31,32) x≫κ.inv)≫XModLambdaN.proj _ 1) =
        shiftHomotopyClass (3,4) (30,33)
          (u.hom≫biSuspensionHomEquiv 31 32 1 A (x≫XModLambdaN.proj A 1)) := by
  obtain ⟨κ,hκ,hδ⟩ := quotient_boundary_shift_any_exists A (3,4) 1
  refine ⟨κ,hκ,?_⟩
  let β : BiHom 30 33 A := biSuspensionHomEquiv 31 32 1 A (x≫XModLambdaN.proj A 1)
  have hx : x≫absoluteBoundary A 1=shiftHomotopyClass (1,-1) (30,33) β := by
    simpa [β,homotopyRegrade] using absolute_boundary_class_shift A 1 31 32 x
  obtain ⟨u,hu⟩ := double_shift_comparison_sphere (1,-1) (3,4) (30,33)
    (boundaryShiftNatIsoAny (3,4) 1) A β
  refine ⟨u,?_⟩
  let c := shiftHomotopyClass (3,4) (31,32) x≫κ.inv
  have hboundary : c≫absoluteBoundary ((SyntheticCategory.biShift (3,4)).obj A) 1 =
      shiftHomotopyClass (1,-1) (33,37)
        (shiftHomotopyClass (3,4) (30,33) (u.hom≫β)) := by
    rw [←hδ]
    dsimp only [c]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
    have hh := congrArg (fun z => z≫(boundaryShiftNatIsoAny (3,4) 1).hom.app A)
      (shift_hom_comp (3,4) (31,32) x (absoluteBoundary A 1))
    apply Eq.trans (by simpa only [Category.assoc] using hh.symm)
    rw [hx]
    simpa [homotopyRegrade] using hu
  apply (biSuspensionHomEquiv 34 36 1 ((SyntheticCategory.biShift (3,4)).obj A)).symm.injective
  rw [AddEquiv.symm_apply_apply,bi_susp_symm_eq]
  have hh := congrArg (fun z => z≫(biSuspensionIso 1 ((SyntheticCategory.biShift (3,4)).obj A)).hom)
    hboundary
  simpa [c,β,absoluteBoundary,homotopyRegrade,shiftHomotopyClass,susp_invariance,Iso.homCongr,
    Category.assoc] using hh


/-- Qualified native nu labels are preserved by the actual boundary in the
shifted quotient.  The source-sphere automorphism in the raw comparison acts
trivially on this detector, rather than being discarded from a map equation. -/
private theorem nu_degree_boundary_shift_detects
    (X : ClassicalObject) (u : Ambient model X (3,33))
    (x : BiHom 31 32 (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (hx : Detects (model.convergence (.nu X)) (3,33,33)
      (nuWeightLabel model X 3 33 33 (by omega) u)
      (biSuspensionHomEquiv 31 32 1 (model.nu.functor.obj (X.obj model.auxiliary))
        (x≫XModLambdaN.proj _ 1))) :
    ∃ κ : XModLambdaN ((SyntheticCategory.biShift (3,4)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
        (SyntheticCategory.biShift (3,4)).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1),
      XModLambdaN.incl _ 1≫κ.hom =
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl _ 1) ∧
      Detects (model.convergence (.shift (3,4) (.nu X))) (3,36,37)
        (((KIP126.AdamsSynthetic.Standard.essShift (3,4)).page (.nu X) 2 (by decide) (30,33) 3).hom
          (nuWeightLabel model X 3 33 33 (by omega) u))
        (biSuspensionHomEquiv 34 36 1
          ((SyntheticCategory.biShift (3,4)).obj (model.nu.functor.obj (X.obj model.auxiliary)))
          ((shiftHomotopyClass (3,4) (31,32) x≫κ.inv)≫XModLambdaN.proj _ 1)) := by
  obtain ⟨κ,hκ,σ,hσ⟩ := nu_degree_boundary_shift (model.nu.functor.obj (X.obj model.auxiliary)) x
  refine ⟨κ,hκ,?_⟩
  rw [hσ]
  have hauto := sphere_automorphism_nu_detects X 3 33 33 (by omega) u σ _ hx
  have hshift := detects_shift (.nu X) (3,4) (30,33) 3
    (nuWeightLabel model X 3 33 33 (by omega) u)
    (σ.hom≫biSuspensionHomEquiv 31 32 1 (model.nu.functor.obj (X.obj model.auxiliary))
      (x≫XModLambdaN.proj _ 1)) (by simpa [homotopyRegrade] using hauto)
  simpa [homotopyRegrade] using hshift


private theorem permanent_member_of_cycle (X : ClassicalObject) (p : ℤ×ℤ)
    (x : Ambient model X p)
    (h : IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) p x) :
    x ∈ permanentCycles model X p := by
  obtain ⟨z,hz⟩ := h
  refine ⟨z,?_⟩
  have hi := normalizeInitialProjection ((model.classical.obj (X.obj model.auxiliary)).ssData p)
    (↑(2-(model.classical.obj (X.obj model.auxiliary)).r₀).toNat) ⊤
    (by rw [model.classical.firstPage];rfl) le_top
  exact (congrArg (fun f => f z) hi).symm.trans hz

private theorem permanent_cycle_of_member (X : ClassicalObject) (p : ℤ×ℤ)
    (x : Ambient model X p) (h : x ∈ permanentCycles model X p) :
    IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) p x := by
  obtain ⟨z,hz⟩ := h
  refine ⟨z,?_⟩
  have hi := normalizeInitialProjection ((model.classical.obj (X.obj model.auxiliary)).ssData p)
    (↑(2-(model.classical.obj (X.obj model.auxiliary)).r₀).toNat) ⊤
    (by rw [model.classical.firstPage];rfl) le_top
  exact (congrArg (fun f => f z) hi).trans hz

/-- Restrict the same full source and image, with both specified detectors,
to a finite page in the defining range. No inverse-limit lift is asserted. -/
private theorem finiteExtension_of_infinite
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (hp : 2 ≤ page)
    (hupper : n ≤ (page:ℤ)-2+normalizedExponent model.classicalTower f)
    (h : InfiniteExtension model X Y f n s t x y) :
    FiniteExtension model X Y f page n s t x y := by
  obtain ⟨W⟩ := h
  let AS := extensionSourceObject model X Y f
  let BY : SyntheticObject := .nu Y
  let qs := XModLambdaN.incl (AS.obj model.nu model.auxiliary) (page-1)
  let qt := XModLambdaN.incl (BY.obj model.nu model.auxiliary) (page-1)
  refine ⟨{
    page_ge_two := hp
    length_lower := W.length_lower
    length_upper := hupper
    source_cycle := ?_
    target_cycle := ?_
    source := (model.family.functor.map qs).eInftyMap
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f) W.source
    target := (model.family.functor.map qt).eInftyMap
      (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f) W.target
    source_rep := ?_
    target_rep := ?_
    equation := ?_ }⟩
  · apply (isCycle_iff_reaches model X page (by omega) (s,t) x).mp
    exact ⟨by omega,permanentCycles_le_cycles model X (s,t) _
      (permanent_member_of_cycle X (s,t) x W.source_cycle)⟩
  · apply (isCycle_iff_reaches model Y
      ((page:ℤ)-n+normalizedExponent model.classicalTower f) (by omega) (s+n,t+n) y).mp
    exact ⟨by omega,permanentCycles_le_cycles model Y (s+n,t+n) _
      (permanent_member_of_cycle Y (s+n,t+n) y W.target_cycle)⟩
  · have H := family_infinity_representative_map qs _ _ W.source W.source_rep
    have hc : familyPageMap model.family qs 2
        (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
        (infiniteSourceForExtension model X Y f s t x) =
        finiteSourceForExtension model X Y f (page-1) s t x := by
      unfold infiniteSourceForExtension finiteSourceForExtension finiteNuLabel
      rw [←page_regrade]
      rfl
    rwa [hc] at H
  · have H := family_infinity_representative_map qt _ _ W.target W.target_rep
    have hc : familyPageMap model.family qt 2
        (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f)
        (infiniteTargetForExtension model X Y f n s t W.length_lower y) =
        finiteTargetForExtension model X Y f (page-1) n s t W.length_lower y := by
      unfold infiniteTargetForExtension finiteTargetForExtension finiteTargetLabel
      rw [←page_regrade]
    rwa [hc] at H
  · exact Paper.extension_square_map AS BY (.quotient (page-1) AS) (.quotient (page-1) BY)
      (model.normalizedMap X Y f).map (finiteExtensionMap model X Y f (page-1)) qs qt
      (XModLambdaN.incl_naturality (model.normalizedMap X Y f).map (page-1)).symm
      (t-s,t+normalizedExponent model.classicalTower f) s n W.source W.target W.equation

private theorem quotient_boundary_evaluation_natural
    {A B : SyntheticSpectrum} (f : A ⟶ B) (q : ℕ) (m w : ℤ)
    (x : BiHom m w (XModLambdaN A q)) :
    biSuspensionHomEquiv m w q B ((x≫XModLambdaN.map f q)≫XModLambdaN.proj B q) =
      biSuspensionHomEquiv m w q A (x≫XModLambdaN.proj A q)≫f := by
  rw [Category.assoc,XModLambdaN.proj_naturality,←Category.assoc]
  exact bi_susp_natural model.quotients.coherence m w q f _

private theorem paper_d2_h5 : HasDifferential model.classical.sphere 2
    (1,32) (3,33) (model.standardClasses.standardHi 5) h0h4Square := by
  exact (KIP126.Literature.Standard.adamsOneLine_d2 5 (by decide)).toHasDifferential

private theorem sphere_native_quotient_label (s t : ℤ)
    (x : Ambient model .sphere (s,t)) :
    KIP126.Literature.sphereFirstQuotient model s t
      (nativeFirstLabel .sphere s t x ≫ XModLambdaN.map model.nu.unitIso.hom 1) = x := by
  dsimp only [nativeFirstLabel]
  rw [Category.assoc,←model.quotients.functoriality.map_comp]
  exact sphere_first_quotient_label s t x

private theorem base_h5_boundary :
    ∃ β : BiHom 30 33 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      β≫XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 3 33 h0h4Square ∧
      biSuspensionHomEquiv 31 32 1 (S_0_0 : SyntheticSpectrum)
        (h5Q1≫XModLambdaN.proj _ 1) = β≫model.nu.unitIso.hom := by
  obtain ⟨c,hc,hβ⟩ := adjacent_absolute_boundary .sphere 1 (by decide) 1 32
    (model.standardClasses.standardHi 5) h0h4Square paper_d2_h5
  have hc : c = nativeFirstLabel .sphere 1 32 (model.standardClasses.standardHi 5) := by
    simpa only [(model.quotients.tower _).rho_id,Category.comp_id,nativeFirstLabel] using hc
  let β : BiHom 30 33 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :=
    biSuspensionHomEquiv 31 32 1 _ (c≫XModLambdaN.proj _ 1)
  refine ⟨β,?_,?_⟩
  · simpa [β,homotopyRegrade,nativeFirstLabel] using hβ
  · have hcunit : c≫XModLambdaN.map model.nu.unitIso.hom 1=h5Q1 := by
      apply (KIP126.Literature.sphereFirstQuotient model 1 32).injective
      rw [hc,sphere_native_quotient_label]
      exact (KIP126.Literature.sphereFirstQuotient model 1 32).apply_symm_apply _ |>.symm
    rw [←hcunit]
    exact quotient_boundary_evaluation_natural model.nu.unitIso.hom 1 31 32 c

private theorem target_h2h5_boundary :
    ∃ β : BiHom 33 38 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      β≫XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 5 38 h0p ∧
      biSuspensionHomEquiv 34 36 1 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
        (nativeFirstLabel .sphere 2 36 (KIP126.Literature.Standard.hiProduct 2 5)≫
          XModLambdaN.proj _ 1) = lambdaMultiply 1 β := by
  obtain ⟨c,hc,hβ⟩ := adjacent_absolute_boundary .sphere 2 (by decide) 2 36
    (KIP126.Literature.Standard.hiProduct 2 5) h0p
    paper6_7_classical_d3.toHasDifferential
  let β : BiHom 33 38 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :=
    biSuspensionHomEquiv 34 36 2 _ (c≫XModLambdaN.proj _ 2)
  refine ⟨β,?_,?_⟩
  · simpa [β,homotopyRegrade,nativeFirstLabel] using hβ
  · have hres := absolute_boundary_restriction .sphere 1 2 (by decide) 34 36 c
    change c≫(model.quotients.tower _).rho 1 2 _ = nativeFirstLabel .sphere 2 36
      (KIP126.Literature.Standard.hiProduct 2 5) at hc
    rw [hc] at hres
    simpa [β,homotopyRegrade] using hres
private theorem infinity_rep_of_all_finite
    (D : SSData (ModuleCat.{0} ℤ)) (x : D.page 0)
    (h : ∀ n : ℕ, ∃ z : (Subobject.underlying.obj (D.Z (n : WithTop ℕ)) : ModuleCat.{0} ℤ),
      (Subobject.ofLE _ _ (D.Z_anti bot_le) ≫ D.pageπ 0) z = x) :
    ∃ z : (Subobject.underlying.obj (D.Z ⊤) : ModuleCat.{0} ℤ),
      (Subobject.ofLE _ _ (D.Z_anti bot_le) ≫ D.pageπ 0) z = x := by
  obtain ⟨z0,hz0⟩ := h 0
  change (Subobject.ofLE (D.Z 0) (D.Z 0) _ ≫ D.pageπ 0) z0=x at hz0
  simp only [Subobject.ofLE_refl, Category.id_comp] at hz0
  have hall (n : ℕ) : (D.Z 0).arrow z0 ∈
      (ModuleCat.subobjectModule D.V) (D.Z (n : WithTop ℕ)) := by
    obtain ⟨zn,hzn⟩ := h n
    let j := Subobject.ofLE (D.Z (n : WithTop ℕ)) (D.Z 0) (D.Z_anti bot_le)
    change (j≫D.pageπ 0) zn=x at hzn
    have hz : D.pageπ 0 (z0-j zn)=0 := by
      rw [map_sub,hz0]
      change x-(j≫D.pageπ 0) zn=0
      rw [hzn,sub_self]
    have hb := (subobject_cokernel_π_eq_zero_iff (D.B 0) (D.Z 0) (D.B_le_Z 0) _).mp hz
    have hbn : (D.Z 0).arrow (z0-j zn) ∈
        (ModuleCat.subobjectModule D.V) (D.Z (n : WithTop ℕ)) :=
      (ModuleCat.subobjectModule D.V).monotone
        ((D.B_mono bot_le).trans (D.B_le_Z _)) hb
    have hnmem : (D.Z 0).arrow (j zn) ∈
        (ModuleCat.subobjectModule D.V) (D.Z (n : WithTop ℕ)) := by
      exact ⟨zn,(ConcreteCategory.congr_hom (Subobject.ofLE_arrow (D.Z_anti bot_le)) zn).symm⟩
    have hh := Submodule.add_mem ((ModuleCat.subobjectModule D.V) (D.Z (n : WithTop ℕ))) hbn hnmem
    simpa only [map_sub,sub_add_cancel] using hh
  have htop : D.Z ⊤ = ⨅ n : ℕ, D.Z (n : WithTop ℕ) :=
    le_antisymm (le_iInf fun n => D.Z_anti le_top)
      (D.Z_top_greatest _ (fun n => iInf_le _ n))
  have hm : (D.Z 0).arrow z0 ∈ (ModuleCat.subobjectModule D.V) (D.Z ⊤) := by
    rw [htop, (ModuleCat.subobjectModule D.V).map_iInf]
    exact (Submodule.mem_iInf _).mpr hall
  obtain ⟨z,hz⟩ := hm
  refine ⟨z,?_⟩
  have heq : (Subobject.ofLE (D.Z ⊤) (D.Z 0) (D.Z_anti bot_le)) z = z0 := by
    apply (ModuleCat.mono_iff_injective (D.Z 0).arrow).mp inferInstance
    change (Subobject.ofLE _ _ _ ≫ (D.Z 0).arrow) z = _
    rw [Subobject.ofLE_arrow]
    exact hz
  change D.pageπ 0 ((Subobject.ofLE (D.Z ⊤) (D.Z 0) (D.Z_anti bot_le)) z)=x
  rw [heq,hz0]

private theorem synthetic_infinity_of_all_pages
    (A : SyntheticAdamsSS.{0}) (i : Tridegree) (x : A.E₂ i)
    (h : ∀ r : ℤ, 2 ≤ r → ∃ xr : A.Page r i, SyntheticRepresentsOnPage A r i x xr) :
    ∃ e : (A.sequence.ssData i).eInfty, HasInfinityRepresentative A 2 i x e := by
  rcases A with ⟨⟨⟨r0,D,δ,d⟩,dd,Zs,Bs⟩,hA,hDA⟩
  dsimp at hA
  subst r0
  have hx : ∀ n : ℕ, ∃ z : (Subobject.underlying.obj ((D i).Z (n : WithTop ℕ)) : ModuleCat ℤ),
      (Subobject.ofLE _ _ ((D i).Z_anti bot_le) ≫ (D i).pageπ 0) z = x := by
    intro n
    have hh := h (n+2) (by omega)
    dsimp [SyntheticRepresentsOnPage] at hh
    obtain ⟨xr,_,z,hz,_⟩ := hh
    have hn : ((n:ℤ)+2-2).toNat=n := by omega
    have transport (m : ℕ) (hm : m=n)
        (H : ∃ z : (Subobject.underlying.obj ((D i).Z (m : WithTop ℕ)) : ModuleCat ℤ),
          (Subobject.ofLE _ _ ((D i).Z_anti bot_le) ≫ (D i).pageπ 0) z=x) :
        ∃ z : (Subobject.underlying.obj ((D i).Z (n : WithTop ℕ)) : ModuleCat ℤ),
          (Subobject.ofLE _ _ ((D i).Z_anti bot_le) ≫ (D i).pageπ 0) z=x := by
      subst m
      exact H
    exact transport _ hn ⟨z,hz⟩
  obtain ⟨z,hz⟩ := infinity_rep_of_all_finite (D i) x hx
  exact ⟨_,by omega,z,hz,rfl⟩

private theorem shifted_full_source_exists
    (X : ClassicalObject) (e s t : ℤ) (x : Ambient model X (s,t))
    (hx : x ∈ permanentCycles model X (s,t)) :
    ∃ v : ((model.family.obj ((SyntheticObject.shift (0,e) (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData (s,t,t+e-(0:ℕ))).eInfty,
      HasInfinityRepresentative _ 2 (s,t,t+e-(0:ℕ))
        (model.comparison.nuE2 X e s t 0 x) v := by
  apply synthetic_infinity_of_all_pages
  intro r hr
  lift r to ℕ using (by omega : 0 ≤ r)
  let E := model.classical.obj (X.obj model.auxiliary)
  have hxr : ReachesPage E r (s,t) x := by
    apply (isCycle_iff_reaches model X r hr (s,t) x).mp
    exact ⟨by omega,permanentCycles_le_cycles model X (s,t) (r-1) hx⟩
  obtain ⟨xr,hxr⟩ := hxr
  have hd : (s,t)+E.diffDeg r = (s+r,t+r-1) := by
    rw [model.classical.differentialDegree]
    ext
    · rfl
    · dsimp
      omega
  let yr := (E.d r (s,t)≫eqToHom (congrArg (E.Page r) hd)) xr
  obtain ⟨y,hy⟩ := FinitePageCalculus.page_has_initial_representative hr yr
  have hc : HasDifferential E r (s,t) (s+r,t+r-1) x y :=
    ⟨hd,xr,yr,hxr,hy,rfl⟩
  have hs := (KIP126.Literature.Standard.bhs_differentials X e s t r 0
    (by exact_mod_cast hr) x y).mp hc
  obtain ⟨_,xs,ys,hxs,_,_⟩ := hs
  exact ⟨xs,hxs⟩


private theorem shifted_full_first_kernel_filtration (X : ClassicalObject)
    (e s t : ℤ)
    (a : BiHom (t-s) (t+e)
      ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))))
    (ha : a ≫ XModLambdaN.incl _ 1 = 0) :
    FiltrationAtLeast model.syntheticTower (s+1) a := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let V := (SyntheticCategory.biShift (0,e)).obj A
  let T := XModLambdaN.cofiberTriangle V 1
  obtain ⟨b,hb⟩ := T.coyoneda_exact₂ (XModLambdaN.cofiberTriangle_distinguished V 1) a ha
  change BiHom (t-s) (t+e) ((SyntheticCategory.biShift (0,-(1:ℤ))).obj V) at b
  change a = b ≫ lambdaPow 1 V at hb
  let I : (SyntheticCategory.biShift (0,-(1:ℤ))).obj V ≅
      (SyntheticCategory.biShift (0,e-1)).obj A :=
    (SyntheticCategory.biShift_comp (0,e) (0,-(1:ℤ))).app A ≪≫
      eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj A)
        (by ext <;> simp [sub_eq_add_neg]))
  have hbottom := shifted_nu_bottom_filtration X (0,e-1) (t-s) (t+e) (b≫I.hom)
  have hbottom' : FiltrationAtLeast model.syntheticTower (s+1) (b≫I.hom) := by
    convert hbottom using 1; omega
  have hbf := map_preserves_filtration (model.convergentMap
    (.shift (0,e-1) (.nu X)) (.shift (0,-1) (.shift (0,e) (.nu X))) I.inv)
    (t-s,t+e) (s+1) (b≫I.hom) hbottom'
  have hbfil : FiltrationAtLeast model.syntheticTower (s+1) b := by
    change FiltrationAtLeast model.syntheticTower (s+1) ((b≫I.hom)≫I.inv) at hbf
    simpa only [FiltrationAtLeast,Category.assoc,Iso.hom_inv_id,Category.comp_id] using hbf
  have hmap := map_preserves_filtration (model.convergentMap
    (.shift (0,-1) (.shift (0,e) (.nu X))) (.shift (0,e) (.nu X)) (lambdaPow 1 V))
    (t-s,t+e) (s+1) b hbfil
  rwa [←hb] at hmap

private theorem shifted_full_source_detects_of_first_of_representative
    (X : ClassicalObject) (e s t : ℤ) (x : Ambient model X (s,t))
    (v : ((model.family.obj ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))).sequence.ssData (s,t,t+e)).eInfty)
    (hv : HasInfinityRepresentative _ 2 (s,t,t+e)
      (regradeE2 (by simp) (model.comparison.nuE2 X e s t 0 x)) v)
    (a : BiHom (t-s) (t+e)
      ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))))
    (ha : a≫XModLambdaN.incl _ 1 = (model.firstQuotient X e s t).symm x) :
    Detects (model.convergence (.shift (0,e) (.nu X))) (s,t,t+e)
      (regradeE2 (by simp) (model.comparison.nuE2 X e s t 0 x)) a := by
  let A := (SyntheticCategory.biShift (0,e)).obj
    (model.nu.functor.obj (X.obj model.auxiliary))
  let F := model.syntheticTower.filtration A
  haveI : Epi (F.toAssociatedGraded s (t-s,t+e)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s (t-s,t+e))).mp
    inferInstance (((model.convergence (.shift (0,e) (.nu X))).identification (s,t,t+e)).hom v)
  let a0 : BiHom (t-s) (t+e) A := (F.F s (t-s,t+e)).arrow ar
  have ha0 : Detects (model.convergence (.shift (0,e) (.nu X)))
      (s,t,t+e) (regradeE2 (by simp) (model.comparison.nuE2 X e s t 0 x)) a0 :=
    ⟨v,hv,ar,rfl,har.symm⟩
  have hp := detects_map (.shift (0,e) (.nu X)) (.quotient 1 (.shift (0,e) (.nu X)))
    (XModLambdaN.incl A 1) (s,t,t+e) _ _ ha0
  rw [←page_regrade] at hp
  change Detects (model.convergence (.quotient 1 (.shift (0,e) (.nu X))))
    (s,t,t+e) (regradeE2 _ (finiteNuLabel model X 1 e s t 0 x)) _ at hp
  have hfirst := shifted_finite_source_first X 1 (by decide) e s t x _ hp
  simp only [(model.quotients.tower _).rho_id,Category.comp_id] at hfirst
  have hd := shifted_full_first_kernel_filtration X e s t (a-a0) (by
    rw [Preadditive.sub_comp,ha,hfirst,sub_self])
  exact detects_of_high_difference (.shift (0,e) (.nu X)) (s,t,t+e) _ a0 a ha0 hd

private theorem positive_shift_full_first_label
    (X : ClassicalObject) (s t : ℤ) (x : Ambient model X (s,t))
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1 = firstLabel model X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    (homotopyRegrade (by simp) rfl (shiftHomotopyClass (0,1) (t-s,t) a)) ≫
      XModLambdaN.incl _ 1 = (model.firstQuotient X 1 s t).symm x := by
  letI := model.exactness.shiftCommShift (0,1)
  letI := model.exactness.shiftExact (0,1)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) 1
    (model.nu.functor.obj (X.obj model.auxiliary))
  have hpos := KIP126.AdamsSynthetic.Standard.firstQuotient_positive_shift X s t x ε hε
  rw [←first_label_inline] at hpos
  change homotopyRegrade (m' := t-s) (w' := t+1) (by simp) (by simp)
    (shiftHomotopyClass (0,1) (t-s,t)
      (firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)) ≫
      ε.inv = (model.firstQuotient X 1 s t).symm x at hpos
  rw [←ha] at hpos
  apply (cancel_mono ε.hom).mp
  rw [Category.assoc,hε,←hpos]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  simp only [shiftHomotopyClass,Functor.map_comp,Category.assoc,regrade_precomp]

private theorem shifted_full_source_detects_of_first
    (X : ClassicalObject) (e s t : ℤ) (x : Ambient model X (s,t))
    (hx : x ∈ permanentCycles model X (s,t))
    (a : BiHom (t-s) (t+e)
      ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))))
    (ha : a≫XModLambdaN.incl _ 1 = (model.firstQuotient X e s t).symm x) :
    Detects (model.convergence (.shift (0,e) (.nu X))) (s,t,t+e)
      (regradeE2 (by simp) (model.comparison.nuE2 X e s t 0 x)) a := by
  obtain ⟨v,hv⟩ := shifted_full_source_exists X e s t x hx
  have hv := representative_transport (show (s,t,t+e-(0:ℕ))=(s,t,t+e) by simp) _ _ hv
  exact shifted_full_source_detects_of_first_of_representative X e s t x _ hv a ha

private theorem positive_shift_full_source_detects
    (X : ClassicalObject) (s t : ℤ) (x : Ambient model X (s,t))
    (hx : x ∈ permanentCycles model X (s,t))
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1 = firstLabel model X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (model.convergence (.shift (0,1) (.nu X))) (s,t,t+1)
      (regradeE2 (by simp) (model.comparison.nuE2 X 1 s t 0 x))
      (homotopyRegrade (by simp) rfl (shiftHomotopyClass (0,1) (t-s,t) a)) := by
  exact shifted_full_source_detects_of_first X 1 s t x hx _
    (positive_shift_full_first_label X s t x a ha)

private def positiveNuNormalizedMap :
    (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary)) ⟶
      model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary) := by
  simpa only [KIP126.Literature.Standard.nuCofiber_nu_exponent,Nat.cast_one] using
    (model.normalizedMap (.shift 3 .sphere) .sphere model.auxiliary.nuMap).map

private theorem normalizedNu_positive_coordinates :
    normalizedNu model KIP126.Literature.Standard.nuCofiber_nu_exponent =
      positiveNuSphereThreeIso.inv ≫ positiveNuNormalizedMap ≫ model.nu.unitIso.hom := by
  have H (n : ℕ) (hn : n=1)
      (F : (SyntheticCategory.biShift (0,(n:ℤ))).obj
        (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary)) ⟶
        model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :
      (let E : (SyntheticCategory.biShift (0,(n:ℤ))).obj
          (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary)) ≅
          Smn (Syn:=SyntheticSpectrum) 3 4 := by
            rw [hn]
            exact positiveNuSphereThreeIso
       E.inv≫F≫model.nu.unitIso.hom) =
        positiveNuSphereThreeIso.inv≫
          (by simpa only [hn,Nat.cast_one,ClassicalObject.obj] using F)≫model.nu.unitIso.hom := by
    subst n
    rfl
  exact H _ KIP126.Literature.Standard.nuCofiber_nu_exponent _

private theorem h5_actual_nu_source_quotient_image
    (κ : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≅
      (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (hκ : XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1≫κ.hom =
      (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)) :
    ((shiftHomotopyClass (3,4) (31,32) h5Q1 ≫ κ.inv) ≫
      XModLambdaN.map positiveNuSphereThreeIso.inv 1) ≫
      XModLambdaN.map positiveNuNormalizedMap 1 =
      nativeFirstLabel .sphere 2 36 (KIP126.Literature.Standard.hiProduct 2 5) := by
  haveI : IsIso (XModLambdaN.map model.nu.unitIso.hom 1) := by
    change IsIso ((model.quotients.functoriality.functor 1).map model.nu.unitIso.hom)
    infer_instance
  apply (cancel_mono (XModLambdaN.map model.nu.unitIso.hom 1)).mp
  apply (KIP126.Literature.sphereFirstQuotient model 2 36).injective
  rw [sphere_native_quotient_label]
  have h := normalizedNuQ1_h5 κ hκ
  have hs : susp_invariance 31 32 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) h5Q1 =
      shiftHomotopyClass (3,4) (31,32) h5Q1 := by
    simp [susp_invariance,shiftHomotopyClass,Iso.homCongr]
  rw [hs] at h
  rw [normalizedNu_positive_coordinates,model.quotients.functoriality.map_comp,
    model.quotients.functoriality.map_comp] at h
  simpa only [Category.assoc] using h
/-- The actual full normalized-nu representatives, with their prescribed
first-quotient labels and the strict lambda relation. -/
private theorem paper6_24_full_nu_representatives :
    ∃ x : Ambient model (.shift 3 .sphere) (3,36),
      IsSphereThreeH0H4Square x ∧
      x ∈ permanentCycles model (.shift 3 .sphere) (3,36) ∧
      ∃ a : BiHom 33 37 ((SyntheticCategory.biShift (0,1)).obj
          (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary))),
      ∃ β : BiHom 33 38 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
        a≫XModLambdaN.incl _ 1 = (model.firstQuotient (.shift 3 .sphere) 1 3 36).symm x ∧
        β≫XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 5 38 h0p ∧
        a≫positiveNuNormalizedMap = lambdaMultiply 1 β := by
  obtain ⟨β0,hβ0,hβunit⟩ := base_h5_boundary
  obtain ⟨β,hβ,hδβ⟩ := target_h2h5_boundary
  obtain ⟨κ,hκ,σ,hγ⟩ := nu_degree_boundary_shift (S_0_0:SyntheticSpectrum) h5Q1
  let cunit := shiftHomotopyClass (3,4) (31,32) h5Q1≫κ.inv
  let c := cunit≫XModLambdaN.map positiveNuSphereThreeIso.inv 1
  let γ := biSuspensionHomEquiv 34 36 1 (Smn (Syn:=SyntheticSpectrum) 3 4)
    (cunit≫XModLambdaN.proj _ 1)
  let a : BiHom 33 37 ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj ((ClassicalObject.shift 3 .sphere).obj model.auxiliary))) :=
    biSuspensionHomEquiv 34 36 1 _ (c≫XModLambdaN.proj _ 1)
  have ha : a=γ≫positiveNuSphereThreeIso.inv :=
    quotient_boundary_evaluation_natural positiveNuSphereThreeIso.inv 1 34 36 cunit
  have hafirst : a≫XModLambdaN.incl _ 1=positiveTripleNuClass β0≫XModLambdaN.incl _ 1 := by
    rw [ha]
    exact geometric_boundary_source_first_quotient β0 _ hβunit γ σ hγ
  obtain ⟨x,hx,hxfirst,hxp,_⟩ := exists_triple_suspension_fixed_source β0 hβ0
  have hpos : positiveTripleNuClass β0≫XModLambdaN.incl _ 1 =
      (model.firstQuotient (.shift 3 .sphere) 1 3 36).symm x := by
    exact positive_shift_full_first_label (.shift 3 .sphere) 3 36 x
      (tripleSuspendNuClass β0) hxfirst
  refine ⟨x,hx,hxp,a,β,hafirst.trans hpos,hβ,?_⟩
  have hcimage := h5_actual_nu_source_quotient_image κ hκ
  change c≫XModLambdaN.map positiveNuNormalizedMap 1=
    nativeFirstLabel .sphere 2 36 (KIP126.Literature.Standard.hiProduct 2 5) at hcimage
  rw [←hδβ,←hcimage]
  exact (quotient_boundary_evaluation_natural positiveNuNormalizedMap 1 34 36 c).symm
private def fullDetectedPairAt (X Y : ClassicalObject) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (e : ℕ)
    (F : (SyntheticCategory.biShift (0,(e:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
        model.nu.functor.obj (Y.obj model.auxiliary)) : Prop :=
  ∃ hn : (e:ℤ) ≤ n,
    ∃ a : BiHom (t-s) (t+e) ((SyntheticCategory.biShift (0,(e:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary))),
    ∃ b : BiHom (t-s) (t+e) (model.nu.functor.obj (Y.obj model.auxiliary)),
      Detects (model.convergence (.shift (0,(e:ℤ)) (.nu X))) (s,t,t+e)
        (regradeE2 (by simp) (model.comparison.nuE2 X e s t 0 x)) a ∧
      Detects (model.convergence (.nu Y)) (s+n,t+n,t+e)
        (nuWeightLabel model Y (s+n) (t+n) (t+e) (by omega) y)
        (homotopyRegrade (by change t-s=(t+n)-(s+n); omega) rfl b) ∧ a≫F=b

private def normalizedMapInPositiveCoordinates
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (hf : normalizedExponent model.classicalTower f = 1) :
    (SyntheticCategory.biShift (0,1)).obj (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
      model.nu.functor.obj (Y.obj model.auxiliary) := by
  simpa only [hf,Nat.cast_one] using (model.normalizedMap X Y f).map

private theorem detected_pair_positive_to_actual
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (hf : normalizedExponent model.classicalTower f = 1)
    (n s t : ℤ) (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (h : fullDetectedPairAt X Y n s t x y 1 (normalizedMapInPositiveCoordinates X Y f hf)) :
    fullDetectedPairAt X Y n s t x y (normalizedExponent model.classicalTower f)
      (model.normalizedMap X Y f).map := by
  have H (e : ℕ) (he : e=1)
      (F : (SyntheticCategory.biShift (0,(e:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
          model.nu.functor.obj (Y.obj model.auxiliary)) :
      fullDetectedPairAt X Y n s t x y 1
        (by simpa only [he,Nat.cast_one] using F) →
        fullDetectedPairAt X Y n s t x y e F := by
    subst e
    exact id
  exact H _ hf (model.normalizedMap X Y f).map h

private theorem actual_detected_pair_infinite
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (n s t : ℤ) (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (hx : IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) (s,t) x)
    (hy : IsPermanentCycle (model.classical.obj (Y.obj model.auxiliary)) (s+n,t+n) y)
    (h : fullDetectedPairAt X Y n s t x y (normalizedExponent model.classicalTower f)
      (model.normalizedMap X Y f).map) : InfiniteExtension model X Y f n s t x y := by
  obtain ⟨hn,a,b,ha,hb,hab⟩ := h
  have h0 : 0 ≤ n := le_trans (by exact_mod_cast Nat.zero_le _) hn
  have hsi : (s,t,t+normalizedExponent model.classicalTower f)=
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f) := by simp
  have hti : (s+n,t+n,t+normalizedExponent model.classicalTower f)=
      (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f) := by
    ext <;> dsimp; omega
  have has := detects_transport hsi _ _ ha
  have hbt := detects_transport hti _ _ hb
  have hsource : regradeE2 hsi
      (regradeE2 (by simp) (model.comparison.nuE2 X
        (normalizedExponent model.classicalTower f) s t 0 x)) =
      infiniteSourceForExtension model X Y f s t x := by
    unfold infiniteSourceForExtension
    rw [normalized_regrade_trans]
  rw [hsource] at has
  have htarget : regradeE2 hti
      (nuWeightLabel model Y (s+n) (t+n)
        (t+normalizedExponent model.classicalTower f) (by omega) y) =
      infiniteTargetForExtension model X Y f n s t hn y := by
    exact eq_of_heq ((regradeE2_heq hti _).trans
      (infinite_target_nuWeight_heq X Y f n s t hn y).symm)
  rw [htarget] at hbt
  obtain ⟨source,target,hsourceRep,htargetRep,heq⟩ :=
    extension_equation_of_detected_pair
      (model.convergentMap (extensionSourceObject model X Y f) (.nu Y)
        (model.normalizedMap X Y f).map)
      (t-s,t+normalizedExponent model.classicalTower f) s n h0
      (infiniteSourceForExtension model X Y f s t x)
      (infiniteTargetForExtension model X Y f n s t hn y) a b
      (by convert has using 1 <;> simp only [extensionSourceObject])
      (by convert hbt using 1; simp only [normalized_homotopy_regrade_trans]) hab
  exact ⟨{
    length_lower := hn
    source_cycle := hx
    target_cycle := hy
    source := source
    target := target
    source_rep := hsourceRep
    target_rep := htargetRep
    equation := heq }⟩

private theorem positive_detected_pair_infinite
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (hf : normalizedExponent model.classicalTower f = 1)
    (n s t : ℤ) (hn : 1 ≤ n)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (hx : IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) (s,t) x)
    (hy : IsPermanentCycle (model.classical.obj (Y.obj model.auxiliary)) (s+n,t+n) y)
    (a : BiHom (t-s) (t+1) ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))))
    (b : BiHom (t-s) (t+1) (model.nu.functor.obj (Y.obj model.auxiliary)))
    (ha : Detects (model.convergence (.shift (0,1) (.nu X))) (s,t,t+1)
      (regradeE2 (by simp) (model.comparison.nuE2 X 1 s t 0 x)) a)
    (hb : Detects (model.convergence (.nu Y)) (s+n,t+n,t+1)
      (nuWeightLabel model Y (s+n) (t+n) (t+1) (by omega) y)
      (homotopyRegrade (by change t-s=(t+n)-(s+n); omega) rfl b))
    (hab : a≫normalizedMapInPositiveCoordinates X Y f hf=b) :
    InfiniteExtension model X Y f n s t x y := by
  apply actual_detected_pair_infinite X Y f n s t x y hx hy
  apply detected_pair_positive_to_actual X Y f hf n s t x y
  exact ⟨hn,a,b,ha,hb,hab⟩

/-- AimPaper 6.24, with the fixed source and archived target, obtained from
the two independent sphere differentials and actual quotient boundaries. -/
private theorem paper6_24_infinite_nu_extension : Paper6_24InfiniteNuExtensionStatement := by
  obtain ⟨x,hx,hxp,a,β,hafirst,hβ,heq⟩ := paper6_24_full_nu_representatives
  refine ⟨x,hx,?_⟩
  have has := shifted_full_source_detects_of_first (.shift 3 .sphere) 1 3 36 x hxp a hafirst
  have hβp := first_label_lift_permanent .sphere 5 38 h0p β hβ
  have hbt := nu_lambda_detects .sphere 1 (by decide) 5 38 h0p hβp β hβ
  have hp : fullDetectedPairAt (.shift 3 .sphere) .sphere 2 3 36 x h0p 1
      (normalizedMapInPositiveCoordinates (.shift 3 .sphere) .sphere
        model.auxiliary.nuMap KIP126.Literature.Standard.nuCofiber_nu_exponent) := by
    refine ⟨by decide,a,lambdaMultiply 1 β,?_,?_,?_⟩
    · simpa using has
    · simpa [homotopyRegrade] using hbt
    · exact heq
  exact actual_detected_pair_infinite (.shift 3 .sphere) .sphere model.auxiliary.nuMap
    2 3 36 x h0p (permanent_cycle_of_member (.shift 3 .sphere) (3,36) x hxp)
    (permanent_cycle_of_member .sphere (5,38) h0p hβp)
    (detected_pair_positive_to_actual (.shift 3 .sphere) .sphere model.auxiliary.nuMap
      KIP126.Literature.Standard.nuCofiber_nu_exponent 2 3 36 x h0p hp)

/-- Restriction of the same full representatives gives the E3 finite
extension of AimPaper 6.19. -/
private theorem paper6_19_finite_nu_extension : Paper6_19FiniteNuExtensionStatement := by
  obtain ⟨x,hx,hfull⟩ := paper6_24_infinite_nu_extension
  have hfinite := finiteExtension_of_infinite (.shift 3 .sphere) .sphere
    model.auxiliary.nuMap 3 2 3 36 x h0p (by decide)
    (by rw [KIP126.Literature.Standard.nuCofiber_nu_exponent]; norm_num) hfull
  obtain ⟨W⟩ := hfinite
  exact ⟨x,hx,W.source_cycle,⟨W⟩⟩

end
end KIP126.ProofTools.Paper.NuNumericalExtensions
end
