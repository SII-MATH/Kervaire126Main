module
import all KIP126.ProofTools.Paper.NumericalExamples
import all KIP126.ProofTools.Paper.NuNumericalExtensions
import all KIP126.ProofTools.GeneralizedLeibniz.Square
import all KIP126.ProofTools.GeneralizedLeibniz.MinimalBottom
import all KIP126.ProofTools.GeneralizedMahowald.ShortSource
import all KIP126.ProofTools.MahowaldLeibniz.FixedModel
import all KIP126.ProofTools.GeneralizedMahowald.RotatedNuTriangle
import KIP126.Literature.Standard.QuotientAlgebra
import KIP126.Literature.Standard.Filtration

/-! Numerical multiplication-by-two relations on the actual Standard model.
All declarations are private. A zero extension means a zero associated grade
of the full image; it does not strengthen that condition to a strictly zero
homotopy image. -/
@[expose] section
namespace KIP126.ProofTools.Paper.DoublingNumericalExtensions
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.AdamsSynthetic.Standard (model Spectrum SyntheticSpectrum)
open KIP126.Computation KIP126.Computation.Standard
open KIP126.ProofTools.Paper.NumericalExamples
open KIP126.ProofTools.Paper.NuNumericalExtensions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
private theorem sphere_quotient_high_filtration_zero (q : ℕ) (hq : 0 < q)
    (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
    (a : BiHom m w (XModLambdaN (S_0_0 : SyntheticSpectrum) q))
    (ha : FiltrationAtLeast model.syntheticTower s a) : a = 0 := by
  let g : XModLambdaN (S_0_0 : SyntheticSpectrum) q ⟶ XModLambdaN (model.nu.functor.obj SphereSpectrum) q :=
    XModLambdaN.map model.nu.unitIso.inv q
  let f : XModLambdaN (model.nu.functor.obj SphereSpectrum) q ⟶ XModLambdaN (S_0_0 : SyntheticSpectrum) q :=
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
    (unique:∀u v:BiHom 15 16 (XModLambdaN (S_0_0:SyntheticSpectrum) 1),u≠0→v≠0→u=v)
    (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1≫κ.hom=
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1))
    (ν:BiHom 0 1 (S_0_0:SyntheticSpectrum))
    (x:BiHom 15 16 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hx:x≠0) :
    sphereAction ν x=(susp_invariance 15 16 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫
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
      ∃e:(SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
          Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1,
        (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)≫e.hom=
          (ρ_ (Smn (Syn:=SyntheticSpectrum) 0 1)).inv≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1) := by
    obtain ⟨e,he⟩:=extend_unit_iso (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)
      ⟨unit_restriction_injective,unit_restriction_surjective ⟩
      (SyntheticCategory.biShift (0,1)) (tensorLeft (Smn (Syn:=SyntheticSpectrum) 0 1))
      (SyntheticCategory.biShift_fullyFaithful (0,1)) (tensorLeft_sphere_fullyFaithful 0 1)
      (ρ_ (Smn (Syn:=SyntheticSpectrum) 0 1)).symm (biShift_eq_tensor_Smn 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    refine ⟨e,?_⟩
    simpa only [Iso.symm_hom,tensorLeft,curriedTensor_obj_map,id_tensorHom] using he
  have q1_scalar_boundary_zero
      (z : BiHom 1 0 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) : z=0 := by
    apply sphere_quotient_high_filtration_zero 1 (by decide) 1 0 0 (by decide) z
    exact filtration_zero z
  have q1_sphere_inclusion_hom_injective :
      Function.Injective (fun f : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ⟶
        XModLambdaN (S_0_0:SyntheticSpectrum) 1 => XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ f) := by
    intro f g hfg
    change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ f =
      XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ g at hfg
    let T := XModLambdaN.cofiberTriangle (Smn (Syn:=SyntheticSpectrum) 0 1) 1
    have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
    have hz : T.mor₂ ≫ (f-g)=0 := by
      change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ (f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩ := T.yoneda_exact₃ hT (f-g) hz
    let e : T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 1 0 :=
      (biSuspensionIso 1 (Smn (Syn:=SyntheticSpectrum) 0 1)).symm ≪≫
        (SyntheticCategory.biShift_comp (0,1) (1,-1)).app (S_0_0:SyntheticSpectrum)
    have he := q1_scalar_boundary_zero (e.inv ≫ δ)
    have hd : δ=0 := by
      apply (cancel_epi e.inv).mp
      simpa only [comp_zero] using he
    apply sub_eq_zero.mp
    simpa only [hd, comp_zero] using hδ
  have q1_tensor_source_square

      (unique:∀u v:BiHom 15 16 (XModLambdaN (S_0_0:SyntheticSpectrum) 1),u≠0→v≠0→u=v)
      (e:(SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
        Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1)
      (d:Smn (Syn:=SyntheticSpectrum) 15 17 ≅ Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ Smn (Syn:=SyntheticSpectrum) 15 16)
      (x:BiHom 15 16 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hx:x≠0) :
      d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ x)=
        (susp_invariance 15 16 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫e.hom := by
    let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1)
    let T:=tensorLeft (Smn (Syn:=SyntheticSpectrum) 0 1)
    letI:=KIP126.AdamsSynthetic.Standard.graded_shiftAdditive (0,1)
    letI:=Standard.mayData.leftShift (Smn (Syn:=SyntheticSpectrum) 0 1)
    letI:=Standard.mayData.leftExact (Smn (Syn:=SyntheticSpectrum) 0 1)
    letI:T.Faithful:=tensorLeft_sphere_faithful 0 1
    let ff:=SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,1)
    let c: F.obj (Smn (Syn:=SyntheticSpectrum) 15 16) ≅ Smn (Syn:=SyntheticSpectrum) 15 17 :=
      (SyntheticCategory.biShift_comp (15,16) (0,1)).app (S_0_0:SyntheticSpectrum)
    let z:BiHom 15 16 (XModLambdaN (S_0_0:SyntheticSpectrum) 1):=
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
    change d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ x)=_
    dsimp only [susp_invariance]
    simp only [Equiv.trans_apply,Functor.FullyFaithful.homEquiv_apply,
      Iso.homCongr_apply,Iso.refl_hom,Category.comp_id]
    simpa only [c,F,T,tensorLeft,curriedTensor_obj_map,id_tensorHom,Category.assoc] using heq.symm
  have q1_algebra_filler

      (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≅
        (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
      (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1≫κ.hom=
        (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)) :
      ∃e:(SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
          Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1,
        letI:=Standard.quotientSyntheticSymmetric
        ∀ν:BiHom 0 1 (S_0_0:SyntheticSpectrum),
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
    rw [←Category.assoc (𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1),
      tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
    rw [←Standard.quotientAlgebra_unit 1 (by decide)]
    have hm:=Mathlib.Tactic.MonTauto.rightUnitor_inv_tensor_one_mul (quotientClass 1 ν)
    change (ρ_ (Smn (Syn:=SyntheticSpectrum) 0 1)).inv≫(quotientClass 1 ν ⊗ₘ MonObj.one)≫MonObj.mul=quotientClass 1 ν at hm
    rw [hm]
    exact XModLambdaN.incl_naturality ν 1
  letI:=Standard.quotientSyntheticSymmetric
  let Q:=Standard.quotientAlgebra 1 (by decide)
  letI:=Q
  letI:=Standard.quotientAlgebra_commutative 1 (by decide)
  obtain ⟨e,he⟩:=q1_algebra_filler  κ hκ
  let d:Smn (Syn:=SyntheticSpectrum) 15 17 ≅ Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ Smn (Syn:=SyntheticSpectrum) 15 16 :=
    ((SyntheticCategory.biShift_comp (0,1) (15,16)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
      biShift_eq_tensor_Smn 15 16 (Smn (Syn:=SyntheticSpectrum) 0 1) ≪≫ β_ (Smn (Syn:=SyntheticSpectrum) 15 16) (Smn (Syn:=SyntheticSpectrum) 0 1)
  have ht:=q1_tensor_source_square  unique e d x hx
  have hc:=IsCommMonObj.mul_comm (XModLambdaN (S_0_0:SyntheticSpectrum) 1)
  change (β_ (XModLambdaN (S_0_0:SyntheticSpectrum) 1) (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).hom≫Q.mul=Q.mul at hc
  have hb:(x ⊗ₘ quotientClass 1 ν)≫Q.mul=
      (β_ (Smn (Syn:=SyntheticSpectrum) 15 16) (Smn (Syn:=SyntheticSpectrum) 0 1)).hom≫
        (quotientClass 1 ν ⊗ₘ x)≫Q.mul := by
    rw [←hc,←Category.assoc,BraidedCategory.braiding_naturality,Category.assoc]
    simp only [hc]
  have hf:(quotientClass 1 ν ⊗ₘ x)=
      (𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ x)≫(quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) := by
    rw [tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
  rw [←Standard.quotientAlgebra_sphere_action 1 (by decide) 0 1 15 16 ν x]
  change Standard.quotientAlgebraProduct Q (quotientClass 1 ν) x=_
  calc
    _=d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ x)≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul := by
      dsimp only [Standard.quotientAlgebraProduct,d,Iso.trans_hom,Iso.symm_hom]
      rw [hb,hf]
      simp only [Category.assoc]
      rfl
    _=(susp_invariance 15 16 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫e.hom≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul := by
      simpa only [Category.assoc] using congrArg (fun z=>z≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul) ht
    _=_ := by
      rw [←he ν]
      simp only [Iso.inv_hom_id_assoc]


private theorem archive_zero (s t : ℕ) (ht : t ≤ 261)
    (hc : archive.basisCount s t = 0)
    (x : model.classical.sphere.Page 2 (s,t)) : x=0 := by
  let e := coordinates s t ht
  haveI : Subsingleton (Fin (archive.basisCount s t) →₀ ZMod 2) := by
    rw [hc]
    infer_instance
  apply e.injective
  exact Subsingleton.elim _ _

private theorem stem13_e2_zero (s : ℤ) (hs : 6 ≤ s)
    (x : model.classical.sphere.Page 2 (s,s+13)) : x=0 := by
  by_cases h9 : 9 ≤ s
  · haveI := KIP126.Literature.Standard.sphereVanishing s (s+13) (by omega) (by omega)
    exact Subsingleton.elim _ _
  · have hh : s=6 ∨ s=7 ∨ s=8 := by omega
    rcases hh with rfl | rfl | rfl
    · exact archive_zero 6 19 (by decide) (by decide) x
    · exact archive_zero 7 20 (by decide) (by decide) x
    · exact archive_zero 8 21 (by decide) (by decide) x

private theorem stem13_page_zero (s r : ℤ) (hs : 6 ≤ s) (hr : 2 ≤ r)
    (x : model.classical.sphere.Page r (s,s+13)) : x=0 := by
  obtain ⟨x2,hx⟩ := page_has_initial_representative hr x
  have hz := stem13_e2_zero s hs x2
  rw [hz] at hx
  exact hx.unique (RepresentsOnPage.zero hr)

private theorem d0_all_outgoing_zero (r : ℤ) (hr : 2 ≤ r) :
    model.classical.sphere.d r (4,18)=0 := by
  have hd : (4,18)+model.classical.sphere.diffDeg r = (4+r,4+r+13) := by
    rw [model.classical.differentialDegree]
    ext <;> dsimp <;> omega
  haveI : Subsingleton (model.classical.sphere.Page r ((4,18)+model.classical.sphere.diffDeg r)) := by
    rw [hd]
    exact ⟨fun x y => (stem13_page_zero (4+r) r (by omega) hr x).trans
      (stem13_page_zero (4+r) r (by omega) hr y).symm⟩
  ext x
  exact Subsingleton.elim _ _

/-- Every actual E2 label in d0's degree is a permanent-cycle label.
No source normalization or multiplicative extension is asserted. -/
private theorem every_d0_degree_label_permanent
    (x : model.classical.sphere.Page 2 (4,18)) :
    IsPermanentCycle model.classical.sphere (4,18) x := by
  apply isPermanentCycle_of_reachesPage model.classical.sphere 2
    (by rw [model.classical.firstPage]) (4,18) x
    ⟨x,RepresentsOnPage.self_two x⟩
  exact d0_all_outgoing_zero

private def twoMap : SphereSpectrum (C := Spectrum) ⟶ SphereSpectrum := 2 • 𝟙 _

private theorem twoMap_exponent : normalizedExponent model.classicalTower twoMap = 1 := by
  let T := model.classicalTower.tower (SphereSpectrum (C := Spectrum))
  obtain ⟨_, _, b, hb, _⟩ := KIP126.Literature.Standard.two_detection
  have hm : KIP126.Literature.classicalTwo (C := Spectrum) ∈ T.filtrationSubmodule 1 0 := by
    have h : KIP126.Literature.classicalTwo (C := Spectrum) ∈
        ModuleCat.subobjectModule _ (T.filtration.F 1 0) := ⟨b, hb⟩
    simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using h
  obtain ⟨a,ha⟩ := hm
  change a ≫ T.projection 1 = KIP126.Literature.classicalTwo (C := Spectrum) at ha
  have hf : MapFiltrationAtLeast model.classicalTower twoMap 1 := by
    refine ⟨(shiftFunctorZero Spectrum ℤ).inv.app SphereSpectrum ≫ a, ?_⟩
    change ((shiftFunctorZero Spectrum ℤ).inv.app SphereSpectrum ≫ a) ≫ T.projection 1 = twoMap
    rw [Category.assoc,ha]
    dsimp only [KIP126.Literature.classicalTwo,twoMap]
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    rfl
  simp only [normalizedExponent,hf,ite_true]


set_option backward.defeqAttrib.useBackward false

private theorem h0_positive_factorization :
    lambdaToPositivePow 1 (S_0_0 : SyntheticSpectrum) ≫
      KIP126.Literature.Standard.syntheticH0 = 2 • 𝟙 _ := by
  have h := congrArg (fun z => SyntheticCategory.biShift_zero.inv.app
    (S_0_0 : SyntheticSpectrum) ≫ z) KIP126.Literature.Standard.toda_lambda_h0
  change (SyntheticCategory.biShift_zero.inv.app (S_0_0 : SyntheticSpectrum) ≫
    lambdaMultiply 1 KIP126.Literature.Standard.syntheticH0) = _ at h
  simp only [lambdaToPositivePow,lambdaMultiply,Route.syntheticTwo,
    eqToHom_refl,Category.id_comp,Category.assoc,Iso.inv_hom_id_app_assoc,
    Smn,S_0_0,Functor.id_obj] at h ⊢
  norm_num only at h ⊢
  exact h

private def h0NormalizedMap :
    (SyntheticCategory.biShift (0,1)).obj (model.nu.functor.obj
      (SphereSpectrum (C := Spectrum))) ⟶ model.nu.functor.obj SphereSpectrum :=
  (SyntheticCategory.biShift (0,1)).map model.nu.unitIso.hom ≫
    KIP126.Literature.Standard.syntheticH0 ≫ model.nu.unitIso.inv

private def positiveLambdaSourceIso (k : ℕ) :
    (𝟭 SyntheticSpectrum) ≅ SyntheticCategory.biShift (0,(k:ℤ)) ⋙
      SyntheticCategory.biShift (0,-(k:ℤ)) :=
  SyntheticCategory.biShift_zero.symm ≪≫
    eqToIso (congrArg SyntheticCategory.biShift
      (show ((0:ℤ),(0:ℤ)) = (0,(k:ℤ))+(0,-(k:ℤ)) by ext <;> simp)) ≪≫
    (SyntheticCategory.biShift_comp (0,(k:ℤ)) (0,-(k:ℤ))).symm

private theorem positiveLambdaNaturality (k : ℕ) {A B : SyntheticSpectrum} (f : A ⟶ B) :
    lambdaToPositivePow k A ≫ (SyntheticCategory.biShift (0,(k:ℤ))).map f =
      f ≫ lambdaToPositivePow k B := by
  have factor (A : SyntheticSpectrum) : lambdaToPositivePow k A =
      (positiveLambdaSourceIso k).hom.app A ≫
        lambdaPow k ((SyntheticCategory.biShift (0,(k:ℤ))).obj A) := by
    simp only [positiveLambdaSourceIso,lambdaToPositivePow,Iso.trans_hom,
      Iso.symm_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,Category.assoc]
  rw [factor,factor,Category.assoc,←lambdaPow_naturality]
  have hn := (positiveLambdaSourceIso k).hom.naturality f
  dsimp only [Functor.id_map,Functor.comp_map] at hn
  simpa only [Category.assoc] using (congrArg (fun z => z ≫
    lambdaPow k ((SyntheticCategory.biShift (0,(k:ℤ))).obj B)) hn).symm

private theorem h0NormalizedMap_factorization :
    lambdaToPositivePow 1 (model.nu.functor.obj (SphereSpectrum (C := Spectrum))) ≫
      h0NormalizedMap = model.nu.functor.map twoMap := by
  letI := model.nu.additive
  have hn := positiveLambdaNaturality 1 model.nu.unitIso.hom
  have hf := congrArg (fun z => z ≫ KIP126.Literature.Standard.syntheticH0 ≫
    model.nu.unitIso.inv) hn
  change lambdaToPositivePow 1 (model.nu.functor.obj (SphereSpectrum (C := Spectrum))) ≫
    h0NormalizedMap = _
  calc
    _ = model.nu.unitIso.hom ≫ lambdaToPositivePow 1
        (S_0_0 : SyntheticSpectrum) ≫ KIP126.Literature.Standard.syntheticH0 ≫
          model.nu.unitIso.inv := by
      simp only [h0NormalizedMap,Category.assoc,S_0_0,Smn,SphereSpectrum,Functor.id_obj] at hf ⊢
      norm_num only at hf ⊢
      exact hf
    _ = model.nu.unitIso.hom ≫ (2 • 𝟙 (S_0_0 : SyntheticSpectrum)) ≫
        model.nu.unitIso.inv := by
      simpa only [Category.assoc] using congrArg (fun z => model.nu.unitIso.hom ≫ z ≫ model.nu.unitIso.inv)
        h0_positive_factorization
    _ = _ := by
      simp only [twoMap,two_smul,Functor.map_add,Functor.map_id,
        Preadditive.comp_add,Preadditive.add_comp,Category.id_comp,Category.comp_id,
        Iso.hom_inv_id,S_0_0]
      rw [model.nu.functor.map_id]


private def selectedTwoNormalized :
    (SyntheticCategory.biShift (0,1)).obj (model.nu.functor.obj
      (SphereSpectrum (C := Spectrum))) ⟶ model.nu.functor.obj SphereSpectrum :=
  eqToHom (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (model.nu.functor.obj (SphereSpectrum (C := Spectrum)))) twoMap_exponent.symm) ≫
      (model.normalizedMap .sphere .sphere twoMap).map

private theorem selectedTwoNormalized_factorization :
    lambdaToPositivePow 1 (model.nu.functor.obj (SphereSpectrum (C := Spectrum))) ≫
      selectedTwoNormalized = model.nu.functor.map twoMap := by
  have transport (e : ℕ) (he : e=1)
      (F : (SyntheticCategory.biShift (0,(e:ℤ))).obj
        (model.nu.functor.obj (SphereSpectrum (C := Spectrum))) ⟶ model.nu.functor.obj SphereSpectrum)
      (hF : lambdaToPositivePow e _ ≫ F = model.nu.functor.map twoMap) :
      lambdaToPositivePow 1 _ ≫
        (eqToHom (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
          (model.nu.functor.obj (SphereSpectrum (C := Spectrum)))) he.symm) ≫ F) =
          model.nu.functor.map twoMap := by
    subst e
    simpa only [eqToHom_refl,Category.id_comp] using hF
  exact transport _ twoMap_exponent _ (model.normalizedMap .sphere .sphere twoMap).factorization

/-- At this sphere source, division by one lambda is unique.  The proof
uses the actual first-quotient vanishing in negative Adams filtration. -/
private theorem positiveLambda_one_unique
    (f g : (SyntheticCategory.biShift (0,1)).obj (model.nu.functor.obj
      (SphereSpectrum (C := Spectrum))) ⟶ model.nu.functor.obj SphereSpectrum)
    (h : lambdaToPositivePow 1 _ ≫ f = lambdaToPositivePow 1 _ ≫ g) : f=g := by
  let U := model.nu.functor.obj (SphereSpectrum (C := Spectrum))
  let a := negativeLift 1 f - negativeLift 1 g
  have ha : a ≫ lambdaPow 1 U = 0 := by
    dsimp only [a]
    rw [Preadditive.sub_comp,negative_lift_factorization,negative_lift_factorization,h,sub_self]
  let z : Smn (Syn := SyntheticSpectrum) 0 0 ⟶
      (SyntheticCategory.biShift (0,-1)).obj U :=
    SyntheticCategory.biShift_zero.hom.app (S_0_0 : SyntheticSpectrum) ≫ model.nu.unitIso.inv ≫ a
  have hz : z=0 := lambda_one_injective_at_diagonal .sphere 0 0 (by decide) z (by
    rw [←lambdaPow_one model.quotients.coherence]
    change (_ ≫ _ ≫ a) ≫ lambdaPow 1 U=0
    rw [Category.assoc,Category.assoc,ha,comp_zero,comp_zero])
  have ha0 : a=0 := by
    apply (cancel_epi model.nu.unitIso.inv).mp
    apply (cancel_epi (SyntheticCategory.biShift_zero.hom.app (S_0_0 : SyntheticSpectrum))).mp
    simpa only [z,comp_zero] using hz
  have hn : negativeLift 1 f=negativeLift 1 g := sub_eq_zero.mp ha0
  have hp : (positiveLambdaSourceIso 1).hom.app U ≫
      (SyntheticCategory.biShift (0,-(1:ℤ))).map f =
    (positiveLambdaSourceIso 1).hom.app U ≫
      (SyntheticCategory.biShift (0,-(1:ℤ))).map g := by
    simp only [positiveLambdaSourceIso,negativeLift,Iso.trans_hom,Iso.symm_hom,
      NatTrans.comp_app,eqToIso.hom,eqToHom_app,Category.assoc,U,Functor.id_obj] at hn ⊢
    norm_num only at hn ⊢
    exact hn
  apply (SyntheticCategory.biShift_fullyFaithful (Syn := SyntheticSpectrum) (0,-(1:ℤ))).map_injective
  exact (cancel_epi ((positiveLambdaSourceIso 1).hom.app U)).mp hp

private theorem selectedTwoNormalized_eq_h0 : selectedTwoNormalized = h0NormalizedMap :=
  positiveLambda_one_unique _ _
    (selectedTwoNormalized_factorization.trans h0NormalizedMap_factorization.symm)


set_option backward.defeqAttrib.useBackward true

private theorem q1_d0_action_actual_map
    (unique:∀u v:BiHom 14 18 (XModLambdaN (S_0_0:SyntheticSpectrum) 1),u≠0→v≠0→u=v)
    (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1≫κ.hom=
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1))
    (ν:BiHom 0 1 (S_0_0:SyntheticSpectrum))
    (x:BiHom 14 18 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hx:x≠0) :
    sphereAction ν x=(susp_invariance 14 18 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫
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
      ∃e:(SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
          Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1,
        (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)≫e.hom=
          (ρ_ (Smn (Syn:=SyntheticSpectrum) 0 1)).inv≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1) := by
    obtain ⟨e,he⟩:=extend_unit_iso (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)
      ⟨unit_restriction_injective,unit_restriction_surjective ⟩
      (SyntheticCategory.biShift (0,1)) (tensorLeft (Smn (Syn:=SyntheticSpectrum) 0 1))
      (SyntheticCategory.biShift_fullyFaithful (0,1)) (tensorLeft_sphere_fullyFaithful 0 1)
      (ρ_ (Smn (Syn:=SyntheticSpectrum) 0 1)).symm (biShift_eq_tensor_Smn 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    refine ⟨e,?_⟩
    simpa only [Iso.symm_hom,tensorLeft,curriedTensor_obj_map,id_tensorHom] using he
  have q1_scalar_boundary_zero
      (z : BiHom 1 0 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) : z=0 := by
    apply sphere_quotient_high_filtration_zero 1 (by decide) 1 0 0 (by decide) z
    exact filtration_zero z
  have q1_sphere_inclusion_hom_injective :
      Function.Injective (fun f : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ⟶
        XModLambdaN (S_0_0:SyntheticSpectrum) 1 => XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ f) := by
    intro f g hfg
    change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ f =
      XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ g at hfg
    let T := XModLambdaN.cofiberTriangle (Smn (Syn:=SyntheticSpectrum) 0 1) 1
    have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
    have hz : T.mor₂ ≫ (f-g)=0 := by
      change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ (f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩ := T.yoneda_exact₃ hT (f-g) hz
    let e : T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 1 0 :=
      (biSuspensionIso 1 (Smn (Syn:=SyntheticSpectrum) 0 1)).symm ≪≫
        (SyntheticCategory.biShift_comp (0,1) (1,-1)).app (S_0_0:SyntheticSpectrum)
    have he := q1_scalar_boundary_zero (e.inv ≫ δ)
    have hd : δ=0 := by
      apply (cancel_epi e.inv).mp
      simpa only [comp_zero] using he
    apply sub_eq_zero.mp
    simpa only [hd, comp_zero] using hδ
  have q1_tensor_source_square

      (unique:∀u v:BiHom 14 18 (XModLambdaN (S_0_0:SyntheticSpectrum) 1),u≠0→v≠0→u=v)
      (e:(SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
        Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1)
      (d:Smn (Syn:=SyntheticSpectrum) 14 19 ≅ Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ Smn (Syn:=SyntheticSpectrum) 14 18)
      (x:BiHom 14 18 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hx:x≠0) :
      d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ x)=
        (susp_invariance 14 18 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫e.hom := by
    let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,1)
    let T:=tensorLeft (Smn (Syn:=SyntheticSpectrum) 0 1)
    letI:=KIP126.AdamsSynthetic.Standard.graded_shiftAdditive (0,1)
    letI:=Standard.mayData.leftShift (Smn (Syn:=SyntheticSpectrum) 0 1)
    letI:=Standard.mayData.leftExact (Smn (Syn:=SyntheticSpectrum) 0 1)
    letI:T.Faithful:=tensorLeft_sphere_faithful 0 1
    let ff:=SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,1)
    let c: F.obj (Smn (Syn:=SyntheticSpectrum) 14 18) ≅ Smn (Syn:=SyntheticSpectrum) 14 19 :=
      (SyntheticCategory.biShift_comp (14,18) (0,1)).app (S_0_0:SyntheticSpectrum)
    let z:BiHom 14 18 (XModLambdaN (S_0_0:SyntheticSpectrum) 1):=
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
    change d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ x)=_
    dsimp only [susp_invariance]
    simp only [Equiv.trans_apply,Functor.FullyFaithful.homEquiv_apply,
      Iso.homCongr_apply,Iso.refl_hom,Category.comp_id]
    simpa only [c,F,T,tensorLeft,curriedTensor_obj_map,id_tensorHom,Category.assoc] using heq.symm
  have q1_algebra_filler

      (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≅
        (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
      (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1≫κ.hom=
        (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)) :
      ∃e:(SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
          Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1,
        letI:=Standard.quotientSyntheticSymmetric
        ∀ν:BiHom 0 1 (S_0_0:SyntheticSpectrum),
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
    rw [←Category.assoc (𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1),
      tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
    rw [←Standard.quotientAlgebra_unit 1 (by decide)]
    have hm:=Mathlib.Tactic.MonTauto.rightUnitor_inv_tensor_one_mul (quotientClass 1 ν)
    change (ρ_ (Smn (Syn:=SyntheticSpectrum) 0 1)).inv≫(quotientClass 1 ν ⊗ₘ MonObj.one)≫MonObj.mul=quotientClass 1 ν at hm
    rw [hm]
    exact XModLambdaN.incl_naturality ν 1
  letI:=Standard.quotientSyntheticSymmetric
  let Q:=Standard.quotientAlgebra 1 (by decide)
  letI:=Q
  letI:=Standard.quotientAlgebra_commutative 1 (by decide)
  obtain ⟨e,he⟩:=q1_algebra_filler  κ hκ
  let d:Smn (Syn:=SyntheticSpectrum) 14 19 ≅ Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ Smn (Syn:=SyntheticSpectrum) 14 18 :=
    ((SyntheticCategory.biShift_comp (0,1) (14,18)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
      biShift_eq_tensor_Smn 14 18 (Smn (Syn:=SyntheticSpectrum) 0 1) ≪≫ β_ (Smn (Syn:=SyntheticSpectrum) 14 18) (Smn (Syn:=SyntheticSpectrum) 0 1)
  have ht:=q1_tensor_source_square  unique e d x hx
  have hc:=IsCommMonObj.mul_comm (XModLambdaN (S_0_0:SyntheticSpectrum) 1)
  change (β_ (XModLambdaN (S_0_0:SyntheticSpectrum) 1) (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).hom≫Q.mul=Q.mul at hc
  have hb:(x ⊗ₘ quotientClass 1 ν)≫Q.mul=
      (β_ (Smn (Syn:=SyntheticSpectrum) 14 18) (Smn (Syn:=SyntheticSpectrum) 0 1)).hom≫
        (quotientClass 1 ν ⊗ₘ x)≫Q.mul := by
    rw [←hc,←Category.assoc,BraidedCategory.braiding_naturality,Category.assoc]
    simp only [hc]
  have hf:(quotientClass 1 ν ⊗ₘ x)=
      (𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ x)≫(quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) := by
    rw [tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
  rw [←Standard.quotientAlgebra_sphere_action 1 (by decide) 0 1 14 18 ν x]
  change Standard.quotientAlgebraProduct Q (quotientClass 1 ν) x=_
  calc
    _=d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ x)≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul := by
      dsimp only [Standard.quotientAlgebraProduct,d,Iso.trans_hom,Iso.symm_hom]
      rw [hb,hf]
      simp only [d,Iso.trans_hom,Iso.symm_hom,Iso.app_inv,Category.assoc]
    _=(susp_invariance 14 18 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫e.hom≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul := by
      simpa only [Category.assoc] using congrArg (fun z=>z≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul) ht
    _=_ := by
      rw [←he ν]
      simp only [Iso.inv_hom_id_assoc]



set_option backward.defeqAttrib.useBackward true

private def h4Q1 : BiHom 15 16 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1) :=
  (KIP126.Literature.sphereFirstQuotient model 1 16).symm h4

private theorem h4Q1_ne_zero : h4Q1 ≠ 0 := by
  obtain ⟨x,hx,hne⟩ := (KIP126.Literature.Standard.adamsOneLine_d2 4 (by decide)).source_survives
  have h4ne : h4 ≠ 0 := by
    intro hz
    apply hne
    rw [←hx.eq_on_page_two]
    exact hz
  intro hz
  apply h4ne
  have h := congrArg (KIP126.Literature.sphereFirstQuotient model 1 16) hz
  simpa only [h4Q1,LinearEquiv.apply_symm_apply,map_zero] using h

private theorem h4Q1_unique
    (u v : BiHom 15 16 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1))
    (hu : u≠0) (hv : v≠0) : u=v := by
  let d : model.classical.sphere.Page 2 (1,16) ≃ₗ[ℤ] (Fin 1 →₀ ZMod 2) :=
    coordinates 1 16 (by decide)
  let e := (KIP126.Literature.sphereFirstQuotient model 1 16).trans d
  have he (z : BiHom 15 16 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1))
      (hz : z≠0) : e z=Finsupp.single 0 1 := by
    rcases NumericalExamples.one_coordinate_cases (e z) with h | h
    · exact False.elim (hz (e.injective (h.trans (map_zero e).symm)))
    · exact h
  exact e.injective ((he u hu).trans (he v hv).symm)

private theorem h0Q1_h4
    (κ : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (hκ : XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1≫κ.hom=
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)) :
    KIP126.Literature.sphereFirstQuotient model 2 17
      ((susp_invariance 15 16 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) h4Q1)≫
        κ.inv≫XModLambdaN.map KIP126.Literature.Standard.syntheticH0 1) =
      KIP126.Literature.Standard.hiProduct 0 4 := by
  rw [←q1_sphere_action_actual_map h4Q1_unique κ hκ _ h4Q1 h4Q1_ne_zero]
  have h := KIP126.Literature.Standard.first_quotient_action 1 1 1 16
    KIP126.Literature.Standard.syntheticH0 h4Q1
  change KIP126.Literature.sphereFirstQuotient model 2 17
      (sphereAction KIP126.Literature.Standard.syntheticH0 h4Q1) =
    model.sphereAlgebra.product (1,1) (1,16)
      (KIP126.Literature.sphereFirstQuotient model 1 1
        (quotientClass 1 KIP126.Literature.Standard.syntheticH0))
      (KIP126.Literature.sphereFirstQuotient model 1 16 h4Q1) at h
  erw [KIP126.Literature.Standard.toda_h0_label] at h
  change _ = model.sphereAlgebra.product (1,1) (1,16)
    (model.standardClasses.standardHi 0) (model.standardClasses.standardHi 4)
  simpa only [h4Q1,LinearEquiv.apply_symm_apply,KIP126.Computation.Standard.h4] using h

private theorem paper_d2_h4 : HasDifferential model.classical.sphere 2
    (1,16) (3,17) h4 h0h3Square :=
  (KIP126.Literature.Standard.adamsOneLine_d2 4 (by decide)).toHasDifferential

private theorem two_degree_boundary_shift
    (A : SyntheticSpectrum)
    (x : BiHom 15 16 (XModLambdaN A 1)) :
    ∃ κ : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj A) 1 ≅
        (SyntheticCategory.biShift (0,1)).obj (XModLambdaN A 1),
      XModLambdaN.incl _ 1≫κ.hom =
        (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl A 1) ∧
      ∃ u : Smn (Syn:=SyntheticSpectrum) 14 17 ≅ Smn 14 17,
        biSuspensionHomEquiv 15 17 1 ((SyntheticCategory.biShift (0,1)).obj A)
          ((shiftHomotopyClass (0,1) (15,16) x≫κ.inv)≫XModLambdaN.proj _ 1) =
        shiftHomotopyClass (0,1) (14,17)
          (u.hom≫biSuspensionHomEquiv 15 16 1 A (x≫XModLambdaN.proj A 1)) := by
  obtain ⟨κ,hκ,hδ⟩ := quotient_boundary_shift_any_exists A (0,1) 1
  refine ⟨κ,hκ,?_⟩
  let β : BiHom 14 17 A := biSuspensionHomEquiv 15 16 1 A (x≫XModLambdaN.proj A 1)
  have hx : x≫absoluteBoundary A 1=shiftHomotopyClass (1,-1) (14,17) β := by
    simpa [β,homotopyRegrade] using absolute_boundary_class_shift A 1 15 16 x
  obtain ⟨u,hu⟩ := double_shift_comparison_sphere (1,-1) (0,1) (14,17)
    (boundaryShiftNatIsoAny (0,1) 1) A β
  refine ⟨u,?_⟩
  let c := shiftHomotopyClass (0,1) (15,16) x≫κ.inv
  have hboundary : c≫absoluteBoundary ((SyntheticCategory.biShift (0,1)).obj A) 1 =
      shiftHomotopyClass (1,-1) (14,18)
        (shiftHomotopyClass (0,1) (14,17) (u.hom≫β)) := by
    rw [←hδ]
    dsimp only [c]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
    have hh := congrArg (fun z => z≫(boundaryShiftNatIsoAny (0,1) 1).hom.app A)
      (shift_hom_comp (0,1) (15,16) x (absoluteBoundary A 1))
    apply Eq.trans (by simpa only [Category.assoc] using hh.symm)
    rw [hx]
    simpa [homotopyRegrade] using hu
  apply (biSuspensionHomEquiv 15 17 1 ((SyntheticCategory.biShift (0,1)).obj A)).symm.injective
  rw [AddEquiv.symm_apply_apply,bi_susp_symm_eq]
  have hh := congrArg (fun z => z≫(biSuspensionIso 1 ((SyntheticCategory.biShift (0,1)).obj A)).hom)
    hboundary
  simpa [c,β,absoluteBoundary,homotopyRegrade,shiftHomotopyClass,susp_invariance,Iso.homCongr,
    Category.assoc] using hh



private theorem base_h4_boundary :
    ∃ β : BiHom 14 17 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      β≫XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 3 17 h0h3Square ∧
      biSuspensionHomEquiv 15 16 1 (S_0_0 : SyntheticSpectrum)
        (h4Q1≫XModLambdaN.proj _ 1) = β≫model.nu.unitIso.hom := by
  obtain ⟨c,hc,hβ⟩ := adjacent_absolute_boundary .sphere 1 (by decide) 1 16
    (model.standardClasses.standardHi 4) h0h3Square paper_d2_h4
  have hc : c = nativeFirstLabel .sphere 1 16 (model.standardClasses.standardHi 4) := by
    simpa only [(model.quotients.tower _).rho_id,Category.comp_id,nativeFirstLabel] using hc
  let β : BiHom 14 17 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :=
    biSuspensionHomEquiv 15 16 1 _ (c≫XModLambdaN.proj _ 1)
  refine ⟨β,?_,?_⟩
  · simpa [β,homotopyRegrade,nativeFirstLabel] using hβ
  · have hcunit : c≫XModLambdaN.map model.nu.unitIso.hom 1=h4Q1 := by
      apply (KIP126.Literature.sphereFirstQuotient model 1 16).injective
      rw [hc,sphere_native_quotient_label]
      exact (KIP126.Literature.sphereFirstQuotient model 1 16).apply_symm_apply _ |>.symm
    rw [←hcunit]
    exact quotient_boundary_evaluation_natural model.nu.unitIso.hom 1 15 16 c

private theorem target_h0h4_boundary :
    ∃ β : BiHom 14 19 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      β≫XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 5 19 h0d0 ∧
      biSuspensionHomEquiv 15 17 1 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))
        (nativeFirstLabel .sphere 2 17 (KIP126.Literature.Standard.hiProduct 0 4)≫
          XModLambdaN.proj _ 1) = lambdaMultiply 1 β := by
  obtain ⟨c,hc,hβ⟩ := adjacent_absolute_boundary .sphere 2 (by decide) 2 17
    (KIP126.Literature.Standard.hiProduct 0 4) h0d0
    paper6_8_classical_d3.toHasDifferential
  let β : BiHom 14 19 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :=
    biSuspensionHomEquiv 15 17 2 _ (c≫XModLambdaN.proj _ 2)
  refine ⟨β,?_,?_⟩
  · simpa [β,homotopyRegrade,nativeFirstLabel] using hβ
  · have hres := absolute_boundary_restriction .sphere 1 2 (by decide) 15 17 c
    change c≫(model.quotients.tower _).rho 1 2 _ = nativeFirstLabel .sphere 2 17
      (KIP126.Literature.Standard.hiProduct 0 4) at hc
    rw [hc] at hres
    simpa [β,homotopyRegrade] using hres


private def positiveTwoSphereIso :
    (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) ≅
      Smn (Syn:=SyntheticSpectrum) 0 1 :=
  (SyntheticCategory.biShift (0,1)).mapIso model.nu.unitIso

private theorem h4_actual_two_source_quotient_image
    (κ : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (hκ : XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1≫κ.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)) :
    (shiftHomotopyClass (0,1) (15,16) h4Q1≫κ.inv≫
      XModLambdaN.map positiveTwoSphereIso.inv 1)≫
      XModLambdaN.map selectedTwoNormalized 1 =
      nativeFirstLabel .sphere 2 17 (KIP126.Literature.Standard.hiProduct 0 4) := by
  haveI : IsIso (XModLambdaN.map model.nu.unitIso.hom 1) := by
    change IsIso ((model.quotients.functoriality.functor 1).map model.nu.unitIso.hom)
    infer_instance
  apply (cancel_mono (XModLambdaN.map model.nu.unitIso.hom 1)).mp
  apply (KIP126.Literature.sphereFirstQuotient model 2 17).injective
  rw [sphere_native_quotient_label]
  have h := h0Q1_h4 κ hκ
  have hs : susp_invariance 15 16 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) h4Q1 =
      shiftHomotopyClass (0,1) (15,16) h4Q1 := by
    simp [susp_invariance,shiftHomotopyClass,Iso.homCongr]
  rw [hs] at h
  rw [selectedTwoNormalized_eq_h0]
  have he : positiveTwoSphereIso.inv ≫ h0NormalizedMap ≫ model.nu.unitIso.hom =
      KIP126.Literature.Standard.syntheticH0 := by
    simp only [positiveTwoSphereIso,h0NormalizedMap,Functor.mapIso_inv,Category.assoc,
      Iso.inv_hom_id,Category.comp_id,Iso.map_inv_hom_id_assoc]
  have heQ := congrArg (fun z => XModLambdaN.map z 1) he
  simp only [model.quotients.functoriality.map_comp] at heQ
  simp only [Category.assoc]
  rw [heQ]
  exact h

private theorem two_geometric_boundary_source_first_quotient
    (βν : BiHom 14 17 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (γ : BiHom 14 18 (Smn (Syn:=SyntheticSpectrum) 0 1))
    (σ : Smn (Syn:=SyntheticSpectrum) 14 17 ≅ Smn 14 17)
    (hγ : γ = shiftHomotopyClass (0,1) (14,17) (σ.hom≫βν≫model.nu.unitIso.hom)) :
    (γ≫positiveTwoSphereIso.inv)≫XModLambdaN.incl _ 1 =
      shiftHomotopyClass (0,1) (14,17) βν≫XModLambdaN.incl _ 1 := by
  haveI : IsIso (XModLambdaN.map positiveTwoSphereIso.hom 1) := by
    change IsIso ((model.quotients.functoriality.functor 1).map positiveTwoSphereIso.hom)
    infer_instance
  apply (cancel_mono (XModLambdaN.map positiveTwoSphereIso.hom 1)).mp
  simp only [Category.assoc]
  rw [←XModLambdaN.incl_naturality]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  rw [hγ]
  have hh := shift_precomp_sphere_automorphism_first_quotient (0,1) (14,17)
    (S_0_0:SyntheticSpectrum) σ (βν≫model.nu.unitIso.hom)
  simp only [Category.assoc] at hh
  trans shiftHomotopyClass (0,1) (14,17) (βν≫model.nu.unitIso.hom)≫XModLambdaN.incl _ 1
  · exact hh
  · simpa only [positiveTwoSphereIso,Functor.mapIso_hom,Category.assoc,Smn,S_0_0,SphereSpectrum,Prod.mk_add_mk,Int.reduceAdd] using
      congrArg (fun z => z≫XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1)
        (shift_hom_comp (0,1) (14,17) βν model.nu.unitIso.hom)

private theorem paper6_8_full_two_representatives :
    ∃ a : BiHom 14 18 ((SyntheticCategory.biShift (0,1)).obj
          (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))),
      ∃ β : BiHom 14 19 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
        a≫XModLambdaN.incl _ 1 = (model.firstQuotient .sphere 1 3 17).symm h0h3Square ∧
        β≫XModLambdaN.incl _ 1 = nativeFirstLabel .sphere 5 19 h0d0 ∧
        a≫selectedTwoNormalized = lambdaMultiply 1 β := by
  obtain ⟨β0,hβ0,hβunit⟩ := base_h4_boundary
  obtain ⟨β,hβ,hδβ⟩ := target_h0h4_boundary
  obtain ⟨κ,hκ,σ,hγ⟩ := two_degree_boundary_shift (S_0_0:SyntheticSpectrum) h4Q1
  let cunit := shiftHomotopyClass (0,1) (15,16) h4Q1≫κ.inv
  let c := cunit≫XModLambdaN.map positiveTwoSphereIso.inv 1
  let γ := biSuspensionHomEquiv 15 17 1 (Smn (Syn:=SyntheticSpectrum) 0 1)
    (cunit≫XModLambdaN.proj _ 1)
  let a : BiHom 14 18 ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) :=
    biSuspensionHomEquiv 15 17 1 _ (c≫XModLambdaN.proj _ 1)
  have ha : a=γ≫positiveTwoSphereIso.inv :=
    quotient_boundary_evaluation_natural positiveTwoSphereIso.inv 1 15 17 cunit
  have hγ' : γ=shiftHomotopyClass (0,1) (14,17) (σ.hom≫β0≫model.nu.unitIso.hom) := by
    rw [←hβunit]
    exact hγ
  have hafirst : a≫XModLambdaN.incl _ 1 =
      shiftHomotopyClass (0,1) (14,17) β0≫XModLambdaN.incl _ 1 := by
    rw [ha]
    exact two_geometric_boundary_source_first_quotient β0 γ σ hγ'
  refine ⟨a,β,?_,hβ,?_⟩
  · rw [hafirst]
    exact positive_shift_full_first_label .sphere 3 17 h0h3Square β0 hβ0
  · have hcimage := h4_actual_two_source_quotient_image κ hκ
    have hcimage : c≫XModLambdaN.map selectedTwoNormalized 1=
        nativeFirstLabel .sphere 2 17 (KIP126.Literature.Standard.hiProduct 0 4) := by
      simpa only [c,cunit,Category.assoc] using hcimage
    rw [←hδβ,←hcimage]
    exact (quotient_boundary_evaluation_natural selectedTwoNormalized 1 15 17 c).symm

private theorem h0d0_ne_zero : h0d0≠0 :=
  nonzero_differential_target_label_ne_zero paper6_8_classical_d3

private theorem d0_ne_zero : d0≠0 := by
  intro hz
  apply h0d0_ne_zero
  simp only [h0d0,hz,product,map_zero,LinearMap.map_zero₂]

private def d0Q1 : BiHom 14 18 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) :=
  (KIP126.Literature.sphereFirstQuotient model 4 18).symm d0

private theorem d0Q1_ne_zero : d0Q1≠0 := by
  intro hz
  apply d0_ne_zero
  have h := congrArg (KIP126.Literature.sphereFirstQuotient model 4 18) hz
  simpa only [d0Q1,LinearEquiv.apply_symm_apply,map_zero] using h

private theorem d0Q1_unique
    (u v : BiHom 14 18 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (hu : u≠0) (hv : v≠0) : u=v := by
  let d : model.classical.sphere.Page 2 (4,18) ≃ₗ[ℤ] (Fin 1 →₀ ZMod 2) :=
    coordinates 4 18 (by decide)
  let e := (KIP126.Literature.sphereFirstQuotient model 4 18).trans d
  have he (z : BiHom 14 18 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
      (hz : z≠0) : e z=Finsupp.single 0 1 := by
    rcases NumericalExamples.one_coordinate_cases (e z) with h | h
    · exact False.elim (hz (e.injective (h.trans (map_zero e).symm)))
    · exact h
  exact e.injective ((he u hu).trans (he v hv).symm)


private theorem h0Q1_d0
    (κ : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (hκ : XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1≫κ.hom=
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)) :
    KIP126.Literature.sphereFirstQuotient model 5 19
      ((susp_invariance 14 18 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) d0Q1)≫
        κ.inv≫XModLambdaN.map KIP126.Literature.Standard.syntheticH0 1) = h0d0 := by
  rw [←q1_d0_action_actual_map d0Q1_unique κ hκ _ d0Q1 d0Q1_ne_zero]
  have h := KIP126.Literature.Standard.first_quotient_action 1 1 4 18
    KIP126.Literature.Standard.syntheticH0 d0Q1
  change KIP126.Literature.sphereFirstQuotient model 5 19
      (sphereAction KIP126.Literature.Standard.syntheticH0 d0Q1) =
    model.sphereAlgebra.product (1,1) (4,18)
      (KIP126.Literature.sphereFirstQuotient model 1 1
        (quotientClass 1 KIP126.Literature.Standard.syntheticH0))
      (KIP126.Literature.sphereFirstQuotient model 4 18 d0Q1) at h
  erw [KIP126.Literature.Standard.toda_h0_label] at h
  change _ = model.sphereAlgebra.product (1,1) (4,18) h0 d0
  simpa only [d0Q1,LinearEquiv.apply_symm_apply,KIP126.Computation.Standard.h0] using h


private theorem d0_full_lift :
    ∃ D : BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      D≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 4 18 d0 := by
  have hp := permanent_member_of_cycle .sphere (4,18) d0 (every_d0_degree_label_permanent d0)
  obtain ⟨D,hD⟩ := (KIP126.Literature.Standard.selected_permanent_lift .sphere 4 18 d0).mp (every_d0_degree_label_permanent d0)
  refine ⟨D≫SyntheticCategory.biShift_zero.hom.app _,?_⟩
  rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
  exact congrArg (fun z => z≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) hD


private theorem d0_positive_normalized_image
    (D : BiHom 14 18 (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)))
    (hD : D≫XModLambdaN.incl _ 1=nativeFirstLabel .sphere 4 18 d0) :
    (shiftHomotopyClass (0,1) (14,18) D≫selectedTwoNormalized)≫XModLambdaN.incl _ 1 =
      nativeFirstLabel .sphere 5 19 h0d0 := by
  letI := model.exactness.shiftCommShift (0,1)
  letI := model.exactness.shiftExact (0,1)
  obtain ⟨κ,hκ,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) 1 (S_0_0:SyntheticSpectrum)
  have hDunit : D≫model.nu.unitIso.hom≫XModLambdaN.incl _ 1=d0Q1 := by
    rw [XModLambdaN.incl_naturality,←Category.assoc,hD]
    apply (KIP126.Literature.sphereFirstQuotient model 4 18).injective
    rw [sphere_native_quotient_label]
    exact (KIP126.Literature.sphereFirstQuotient model 4 18).apply_symm_apply _ |>.symm
  have h := h0Q1_d0 κ hκ
  have hs : susp_invariance 14 18 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) d0Q1=
      shiftHomotopyClass (0,1) (14,18) d0Q1 := by
    simp [susp_invariance,shiftHomotopyClass,Iso.homCongr]
  rw [hs,←hDunit,shift_hom_comp,Functor.map_comp] at h
  have hκ' : (SyntheticCategory.biShift (0,1)).map
      (XModLambdaN.incl (SphereSpectrum (C:=SyntheticSpectrum)) 1)=
      XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1≫κ.hom := hκ.symm
  rw [hκ'] at h
  simp only [Category.assoc,Iso.hom_inv_id_assoc] at h
  haveI : IsIso (XModLambdaN.map model.nu.unitIso.hom 1) := by
    change IsIso ((model.quotients.functoriality.functor 1).map model.nu.unitIso.hom)
    infer_instance
  apply (cancel_mono (XModLambdaN.map model.nu.unitIso.hom 1)).mp
  apply (KIP126.Literature.sphereFirstQuotient model 5 19).injective
  rw [sphere_native_quotient_label]
  rw [selectedTwoNormalized_eq_h0]
  simp only [h0NormalizedMap,Category.assoc]
  rw [←XModLambdaN.incl_naturality model.nu.unitIso.hom 1]
  simp only [Iso.inv_hom_id_assoc]
  have hh0 : KIP126.Literature.Standard.syntheticH0≫
      XModLambdaN.incl (SphereSpectrum (C:=SyntheticSpectrum)) 1=
      XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1≫
        XModLambdaN.map KIP126.Literature.Standard.syntheticH0 1 :=
    XModLambdaN.incl_naturality KIP126.Literature.Standard.syntheticH0 1
  rw [hh0]
  simpa only [Category.assoc] using h


private theorem selectedTwoNormalized_eq_positive : selectedTwoNormalized =
    normalizedMapInPositiveCoordinates .sphere .sphere twoMap twoMap_exponent := by
  have H (e : ℕ) (he : e=1)
      (F : (SyntheticCategory.biShift (0,(e:ℤ))).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) ⟶
          model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :
      eqToHom (congrArg (fun z : ℕ => (SyntheticCategory.biShift (0,(z:ℤ))).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) he.symm)≫F =
        (by simpa only [he,Nat.cast_one] using F) := by
    subst e
    simp only [eqToHom_refl,Category.id_comp,eq_mp_eq_cast,eq_mpr_eq_cast,cast_cast,cast_eq]
  exact H _ twoMap_exponent (model.normalizedMap .sphere .sphere twoMap).map


private theorem h0h3Square_permanent : h0h3Square∈permanentCycles model .sphere (3,17) := by
  obtain ⟨a,ha,_⟩ := base_h4_boundary
  exact first_label_lift_permanent .sphere 3 17 h0h3Square a ha


private theorem paper6_8_long_nonzero_extension :
    InfiniteExtension model .sphere .sphere twoMap 2 3 17 h0h3Square h0d0 := by
  obtain ⟨a,β,hafirst,hβ,heq⟩ := paper6_8_full_two_representatives
  have has := shifted_full_source_detects_of_first .sphere 1 3 17 h0h3Square
    h0h3Square_permanent a hafirst
  have hβp := first_label_lift_permanent .sphere 5 19 h0d0 β hβ
  have hbt := nu_lambda_detects .sphere 1 (by decide) 5 19 h0d0 hβp β hβ
  have hp : fullDetectedPairAt .sphere .sphere 2 3 17 h0h3Square h0d0 1
      (normalizedMapInPositiveCoordinates .sphere .sphere twoMap twoMap_exponent) := by
    refine ⟨by decide,a,lambdaMultiply 1 β,?_,?_,?_⟩
    · simpa using has
    · simpa [homotopyRegrade] using hbt
    · rw [←selectedTwoNormalized_eq_positive]
      exact heq
  exact actual_detected_pair_infinite .sphere .sphere twoMap 2 3 17 h0h3Square h0d0
    (permanent_cycle_of_member .sphere (3,17) h0h3Square h0h3Square_permanent)
    (permanent_cycle_of_member .sphere (5,19) h0d0 hβp)
    (detected_pair_positive_to_actual .sphere .sphere twoMap twoMap_exponent
      2 3 17 h0h3Square h0d0 hp)


private theorem paper6_8_short_extension :
    InfiniteExtension model .sphere .sphere twoMap 1 4 18 d0 h0d0 := by
  obtain ⟨D,hD⟩ := d0_full_lift
  have hDp := permanent_member_of_cycle .sphere (4,18) d0 (every_d0_degree_label_permanent d0)
  have has := positive_shift_full_source_detects .sphere 4 18 d0 hDp D hD
  have hfirst := d0_positive_normalized_image D hD
  let a : BiHom 14 19 ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) :=
    shiftHomotopyClass (0,1) (14,18) D
  let b := a≫selectedTwoNormalized
  have hbp := first_label_lift_permanent .sphere 5 19 h0d0 b hfirst
  have hbt := nu_first_label_detects .sphere 5 19 h0d0 hbp b hfirst
  have hp : fullDetectedPairAt .sphere .sphere 1 4 18 d0 h0d0 1
      (normalizedMapInPositiveCoordinates .sphere .sphere twoMap twoMap_exponent) := by
    refine ⟨by decide,a,b,?_,?_,?_⟩
    · simpa [a,homotopyRegrade] using has
    · simpa [homotopyRegrade] using hbt
    · rw [←selectedTwoNormalized_eq_positive]
  exact actual_detected_pair_infinite .sphere .sphere twoMap 1 4 18 d0 h0d0
    (every_d0_degree_label_permanent d0)
    (permanent_cycle_of_member .sphere (5,19) h0d0 hbp)
    (detected_pair_positive_to_actual .sphere .sphere twoMap twoMap_exponent
      1 4 18 d0 h0d0 hp)


private theorem minimal_length_full_nu_tower_no_crossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (p : ℤ×ℤ) (s l : ℤ)
    (hl : l≤normalizedExponent model.classicalTower f) :
    TowerNoCrossing (model.convergentMap (extensionSourceObject model X Y f) (.nu Y)
      (model.normalizedMap X Y f).map) p s l := by
  apply tower_no_crossing_of_correction (E:=model.family) (P:=model.syntheticTower)
    (cx:=model.convergence (extensionSourceObject model X Y f))
    (cy:=model.convergence (.nu Y))
    (model.convergentMap (extensionSourceObject model X Y f) (.nu Y)
      (model.normalizedMap X Y f).map) p s l
  intro u v hsu huv hvs a ha hfa
  refine ⟨a,ha,?_,?_⟩
  · simp only [sub_self]
    exact (model.syntheticTower.filtrationSubmodule _ _ _).zero_mem
  · have h := normalized_nu_image_filtration X Y f p.1 p.2 u a ha
    exact model.syntheticTower.filtrationSubmodule_antitone
      (model.nu.functor.obj (Y.obj model.auxiliary)) p (by omega) h


private theorem minimal_full_witness_essential_of_target_not_boundary
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (n s t : ℤ) (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : InfiniteExtensionWitness model X Y f n s t x y)
    (hn : n≤normalizedExponent model.classicalTower f)
    (hy : y∉boundaries model Y (1+n-normalizedExponent model.classicalTower f) (s+n,t+n)) :
    W.Essential := by
  have hnc := minimal_length_full_nu_tower_no_crossing X Y f
    (t-s,t+normalizedExponent model.classicalTower f) s n hn
  apply (tower_essential_iff_target_nonzero_of_no_crossing
    (E:=model.family) (P:=model.syntheticTower)
    (cx:=model.convergence (extensionSourceObject model X Y f))
    (cy:=model.convergence (.nu Y))
    (model.convergentMap (extensionSourceObject model X Y f) (.nu Y)
      (model.normalizedMap X Y f).map)
    (t-s,t+normalizedExponent model.classicalTower f) s n
    W.source W.target W.equation hnc).mpr
  intro hz
  have hi : (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f)=
      (s+n,t+n,t+normalizedExponent model.classicalTower f) := by
    ext <;> dsimp; omega
  have hr := representative_transport hi _ _ W.target_rep
  have hlabel : regradeE2 hi (infiniteTargetForExtension model X Y f n s t W.length_lower y)=
      nuWeightLabel model Y (s+n) (t+n) (t+normalizedExponent model.classicalTower f)
        (by have := W.length_lower; omega) y := by
    exact eq_of_heq ((regradeE2_heq hi _).trans
      (infinite_target_nuWeight_heq X Y f n s t W.length_lower y))
  rw [hlabel] at hr
  have hc := (KIP126.Literature.Standard.eInfinity_nu_labels Y (s+n) (t+n)
    (t+normalizedExponent model.classicalTower f) (by have := W.length_lower; omega) y _).mp hr
  have hb : y∈boundaries model Y (1+(t+n)-(t+normalizedExponent model.classicalTower f))
      (s+n,t+n) := by
    apply (CrossingLabels.subquotient_zero_iff _ _ ⟨y,hc.1⟩).mp
    rw [←hc.2]
    simp only [hz,map_zero]
  exact hy (by convert hb using 1; congr 1; omega)


private theorem paper6_8_short_essential :
    ∃ W : InfiniteExtensionWitness model .sphere .sphere twoMap 1 4 18 d0 h0d0,
      W.Essential := by
  obtain ⟨W⟩ := paper6_8_short_extension
  refine ⟨W,minimal_full_witness_essential_of_target_not_boundary .sphere .sphere twoMap
    1 4 18 d0 h0d0 W (by rw [twoMap_exponent]; norm_num) ?_⟩
  simpa only [twoMap_exponent,Nat.cast_one,add_sub_cancel_right,boundaries_one,
    Submodule.mem_bot] using h0d0_ne_zero


private theorem detects_zero_of_next_filtration (A : SyntheticObject) (i : Tridegree)
    (a : BiHom (i.2.1-i.1) i.2.2 (A.obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower (i.1+1) a) :
    Detects (model.convergence A) i 0 a := by
  have hz : Detects (model.convergence A) i 0
      (0 : BiHom (i.2.1-i.1) i.2.2 (A.obj model.nu model.auxiliary)) := by
    refine ⟨0,HasInfinityRepresentative.zero _ 2 (by decide) i,0,map_zero _,?_⟩
    simp only [map_zero]
  exact detects_of_high_difference A i 0 0 a hz (by simpa only [sub_zero] using ha)

private theorem nu_weight_zero_label (X : ClassicalObject) (s t w : ℤ) (hw : w≤t) :
    nuWeightLabel model X s t w hw 0=0 := by
  have cast_zero (E : SyntheticAdamsSS.{0}) (s t w w' : ℤ) (hw : w=w')
      (he : (E.E₂ (s,t,w) : Type)=(E.E₂ (s,t,w') : Type)) :
      he.mp (0 : E.E₂ (s,t,w))=0 := by subst w';rfl
  simp only [nuWeightLabel,regradeE2,targetNuLabel,map_zero]
  rw [cast_zero _ _ _ _ _ (by omega)]
  simp only [map_zero]

/-- Subtract the one-lambda multiple of the shorter source. Its image has
zero associated grade in filtration five; no strict zero homotopy image or
vanishing of the whole sixth filtration is asserted. -/

private theorem paper6_8_long_zero_extension :
    InfiniteExtension model .sphere .sphere twoMap 2 3 17 h0h3Square 0 := by
  obtain ⟨a,β,hafirst,hβ,heq⟩ := paper6_8_full_two_representatives
  obtain ⟨D,hD⟩ := d0_full_lift
  let d : BiHom 14 19 ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) :=
    shiftHomotopyClass (0,1) (14,18) D
  let b : BiHom 14 19 (model.nu.functor.obj
      (ClassicalObject.sphere.obj model.auxiliary)) := d≫selectedTwoNormalized
  let q : BiHom 14 18 ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary))) := lambdaMultiply 1 d
  let a' := a-q
  have hbp := first_label_lift_permanent .sphere 5 19 h0d0 b
    (d0_positive_normalized_image D hD)
  have hβp := first_label_lift_permanent .sphere 5 19 h0d0 β hβ
  have ht := nu_lambda_detects .sphere 1 (by decide) 5 19 h0d0 hβp β hβ
  have ht' := nu_lambda_detects .sphere 1 (by decide) 5 19 h0d0 hbp b
    (d0_positive_normalized_image D hD)
  have hdifference := detects_sub_filtration (model.convergence (.nu .sphere))
    (5,19,18) ht ht'
  have hq : FiltrationAtLeast model.syntheticTower 4 q :=
    shifted_full_first_kernel_filtration .sphere 1 3 17 q
      (lambdaMultiply_quotient_zero _ 1 14 19 d)
  have has := shifted_full_source_detects_of_first .sphere 1 3 17 h0h3Square
    h0h3Square_permanent a hafirst
  have hsource := detects_of_high_difference (.shift (0,1) (.nu .sphere)) (3,17,18)
    _ a a' has (by
      have he : a'-a = -q := by dsimp only [a']; abel
      rw [he]
      exact (model.syntheticTower.filtrationSubmodule _ _ _).neg_mem hq)
  have himage : a'≫selectedTwoNormalized=lambdaMultiply 1 β-lambdaMultiply 1 b := by
    dsimp only [a',q,b]
    rw [Preadditive.sub_comp,heq]
    simp only [lambdaMultiply,Category.assoc]
  have htarget : Detects (model.convergence (.nu .sphere)) (5,19,18) 0
      (a'≫selectedTwoNormalized) := by
    apply detects_zero_of_next_filtration (.nu .sphere) (5,19,18)
    rw [himage]
    exact hdifference
  have hp : fullDetectedPairAt .sphere .sphere 2 3 17 h0h3Square 0 1
      (normalizedMapInPositiveCoordinates .sphere .sphere twoMap twoMap_exponent) := by
    refine ⟨by decide,a',a'≫selectedTwoNormalized,?_,?_,?_⟩
    · simpa using hsource
    · have htzero : Detects (model.convergence (.nu .sphere)) (5,19,18)
          (nuWeightLabel model .sphere 5 19 18 (by decide) 0)
          (a'≫selectedTwoNormalized) := by
        rw [nu_weight_zero_label]
        exact htarget
      convert htzero using 1 <;> norm_num [nu_weight_zero_label,homotopyRegrade]
    · rw [←selectedTwoNormalized_eq_positive]
  exact actual_detected_pair_infinite .sphere .sphere twoMap 2 3 17 h0h3Square 0
    (permanent_cycle_of_member .sphere (3,17) h0h3Square h0h3Square_permanent)
    (permanent_cycle_of_member .sphere (5,19) 0 (Submodule.zero_mem _))
    (detected_pair_positive_to_actual .sphere .sphere twoMap twoMap_exponent
      2 3 17 h0h3Square 0 hp)

private theorem h4_q1_actual_source_detects
    (κ : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) :
    Detects (model.convergence (.quotient 1 (.shift (0,1) (.nu .sphere))))
      (1,16,17) (regradeE2 (by simp) (finiteNuLabel model .sphere 1 1 1 16 0 h4))
      (shiftHomotopyClass (0,1) (15,16) h4Q1≫κ.inv≫
        XModLambdaN.map positiveTwoSphereIso.inv 1) := by
  let c := shiftHomotopyClass (0,1) (15,16) h4Q1≫κ.inv≫
    XModLambdaN.map positiveTwoSphereIso.inv 1
  have hcne : c≠0 := by
    intro hz
    have hh := congrArg (fun z => z≫XModLambdaN.map positiveTwoSphereIso.hom 1≫κ.hom) hz
    let E := (model.quotients.functoriality.functor 1).mapIso positiveTwoSphereIso
    change (shiftHomotopyClass (0,1) (15,16) h4Q1≫κ.inv≫E.inv)≫E.hom≫κ.hom=0≫_ at hh
    simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id,zero_comp] at hh
    apply h4Q1_ne_zero
    apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,1)).map_injective
    rw [Functor.map_zero]
    apply (cancel_epi ((SyntheticCategory.biShift_comp (15,16) (0,1)).inv.app S_0_0)).mp
    change shiftHomotopyClass (0,1) (15,16) h4Q1=_
    simpa only [comp_zero] using hh
  obtain ⟨x,hxc,hcd⟩ := positive_finite_source_label_exists .sphere 1 (by decide) 1 16 c
  have hcfirst := shifted_finite_source_first .sphere 1 (by decide) 1 1 16 x c hcd
  simp only [(model.quotients.tower _).rho_id,Category.comp_id] at hcfirst
  have hxne : x≠0 := by
    intro hz
    apply hcne
    rw [hcfirst,hz,map_zero]
  have hx : x=h4 := by
    apply (KIP126.Literature.sphereFirstQuotient model 1 16).symm.injective
    apply h4Q1_unique _ _ _ h4Q1_ne_zero
    intro hz
    apply hxne
    have hh := congrArg (KIP126.Literature.sphereFirstQuotient model 1 16) hz
    simpa only [LinearEquiv.apply_symm_apply,map_zero] using hh
  subst x
  exact hcd

private theorem finite_pair_regrade_trans {A : SyntheticAdamsSS.{0}} {i j k : Tridegree}
    (hij : i=j) (hjk : j=k) (x : A.E₂ i) :
    regradeE2 hjk (regradeE2 hij x)=regradeE2 (hij.trans hjk) x := by
  subst j
  subst k
  rfl

private theorem finite_pair_homotopy_regrade_trans {A : SyntheticSpectrum}
    {m m' m'' w w' w'' : ℤ} (hm : m=m') (hm' : m'=m'')
    (hw : w=w') (hw' : w'=w'') (a : BiHom m w A) :
    homotopyRegrade hm' hw' (homotopyRegrade hm hw a)=
      homotopyRegrade (hm.trans hm') (hw.trans hw') a := by
  subst m'
  subst m''
  subst w'
  subst w''
  rfl

private theorem actual_detected_pair_finite_page_two
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (s t : ℤ) (x : Ambient model X (s,t))
    (y : Ambient model Y (s+normalizedExponent model.classicalTower f,
      t+normalizedExponent model.classicalTower f))
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) 1))
    (b : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) 1))
    (ha : Detects (model.convergence (.quotient 1 (extensionSourceObject model X Y f)))
      (s,t,t+normalizedExponent model.classicalTower f)
      (regradeE2 (by simp) (finiteNuLabel model X 1
        (normalizedExponent model.classicalTower f) s t 0 x)) a)
    (hb : Detects (model.convergence (.quotient 1 (.nu Y)))
      (s+normalizedExponent model.classicalTower f,t+normalizedExponent model.classicalTower f,
        t+normalizedExponent model.classicalTower f)
      (regradeE2 (by simp) (finiteTargetLabel model Y 1
        (s+normalizedExponent model.classicalTower f)
        (t+normalizedExponent model.classicalTower f) 0 y))
      (homotopyRegrade (by change t-s=(t+normalizedExponent model.classicalTower f)-
        (s+normalizedExponent model.classicalTower f); omega) rfl b))
    (hab : a≫finiteExtensionMap model X Y f 1=b) :
    FiniteExtension model X Y f 2 (normalizedExponent model.classicalTower f) s t x y := by
  let e : ℤ := normalizedExponent model.classicalTower f
  have he0 : 0 ≤ e := by dsimp [e]; omega
  have hsi : (s,t,t+e)=(s,(t-s)+s,t+e) := by simp
  have hti : (s+e,t+e,t+e)=(s+e,(t-s)+(s+e),t+e) := by
    ext <;> dsimp; omega
  have has := detects_transport hsi _ _ ha
  have hbt := detects_transport hti _ _ hb
  have hsource : regradeE2 hsi
      (regradeE2 (by simp) (finiteNuLabel model X 1 e s t 0 x)) =
      finiteSourceForExtension model X Y f 1 s t x := by
    unfold finiteSourceForExtension
    rw [finite_pair_regrade_trans]
  rw [hsource] at has
  have htarget : regradeE2 hti
      (regradeE2 (by simp) (finiteTargetLabel model Y 1 (s+e) (t+e) 0 y)) =
      finiteTargetForExtension model X Y f 1 e s t (le_refl e) y := by
    unfold finiteTargetForExtension
    change regradeE2 hti (regradeE2 _ (finiteTargetLabel model Y 1 (s+e) (t+e) 0 y)) =
      regradeE2 _ (finiteTargetLabel model Y 1 (s+e) (t+e) (e-e).toNat y)
    rw [finite_pair_regrade_trans]
    have hzero : (e-e).toNat=0 := by omega
    have labels (j k : ℕ) (hjk : j=k)
        (hi : (s+e,t+e,(t+e)-j)=(s+e,(t-s)+(s+e),t+e))
        (hj : (s+e,t+e,(t+e)-k)=(s+e,(t-s)+(s+e),t+e)) :
        regradeE2 hi (finiteTargetLabel model Y 1 (s+e) (t+e) j y)=
          regradeE2 hj (finiteTargetLabel model Y 1 (s+e) (t+e) k y) := by
      subst k
      rfl
    exact labels _ _ hzero.symm _ _
  rw [htarget] at hbt
  obtain ⟨source,target,hsourceRep,htargetRep,heq⟩ :=
    extension_equation_of_detected_pair
      (model.convergentMap (.quotient 1 (extensionSourceObject model X Y f))
        (.quotient 1 (.nu Y)) (finiteExtensionMap model X Y f 1))
      (t-s,t+e) s e he0
      (finiteSourceForExtension model X Y f 1 s t x)
      (finiteTargetForExtension model X Y f 1 e s t (le_refl e) y) a b
      (by convert has using 1)
      (by convert hbt using 1; simp only [finite_pair_homotopy_regrade_trans]) hab
  exact ⟨{
    page_ge_two := by omega
    length_lower := le_refl e
    length_upper := by dsimp [e]; omega
    source_cycle := ⟨x,RepresentsOnPage.self_two x⟩
    target_cycle := by
      change ReachesPage _ ((2:ℤ)-e+e) (s+e,t+e) y
      simpa only [sub_add_cancel] using (show ReachesPage _ 2 (s+e,t+e) y from
        ⟨y,RepresentsOnPage.self_two y⟩)
    source := source
    target := target
    source_rep := hsourceRep
    target_rep := htargetRep
    equation := heq }⟩

private def finiteDetectedPairConclusionAt
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (s t : ℤ) (x : Ambient model X (s,t)) (e : ℕ)
    (F : (SyntheticCategory.biShift (0,(e:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
        model.nu.functor.obj (Y.obj model.auxiliary)) : Prop :=
  ∀ (y : Ambient model Y (s+e,t+e))
    (a : BiHom (t-s) (t+e)
      (XModLambdaN ((SyntheticCategory.biShift (0,(e:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1))
    (b : BiHom (t-s) (t+e)
      (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) 1)),
    Detects (model.convergence (.quotient 1 (.shift (0,(e:ℤ)) (.nu X))))
      (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel model X 1 e s t 0 x)) a →
    Detects (model.convergence (.quotient 1 (.nu Y))) (s+e,t+e,t+e)
      (regradeE2 (by simp) (finiteTargetLabel model Y 1 (s+e) (t+e) 0 y))
      (homotopyRegrade (by change t-s=(t+e)-(s+e); omega) rfl b) →
    a≫XModLambdaN.map F 1=b → FiniteExtension model X Y f 2 e s t x y

private theorem positive_detected_pair_finite_page_two
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (hf : normalizedExponent model.classicalTower f=1)
    (s t : ℤ) (x : Ambient model X (s,t)) (y : Ambient model Y (s+1,t+1))
    (a : BiHom (t-s) (t+1)
      (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1))
    (b : BiHom (t-s) (t+1)
      (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) 1))
    (ha : Detects (model.convergence (.quotient 1 (.shift (0,1) (.nu X))))
      (s,t,t+1) (regradeE2 (by simp) (finiteNuLabel model X 1 1 s t 0 x)) a)
    (hb : Detects (model.convergence (.quotient 1 (.nu Y))) (s+1,t+1,t+1)
      (regradeE2 (by simp) (finiteTargetLabel model Y 1 (s+1) (t+1) 0 y))
      (homotopyRegrade (by change t-s=(t+1)-(s+1); omega) rfl b))
    (hab : a≫XModLambdaN.map
      (KIP126.ProofTools.Paper.NuNumericalExtensions.normalizedMapInPositiveCoordinates X Y f hf) 1=b) :
    FiniteExtension model X Y f 2 1 s t x y := by
  have transport (e : ℕ) (he : e=1)
      (F : (SyntheticCategory.biShift (0,(e:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
          model.nu.functor.obj (Y.obj model.auxiliary)) :
      finiteDetectedPairConclusionAt X Y f s t x e F →
        finiteDetectedPairConclusionAt X Y f s t x 1
          (by simpa only [he,Nat.cast_one] using F) := by
    subst e
    exact id
  have hc : finiteDetectedPairConclusionAt X Y f s t x
      (normalizedExponent model.classicalTower f) (model.normalizedMap X Y f).map := by
    intro y a b ha hb hab
    exact actual_detected_pair_finite_page_two X Y f s t x y a b ha hb hab
  exact transport _ hf (model.normalizedMap X Y f).map hc y a b ha hb hab

private theorem selectedTwoNormalized_eq_positive_coordinates :
    selectedTwoNormalized = normalizedMapInPositiveCoordinates .sphere .sphere twoMap twoMap_exponent := by
  have H (e : ℕ) (he : e=1)
      (F : (SyntheticCategory.biShift (0,(e:ℤ))).obj
        (model.nu.functor.obj (SphereSpectrum (C:=Spectrum))) ⟶
        model.nu.functor.obj (SphereSpectrum (C:=Spectrum))) :
      eqToHom (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
        (model.nu.functor.obj (SphereSpectrum (C:=Spectrum)))) he.symm)≫F =
      (by simpa only [he,Nat.cast_one,ClassicalObject.obj] using F) := by
    subst e
    simp
  exact H _ twoMap_exponent _

private theorem finite_two_h4_extension :
    FiniteExtension model .sphere .sphere twoMap 2 1 1 16 h4
      (KIP126.Literature.Standard.hiProduct 0 4) := by
  letI := model.exactness.shiftCommShift (0,1)
  letI := model.exactness.shiftExact (0,1)
  obtain ⟨κ,hκ,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) 1 (S_0_0:SyntheticSpectrum)
  let c := shiftHomotopyClass (0,1) (15,16) h4Q1≫κ.inv≫
    XModLambdaN.map positiveTwoSphereIso.inv 1
  let b := c≫XModLambdaN.map selectedTwoNormalized 1
  have hc := h4_q1_actual_source_detects κ
  have hbfirst : b=nativeFirstLabel .sphere 2 17 (KIP126.Literature.Standard.hiProduct 0 4) :=
    h4_actual_two_source_quotient_image κ hκ
  have hb := first_label_detects_unshifted .sphere 1 (by decide) 2 17
    (KIP126.Literature.Standard.hiProduct 0 4) b (by
      simpa only [(model.quotients.tower _).rho_id,Category.comp_id,nativeFirstLabel] using hbfirst)
  apply positive_detected_pair_finite_page_two .sphere .sphere twoMap twoMap_exponent
    1 16 h4 (KIP126.Literature.Standard.hiProduct 0 4) c b hc
    (by simpa [homotopyRegrade] using hb)
  rw [←selectedTwoNormalized_eq_positive_coordinates]

private theorem paper6_8_crossing_warning : Paper6_8CrossingWarningStatement := by
  exact ⟨⟨by decide,paper_d2_h4⟩,finite_two_h4_extension,paper6_8_long_zero_extension,
    paper6_8_short_essential,paper6_8_long_nonzero_extension,paper6_8_not_zero⟩

end
end KIP126.ProofTools.Paper.DoublingNumericalExtensions