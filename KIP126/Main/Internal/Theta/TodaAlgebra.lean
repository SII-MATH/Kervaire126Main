module
public import KIP126.Main.Conditions
public import KIP126.Literature.Standard.QuotientAlgebra
public import KIP126.Literature.Standard.Filtration
public import KIP126.Computation.Table.Values
import all KIP126.Main.Internal.NuThree.Shift
import all KIP126.Main.Internal.Choice.OrderTwo
import all KIP126.Main.Internal.Theta.Products
import all KIP126.Main.Internal.Theta.TodaCofiber

/-! Original quotient algebra filler and candidate, ThetaToda.lean:565–781, bbac1fc05843 (MIT). The entire cofiber argument is retained. -/
@[expose] section
namespace KIP126.Main.Internal.Theta
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Toda
open KIP126.Core.SpectralSequence KIP126.Core.Algebra
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature.Route
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum Spectrum)
open KIP126.Literature.Standard (quotientSyntheticSymmetric quotientAlgebra quotientAlgebraProduct quotientAlgebra_commutative quotientAlgebra_unit quotientAlgebra_sphere_action quotientAlgebra_first_quotient)
open KIP126.Computation.Standard (product h0 h6 h5Square atom_h0 atom_h5 atom_h6)
open KIP126.Computation.Table
noncomputable section
local instance shiftAdditive (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := SyntheticSpectrum) p).Additive := model.exactness.shiftAdditive p
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem tensorLeft_sphere_faithful (m n:ℤ) : (tensorLeft (Smn (Syn:=SyntheticSpectrum) m n)).Faithful := by
  let e : Smn (Syn:=SyntheticSpectrum) (-m) (-n) ⊗ Smn m n ≅ (𝟙_ SyntheticSpectrum) :=
    (biShift_eq_tensor_Smn (-m) (-n) (Smn m n)).symm ≪≫
      (SyntheticCategory.biShift_comp (m,n) (-m,-n)).app (S_0_0:SyntheticSpectrum) ≪≫
        eqToIso (by simp [S_0_0]) ≪≫ SyntheticCategory.biShift_zero.app (S_0_0:SyntheticSpectrum)
  let f : tensorLeft (Smn (Syn:=SyntheticSpectrum) m n) ⋙ tensorLeft (Smn (-m) (-n)) ≅ 𝟭 SyntheticSpectrum :=
    (tensorLeftTensor _ _).symm ≪≫ (tensoringLeft SyntheticSpectrum).mapIso e ≪≫ leftUnitorNatIso SyntheticSpectrum
  exact Functor.Faithful.of_comp_iso f
private theorem q1_nonzero_unique

 (u v:BiHom 63 64 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hu:u≠0) (hv:v≠0) : u=v := by
  classical
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,1,64,["69,1"]⟩ (by
    unfold Raw.degrees
    iterate 85 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change model.classical.sphere.Page 2 (1,64) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  have hc (u:BiHom 63 64 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hu:u≠0) :
      e ((KIP126.Literature.sphereFirstQuotient model) 1 64 u)=Finsupp.single 0 1 := by
    let x:=e ((KIP126.Literature.sphereFirstQuotient model) 1 64 u)
    have heq:x=Finsupp.single 0 (x 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    generalize h:x 0=c at heq
    fin_cases c
    · simp only [show (⟨0,by decide⟩:F2)=0 from rfl,Finsupp.single_zero] at heq
      exfalso
      apply hu
      apply ((KIP126.Literature.sphereFirstQuotient model) 1 64).injective
      apply e.injective
      simpa only [map_zero] using heq
    · exact heq
  apply ((KIP126.Literature.sphereFirstQuotient model) 1 64).injective
  apply e.injective
  rw [hc u hu,hc v hv]
private theorem h6_tensor_square
   (may:MayContext SyntheticSpectrum)
 (u:BiHom 63 64 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hu:u≠0) :
 (biShift_eq_tensor_Smn 62 70 (Smn (Syn:=SyntheticSpectrum) 63 64)).hom≫
    (𝟙 (Smn (Syn:=SyntheticSpectrum) 62 70) ⊗ₘ u)=
 (SyntheticCategory.biShift (62,70)).map u≫
    (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).hom := by
  let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (62,70)
  let T:=tensorLeft (Smn (Syn:=SyntheticSpectrum) 62 70)
  letI:=model.exactness.shiftAdditive (62,70)
  letI:=may.leftShift (Smn (Syn:=SyntheticSpectrum) 62 70)
  letI:=may.leftExact (Smn (Syn:=SyntheticSpectrum) 62 70)
  letI : T.Faithful := tensorLeft_sphere_faithful 62 70
  let ff:=SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (62,70)
  let z : BiHom 63 64 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) := ff.preimage
    ((biShift_eq_tensor_Smn 62 70 (Smn (Syn:=SyntheticSpectrum) 63 64)).hom≫T.map u≫
      (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).inv)
  have hz : F.map z=(biShift_eq_tensor_Smn 62 70 (Smn (Syn:=SyntheticSpectrum) 63 64)).hom≫T.map u≫
      (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).inv := ff.map_preimage _
  have hzn:z≠0 := by
    intro h
    rw [h,Functor.map_zero] at hz
    have ht:T.map u=0 := by
      apply (cancel_epi (biShift_eq_tensor_Smn 62 70 (Smn (Syn:=SyntheticSpectrum) 63 64)).hom).mp
      apply (cancel_mono (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).inv).mp
      simpa only [Category.assoc,Limits.comp_zero,Limits.zero_comp] using hz.symm
    apply hu
    apply T.map_injective
    simpa only [Functor.map_zero] using ht
  have he:z=u:=q1_nonzero_unique z u hzn hu
  rw [he] at hz
  apply (cancel_mono (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).inv).mp
  simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id, T, tensorLeft, curriedTensor_obj_map, F, id_tensorHom] using hz.symm
private theorem quotient_inclusion_nonzero
  (may:MayContext SyntheticSpectrum)
 (u:BiHom 63 64 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hu:u≠0) :
 XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≠0 := by
  letI:=quotientSyntheticSymmetric
  letI:=quotientAlgebra 1 (by decide)
  letI:=may.rightShift
  letI:=may.rightExact
  intro h
  have hunit : (MonObj.one (X:=XModLambdaN (S_0_0:SyntheticSpectrum) 1))=0 :=
    (quotientAlgebra_unit 1 (by decide)).trans h
  have hm:=Mathlib.Tactic.MonTauto.leftUnitor_inv_one_tensor_mul u
  rw [hunit] at hm
  have hz : (0:(S_0_0:SyntheticSpectrum)⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1) ⊗ₘ u=0 := by
    rw [tensorHom_def]
    have hz' : (0:(S_0_0:SyntheticSpectrum)⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1) ▷ Smn (Syn:=SyntheticSpectrum) 63 64=0 :=
      (tensorRight (Smn (Syn:=SyntheticSpectrum) 63 64)).map_zero _ _
    rw [hz',Limits.zero_comp]
  rw [hz,Limits.zero_comp,Limits.comp_zero] at hm
  exact hu hm.symm
private theorem tensor_inclusion_square
 (may:MayContext SyntheticSpectrum)
 (hi:XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≠0)
 (unique : ∀f g:(S_0_0:SyntheticSpectrum)⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1, f≠0→g≠0→f=g) :
 (SyntheticCategory.biShift (62,70)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)≫
    (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).hom=
 (ρ_ (Smn (Syn:=SyntheticSpectrum) 62 70)).inv≫
    (𝟙 (Smn (Syn:=SyntheticSpectrum) 62 70) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1) := by
  let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (62,70)
  let T:=tensorLeft (Smn (Syn:=SyntheticSpectrum) 62 70)
  letI:=model.exactness.shiftAdditive (62,70)
  letI:=may.leftShift (Smn (Syn:=SyntheticSpectrum) 62 70)
  letI:=may.leftExact (Smn (Syn:=SyntheticSpectrum) 62 70)
  letI : T.Faithful := tensorLeft_sphere_faithful 62 70
  let ff:=SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (62,70)
  let z : (S_0_0:SyntheticSpectrum)⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1 := ff.preimage
    ((ρ_ (Smn (Syn:=SyntheticSpectrum) 62 70)).inv≫T.map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)≫
      (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).inv)
  have hz : F.map z=(ρ_ (Smn (Syn:=SyntheticSpectrum) 62 70)).inv≫T.map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)≫
      (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).inv := ff.map_preimage _
  have hzn:z≠0 := by
    intro h
    rw [h,Functor.map_zero] at hz
    have ht:T.map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)=0 := by
      apply (cancel_epi (ρ_ (Smn (Syn:=SyntheticSpectrum) 62 70)).inv).mp
      apply (cancel_mono (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).inv).mp
      simpa only [Category.assoc,Limits.comp_zero,Limits.zero_comp] using hz.symm
    apply hi
    apply T.map_injective
    simpa only [Functor.map_zero] using ht
  have he:z=XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1:=unique _ _ hzn hi
  rw [he] at hz
  apply (cancel_mono (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).inv).mp
  simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id,T,tensorLeft,curriedTensor_obj_map,F,id_tensorHom] using hz
private theorem algebra_filler_inclusion
  (may:MayContext SyntheticSpectrum)
 (hi:XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≠0)
 (unique : ∀f g:(S_0_0:SyntheticSpectrum)⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1, f≠0→g≠0→f=g)
 (b:BiHom 62 70 (S_0_0:SyntheticSpectrum))
 (e:(SyntheticCategory.biShift (62,70)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
     XModLambdaN (Smn (Syn:=SyntheticSpectrum) 62 70) 1)
 (he:(SyntheticCategory.biShift (62,70)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)≫e.hom=
     XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 62 70) 1) :
 letI:=quotientSyntheticSymmetric
 XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 62 70) 1≫e.inv≫
    (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).hom≫
    (quotientClass 1 b ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫
    (quotientAlgebra 1 (by decide)).mul=quotientClass 1 b := by
  letI:=quotientSyntheticSymmetric
  letI:=quotientAlgebra 1 (by decide)
  have hh:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 62 70) 1≫e.inv=
      (SyntheticCategory.biShift (62,70)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1) := by
    rw [←he,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  rw [←Category.assoc,←Category.assoc,←Category.assoc,hh]
  rw [Category.assoc,Category.assoc]
  rw [←Category.assoc,tensor_inclusion_square may hi unique]
  simp only [Category.assoc]
  rw [←Category.assoc (𝟙 (Smn (Syn:=SyntheticSpectrum) 62 70) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1),
    tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
  rw [←quotientAlgebra_unit 1 (by decide)]
  exact Mathlib.Tactic.MonTauto.rightUnitor_inv_tensor_one_mul (quotientClass 1 b)
private theorem theta_b_algebra_toda_candidate


 (may:MayContext SyntheticSpectrum)
 (unique : ∀f g:(S_0_0:SyntheticSpectrum)⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1, f≠0→g≠0→f=g)
 (h0:BiHom 0 1 (S_0_0:SyntheticSpectrum)) (theta:BiHom 62 64 (S_0_0:SyntheticSpectrum))
 (h0label:(KIP126.Literature.sphereFirstQuotient model) 1 1 (quotientClass 1 h0)=KIP126.Computation.Standard.h0)
 (htheta:ThetaChoice theta)
 (hlambda:lambdaMultiply 1 h0=syntheticTwo) (horder:theta+theta=0)
 (b:BiHom 62 70 (S_0_0:SyntheticSpectrum)) :
 ∃ z:BiHom 125 134 (XModLambdaN (S_0_0:SyntheticSpectrum) 1),
   Toda.Relation ((tripleTodaSource (Syn:=SyntheticSpectrum) 62 64 0 0 62 70).inv≫z)
     ((SyntheticCategory.biShift (62,70)).map theta) (2 • 𝟙 (Smn 62 70)) (quotientClass 1 b) ∧
   (KIP126.Literature.sphereFirstQuotient model) 9 134 z=
     product
       (h6) ((KIP126.Literature.sphereFirstQuotient model) 8 70 (quotientClass 1 b)) := by
  letI:=quotientSyntheticSymmetric
  obtain ⟨e,a,u,he,hu,hun,hul,ha⟩:=theta_b_actual_h6_cofiber_candidate_universal
    h0 theta h0label htheta hlambda horder b
  let Q:=quotientAlgebra 1 (by decide)
  let R:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 62 70) 1⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1:=
    e.inv≫(biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).hom≫
      (quotientClass 1 b ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul
  have hi:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 62 70) 1≫R=quotientClass 1 b :=
    algebra_filler_inclusion may (quotient_inclusion_nonzero may u hun) unique b e he
  let src:=tripleTodaSource (Syn:=SyntheticSpectrum) 62 64 0 0 62 70
  refine ⟨src.hom≫a≫R,?_,?_⟩
  · simpa only [src,Iso.inv_hom_id_assoc] using ha R hi
  have hp:src.hom≫a≫R=quotientAlgebraProduct Q u (quotientClass 1 b) := by
    have huR:src.hom≫a≫R=(susp_invariance 63 64 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) u)≫
        (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).hom≫
        (quotientClass 1 b ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul := by
      dsimp only [R]
      simpa only [Category.assoc] using congrArg (fun v=>v≫
        (biShift_eq_tensor_Smn 62 70 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).hom≫
        (quotientClass 1 b ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul) hu.symm
    rw [huR]
    dsimp only [susp_invariance]
    simp only [Equiv.trans_apply,Functor.FullyFaithful.homEquiv_apply,
      Iso.homCongr_apply,Iso.refl_hom,Category.comp_id,Category.assoc]
    rw [←Category.assoc ((SyntheticCategory.biShift (62,70)).map u),←h6_tensor_square may u hun]
    simp only [Category.assoc]
    rw [←Category.assoc (𝟙 (Smn (Syn:=SyntheticSpectrum) 62 70) ⊗ₘ u),tensorHom_comp_tensorHom,
      Category.id_comp,Category.comp_id]
    rfl
  rw [hp]
  have hm:=quotientAlgebra_first_quotient 1 64 8 70 u (quotientClass 1 b)
  change (KIP126.Literature.sphereFirstQuotient model) 9 134 (quotientAlgebraProduct Q u (quotientClass 1 b))=
    product
      ((KIP126.Literature.sphereFirstQuotient model) 1 64 u) ((KIP126.Literature.sphereFirstQuotient model) 8 70 (quotientClass 1 b)) at hm
  rw [hul] at hm
  exact hm
private theorem zero_hom_nonzero_unique
 (zero_nonzero_unique : ∀ x y : model.classical.sphere.Page 2 (0,0), x ≠ 0 → y ≠ 0 → x = y) :
 ∀f g:(S_0_0:SyntheticSpectrum)⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1,f≠0→g≠0→f=g := by
  intro f g hf hg
  have hn (x:(S_0_0:SyntheticSpectrum)⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1) (hx:x≠0) :
      (KIP126.Literature.sphereFirstQuotient model) 0 0 (SyntheticCategory.biShift_zero.hom.app (S_0_0:SyntheticSpectrum)≫x)≠0 := by
    intro h
    apply hx
    apply (cancel_epi (SyntheticCategory.biShift_zero.hom.app (S_0_0:SyntheticSpectrum))).mp
    apply ((KIP126.Literature.sphereFirstQuotient model) 0 0).injective
    simpa only [Limits.comp_zero,map_zero] using h
  apply (cancel_epi (SyntheticCategory.biShift_zero.hom.app (S_0_0:SyntheticSpectrum))).mp
  apply ((KIP126.Literature.sphereFirstQuotient model) 0 0).injective
  exact zero_nonzero_unique _ _ (hn f hf) (hn g hg)


end
end KIP126.Main.Internal.Theta
