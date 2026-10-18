module
import KIP126.ProofTools.Laws
import Mathlib.Algebra.CharP.Two
/-! Sign transport for actual Mahowald representatives. Classical Adams pages
have exponent two by the HF₂ universal-coefficient comparison, its coefficient
tower layers and their page quotients. Actual homotopy representatives are
negated; no exponent-two assertion is made about their homotopy groups. -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
private theorem cohomology_two (n : ℤ) (X : Spectrum)
    (a : ModTwoCohomology model n X) : a+a=0 := by
  apply (KIP126.Literature.Standard.universal_coefficient n X).injective
  simp only [map_add,map_zero]
  ext x
  simp only [AddMonoidHom.add_apply, AddMonoidHom.zero_apply]
  exact CharTwo.add_self_eq_zero _
private theorem coefficient_identity_two :
    (𝟙 model.coefficients.object : model.coefficients.object ⟶ model.coefficients.object) +
      𝟙 model.coefficients.object = 0 := by
  let z : (shiftFunctor Spectrum (0:ℤ)).obj model.coefficients.object ⟶ model.coefficients.object :=
    (shiftFunctorZero Spectrum ℤ).hom.app model.coefficients.object
  have hz := cohomology_two 0 model.coefficients.object z
  apply (cancel_epi z).mp
  rw [Preadditive.comp_add,Category.comp_id,comp_zero]
  exact hz
private theorem tensor_coefficient_identity_two (X : Spectrum) :
    (𝟙 (model.coefficients.object ⊗ X) : _ ⟶ _) + 𝟙 _ = 0 := by
  letI := closedBackground.tensorShift X
  letI := closedBackground.tensorExact X
  have h := congrArg (fun f => (tensorRight X).map f) coefficient_identity_two
  change (tensorRight X).map (𝟙 model.coefficients.object + 𝟙 model.coefficients.object) = (tensorRight X).map 0 at h
  rw [Functor.map_add,CategoryTheory.Functor.map_id,Functor.map_zero] at h
  exact h
private theorem layer_identity_two (X : Spectrum) (s : ℤ) :
    (𝟙 ((model.classicalTower.tower X).layer s) : _ ⟶ _) + 𝟙 _ = 0 := by
  let T := model.classicalTower.tower X
  have cofib_transport (a b c d : ℕ) (ha : a=c) (hb : b=d)
      (h : a≤b) (h' : c≤d) :
      HasFunctorialCofiber.cofib (T.map h) = HasFunctorialCofiber.cofib (T.map h') := by
    subst c; subst d; rfl
  by_cases hs : 0 ≤ s
  · have he : T.layer s = HasFunctorialCofiber.cofib (T.map (Nat.le_succ s.toNat)) := by
      dsimp [AbstractAdamsTower.layer,AbstractAdamsTower.mapAt]
      have hs1 : (s+1).toNat=s.toNat+1 := by omega
      exact cofib_transport _ _ _ _ rfl hs1 _ _
    let e : T.layer s ≅ model.coefficients.object ⊗ T.stage s.toNat :=
      eqToIso he ≪≫ T.layerIso s.toNat
    apply (cancel_epi e.inv).mp
    apply (cancel_mono e.hom).mp
    change (e.inv ≫ (𝟙 (T.layer s) + 𝟙 (T.layer s))) ≫ e.hom = (e.inv ≫ 0) ≫ e.hom
    rw [Preadditive.comp_add,Preadditive.add_comp,Category.comp_id,
      Iso.inv_hom_id,comp_zero,zero_comp]
    exact tensor_coefficient_identity_two (T.stage s.toNat)
  · have hs0 : s.toNat=0 := by omega
    have hs10 : (s+1).toNat=0 := by omega
    have he : T.layer s = HasFunctorialCofiber.cofib (𝟙 (T.stage 0)) := by
      dsimp only [AbstractAdamsTower.layer,AbstractAdamsTower.mapAt]
      exact (cofib_transport _ _ _ _ hs0 hs10 _ (le_refl 0)).trans
        (congrArg HasFunctorialCofiber.cofib (T.map_self 0))
    have hz : IsZero (HasFunctorialCofiber.cofib (𝟙 (T.stage 0))) :=
      (Triangle.mk _ _ _).isZero₃_of_isIso₁ (HasFunctorialCofiber.cofib_distinguished (𝟙 (T.stage 0))) (by change IsIso (𝟙 (T.stage 0)); infer_instance)
    have hz' : IsZero (T.layer s) := he.symm ▸ hz
    exact hz'.eq_of_tgt _ _
private theorem first_page_two (X : Spectrum) (p : ℤ×ℤ)
    (a : (model.classicalTower.tower X).FirstPage p) : a+a=0 := by
  have h := congrArg (fun f => a ≫ f) (layer_identity_two X p.1)
  simpa only [Preadditive.comp_add,Category.comp_id,comp_zero] using h
private theorem ambient_two (X : Spectrum) (p : ℤ×ℤ)
    (a : ((model.classical.obj X).ssData p).V) : a+a=0 := by
  apply (ModuleCat.mono_iff_injective ((model.classicalTower.sequence X).ambient p).hom).mp inferInstance
  simp only [map_add,map_zero]
  apply Subtype.ext
  exact first_page_two X p (((model.classicalTower.sequence X).ambient p).hom a).val
private theorem classical_page_two (X : Spectrum) (r : ℤ) (p : ℤ×ℤ)
    (a : (model.classical.obj X).Page r p) : a+a=0 := by
  let D := (model.classical.obj X).ssData p
  let j : WithTop ℕ := ↑(r-(model.classical.obj X).r₀).toNat
  haveI : Epi (D.pageπ j) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (D.pageπ j)).mp inferInstance a
  have hz : z+z=0 := by
    apply (ModuleCat.mono_iff_injective (D.Z j).arrow).mp inferInstance
    simpa only [map_add,map_zero] using ambient_two X p ((D.Z j).arrow z)
  rw [← map_add,hz,map_zero]

private theorem detects_neg {A : SyntheticObject} {i : Tridegree}
    {x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ i}
    {a : BiHom (i.2.1-i.1) i.2.2 (A.obj model.nu model.auxiliary)}
    (ha : Detects (model.convergence A) i x a) :
    Detects (model.convergence A) i (-x) (-a) := by
  obtain ⟨e, ⟨hr,z,hz,he⟩,a',ha',hga⟩ := ha
  refine ⟨-e,⟨hr,-z,?_,?_⟩,-a',?_,?_⟩
  · rw [map_neg,hz]
  · rw [map_neg,he]
  · rw [map_neg,ha']
  · rw [map_neg,map_neg,hga]
private theorem finite_target_neg (X : ClassicalObject) (q : ℕ) (s t : ℤ) (k : ℕ)
    (x : Ambient model X (s,t)) :
    -(finiteTargetLabel model X q s t k x) = finiteTargetLabel model X q s t k x := by
  have hx : -x=x := neg_eq_of_add_eq_zero_left (classical_page_two (X.obj model.auxiliary) 2 (s,t) x)
  have hneg : finiteTargetLabel model X q s t k (-x) = -(finiteTargetLabel model X q s t k x) := by
    have cast_neg (A B : ModuleCat ℤ) (h : A=B) (he : (A:Type)=(B:Type)) (z : A) :
        he.mp (-z) = -(he.mp z) := by
      subst B
      rfl
    simp only [finiteTargetLabel,targetNuLabel,map_neg]
    rw [cast_neg _ _ (by congr 2; simp),map_neg,map_neg]
  exact hneg.symm.trans (congrArg (finiteTargetLabel model X q s t k) hx)
private theorem finite_target_detects_neg (X : ClassicalObject) (q : ℕ) (s t : ℤ) (k : ℕ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x) a) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x) (-a) := by
  have h := detects_neg ha
  rw [finite_target_neg] at h
  exact h
private theorem finite_source_detects_neg (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (q : ℕ) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (((t-s)+s)-s) (t+normalizedExponent model.classicalTower f)
      ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary))
    (ha : Detects (model.convergence (.quotient q (extensionSourceObject model X Y f)))
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
      (finiteSourceForExtension model X Y f q s t x) a) :
    Detects (model.convergence (.quotient q (extensionSourceObject model X Y f)))
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
      (finiteSourceForExtension model X Y f q s t x) (-a) := by
  have hx : -x=x := neg_eq_of_add_eq_zero_left (classical_page_two (X.obj model.auxiliary) 2 (s,t) x)
  have hneg : finiteSourceForExtension model X Y f q s t (-x) =
      -(finiteSourceForExtension model X Y f q s t x) := by
    simp only [finiteSourceForExtension,finiteNuLabel,regradeE2,map_neg]
  have h := detects_neg ha
  rw [←hneg,hx] at h
  exact h

end
end KIP126.ProofTools.Internal.Mahowald
