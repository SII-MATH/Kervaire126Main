module

import all KIP126.Literature.Standard.FiniteQuotientPositive
import all KIP126.Literature.Standard.FiniteQuotientAdditivity

/-! Strict lambda annihilation and boundary comparison for finite-source rows.
The private construction retains the actual quotient maps and both structure
arrows; it consumes a row only after its first two arrows have been identified. -/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
set_option Elab.async false

universe u v

private theorem quotient_incl_precomp_injective_of_negative_hom
    {Syn : Type u} [SyntheticCategory.{u,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    (A Z : Syn) (q : ℕ)
    (hz : ∀ z : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶ Z,
      z=0) :
    Function.Injective (fun f : XModLambdaN A q ⟶ Z => XModLambdaN.incl A q ≫ f) := by
  intro f g hfg
  change XModLambdaN.incl A q ≫ f = XModLambdaN.incl A q ≫ g at hfg
  have hzero : XModLambdaN.incl A q ≫ (f-g)=0 := by
    rw [Preadditive.comp_sub,hfg,sub_self]
  obtain ⟨z,hz'⟩ := (XModLambdaN.cofiberTriangle A q).yoneda_exact₃
    (XModLambdaN.cofiberTriangle_distinguished A q) (f-g) hzero
  apply sub_eq_zero.mp
  rw [hz',hz z,comp_zero]

/-- The actual lambda power on the actual quotient vanishes whenever the
second shifted source of its mapped cofiber triangle has no Hom to it. -/
private theorem quotient_lambda_power_zero_of_double_negative_hom
    {Syn : Type u} [SyntheticCategory.{u,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    (A : Syn) (q : ℕ)
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-(q:ℤ))).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-(q:ℤ))).IsTriangulated]
    (hz : ∀ z : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj A))⟦(1:ℤ)⟧ ⟶
          XModLambdaN A q, z=0) :
    lambdaPow q (XModLambdaN A q)=0 := by
  let F := SyntheticCategory.biShift (Syn:=Syn) (0,-(q:ℤ))
  let T := XModLambdaN.cofiberTriangle A q
  have hT : T ∈ distTriang Syn := XModLambdaN.cofiberTriangle_distinguished A q
  have hzero : (F.mapTriangle.obj T).mor₂ ≫ lambdaPow q (XModLambdaN A q)=0 := by
    change F.map (XModLambdaN.incl A q) ≫ lambdaPow q (XModLambdaN A q)=0
    rw [lambdaPow_naturality,XModLambdaN.lambdaPow_comp_incl]
  obtain ⟨z,hz'⟩ := (F.mapTriangle.obj T).yoneda_exact₃
    (F.map_distinguished T hT) (lambdaPow q (XModLambdaN A q)) hzero
  rw [hz',hz z,comp_zero]

/-- Lambda annihilation of the finite target makes every literal map into
that target descend through the actual quotient inclusion, even for an
infinite source. -/
private theorem quotient_target_descent_of_lambda_zero
    {Syn : Type u} [SyntheticCategory.{u,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    (Z : Syn) (q : ℕ) (hZ : lambdaPow q Z=0) {B : Syn} (t : B ⟶ Z) :
    ∃ s : XModLambdaN B q ⟶ Z, t=XModLambdaN.incl B q ≫ s := by
  have ht : lambdaPow q B ≫ t=0 := by
    rw [←lambdaPow_naturality,hZ,comp_zero]
  exact (XModLambdaN.cofiberTriangle B q).yoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished B q) t ht

/-- Once the actual first two quotient arrows form a distinguished row and
the original triangle maps to it via actual inclusions, its tail is forced.
No identification of a target row or cone is given as a premise. -/
private theorem quotient_tail_eq_of_lambda_zero
    {Syn : Type u} [SyntheticCategory.{u,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    (Phi : LambdaQuotientFunctoriality (Syn:=Syn)) (q : ℕ)
    [(Phi.functor q).PreservesZeroMorphisms]
    (N : Triangle Syn) (hN : N ∈ distTriang Syn)
    (k0 : XModLambdaN N.obj₃ q ⟶ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧)
    (hR : Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q) k0 ∈
      distTriang Syn)
    (hinc : XModLambdaN.incl N.obj₃ q ≫ k0 =
      N.mor₃ ≫ (shiftFunctor Syn (1:ℤ)).map (XModLambdaN.incl N.obj₁ q))
    (esusp : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ≅
      (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧)
    (he : XModLambdaN.incl (N.obj₁⟦(1:ℤ)⟧) q ≫ esusp.hom =
      (shiftFunctor Syn (1:ℤ)).map (XModLambdaN.incl N.obj₁ q))
    (hlam : lambdaPow q (XModLambdaN N.obj₁ q)=0)
    (hneg : ∀ z : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₁)⟦(1:ℤ)⟧ ⟶
        XModLambdaN N.obj₁ q, z=0) :
    XModLambdaN.map N.mor₃ q ≫ esusp.hom = k0 := by
  let S := shiftFunctor Syn (1:ℤ)
  let Q := Phi.functor q
  let R := Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q) k0
  let k1 := XModLambdaN.map N.mor₃ q ≫ esusp.hom
  have hzero : R.mor₂ ≫ k1=0 := by
    change (Q.map N.mor₂) ≫ (Q.map N.mor₃ ≫ esusp.hom)=0
    rw [←Category.assoc,←Functor.map_comp,comp_distTriang_mor_zero₂₃ N hN,
      Functor.map_zero,zero_comp]
  obtain ⟨b,hb⟩ := R.yoneda_exact₃ hR k1 hzero
  change S.obj (XModLambdaN N.obj₁ q) ⟶ S.obj (XModLambdaN N.obj₁ q) at b
  change k1=k0≫b at hb
  have hinc1 : XModLambdaN.incl N.obj₃ q ≫ k1=N.mor₃≫S.map (XModLambdaN.incl N.obj₁ q) := by
    dsimp only [k1]
    rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,he]
  have hh : N.mor₃ ≫ (S.map (XModLambdaN.incl N.obj₁ q) ≫ (b-𝟙 _))=0 := by
    rw [←Category.assoc,←hinc,Preadditive.comp_sub,Category.comp_id,
      Category.assoc,←hb,hinc1,hinc,sub_self]
  obtain ⟨t,ht⟩ := N.rotate.yoneda_exact₃ (rot_of_distTriang N hN)
    (S.map (XModLambdaN.incl N.obj₁ q) ≫ (b-𝟙 _)) hh
  change S.obj N.obj₂ ⟶ S.obj (XModLambdaN N.obj₁ q) at t
  change S.map (XModLambdaN.incl N.obj₁ q) ≫ (b-𝟙 _) = (-S.map N.mor₁) ≫ t at ht
  let ff := Functor.FullyFaithful.ofFullyFaithful S
  let t0 : N.obj₂ ⟶ XModLambdaN N.obj₁ q := ff.preimage t
  have ht0 : S.map t0=t := ff.map_preimage t
  obtain ⟨s,hs⟩ := quotient_target_descent_of_lambda_zero _ q hlam t0
  have ht' : t=S.map (XModLambdaN.incl N.obj₂ q) ≫ S.map s := by
    rw [←ht0,hs,Functor.map_comp]
  have hcomm : S.map N.mor₁ ≫ S.map (XModLambdaN.incl N.obj₂ q) =
      S.map (XModLambdaN.incl N.obj₁ q) ≫ S.map (XModLambdaN.map N.mor₁ q) := by
    rw [←Functor.map_comp,←Functor.map_comp,XModLambdaN.incl_naturality]
  have ht'' : S.map (XModLambdaN.incl N.obj₁ q) ≫ (b-𝟙 _) =
      S.map (XModLambdaN.incl N.obj₁ q) ≫
        (-(S.map (XModLambdaN.map N.mor₁ q) ≫ S.map s)) := by
    rw [ht,ht',←Category.assoc,Preadditive.neg_comp,hcomm]
    simp only [Preadditive.neg_comp,Preadditive.comp_neg,Category.assoc]
  let d := -(S.map (XModLambdaN.map N.mor₁ q) ≫ S.map s)
  let b0 := ff.preimage (b-𝟙 _)
  let d0 := ff.preimage d
  have hb0 : S.map b0=b-𝟙 _ := ff.map_preimage _
  have hd0 : S.map d0=d := ff.map_preimage _
  have hpre : XModLambdaN.incl N.obj₁ q ≫ b0 = XModLambdaN.incl N.obj₁ q ≫ d0 := by
    apply ff.map_injective
    rw [Functor.map_comp,Functor.map_comp,hb0,hd0]
    exact ht''
  have hbd : b-𝟙 _=d := by
    have h := quotient_incl_precomp_injective_of_negative_hom
      N.obj₁ (XModLambdaN N.obj₁ q) q hneg hpre
    exact hb0.symm.trans ((congrArg S.map h).trans hd0)
  have hk : k0≫d=0 := by
    have hr := comp_distTriang_mor_zero₃₁ R hR
    change k0≫S.map (XModLambdaN.map N.mor₁ q)=0 at hr
    dsimp only [d]
    rw [Preadditive.comp_neg,←Category.assoc,hr,zero_comp,neg_zero]
  have hkb : k0≫b=k0 := by
    have h := congrArg (fun z => k0≫z) hbd
    rw [Preadditive.comp_sub,Category.comp_id,hk,sub_eq_zero] at h
    exact h
  exact hb.trans hkb

/-- Shift the whole source and target of the actual negative-Hom assertion.
The comparison is obtained from the proved quotient/shift construction;
only the stored exact-shift structure is used for ordinary suspension. -/
private theorem quotient_self_negative_hom_bishift
    (V : SyntheticSpectrum) (p : ℤ × ℤ) (q r : ℕ)
    (hbase : ∀ b : ((SyntheticCategory.biShift (0,-(r:ℤ))).obj V)⟦(1:ℤ)⟧ ⟶
      XModLambdaN V q, b=0)
    (b : ((SyntheticCategory.biShift (0,-(r:ℤ))).obj
      ((SyntheticCategory.biShift p).obj V))⟦(1:ℤ)⟧ ⟶
      XModLambdaN ((SyntheticCategory.biShift p).obj V) q) : b=0 := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) p
  let d : ℤ × ℤ := (0,-(r:ℤ))
  letI : F.Additive := model.exactness.shiftAdditive p
  letI : F.CommShift ℤ := model.exactness.shiftCommShift p
  letI : F.IsTriangulated := model.exactness.shiftExact p
  obtain ⟨eQ,_⟩ := finite_quotient_shift_comparison model.quotients.coherence p q V
  let e0 : (SyntheticCategory.biShift d).obj (F.obj V) ≅
      F.obj ((SyntheticCategory.biShift d).obj V) :=
    (biShiftAddIso p d (p+d) rfl).app V ≪≫
      ((biShiftAddIso d p (p+d) (add_comm _ _)).app V).symm
  let eS := (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso e0 ≪≫
    ((F.commShiftIso (1:ℤ)).app ((SyntheticCategory.biShift d).obj V)).symm
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) p
  let b0 := ff.preimage (eS.inv≫b≫eQ.hom)
  have hb0 : F.map b0=eS.inv≫b≫eQ.hom := ff.map_preimage _
  have hb0zero : b0=0 := hbase b0
  have hzero : eS.inv≫b≫eQ.hom=0 := by
    rw [←hb0,hb0zero,Functor.map_zero]
  apply (cancel_epi eS.inv).mp
  apply (cancel_mono eQ.hom).mp
  simpa only [Category.assoc,comp_zero,zero_comp] using hzero

private theorem quotient_self_negative_hom_base
    (X : ClassicalObject) (hX : X=.sphere ∨ X=.nuCofiber)
    (q r : ℕ) (hq : 0<q) (hr : q≤r)
    (b : ((SyntheticCategory.biShift (0,-(r:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧ ⟶
      XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) : b=0 := by
  rcases hX with rfl | rfl
  · let V := model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)
    let eV : V ≅ Smn (Syn:=SyntheticSpectrum) 0 0 :=
      model.nu.unitIso ≪≫ SyntheticCategory.biShift_zero.symm.app S_0_0
    let e0 : (SyntheticCategory.biShift (0,-(r:ℤ))).obj V ≅ Smn 0 (-(r:ℤ)) :=
      (SyntheticCategory.biShift (0,-(r:ℤ))).mapIso eV ≪≫
        (biShiftAddIso (0,0) (0,-(r:ℤ)) (0,-(r:ℤ)) (by ext <;> simp)).app S_0_0
    let e := (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso e0 ≪≫
      positive_sphere_suspension_iso 0 (-(r:ℤ))
    exact negative_hom_finite_sphere_iso .sphere q hq 1 (-(r:ℤ)) (by omega) e b
  · exact negative_hom_shifted_nu_cofiber_finite .nuCofiber q hq 0 (-(r:ℤ))
      (by omega) b

private theorem quotient_self_negative_hom_shifted_finite
    (X : ClassicalObject) (hX : X=.sphere ∨ X=.nuCofiber)
    (p : ℤ × ℤ) (q r : ℕ) (hq : 0<q) (hr : q≤r)
    (b : ((SyntheticCategory.biShift (0,-(r:ℤ))).obj
      ((SyntheticCategory.biShift p).obj
        (model.nu.functor.obj (X.obj model.auxiliary))))⟦(1:ℤ)⟧ ⟶
      XModLambdaN ((SyntheticCategory.biShift p).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q) : b=0 := by
  exact quotient_self_negative_hom_bishift _ p q r
    (quotient_self_negative_hom_base X hX q r hq hr) b

private theorem quotient_self_negative_hom_of_iso
    {A B : SyntheticSpectrum} (e : A ≅ B) (q r : ℕ)
    (hB : ∀ b : ((SyntheticCategory.biShift (0,-(r:ℤ))).obj B)⟦(1:ℤ)⟧ ⟶
      XModLambdaN B q, b=0)
    (b : ((SyntheticCategory.biShift (0,-(r:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶
      XModLambdaN A q) : b=0 := by
  let eS := (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
    ((SyntheticCategory.biShift (0,-(r:ℤ))).mapIso e)
  let eQ := (model.quotients.functoriality.functor q).mapIso e
  have hzero : eS.inv≫b≫eQ.hom=0 := hB _
  apply (cancel_epi eS.inv).mp
  apply (cancel_mono eQ.hom).mp
  simpa only [Category.assoc,comp_zero,zero_comp] using hzero

/-- In particular, the actual lambda^q action is strictly zero on a finite
sphere/Cnu quotient, after any bigraded shift and source isomorphism. -/
private theorem quotient_lambda_power_zero_finite_source
    {A : SyntheticSpectrum} (X : ClassicalObject) (hX : X=.sphere ∨ X=.nuCofiber)
    (p : ℤ × ℤ) (e : A ≅ (SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (q : ℕ) (hq : 0<q) :
    lambdaPow q (XModLambdaN A q)=0 := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  letI : F.CommShift ℤ := model.exactness.shiftCommShift (0,-(q:ℤ))
  letI : F.IsTriangulated := model.exactness.shiftExact (0,-(q:ℤ))
  apply quotient_lambda_power_zero_of_double_negative_hom A q
  intro z
  let e2 : F.obj (F.obj A) ≅ (SyntheticCategory.biShift (0,-((2*q:ℕ):ℤ))).obj A :=
    (biShiftAddIso (0,-(q:ℤ)) (0,-(q:ℤ)) (0,-((2*q:ℕ):ℤ)) (by ext <;> simp; omega)).app A
  have hzero : ((shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso e2).inv≫z=0 :=
    quotient_self_negative_hom_of_iso e q (2*q)
      (quotient_self_negative_hom_shifted_finite X hX p q (2*q) hq (by omega)) _
  exact (cancel_epi ((shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso e2).inv).mp
    (by simpa only [comp_zero] using hzero)

/-- Actual finite-source specialization of the tail criterion. The finite
source is supplied as an object isomorphism, not a caller's desired row. -/
private theorem quotient_tail_eq_finite_source
    (N : Triangle SyntheticSpectrum) (hN : N ∈ distTriang SyntheticSpectrum)
    (X : ClassicalObject) (hX : X=.sphere ∨ X=.nuCofiber)
    (p : ℤ × ℤ) (e : N.obj₁ ≅ (SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (q : ℕ) (hq : 0<q)
    (k0 : XModLambdaN N.obj₃ q ⟶ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧)
    (hR : Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q) k0 ∈
      distTriang SyntheticSpectrum)
    (hinc : XModLambdaN.incl N.obj₃ q ≫ k0 =
      N.mor₃ ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₁ q))
    (esusp : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧)
    (he : XModLambdaN.incl (N.obj₁⟦(1:ℤ)⟧) q ≫ esusp.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₁ q)) :
    XModLambdaN.map N.mor₃ q ≫ esusp.hom = k0 := by
  let Q := model.quotients.functoriality.functor q
  letI : Q.Additive := KIP126.Literature.Standard.Internal.quotient_additive q
  apply quotient_tail_eq_of_lambda_zero model.quotients.functoriality q N hN k0 hR hinc esusp he
  · exact quotient_lambda_power_zero_finite_source X hX p e q hq
  · exact quotient_self_negative_hom_of_iso e q q
      (quotient_self_negative_hom_shifted_finite X hX p q q hq le_rfl)


end
end KIP126.Literature.Standard
