module
import all KIP126.Literature.Standard.FiniteQuotientAdditivity
import all KIP126.Literature.Standard.FiniteQuotientTriangle
import all KIP126.Literature.Standard.FiniteQuotientRowCriterion
import all KIP126.Literature.Standard.FiniteQuotientRows
import all KIP126.Literature.Standard.FiniteQuotientPositive

/-! Direct construction into the same fixed quotient vertex.
No target-row distinguishedness or target cone isomorphism is assumed.
The two endpoint equations in the adjustment lemma are retained explicitly;
this file does not assert their automatic satisfaction. -/

@[expose] section
namespace KIP126.Literature.Standard.Internal
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Kervaire.Route KIP126.Literature
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000
set_option Elab.async false

/-- There is an actual comparison map from the chosen cone of the selected
Q(g) into the desired fixed Q(ΣX) vertex, preserving the displayed inclusion.
Its signed boundary defect is retained on the same map. -/
private theorem fixed_cone_map_with_signed_boundary_defect
    (N : Triangle SyntheticSpectrum) (hN : N ∈ distTriang SyntheticSpectrum)
    (q : ℕ) :
    ∃ (esusp : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅
        (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧)
      (v : HasFunctorialCofiber.cofib (XModLambdaN.map N.mor₂ q) ⟶
        XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q)
      (z : (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧ ⟶ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧),
      XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q≫esusp.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) ∧
      HasFunctorialCofiber.cofibι (XModLambdaN.map N.mor₂ q)≫v=
        XModLambdaN.map N.mor₃ q ∧
      v≫(-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫
        esusp.hom))-HasFunctorialCofiber.cofibδ (XModLambdaN.map N.mor₂ q)=
          HasFunctorialCofiber.cofibδ (XModLambdaN.map N.mor₂ q)≫z := by
  let Q := model.quotients.functoriality.functor q
  letI : Q.Additive := quotient_additive q
  let g := XModLambdaN.map N.mor₂ q
  let h := XModLambdaN.map N.mor₃ q
  have hgh : g≫h=0 := by
    change Q.map N.mor₂≫Q.map N.mor₃=0
    rw [←Functor.map_comp,comp_distTriang_mor_zero₂₃ N hN,Functor.map_zero]
  let K := Triangle.mk g (HasFunctorialCofiber.cofibι g) (HasFunctorialCofiber.cofibδ g)
  have hK : K ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished g
  obtain ⟨v,hv⟩ := K.yoneda_exact₂ hK h hgh
  change HasFunctorialCofiber.cofib g ⟶ XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q at v
  change h=HasFunctorialCofiber.cofibι g≫v at hv
  obtain ⟨esusp,hesusp⟩ := finite_quotient_suspension_comparison q N.obj₂
  let k := -(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫esusp.hom)
  have hhk : h≫k=0 := by
    dsimp only [h,k]
    rw [Preadditive.comp_neg,←Category.assoc,←model.quotients.functoriality.map_comp,
      comp_distTriang_mor_zero₃₁ N hN]
    change -(Q.map (0 : N.obj₃ ⟶ N.obj₂⟦(1:ℤ)⟧)≫esusp.hom)=0
    rw [Functor.map_zero,zero_comp,neg_zero]
  have hcone : HasFunctorialCofiber.cofibι g≫HasFunctorialCofiber.cofibδ g=0 :=
    comp_distTriang_mor_zero₂₃ K hK
  have hdefect : HasFunctorialCofiber.cofibι g≫(v≫k-HasFunctorialCofiber.cofibδ g)=0 := by
    rw [Preadditive.comp_sub,←Category.assoc,←hv,hhk,
      hcone,sub_self]
  obtain ⟨z,hz⟩ := K.yoneda_exact₃ hK (v≫k-HasFunctorialCofiber.cofibδ g) hdefect
  exact ⟨esusp,v,z,hesusp,hv.symm,hz⟩

/-- A lawful identity shear is a genuine triangle automorphism; no
vanishing-on-spheres inference or nilpotence premise is used. -/
private theorem triangle_identity_shear_isIso
    {C : Type u} [StableHomotopyCategory.{u,v} C]
    (T : Triangle C) (hT : T ∈ distTriang C) (z : T.obj₃ ⟶ T.obj₃)
    (hleft : T.mor₂≫z=0) (hright : z≫T.mor₃=0) : IsIso (𝟙 T.obj₃+z) := by
  let φ : T ⟶ T :=
    { hom₁ := 𝟙 _
      hom₂ := 𝟙 _
      hom₃ := 𝟙 _+z
      comm₁ := by simp
      comm₂ := by rw [Preadditive.comp_add,Category.comp_id,hleft,add_zero,Category.id_comp]
      comm₃ := by rw [CategoryTheory.Functor.map_id,Category.comp_id,Preadditive.add_comp,
        Category.id_comp,hright,add_zero] }
  exact isIso₃_of_isIso₁₂ φ hT hT (by dsimp [φ]; infer_instance) (by dsimp [φ]; infer_instance)

private theorem quotient_suspension_shear_isIso (Y : SyntheticSpectrum) (q : ℕ)
    (z : (XModLambdaN Y q)⟦(1:ℤ)⟧ ⟶ (XModLambdaN Y q)⟦(1:ℤ)⟧)
    (hi : (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl Y q)≫z=0)
    (hp : z≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.proj Y q)=0) :
    IsIso (𝟙 _+z) := by
  let T₀ := XModLambdaN.cofiberTriangle Y q
  let T := T₀.rotate.rotate.rotate
  have hT : T ∈ distTriang SyntheticSpectrum :=
    rot_of_distTriang _ (rot_of_distTriang _ (rot_of_distTriang _
      (XModLambdaN.cofiberTriangle_distinguished Y q)))
  have hl : T.mor₂≫z=0 := by
    change (-(shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (XModLambdaN.incl Y q))≫z=0
    rw [Preadditive.neg_comp,hi,neg_zero]
  have hr : z≫T.mor₃=0 := by
    change z≫(-(shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (XModLambdaN.proj Y q))=0
    rw [Preadditive.comp_neg,hp,neg_zero]
  exact triangle_identity_shear_isIso T hT z hl hr

/-- If the retained defect has both actual absolute-quotient endpoint squares,
its boundary error can be absorbed into the same inclusion-compatible
suspension comparison. This does not assert that the cone map is invertible. -/
private theorem signed_boundary_defect_absorbed
    (N : Triangle SyntheticSpectrum) (q : ℕ)
    (esusp : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅
      (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧)
    (v : HasFunctorialCofiber.cofib (XModLambdaN.map N.mor₂ q) ⟶
      XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q)
    (z : (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧ ⟶
      (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧)
    (he : XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q≫esusp.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q))
    (hz : v≫(-(XModLambdaN.map
        ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫esusp.hom))-
      HasFunctorialCofiber.cofibδ (XModLambdaN.map N.mor₂ q)=
        HasFunctorialCofiber.cofibδ (XModLambdaN.map N.mor₂ q)≫z)
    (hi : (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (XModLambdaN.incl N.obj₂ q)≫z=0)
    (hp : z≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (XModLambdaN.proj N.obj₂ q)=0) :
    ∃ esusp' : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅
        (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q≫esusp'.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) ∧
      v≫(-(XModLambdaN.map
        ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫esusp'.hom))=
          HasFunctorialCofiber.cofibδ (XModLambdaN.map N.mor₂ q) := by
  let α := 𝟙 ((XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧)+z
  letI : IsIso α := quotient_suspension_shear_isIso N.obj₂ q z hi hp
  let β := asIso α
  let e' := esusp ≪≫ β.symm
  have hiα : (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (XModLambdaN.incl N.obj₂ q)≫α=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) := by
    dsimp only [α]
    rw [Preadditive.comp_add,Category.comp_id,hi,add_zero]
  have hiβ : (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (XModLambdaN.incl N.obj₂ q)≫β.inv=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) := by
    apply (cancel_mono β.hom).mp
    rw [Category.assoc,β.inv_hom_id,Category.comp_id]
    exact hiα.symm
  refine ⟨e',?_,?_⟩
  · change XModLambdaN.incl _ q≫esusp.hom≫β.inv=_
    rw [←Category.assoc,he,hiβ]
  · let k := -(XModLambdaN.map
      ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫esusp.hom)
    let δ := HasFunctorialCofiber.cofibδ (XModLambdaN.map N.mor₂ q)
    have hv : v≫k=δ≫α := by
      change v≫k-δ=δ≫z at hz
      rw [show α=𝟙 _+z from rfl,Preadditive.comp_add,Category.comp_id]
      exact (sub_eq_iff_eq_add.mp hz).trans (add_comm _ _)
    change v≫(-(XModLambdaN.map _ q≫esusp.hom≫β.inv))=δ
    rw [←Category.assoc,←Preadditive.neg_comp,←Category.assoc,hv]
    change (δ≫β.hom)≫β.inv=δ
    rw [Category.assoc,β.hom_inv_id,Category.comp_id]

/-- The actual admissible gauge family keeps the selected cone inclusion and
its signed boundary defect on the same morphism. -/
private theorem cone_defect_gauge
    {C : Type u} [StableHomotopyCategory.{u,v} C]
    (T : Triangle C) (hT : T ∈ distTriang C) {D : C}
    (v : T.obj₃ ⟶ D) (k : D ⟶ T.obj₁⟦(1:ℤ)⟧)
    (z : T.obj₁⟦(1:ℤ)⟧ ⟶ T.obj₁⟦(1:ℤ)⟧)
    (hz : v≫k-T.mor₃=T.mor₃≫z)
    (t : T.obj₁⟦(1:ℤ)⟧ ⟶ D)
    (u : T.obj₂⟦(1:ℤ)⟧ ⟶ T.obj₁⟦(1:ℤ)⟧) :
    T.mor₂≫(v+T.mor₃≫t)=T.mor₂≫v ∧
    (v+T.mor₃≫t)≫k-T.mor₃=
      T.mor₃≫(z+t≫k+(shiftFunctor C (1:ℤ)).map T.mor₁≫u) := by
  constructor
  · rw [Preadditive.comp_add,←Category.assoc,
      comp_distTriang_mor_zero₂₃ T hT,zero_comp,add_zero]
  · have hzero : T.mor₃≫((shiftFunctor C (1:ℤ)).map T.mor₁≫u)=0 := by
      rw [←Category.assoc,comp_distTriang_mor_zero₃₁ T hT,zero_comp]
    rw [Preadditive.comp_add,hzero,add_zero,Preadditive.comp_add,
      Preadditive.add_comp,Category.assoc]
    rw [show v≫k+T.mor₃≫t≫k-T.mor₃=(v≫k-T.mor₃)+T.mor₃≫t≫k by abel]
    rw [hz]


/-- A map from the actual negatively weighted nu-sphere into the same
nu-sphere has an actual factor through its specified lambda power. -/
private theorem finite_sphere_lambda_factorization (q : ℕ) (hq : 0<q)
    (l : (SyntheticCategory.biShift (0,-(q:ℤ))).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) ⟶
      model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) :
    ∃ a : (SyntheticCategory.biShift (0,-(q:ℤ))).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)) ⟶
      (SyntheticCategory.biShift (0,-(q:ℤ))).obj
        (model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)),
      l=a≫lambdaPow q _ := by
  let C := model.nu.functor.obj (ClassicalObject.sphere.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let e : F.obj C ≅ Smn (Syn:=SyntheticSpectrum) 0 (-(q:ℤ)) :=
    F.mapIso model.nu.unitIso
  have hz : l≫XModLambdaN.incl C q=0 := by
    have he : e.inv≫(l≫XModLambdaN.incl C q)=0 :=
      negative_hom_finite_sphere .sphere q hq 0 (-(q:ℤ)) (by omega) _
    exact (cancel_epi e.inv).mp (by simpa only [comp_zero] using he)
  exact (XModLambdaN.cofiberTriangle C q).coyoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished C q) l hz

/-- The same genuine post-lambda division holds on nu Cnu. The source
is recognized by its actual two-cell triangle, not by sphere generation. -/
private theorem finite_nu_cofiber_lambda_factorization (q : ℕ) (hq : 0<q)
    (l : (SyntheticCategory.biShift (0,-(q:ℤ))).obj
        (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)) ⟶
      model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)) :
    ∃ a : (SyntheticCategory.biShift (0,-(q:ℤ))).obj
        (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)) ⟶
      (SyntheticCategory.biShift (0,-(q:ℤ))).obj
        (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)),
      l=a≫lambdaPow q _ := by
  let C := model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let e : ((SyntheticCategory.biShift (-1,-(q:ℤ))).obj C)⟦(1:ℤ)⟧ ≅ F.obj C :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (biShiftAddIso (-1,-(q:ℤ)) (1,0) (0,-(q:ℤ)) (by ext <;> simp)).app C
  have hz : l≫XModLambdaN.incl C q=0 := by
    have he : e.hom≫(l≫XModLambdaN.incl C q)=0 :=
      negative_hom_shifted_nu_cofiber_finite .nuCofiber q hq (-1) (-(q:ℤ)) (by omega) _
    exact (cancel_epi e.hom).mp (by simpa only [comp_zero] using he)
  exact (XModLambdaN.cofiberTriangle C q).coyoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished C q) l hz

/-- The finite-source nilpotence argument only needs the square of the
reverse composite to vanish. The displayed inverse is literal. -/
private theorem one_add_composite_isIso_of_reverse_square_zero
    {C : Type u} [Category.{v} C] [Preadditive C]
    {A B : C} (f : A ⟶ B) (g : B ⟶ A)
    (h : (g≫f)≫(g≫f)=0) : IsIso (𝟙 A+f≫g) := by
  let x := f≫g
  have hx : (x≫x)≫x=0 := by
    calc
      _ = f≫((g≫f)≫(g≫f))≫g := by simp only [x,Category.assoc]
      _ = 0 := by rw [h,zero_comp,comp_zero]
  have hx' : x≫(x≫x)=0 := by simpa only [Category.assoc] using hx
  refine ⟨𝟙 A-x+x≫x,?_,?_⟩
  · change (𝟙 A+x)≫(𝟙 A-x+x≫x)=𝟙 A
    simp only [Preadditive.add_comp,Preadditive.comp_add,Preadditive.comp_sub,
      Category.id_comp,Category.comp_id,hx']
    abel
  · change (𝟙 A-x+x≫x)≫(𝟙 A+x)=𝟙 A
    simp only [Preadditive.add_comp,Preadditive.sub_comp,Preadditive.comp_add,
      Category.id_comp,Category.comp_id,hx]
    abel

private theorem finite_source_second_arrow_common_shear
    (N : Triangle SyntheticSpectrum) (hN : N ∈ distTriang SyntheticSpectrum)
    (q : ℕ)
    (v : XModLambdaN N.obj₂ q ⟶ XModLambdaN N.obj₃ q)
    (hι : XModLambdaN.incl N.obj₂ q≫v=N.mor₂≫XModLambdaN.incl N.obj₃ q)
    (hδ : v≫XModLambdaN.proj N.obj₃ q=XModLambdaN.proj N.obj₂ q≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(q:ℤ))).map N.mor₂))
    (hz : ∀ r : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₁)⟦(1:ℤ)⟧ ⟶
      XModLambdaN N.obj₃ q, r=0) :
    ∃ a : XModLambdaN N.obj₃ q ⟶ XModLambdaN N.obj₃ q,
      XModLambdaN.incl N.obj₃ q≫a=0 ∧
      v-XModLambdaN.map N.mor₂ q=XModLambdaN.map N.mor₂ q≫a ∧
      v-XModLambdaN.map N.mor₂ q=v≫a := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  letI : F.Additive := model.exactness.shiftAdditive (0,-(q:ℤ))
  letI : F.CommShift ℤ := model.exactness.shiftCommShift (0,-(q:ℤ))
  letI : F.IsTriangulated := model.exactness.shiftExact (0,-(q:ℤ))
  obtain ⟨z,hzv⟩ := finite_quotient_map_difference_factors N.mor₂ q v hι
  let T := (F.mapTriangle.obj N)⟦(1:ℤ)⟧
  have hT : T ∈ distTriang SyntheticSpectrum :=
    Triangle.shift_distinguished _ (F.map_distinguished N hN) 1
  have hz0 : T.mor₁≫z=0 := hz _
  obtain ⟨w,hw⟩ := T.yoneda_exact₂ hT z hz0
  let zC := -w
  have hzw : z=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (F.map N.mor₂)≫zC := by
    change z=((1:ℤ).negOnePow • (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (F.map N.mor₂))≫w at hw
    simpa only [Int.negOnePow_one,Units.neg_smul,one_smul,Preadditive.neg_comp,
      Preadditive.comp_neg,zC] using hw
  refine ⟨XModLambdaN.proj N.obj₃ q≫zC,?_,?_,?_⟩
  · rw [←Category.assoc,XModLambdaN.incl_comp_proj,zero_comp]
  · rw [hzv,hzw,←Category.assoc,←XModLambdaN.proj_naturality,Category.assoc]
  · rw [hzv,hzw,←Category.assoc,←hδ,Category.assoc]

private theorem common_shear_square_factors_through_tail
    (R : Triangle SyntheticSpectrum) (hR : R ∈ distTriang SyntheticSpectrum)
    (g : R.obj₂ ⟶ R.obj₃) (a : R.obj₃ ⟶ R.obj₃)
    (ha : R.mor₂-g=g≫a) (ha' : R.mor₂-g=R.mor₂≫a) :
    ∃ t : R.obj₁⟦(1:ℤ)⟧ ⟶ R.obj₃, a≫a=R.mor₃≫t := by
  have hea : (R.mor₂-g)≫a=0 := by
    rw [Preadditive.sub_comp,←ha',←ha,sub_self]
  have hzero : R.mor₂≫(a≫a)=0 := by
    rw [←Category.assoc,←ha',hea]
  exact R.yoneda_exact₃ hR (a≫a) hzero

end
end KIP126.Literature.Standard.Internal
