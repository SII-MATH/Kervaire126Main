module
import all KIP126.Literature.Standard.FiniteQuotientRecognition
import all KIP126.Literature.Standard.FiniteQuotientCone
import all KIP126.Literature.Standard.FiniteQuotientGhosts
import all KIP126.Literature.Standard.FiniteQuotientNoReturn
import all KIP126.Literature.Standard.FiniteQuotientTail
import all KIP126.Literature.Standard.FiniteQuotientSuspension

/-! Actual three-octahedron constructions and finite-source corrections
on the existing selected lambda quotients. No exactness of the selected
quotient functor or substitute Mahowald theorem is assumed. -/

@[expose] section
namespace KIP126.Literature.Standard.Internal
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Kervaire.Route KIP126.Literature
open GhostResearch
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
set_option Elab.async false
section GoodFoundation
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] [IsTriangulated C]
/-- Three actual octahedra deliver the good filling and its complementary
distinguished triangle directly on N.obj3 and F(N.obj3). -/
private theorem good_fill_complementary_row
    (F : C ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
    (alpha : F ⟶ 𝟭 C) (N : Triangle C) (hN : N ∈ distTriang C) :
    ∃ (u : HasFunctorialCofiber.cofib (alpha.app N.obj₁) ⟶
        HasFunctorialCofiber.cofib (alpha.app N.obj₂))
      (l : F.obj N.obj₃ ⟶ N.obj₃)
      (v : N.obj₃ ⟶ HasFunctorialCofiber.cofib u)
      (w : HasFunctorialCofiber.cofib u ⟶ (F.obj N.obj₃)⟦(1:ℤ)⟧),
      HasFunctorialCofiber.cofibι (alpha.app N.obj₁) ≫ u =
        N.mor₁ ≫ HasFunctorialCofiber.cofibι (alpha.app N.obj₂) ∧
      u ≫ HasFunctorialCofiber.cofibδ (alpha.app N.obj₂) =
        HasFunctorialCofiber.cofibδ (alpha.app N.obj₁) ≫
          (shiftFunctor C (1:ℤ)).map (F.map N.mor₁) ∧
      F.map N.mor₂ ≫ l = alpha.app N.obj₂ ≫ N.mor₂ ∧
      l ≫ N.mor₃ = (F.map N.mor₃ ≫ (F.commShiftIso (1:ℤ)).hom.app N.obj₁) ≫
        (shiftFunctor C (1:ℤ)).map (alpha.app N.obj₁) ∧
      N.mor₂ ≫ v = HasFunctorialCofiber.cofibι (alpha.app N.obj₂) ≫
        HasFunctorialCofiber.cofibι u ∧
      v ≫ HasFunctorialCofiber.cofibδ u = N.mor₃ ≫
        (shiftFunctor C (1:ℤ)).map (HasFunctorialCofiber.cofibι (alpha.app N.obj₁)) ∧
      HasFunctorialCofiber.cofibι u ≫ w =
        HasFunctorialCofiber.cofibδ (alpha.app N.obj₂) ≫
          (shiftFunctor C (1:ℤ)).map (F.map N.mor₂) ∧
      Triangle.mk v w (-(shiftFunctor C (1:ℤ)).map l) ∈ distTriang C := by
  let c := alpha.app N.obj₁ ≫ N.mor₁
  let NF := F.mapTriangle.obj N
  have hNF : NF ∈ distTriang C := F.map_distinguished N hN
  let O := Triangulated.someOctahedron rfl
    (HasFunctorialCofiber.cofib_distinguished (alpha.app N.obj₁)) hN
    (HasFunctorialCofiber.cofib_distinguished c)
  have hSquare : F.map N.mor₁ ≫ alpha.app N.obj₂ = c := alpha.naturality N.mor₁
  let O' := Triangulated.someOctahedron hSquare hNF
    (HasFunctorialCofiber.cofib_distinguished (alpha.app N.obj₂))
    (HasFunctorialCofiber.cofib_distinguished c)
  let u := O.m₁ ≫ O'.m₃
  let l := O'.m₁ ≫ O.m₃
  let O'' := Triangulated.someOctahedron rfl O.mem
    (rot_of_distTriang O'.triangle O'.mem)
    (HasFunctorialCofiber.cofib_distinguished u)
  refine ⟨u,l,O''.m₁,O''.m₃,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [u]
    rw [← Category.assoc,O.comm₁,Category.assoc,O'.comm₃]
  · dsimp [u]
    rw [Category.assoc,← O'.comm₄,← Category.assoc,O.comm₂]
  · dsimp [l]
    rw [← Category.assoc,O'.comm₁,Category.assoc,O.comm₃]
  · dsimp [l]
    rw [Category.assoc,← O.comm₄,← Category.assoc,O'.comm₂]
  · calc
      _ = (HasFunctorialCofiber.cofibι c ≫ O.m₃) ≫ O''.m₁ := by rw [O.comm₃]
      _ = _ := by
        rw [Category.assoc,O''.comm₁]
        change HasFunctorialCofiber.cofibι c ≫ O'.m₃ ≫ _ = _
        rw [← Category.assoc,O'.comm₃]
  · exact O''.comm₂
  · exact O''.comm₃
  · simpa only [Triangulated.Octahedron.triangle,Triangle.rotate,Triangle.mk,
      Preadditive.neg_comp,← Functor.map_comp] using O''.mem

/-- The complete actual good-three-by-three schema, with the bottom's third
object equal to the chosen cofiber of the same delivered l. -/
private theorem good_fill_chosen_cofiber_row
    (F : C ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
    (alpha : F ⟶ 𝟭 C) (N : Triangle C) (hN : N ∈ distTriang C) :
    ∃ (u : HasFunctorialCofiber.cofib (alpha.app N.obj₁) ⟶
        HasFunctorialCofiber.cofib (alpha.app N.obj₂))
      (l : F.obj N.obj₃ ⟶ N.obj₃)
      (j : HasFunctorialCofiber.cofib (alpha.app N.obj₂) ⟶
        HasFunctorialCofiber.cofib l)
      (k : HasFunctorialCofiber.cofib l ⟶
        (HasFunctorialCofiber.cofib (alpha.app N.obj₁))⟦(1:ℤ)⟧),
      HasFunctorialCofiber.cofibι (alpha.app N.obj₁) ≫ u =
        N.mor₁ ≫ HasFunctorialCofiber.cofibι (alpha.app N.obj₂) ∧
      u ≫ HasFunctorialCofiber.cofibδ (alpha.app N.obj₂) =
        HasFunctorialCofiber.cofibδ (alpha.app N.obj₁) ≫
          (shiftFunctor C (1:ℤ)).map (F.map N.mor₁) ∧
      F.map N.mor₂ ≫ l = alpha.app N.obj₂ ≫ N.mor₂ ∧
      l ≫ N.mor₃ = (F.map N.mor₃ ≫ (F.commShiftIso (1:ℤ)).hom.app N.obj₁) ≫
        (shiftFunctor C (1:ℤ)).map (alpha.app N.obj₁) ∧
      Triangle.mk u j k ∈ distTriang C ∧
      HasFunctorialCofiber.cofibι (alpha.app N.obj₂) ≫ j =
        N.mor₂ ≫ HasFunctorialCofiber.cofibι l ∧
      j ≫ HasFunctorialCofiber.cofibδ l =
        HasFunctorialCofiber.cofibδ (alpha.app N.obj₂) ≫
          (shiftFunctor C (1:ℤ)).map (F.map N.mor₂) ∧
      HasFunctorialCofiber.cofibι l ≫ k = N.mor₃ ≫
        (shiftFunctor C (1:ℤ)).map (HasFunctorialCofiber.cofibι (alpha.app N.obj₁)) := by
  obtain ⟨u,l,v,w,huι,huδ,hlι,hlδ,hvι,hvδ,hwι,hrot⟩ :=
    good_fill_complementary_row F alpha N hN
  let L := Triangle.mk l v w
  have hL : L ∈ distTriang C := (rotate_distinguished_triangle L).mpr hrot
  let K := Triangle.mk l (HasFunctorialCofiber.cofibι l) (HasFunctorialCofiber.cofibδ l)
  have hK : K ∈ distTriang C := HasFunctorialCofiber.cofib_distinguished l
  let E := isoTriangleOfIso₁₂ L K hL hK (Iso.refl _) (Iso.refl _) (by simp [L,K])
  let e := Triangle.π₃.mapIso E
  have heι : v ≫ e.hom = HasFunctorialCofiber.cofibι l := by
    have he := E.hom.comm₂
    change v ≫ E.hom.hom₃ = E.hom.hom₂ ≫ HasFunctorialCofiber.cofibι l at he
    change v ≫ E.hom.hom₃ = HasFunctorialCofiber.cofibι l
    simpa only [E,isoTriangleOfIso₁₂_hom_hom₂,Iso.refl_hom,Category.id_comp] using he
  have heδ : e.hom ≫ HasFunctorialCofiber.cofibδ l = w := by
    have he := E.hom.comm₃.symm
    change E.hom.hom₃ ≫ HasFunctorialCofiber.cofibδ l =
      w ≫ (shiftFunctor C (1:ℤ)).map E.hom.hom₁ at he
    change E.hom.hom₃ ≫ HasFunctorialCofiber.cofibδ l = w
    have he₁ : E.hom.hom₁ = 𝟙 L.obj₁ := by
      simp only [E,isoTriangleOfIso₁₂_hom_hom₁,Iso.refl_hom]
    exact he.trans (by
      rw [he₁]
      change w ≫ (shiftFunctor C (1:ℤ)).map (𝟙 (F.obj N.obj₃)) = w
      rw [CategoryTheory.Functor.map_id,Category.comp_id])
  let j := HasFunctorialCofiber.cofibι u ≫ e.hom
  let k := e.inv ≫ HasFunctorialCofiber.cofibδ u
  have hrow : Triangle.mk u j k ∈ distTriang C := by
    let U := Triangle.mk u (HasFunctorialCofiber.cofibι u) (HasFunctorialCofiber.cofibδ u)
    let V := Triangle.mk u j k
    have hU : U ∈ distTriang C := HasFunctorialCofiber.cofib_distinguished u
    let erow : U ≅ V := Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
      (by simp [U,V]) (by simp [U,V,j]) (by simp [U,V,k])
    exact isomorphic_distinguished U hU V erow.symm
  refine ⟨u,l,j,k,huι,huδ,hlι,hlδ,hrow,?_,?_,?_⟩
  · change HasFunctorialCofiber.cofibι (alpha.app N.obj₂) ≫
      (HasFunctorialCofiber.cofibι u ≫ e.hom) = N.mor₂ ≫ HasFunctorialCofiber.cofibι l
    rw [← Category.assoc,← hvι,Category.assoc,heι]
  · change (HasFunctorialCofiber.cofibι u ≫ e.hom) ≫ HasFunctorialCofiber.cofibδ l = _
    rw [Category.assoc,heδ,hwι]
  · change HasFunctorialCofiber.cofibι l ≫ (e.inv ≫ HasFunctorialCofiber.cofibδ u) = _
    rw [← heι,Category.assoc,Iso.hom_inv_id_assoc]
    exact hvδ

end GoodFoundation

section Jacobson
variable {C : Type u} [Category.{v} C] [Preadditive C]
private theorem correction_jacobson_isIso
    {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
    (h : IsIso (𝟙 Y+g ≫ f)) : IsIso (𝟙 X+f ≫ g) := by
  letI := h
  let e := asIso (𝟙 Y+g ≫ f)
  have hl : f ≫ e.inv ≫ g + f ≫ g ≫ f ≫ e.inv ≫ g = f ≫ g := by
    have hh := congrArg (fun z => f ≫ z ≫ g) e.hom_inv_id
    simpa only [e, asIso_hom, Preadditive.add_comp, Preadditive.comp_add,
      Category.assoc, Category.id_comp, Category.comp_id] using hh
  have hr : f ≫ e.inv ≫ g + f ≫ e.inv ≫ g ≫ f ≫ g = f ≫ g := by
    have hh := congrArg (fun z => f ≫ z ≫ g) e.inv_hom_id
    simpa only [e, asIso_hom, Preadditive.add_comp, Preadditive.comp_add,
      Category.assoc, Category.id_comp, Category.comp_id] using hh
  refine ⟨⟨𝟙 X-f ≫ e.inv ≫ g, ?_, ?_⟩⟩
  · calc
      _ = 𝟙 X + (f ≫ g - (f ≫ e.inv ≫ g + f ≫ g ≫ f ≫ e.inv ≫ g)) := by
        simp only [Preadditive.add_comp,Preadditive.comp_sub,Category.id_comp,
          Category.comp_id,Category.assoc]
        abel
      _ = 𝟙 X := by rw [hl,sub_self,add_zero]
  · calc
      _ = 𝟙 X + (f ≫ g - (f ≫ e.inv ≫ g + f ≫ e.inv ≫ g ≫ f ≫ g)) := by
        simp only [Preadditive.sub_comp,Preadditive.comp_add,Category.id_comp,
          Category.comp_id,Category.assoc]
        abel
      _ = 𝟙 X := by rw [hr,sub_self,add_zero]

end Jacobson

private theorem good_triangle_lambda_source_correction
    (N : Triangle SyntheticSpectrum) (hN : N ∈ distTriang SyntheticSpectrum)
    (q : ℕ)
    (l : (SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₃ ⟶ N.obj₃)
    (hleft : (SyntheticCategory.biShift (0,-(q:ℤ))).map N.mor₂≫l=
      lambdaPow q N.obj₂≫N.mor₂)
    (hlast : l≫N.mor₃=
      ((SyntheticCategory.biShift (0,-(q:ℤ))).map N.mor₃≫
        ((model.exactness.shiftCommShift (0,-(q:ℤ))).commShiftIso (1:ℤ)).hom.app N.obj₁)≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (lambdaPow q N.obj₁))
    (hzero : ∀ r : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₁)⟦(1:ℤ)⟧ ⟶
      XModLambdaN N.obj₃ q, r=0)
    (hreflect : ∀ b : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₁)⟦(1:ℤ)⟧ ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₁)⟦(1:ℤ)⟧,
      IsIso (model.recovery.realization.map b) → IsIso b) :
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
    letI : F.CommShift ℤ := model.exactness.shiftCommShift (0,-(q:ℤ))
    let p : F.obj N.obj₃ ⟶ (F.obj N.obj₁)⟦(1:ℤ)⟧ :=
      F.map N.mor₃≫(F.commShiftIso (1:ℤ)).hom.app N.obj₁
    ∃ t : (F.obj N.obj₁)⟦(1:ℤ)⟧ ⟶ F.obj N.obj₃,
      IsIso (𝟙 (F.obj N.obj₃)+p≫t) ∧
      l=(𝟙 (F.obj N.obj₃)+p≫t)≫lambdaPow q N.obj₃ := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  letI : F.Additive := model.exactness.shiftAdditive (0,-(q:ℤ))
  letI : F.CommShift ℤ := model.exactness.shiftCommShift (0,-(q:ℤ))
  letI : F.IsTriangulated := model.exactness.shiftExact (0,-(q:ℤ))
  let R := model.recovery.realization
  letI : R.Additive := realization_additive
  letI : R.CommShift ℤ := model.exactness.realizationShift
  letI : R.IsTriangulated := model.exactness.realizationExact
  let FN := F.mapTriangle.obj N
  have hFN : FN ∈ distTriang SyntheticSpectrum := F.map_distinguished N hN
  let p : F.obj N.obj₃ ⟶ (F.obj N.obj₁)⟦(1:ℤ)⟧ :=
    F.map N.mor₃≫(F.commShiftIso (1:ℤ)).hom.app N.obj₁
  have hd : FN.mor₂≫(l-lambdaPow q N.obj₃)=0 := by
    change F.map N.mor₂≫(l-lambdaPow q N.obj₃)=0
    rw [Preadditive.comp_sub,hleft,lambdaPow_naturality,sub_self]
  obtain ⟨r,hr⟩ := FN.yoneda_exact₃ hFN (l-lambdaPow q N.obj₃) hd
  change (F.obj N.obj₁)⟦(1:ℤ)⟧ ⟶ N.obj₃ at r
  change l-lambdaPow q N.obj₃=p≫r at hr
  have hr0 : r≫XModLambdaN.incl N.obj₃ q=0 := hzero _
  obtain ⟨t,ht⟩ := (XModLambdaN.cofiberTriangle N.obj₃ q).coyoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished N.obj₃ q) r hr0
  change (F.obj N.obj₁)⟦(1:ℤ)⟧ ⟶ F.obj N.obj₃ at t
  change r=t≫lambdaPow q N.obj₃ at ht
  let α := 𝟙 (F.obj N.obj₃)+p≫t
  let β := 𝟙 ((F.obj N.obj₁)⟦(1:ℤ)⟧)+t≫p
  have hl : l=α≫lambdaPow q N.obj₃ := by
    rw [show α=𝟙 _+p≫t from rfl,Preadditive.add_comp,Category.id_comp,
      Category.assoc,←ht]
    exact (sub_eq_iff_eq_add.mp hr).trans (add_comm _ _)
  let φ : FN ⟶ N :=
    { hom₁ := lambdaPow q N.obj₁
      hom₂ := lambdaPow q N.obj₂
      hom₃ := l
      comm₁ := lambdaPow_naturality q N.mor₁
      comm₂ := hleft
      comm₃ := hlast.symm }
  haveI : IsIso (R.map (lambdaPow q N.obj₁)) := recognition_realization_lambda_pow_isIso q _
  haveI : IsIso (R.map (lambdaPow q N.obj₂)) := recognition_realization_lambda_pow_isIso q _
  haveI : IsIso (R.map (lambdaPow q N.obj₃)) := recognition_realization_lambda_pow_isIso q _
  haveI : IsIso (R.map l) :=
    isIso₃_of_isIso₁₂ (R.mapTriangle.map φ)
      (R.map_distinguished FN hFN) (R.map_distinguished N hN)
      (by change IsIso (R.map (lambdaPow q N.obj₁)); infer_instance)
      (by change IsIso (R.map (lambdaPow q N.obj₂)); infer_instance)
  haveI : IsIso (R.map α) := by
    haveI : IsIso (R.map α≫R.map (lambdaPow q N.obj₃)) := by
      rw [←Functor.map_comp,←hl]
      infer_instance
    exact IsIso.of_isIso_comp_right (R.map α) (R.map (lambdaPow q N.obj₃))
  have hβR : IsIso (R.map β) := by
    change IsIso (R.map (𝟙 _+t≫p))
    rw [Functor.map_add,CategoryTheory.Functor.map_id,Functor.map_comp]
    apply correction_jacobson_isIso (R.map t) (R.map p)
    simpa only [α,Functor.map_add,CategoryTheory.Functor.map_id,Functor.map_comp] using
      (inferInstance : IsIso (R.map α))
  have hβ : IsIso β := hreflect β hβR
  refine ⟨t,?_,hl⟩
  exact correction_jacobson_isIso p t hβ

/-- Transport the actual good row across the corrected lambda cofiber.
Both inclusion and projection squares of its second arrow are retained. -/
private theorem corrected_good_row_on_fixed_quotient
    (N : Triangle SyntheticSpectrum) (q : ℕ)
    (u : XModLambdaN N.obj₁ q ⟶ XModLambdaN N.obj₂ q)
    (l : (SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₃ ⟶ N.obj₃)
    (j : XModLambdaN N.obj₂ q ⟶ HasFunctorialCofiber.cofib l)
    (k : HasFunctorialCofiber.cofib l ⟶ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧)
    (hR : Triangle.mk u j k ∈ distTriang SyntheticSpectrum)
    (hjι : XModLambdaN.incl N.obj₂ q≫j=N.mor₂≫HasFunctorialCofiber.cofibι l)
    (hjδ : j≫HasFunctorialCofiber.cofibδ l=XModLambdaN.proj N.obj₂ q≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(q:ℤ))).map N.mor₂))
    (hk : HasFunctorialCofiber.cofibι l≫k=N.mor₃≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₁ q))
    (α : (SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₃ ⟶
      (SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₃)
    (hα : IsIso α) (hl : l=α≫lambdaPow q N.obj₃)
    (hfix : (SyntheticCategory.biShift (0,-(q:ℤ))).map N.mor₂≫α=
      (SyntheticCategory.biShift (0,-(q:ℤ))).map N.mor₂) :
    ∃ (v : XModLambdaN N.obj₂ q ⟶ XModLambdaN N.obj₃ q)
      (k' : XModLambdaN N.obj₃ q ⟶ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧),
      Triangle.mk u v k' ∈ distTriang SyntheticSpectrum ∧
      XModLambdaN.incl N.obj₂ q≫v=N.mor₂≫XModLambdaN.incl N.obj₃ q ∧
      v≫XModLambdaN.proj N.obj₃ q=XModLambdaN.proj N.obj₂ q≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map N.mor₂) ∧
      XModLambdaN.incl N.obj₃ q≫k'=N.mor₃≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₁ q) := by
  letI := hα
  let T := Triangle.mk l (HasFunctorialCofiber.cofibι l) (HasFunctorialCofiber.cofibδ l)
  let U := XModLambdaN.cofiberTriangle N.obj₃ q
  let E := isoTriangleOfIso₁₂ T U (HasFunctorialCofiber.cofib_distinguished l)
    (XModLambdaN.cofiberTriangle_distinguished N.obj₃ q) (asIso α) (Iso.refl _)
    (by
      change l≫𝟙 N.obj₃=α≫lambdaPow q N.obj₃
      rw [Category.comp_id]
      exact hl)
  let e : HasFunctorialCofiber.cofib l ≅ XModLambdaN N.obj₃ q := Triangle.π₃.mapIso E
  have hei : HasFunctorialCofiber.cofibι l≫e.hom=XModLambdaN.incl N.obj₃ q := by
    have hh := E.hom.comm₂
    change HasFunctorialCofiber.cofibι l≫E.hom.hom₃=E.hom.hom₂≫XModLambdaN.incl N.obj₃ q at hh
    change HasFunctorialCofiber.cofibι l≫E.hom.hom₃=XModLambdaN.incl N.obj₃ q
    simpa only [E,isoTriangleOfIso₁₂_hom_hom₂,Iso.refl_hom,Category.id_comp] using hh
  have heδ : e.hom≫XModLambdaN.proj N.obj₃ q=
      HasFunctorialCofiber.cofibδ l≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map α := by
    have hh := E.hom.comm₃.symm
    change E.hom.hom₃≫XModLambdaN.proj N.obj₃ q=
      HasFunctorialCofiber.cofibδ l≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map E.hom.hom₁ at hh
    change E.hom.hom₃≫XModLambdaN.proj N.obj₃ q=
      HasFunctorialCofiber.cofibδ l≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map α
    simpa only [E,isoTriangleOfIso₁₂_hom_hom₁,asIso_hom] using hh
  let v := j≫e.hom
  let k' := e.inv≫k
  let S := Triangle.mk u v k'
  let ER : Triangle.mk u j k ≅ S := Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
    (by
      change u≫𝟙 _=𝟙 _≫u
      rw [Category.comp_id,Category.id_comp])
    (by simp only [Iso.refl_hom,Category.id_comp]; rfl)
    (by
      change k≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (𝟙 _)=e.hom≫(e.inv≫k)
      rw [CategoryTheory.Functor.map_id,Category.comp_id,←Category.assoc,e.hom_inv_id,
        Category.id_comp])
  refine ⟨v,k',isomorphic_distinguished _ hR S ER.symm,?_,?_,?_⟩
  · dsimp only [v]
    rw [←Category.assoc,hjι,Category.assoc,hei]
  · dsimp only [v]
    rw [Category.assoc,heδ,←Category.assoc,hjδ,Category.assoc,
      ←Functor.map_comp,hfix]
  · have hiinv : XModLambdaN.incl N.obj₃ q≫e.inv=HasFunctorialCofiber.cofibι l := by
      rw [←hei,Category.assoc,e.hom_inv_id,Category.comp_id]
    dsimp only [k']
    rw [←Category.assoc,hiinv,hk]

/-- Actual finite-source assembly through the first two selected quotient
arrows. Each mapping input is discharged by the fixed finite-source
lemmas in the concrete sphere/Cnu branch; no quotient row is an input. -/
private theorem actual_quotient_row_first_two_from_finite_mapping_facts
    (N : Triangle SyntheticSpectrum) (hN : N ∈ distTriang SyntheticSpectrum)
    (q : ℕ)
    (hzeroB : ∀ r : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₁)⟦(1:ℤ)⟧ ⟶
      XModLambdaN N.obj₂ q, r=0)
    (hzeroC : ∀ r : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₁)⟦(1:ℤ)⟧ ⟶
      XModLambdaN N.obj₃ q, r=0)
    (hreflect : ∀ b : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₁)⟦(1:ℤ)⟧ ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj N.obj₁)⟦(1:ℤ)⟧,
      IsIso (model.recovery.realization.map b) → IsIso b)
    (hbound : GhostBound ((XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧) 4)
    (hghost : ∀ a : XModLambdaN N.obj₃ q ⟶ XModLambdaN N.obj₃ q,
      XModLambdaN.incl N.obj₃ q≫a=0 → SphereGhost a) :
    ∃ k : XModLambdaN N.obj₃ q ⟶ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧,
      Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q) k ∈
        distTriang SyntheticSpectrum ∧
      XModLambdaN.incl N.obj₃ q≫k=N.mor₃≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₁ q) := by
  letI := model.exactness.syntheticTriangulated
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  letI : F.Additive := model.exactness.shiftAdditive (0,-(q:ℤ))
  letI : F.CommShift ℤ := model.exactness.shiftCommShift (0,-(q:ℤ))
  letI : F.IsTriangulated := model.exactness.shiftExact (0,-(q:ℤ))
  let lamNat : F ⟶ 𝟭 SyntheticSpectrum :=
    { app := fun A => lambdaPow q A
      naturality := by intro A B f; exact lambdaPow_naturality q f }
  obtain ⟨u,l,j,k,huι,huδ,hlι,hlδ,hR,hjι,hjδ,hk⟩ :=
    good_fill_chosen_cofiber_row F lamNat N hN
  change XModLambdaN N.obj₁ q ⟶ XModLambdaN N.obj₂ q at u
  change F.obj N.obj₃ ⟶ N.obj₃ at l
  change XModLambdaN N.obj₂ q ⟶ HasFunctorialCofiber.cofib l at j
  change HasFunctorialCofiber.cofib l ⟶ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧ at k
  change XModLambdaN.incl N.obj₁ q≫u=N.mor₁≫XModLambdaN.incl N.obj₂ q at huι
  have hu : u=XModLambdaN.map N.mor₁ q := by
    obtain ⟨z,hz⟩ := finite_quotient_map_difference_factors N.mor₁ q u huι
    rw [hzeroB z,comp_zero] at hz
    exact sub_eq_zero.mp hz
  obtain ⟨t,htIso,htl⟩ :=
    good_triangle_lambda_source_correction N hN q l hlι hlδ hzeroC hreflect
  let p : F.obj N.obj₃ ⟶ (F.obj N.obj₁)⟦(1:ℤ)⟧ :=
    F.map N.mor₃≫(F.commShiftIso (1:ℤ)).hom.app N.obj₁
  let α := 𝟙 (F.obj N.obj₃)+p≫t
  have hgp : F.map N.mor₂≫p=0 :=
    comp_distTriang_mor_zero₂₃ (F.mapTriangle.obj N) (F.map_distinguished N hN)
  have hfix : F.map N.mor₂≫α=F.map N.mor₂ := by
    rw [show α=𝟙 _+p≫t from rfl,Preadditive.comp_add,Category.comp_id,
      ←Category.assoc,hgp,zero_comp,add_zero]
  obtain ⟨v,k0,hS,hvι,hvδ,hk0⟩ := corrected_good_row_on_fixed_quotient
    N q u l j k hR hjι hjδ hk α htIso htl hfix
  rw [hu] at hS
  obtain ⟨a,haι,ha,ha'⟩ := finite_source_second_arrow_common_shear N hN q v hvι hvδ hzeroC
  let S := Triangle.mk (XModLambdaN.map N.mor₁ q) v k0
  obtain ⟨t0,ht0⟩ := common_shear_square_factors_through_tail S hS
    (XModLambdaN.map N.mor₂ q) a ha ha'
  have haIso : IsIso (𝟙 _+a) :=
    ghost_one_add_isIso_of_square_factor a (hghost a haι) k0 t0 4 hbound ht0
  letI := haIso
  let β := asIso (𝟙 _+a)
  have hv : v=XModLambdaN.map N.mor₂ q≫β.hom := by
    change v=XModLambdaN.map N.mor₂ q≫(𝟙 _+a)
    rw [Preadditive.comp_add,Category.comp_id]
    exact (sub_eq_iff_eq_add.mp ha).trans (add_comm _ _)
  let k1 := β.hom≫k0
  let U := Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q) k1
  let E : S ≅ U := Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) β.symm
    (by change XModLambdaN.map N.mor₁ q≫𝟙 _=𝟙 _≫XModLambdaN.map N.mor₁ q; simp)
    (by
      dsimp only [S,U,Triangle.mk,Iso.refl_hom,Iso.symm_hom]
      rw [Category.id_comp]
      rw [hv,Category.assoc,β.hom_inv_id,Category.comp_id])
    (by
      change k0≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (𝟙 _)=β.inv≫(β.hom≫k0)
      rw [CategoryTheory.Functor.map_id,Category.comp_id,←Category.assoc,β.inv_hom_id,
        Category.id_comp])
  refine ⟨k1,isomorphic_distinguished S hS U E.symm,?_⟩
  have hinc : XModLambdaN.incl N.obj₃ q≫β.hom=XModLambdaN.incl N.obj₃ q := by
    change XModLambdaN.incl N.obj₃ q≫(𝟙 _+a)=XModLambdaN.incl N.obj₃ q
    rw [Preadditive.comp_add,Category.comp_id,haι,add_zero]
  dsimp only [k1]
  rw [←Category.assoc,hinc,hk0]

private theorem construction_finite_source_reflects_iso
    {A : SyntheticSpectrum} (X : ClassicalObject) (hX : X=.sphere ∨ X=.nuCofiber)
    (p : ℤ×ℤ) (eA : A ≅ (SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (q : ℕ)
    (b : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶
      ((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧)
    (hRb : IsIso (model.recovery.realization.map b)) : IsIso b := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let eS : (F.obj A)⟦(1:ℤ)⟧ ≅
      ((SyntheticCategory.biShift (p+(0,-(q:ℤ)))).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧ :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      (F.mapIso eA ≪≫ (biShiftAddIso p (0,-(q:ℤ)) (p+(0,-(q:ℤ))) rfl).app _)
  apply recognition_realization_reflects_iso_of_obj_iso eS _ b hRb
  rcases hX with rfl | rfl
  · exact recognition_realization_shifted_nu_sphere_reflects_iso (p+(0,-(q:ℤ))) 1
  · exact recognition_realization_shifted_nu_cofiber_reflects_iso (p+(0,-(q:ℤ))) 1

private theorem construction_finite_quotient_ghost_bound
    {A : SyntheticSpectrum} (X : ClassicalObject) (hX : X=.sphere ∨ X=.nuCofiber)
    (p : ℤ×ℤ) (eA : A ≅ (SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (q : ℕ) :
    GhostBound ((XModLambdaN A q)⟦(1:ℤ)⟧) 4 := by
  have hXlit : ghost_cells_literal_finite_source_case X :=
    ghost_cells_descriptor_none_literal_actual X (by rcases hX with rfl | rfl <;> rfl)
  rcases sphereCells_literal_finite_source X hXlit with h1 | h2
  · exact ghostBound_mono (sphereCells_ghostBound
      (sphereCells_ordinaryShift 1 (sphereCells_quotient q
        (SphereCells.iso eA (sphereCells_biShift p h1))))) (by omega)
  · exact sphereCells_ghostBound
      (sphereCells_ordinaryShift 1 (sphereCells_quotient q
        (SphereCells.iso eA (sphereCells_biShift p h2))))

/-- The actual inclusion-kernel endomorphism is a sphere ghost after an
arbitrary bigraded shift of the selected nu-object. -/
private theorem shifted_quotient_nu_endomorphism_sphere_ghost
    (Y : ClassicalObject) (p : ℤ×ℤ) (q : ℕ) (hq : 0<q)
    (a : XModLambdaN ((SyntheticCategory.biShift p).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) q ⟶
      XModLambdaN ((SyntheticCategory.biShift p).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) q)
    (ha : XModLambdaN.incl _ q ≫ a = 0) : SphereGhost a := by
  let V := model.nu.functor.obj (Y.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) p
  letI : F.Additive := model.exactness.shiftAdditive p
  letI : F.CommShift ℤ := model.exactness.shiftCommShift p
  letI : F.IsTriangulated := model.exactness.shiftExact p
  obtain ⟨e,he⟩ := finite_quotient_shift_comparison model.quotients.coherence p q V
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) p
  let a0 : XModLambdaN V q ⟶ XModLambdaN V q :=
    ff.preimage (e.inv ≫ a ≫ e.hom)
  have hmapa : F.map a0 = e.inv ≫ a ≫ e.hom := ff.map_preimage _
  have hincl : XModLambdaN.incl V q ≫ a0 = 0 := by
    apply ff.map_injective
    change F.map (XModLambdaN.incl V q ≫ a0) = F.map 0
    rw [Functor.map_comp,hmapa,Functor.map_zero,←he]
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    rw [←Category.assoc,ha,zero_comp]
  have hbase := quotient_nu_endomorphism_sphere_ghost Y q hq a0 hincl
  intro m w c
  let eS : F.obj (Smn (Syn:=SyntheticSpectrum) (m-p.1) (w-p.2)) ≅ Smn m w :=
    (biShiftAddIso (m-p.1,w-p.2) p (m,w) (by ext <;> simp)).app S_0_0
  let c0 : BiHom (m-p.1) (w-p.2) (XModLambdaN V q) :=
    ff.preimage (eS.hom ≫ c ≫ e.hom)
  have hmapc : F.map c0 = eS.hom ≫ c ≫ e.hom := ff.map_preimage _
  have hzero : eS.hom ≫ (c ≫ a) ≫ e.hom = 0 := by
    have h := congrArg (fun z => F.map z) (hbase (m-p.1) (w-p.2) c0)
    rw [Functor.map_comp,hmapc,hmapa,Functor.map_zero] at h
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h
  exact (cancel_mono e.hom).mp ((cancel_epi eS.hom).mp
    (by simpa only [Category.assoc,zero_comp,comp_zero] using hzero))

/-- Arbitrary actual coordinates on the same underlying object are allowed;
the quotient coordinate is induced by the selected quotient functor. -/
private theorem quotient_nu_endomorphism_sphere_ghost_of_coordinates
    (Y : ClassicalObject) (p : ℤ×ℤ) (q : ℕ) (hq : 0<q)
    {C : SyntheticSpectrum}
    (e : C ≅ (SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))
    (a : XModLambdaN C q ⟶ XModLambdaN C q)
    (ha : XModLambdaN.incl C q ≫ a = 0) : SphereGhost a := by
  let Q := model.quotients.functoriality.functor q
  let eQ := Q.mapIso e
  let b := eQ.inv ≫ a ≫ eQ.hom
  have hincl : XModLambdaN.incl _ q ≫ b = 0 := by
    have hn : XModLambdaN.incl _ q ≫ eQ.inv = e.inv ≫ XModLambdaN.incl C q :=
      (XModLambdaN.incl_naturality e.inv q).symm
    change XModLambdaN.incl _ q ≫ (eQ.inv ≫ a ≫ eQ.hom) = 0
    rw [←Category.assoc,←Category.assoc,hn]
    simpa only [Category.assoc,comp_zero,zero_comp] using
      congrArg (fun z => e.inv ≫ z ≫ eQ.hom) ha
  have hb := shifted_quotient_nu_endomorphism_sphere_ghost Y p q hq b hincl
  intro m w c
  have h := hb m w (c ≫ eQ.hom)
  change (c ≫ eQ.hom) ≫ (eQ.inv ≫ a ≫ eQ.hom) = 0 at h
  have hz : (c ≫ a) ≫ eQ.hom = 0 := by
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h
  exact (cancel_mono eQ.hom).mp (by simpa only [zero_comp] using hz)


/-- Literal coordinate finite-first assembly. The sole remaining argument
in this intermediate lemma is the independently constructed sphere-ghost
property of the specified target quotient, not an exact-row assertion. -/
private theorem actual_finite_first_quotient_row_of_coordinates_with_ghost
    (N : Triangle SyntheticSpectrum) (hN : N ∈ distTriang SyntheticSpectrum)
    (X Y Z : ClassicalObject) (hX : X=.sphere ∨ X=.nuCofiber)
    (p r s : ℤ×ℤ)
    (eA : N.obj₁ ≅ (SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (eB : N.obj₂ ≅ (SyntheticCategory.biShift r).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))
    (eC : N.obj₃ ≅ (SyntheticCategory.biShift s).obj
      (model.nu.functor.obj (Z.obj model.auxiliary)))
    (q : ℕ) (hq : 0<q)
    (hAB : p.2-p.1-(r.2-r.1)≤1) (hAC : p.2-p.1-(s.2-s.1)≤1)
    (hghost : ∀ a : XModLambdaN N.obj₃ q ⟶ XModLambdaN N.obj₃ q,
      XModLambdaN.incl N.obj₃ q≫a=0 → SphereGhost a) :
    ∃ esusp : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (N.obj₁⟦(1:ℤ)⟧) q≫esusp.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₁ q) ∧
      Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
        (XModLambdaN.map N.mor₃ q≫esusp.hom) ∈ distTriang SyntheticSpectrum := by
  have hXlit : ghost_cells_literal_finite_source_case X :=
    ghost_cells_descriptor_none_literal_actual X (by rcases hX with rfl | rfl <;> rfl)
  obtain ⟨k0,hR,hinc⟩ := actual_quotient_row_first_two_from_finite_mapping_facts N hN q
    (fun z => suspension_finite_source_to_quotient_vanishing_of_coordinates
      X Y hXlit p r q hq hAB eA eB z)
    (fun z => suspension_finite_source_to_quotient_vanishing_of_coordinates
      X Z hXlit p s q hq hAC eA eC z)
    (construction_finite_source_reflects_iso X hX p eA q)
    (construction_finite_quotient_ghost_bound X hX p eA q) hghost
  obtain ⟨esusp,he⟩ := finite_quotient_suspension_comparison q N.obj₁
  have htail := quotient_tail_eq_finite_source N hN X hX p eA q hq k0 hR hinc esusp he
  exact ⟨esusp,he,by rwa [htail]⟩

/-- A constructed actual finite quotient row whenever the first vertex is
an actual shifted nu-sphere or nu-Cnu and the displayed relative weight
bounds hold. All three arrows are the specified quotient maps. -/
private theorem actual_finite_first_quotient_row_of_coordinates
    (N : Triangle SyntheticSpectrum) (hN : N ∈ distTriang SyntheticSpectrum)
    (X Y Z : ClassicalObject) (hX : X=.sphere ∨ X=.nuCofiber)
    (p r s : ℤ×ℤ)
    (eA : N.obj₁ ≅ (SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (eB : N.obj₂ ≅ (SyntheticCategory.biShift r).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))
    (eC : N.obj₃ ≅ (SyntheticCategory.biShift s).obj
      (model.nu.functor.obj (Z.obj model.auxiliary)))
    (q : ℕ) (hq : 0<q)
    (hAB : p.2-p.1-(r.2-r.1)≤1) (hAC : p.2-p.1-(s.2-s.1)≤1) :
    ∃ esusp : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (N.obj₁⟦(1:ℤ)⟧) q≫esusp.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₁ q) ∧
      Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
        (XModLambdaN.map N.mor₃ q≫esusp.hom) ∈ distTriang SyntheticSpectrum := by
  exact actual_finite_first_quotient_row_of_coordinates_with_ghost
    N hN X Y Z hX p r s eA eB eC q hq hAB hAC
    (quotient_nu_endomorphism_sphere_ghost_of_coordinates Z s q hq eC)

end
end KIP126.Literature.Standard.Internal
