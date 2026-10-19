module
import KIP126.AdamsSynthetic.Standard
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! The actual chosen finite lambda quotient functor is additive.
The proof compares its cofiber triangle on a finite product with the product
of the actual cofiber triangles. It does not assert preservation of arbitrary
distinguished triangles. All declarations are private. -/

@[expose] section
namespace KIP126.Literature.Standard.Internal
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
noncomputable section
attribute [local instance] HasZeroObject.zero'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
set_option Elab.async false

private def quotientTriangleMap {X Y : SyntheticSpectrum} (f : X ⟶ Y) (q : ℕ) :
    XModLambdaN.cofiberTriangle X q ⟶ XModLambdaN.cofiberTriangle Y q where
  hom₁ := (SyntheticCategory.biShift (0,-(q:ℤ))).map f
  hom₂ := f
  hom₃ := XModLambdaN.map f q
  comm₁ := (lambdaPow_naturality q f).symm
  comm₂ := (XModLambdaN.incl_naturality f q).symm
  comm₃ := (XModLambdaN.proj_naturality f q).symm

private theorem quotient_pi_comparison_isIso (q : ℕ) {J : Type} [Fintype J]
    (X : J → SyntheticSpectrum) :
    IsIso (piComparison (quotients.functoriality.functor q) X) := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let Q := quotients.functoriality.functor q
  letI := exactness.shiftAdditive (0,-(q:ℤ))
  let T : J → Triangle SyntheticSpectrum := fun j => XModLambdaN.cofiberTriangle (X j) q
  let φ : XModLambdaN.cofiberTriangle (∏ᶜ X) q ⟶ productTriangle T :=
    productTriangle.lift T (fun j => quotientTriangleMap (Pi.π X j) q)
  have h₁ : φ.hom₁ = piComparison F X := rfl
  have h₂ : φ.hom₂ = 𝟙 _ := by
    dsimp only [φ,productTriangle.lift,quotientTriangleMap]
    apply Pi.hom_ext
    intro j
    simp
    rfl
  have h₃ : φ.hom₃ = piComparison Q X := rfl
  have hφ₁ : IsIso φ.hom₁ := by rw [h₁]; infer_instance
  have hφ₂ : IsIso φ.hom₂ := by rw [h₂]; infer_instance
  have hφ₃ := isIso₃_of_isIso₁₂ φ (XModLambdaN.cofiberTriangle_distinguished _ q)
    (productTriangle_distinguished T (fun j => XModLambdaN.cofiberTriangle_distinguished _ q))
    hφ₁ hφ₂
  rwa [h₃] at hφ₃

private theorem quotient_preserves_zero (q : ℕ) :
    (quotients.functoriality.functor q).PreservesZeroMorphisms := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  letI := exactness.shiftAdditive (0,-(q:ℤ))
  have hF : IsZero (F.obj (0:SyntheticSpectrum)) := F.map_isZero (isZero_zero _)
  have hQ : IsZero (XModLambdaN (0:SyntheticSpectrum) q) :=
    (XModLambdaN.cofiberTriangle _ q).isZero₃_of_isZero₁₂
      (XModLambdaN.cofiberTriangle_distinguished _ q) hF (isZero_zero _)
  exact Functor.preservesZeroMorphisms_of_map_zero_object (hQ.isoZero)

private theorem quotient_additive (q : ℕ) :
    (quotients.functoriality.functor q).Additive := by
  let Q := quotients.functoriality.functor q
  letI : Q.PreservesZeroMorphisms := quotient_preserves_zero q
  letI : PreservesLimitsOfShape (Discrete WalkingPair) Q :=
    ⟨fun {K} => by
      let X : WalkingPair → SyntheticSpectrum := K.obj ∘ Discrete.mk
      haveI : IsIso (piComparison Q X) := quotient_pi_comparison_isIso q X
      haveI : PreservesLimit (Discrete.functor X) Q := PreservesProduct.of_iso_comparison Q X
      exact preservesLimit_of_iso_diagram Q (Discrete.natIsoFunctor (F:=K)).symm⟩
  exact Functor.additive_of_preserves_binary_products Q

private theorem quotient_map_neg {X Y : SyntheticSpectrum} (f : X ⟶ Y) (q : ℕ) :
    XModLambdaN.map (-f) q = -XModLambdaN.map f q := by
  let Q := quotients.functoriality.functor q
  letI : Q.Additive := quotient_additive q
  exact Q.map_neg

/-- Additivity gives the expected split distinguished row without any
claim that Q preserves a general distinguished triangle. -/
private theorem quotient_standard_split_triangle (q : ℕ) (X Y : SyntheticSpectrum) :
    Triangle.mk (XModLambdaN.map (biprod.inl : X ⟶ X ⊞ Y) q)
      (XModLambdaN.map (biprod.snd : X ⊞ Y ⟶ Y) q) 0 ∈
      distTriang SyntheticSpectrum := by
  let Q := quotients.functoriality.functor q
  letI : Q.Additive := quotient_additive q
  letI : PreservesBinaryBiproduct X Y Q :=
    preservesBinaryBiproduct_of_preservesBinaryProduct Q (X:=X) (Y:=Y)
  let T := Triangle.mk (Q.map (biprod.inl : X ⟶ X ⊞ Y))
    (Q.map (biprod.snd : X ⊞ Y ⟶ Y)) 0
  let e : T ≅ binaryBiproductTriangle (Q.obj X) (Q.obj Y) :=
    Triangle.isoMk _ _ (Iso.refl _) (Q.mapBiprod X Y) (Iso.refl _)
      (by
        dsimp only [T,binaryBiproductTriangle,Triangle.mk_mor₁,Iso.refl_hom]
        simp only [Category.id_comp]
        apply biprod.hom_ext <;> simp [←Functor.map_comp])
      (by simp [T])
      (by simp [T])
  exact isomorphic_distinguished _ (binaryBiproductTriangle_distinguished (Q.obj X) (Q.obj Y)) _ e

private theorem quotient_preserves_finite_biproducts (q : ℕ) :
    letI := quotient_additive q
    PreservesFiniteBiproducts (quotients.functoriality.functor q) := by
  letI := quotient_additive q
  infer_instance

end
end KIP126.Literature.Standard.Internal
