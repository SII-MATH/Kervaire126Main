module

public import KIP126.AdamsSynthetic.Standard
public import KIP126.AdamsSynthetic.Standard.Filtration
public import KIP126.AdamsSynthetic.AdamsFiltration
public import KIP126.AdamsSynthetic.Internal.SteenrodComodules
import all KIP126.AdamsSynthetic.Internal.SteenrodComodules

/-! The minimal coefficient-Ext source used by finite-layer composition.
The homology source and comparisons are registered upstream boundaries.
Ext itself and the SES connecting operation use mathlib's derived category;
neither is defined by a synthetic first-quotient operation. -/

@[expose] section
set_option backward.privateInPublic true
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open Internal.SteenrodComodules
open scoped TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

/-- Internally graded comodules over the specified Milnor polynomial coproduct. -/
public def SteenrodComodule : Type 1 := GradedSteenrodComodule

@[no_expose] public instance steenrodComoduleCategory : Category.{0} SteenrodComodule :=
  inferInstanceAs (Category GradedSteenrodComodule)

@[reducible] private def steenrodComodulePreadditive : Preadditive SteenrodComodule :=
  inferInstanceAs (Preadditive GradedSteenrodComodule)

private def canonicalComoduleAbelian :
    {A : Abelian SteenrodComodule // A.toPreadditive = steenrodComodulePreadditive} := by
  sorry

/-- The canonical abelian structure on the actual graded comodule category.
Its construction is an upstream responsibility, not an assumption of composition. -/
public instance steenrodComoduleAbelian : Abelian SteenrodComodule :=
  canonicalComoduleAbelian.val

private def homologyCoactionMap (X : Spectrum) :
    coefficients.object ⊗ X ⟶ coefficients.object ⊗ (coefficients.object ⊗ X) :=
  coefficients.object ◁ ((λ_ X).inv ≫ (coefficients.unit ▷ X))

private def coefficientExternalProduct
    (μ : coefficients.object ⊗ coefficients.object ⟶ coefficients.object)
    (X : Spectrum) (m n : ℤ)
    (a : ModTwoHomology coefficients m coefficients.object)
    (b : ModTwoHomology coefficients n X) :
    HomotopyGroup (m+n) (coefficients.object ⊗ (coefficients.object ⊗ X)) := by
  letI := closedBackground.symmetric
  exact (closedBackground.smashSpheres m n).inv ≫ (a ⊗ₘ b) ≫
    tensorμ coefficients.object coefficients.object coefficients.object X ≫
      (μ ▷ (coefficients.object ⊗ X))

/- This recognition boundary fixes the actual HF2 homology and its spectral
coaction, in addition to the polynomial coalgebra and degree grading. -/
private structure HomologyComoduleSource where
  functor : Spectrum ⥤ SteenrodComodule
  additive : functor.Additive
  degree : ∀ (X : Spectrum) (n : ℤ),
    ((functor.obj X).grade n) ≃+ ModTwoHomology coefficients n X
  natural : ∀ {X Y : Spectrum} (f : X ⟶ Y) (n : ℤ)
    (x : (functor.obj X).grade n),
    degree Y n ⟨(functor.map f).linearMap x,
      (functor.map f).graded n x x.property⟩ =
        modTwoHomologyMap coefficients f n (degree X n x)
  multiplication : coefficients.object ⊗ coefficients.object ⟶ coefficients.object
  unit_left : (coefficients.unit ▷ coefficients.object) ≫ multiplication =
    (λ_ coefficients.object).hom
  unit_right : (coefficients.object ◁ coefficients.unit) ≫ multiplication =
    (ρ_ coefficients.object).hom
  associative : (multiplication ▷ coefficients.object) ≫ multiplication =
    (α_ coefficients.object coefficients.object coefficients.object).hom ≫
      (coefficients.object ◁ multiplication) ≫ multiplication
  cooperations : (functor.obj coefficients.object).carrier ≃ₗ[F2] DualSteenrod
  cooperation_grade : ∀ (n : ℤ) (a : (functor.obj coefficients.object).carrier),
    a ∈ (functor.obj coefficients.object).grade n ↔
      if 0 ≤ n then MvPolynomial.IsWeightedHomogeneous milnorWeight (cooperations a) n.toNat
      else a = 0
  cooperation_coproduct :
    TensorProduct.map (LinearMap.id : DualSteenrod →ₗ[F2] DualSteenrod)
      cooperations.toLinearMap ∘ₗ
      (functor.obj coefficients.object).rho =
        milnorCoproduct.toLinearMap ∘ₗ cooperations.toLinearMap
  kunneth : ∀ (X : Spectrum) (n : ℤ),
    HomotopyGroup n (coefficients.object ⊗ (coefficients.object ⊗ X)) ≃+
      tensorGrade (functor.obj X).carrier (functor.obj X).grade n
  kunneth_tensor : ∀ (X : Spectrum) (m n : ℤ)
    (a : (functor.obj coefficients.object).grade m) (b : (functor.obj X).grade n),
    (kunneth X (m+n) (coefficientExternalProduct multiplication X m n
      (degree coefficients.object m a) (degree X n b))).val =
        cooperations a ⊗ₜ[F2] b.val
  coaction : ∀ (X : Spectrum) (n : ℤ) (x : (functor.obj X).grade n),
    (kunneth X n (degree X n x ≫ homologyCoactionMap X)).val =
      (functor.obj X).rho x

private def canonicalHomologyComoduleSource : HomologyComoduleSource := by
  sorry

/-- The actual HF2 homology comodule functor, with the spectral coaction. -/
@[no_expose] public def homologyComodule : Spectrum ⥤ SteenrodComodule :=
  canonicalHomologyComoduleSource.functor

private instance homologyComoduleAdditive : homologyComodule.Additive :=
  canonicalHomologyComoduleSource.additive

/-- Integer-graded derived Ext from H_*(Sigma^t S) to the same H_*X.
For nonnegative s this is mathlib's ordinary Ext; no negative degree is
silently replaced by zero via Int.toNat. -/
@[no_expose] public def ClassicalExt (X : Spectrum) (s t : ℤ) : Type 1 :=
  IntExt (homologyComodule.obj (Sphere t)) (homologyComodule.obj X) s

@[reducible] private def extAddCommGroup (X : Spectrum) (s t : ℤ) :
    AddCommGroup (ClassicalExt X s t) := inferInstanceAs (AddCommGroup (IntExt _ _ s))

public instance classicalExtAddCommGroup (X : Spectrum) (s t : ℤ) :
    AddCommGroup (ClassicalExt X s t) := extAddCommGroup X s t

private structure AdamsExtComparison where
  e2 : ∀ (X : ClassicalObject) (s t : ℤ),
    (classical.obj (X.obj auxiliary)).Page 2 (s,t) ≃+ ClassicalExt (X.obj auxiliary) s t
  natural : ∀ (X Y : ClassicalObject) (f : X.obj auxiliary ⟶ Y.obj auxiliary)
    (s t : ℤ) (x : (classical.obj (X.obj auxiliary)).Page 2 (s,t)),
    e2 Y s t ((classical.functor.map f).pageMap 2 (s,t) x) =
      IntExt.map (homologyComodule.map f) s (e2 X s t x)
  suspended : ∀ (X : ClassicalObject) (s t : ℤ),
    (classical.obj (X.obj auxiliary)).Page 2 (s,t) ≃+
      ClassicalExt ((X.obj auxiliary)⟦(1 : ℤ)⟧) s (t+1)
  suspension : ∀ (X : ClassicalObject) (s t : ℤ)
    (x : (classical.obj (X.obj auxiliary)).Page 2 (s,t))
    (sx : (classical.obj ((X.obj auxiliary)⟦(1 : ℤ)⟧)).Page 2 (s,t+1)),
    (classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x) →
      suspended X s t x = e2 (.shift 1 X) s (t+1) sx

private def canonicalAdamsExtComparison : AdamsExtComparison := by
  sorry

/-- The fixed Adams E2/derived coefficient-Ext coordinates. -/
@[no_expose] public def e2ExtEquiv (X : ClassicalObject) (s t : ℤ) :
    (classical.obj (X.obj auxiliary)).Page 2 (s,t) ≃+ ClassicalExt (X.obj auxiliary) s t :=
  canonicalAdamsExtComparison.e2 X s t

/-- The same coordinates followed by the actual internal suspension. -/
@[no_expose] public def suspendedE2ExtEquiv (X : ClassicalObject) (s t : ℤ) :
    (classical.obj (X.obj auxiliary)).Page 2 (s,t) ≃+
      ClassicalExt ((X.obj auxiliary)⟦(1 : ℤ)⟧) s (t+1) :=
  canonicalAdamsExtComparison.suspended X s t

/-- The same actual g and h, viewed as homology-comodule maps. -/
public def cofiberHomologyShortComplex (T : TriangleData model.auxiliary) :
    ShortComplex SteenrodComodule :=
  ShortComplex.mk (homologyComodule.map T.g) (homologyComodule.map T.h) (by
    have hz : T.g ≫ T.h = 0 := comp_distTriang_mor_zero₂₃ _ T.distinguished
    rw [← Functor.map_comp, hz, Functor.map_zero])

/-- The canonical comodule exact structure detects the already proved
degreewise HF2 short exactness. This is a minimal upstream exactness boundary. -/
public theorem cofiberHomologyShortComplex_shortExact
    (T : TriangleData model.auxiliary)
    (hH : HomologyShortExact coefficients (Triangle.mk T.f T.g T.h).rotate) :
    (cofiberHomologyShortComplex T).ShortExact := by
  sorry

/-- The genuine connecting map of the same homology SES, transported to
the fixed Adams E2 coordinates. Its definition uses the SES extension class. -/
@[no_expose] public def cofiberExtBoundary
    (T : TriangleData model.auxiliary)
    (hH : HomologyShortExact coefficients (Triangle.mk T.f T.g T.h).rotate)
    (s t : ℤ) (x : (classical.obj (T.X.obj auxiliary)).Page 2 (s,t)) :
    (classical.obj (T.Y.obj auxiliary)).Page 2 (s+1,t+1) :=
  (e2ExtEquiv T.Y (s+1) (t+1)).symm
    (IntExt.sesBoundary (C := SteenrodComodule) (cofiberHomologyShortComplex T)
      (cofiberHomologyShortComplex_shortExact T hH)
      (homologyComodule.obj (Sphere (t+1))) s (suspendedE2ExtEquiv T.X s t x))

end
end KIP126.AdamsSynthetic.Standard
