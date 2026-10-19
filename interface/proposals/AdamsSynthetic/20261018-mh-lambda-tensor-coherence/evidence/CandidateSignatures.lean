module

import KIP126.AdamsSynthetic.Quotients
import KIP126.AdamsSynthetic.SphereTensor
import KIP126.Literature.May
import KIP126.Literature.Standard

/- Review evidence only. These are candidate types, not implementations or
new assumptions installed in any production proof. -/

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v

namespace KIP126.InterfaceReview.MHLambdaTensor

variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- Ordinary suspension comparison induced by the same quotient/tensor
isomorphism and the right-tensor shift comparison used by May. -/
noncomputable def quotientSuspensionIso
    (rightShift : ∀ W : Syn, (tensorRight W).CommShift ℤ)
    (quotientIso : ∀ (X : Syn) (n : ℕ),
      X ⊗ XModLambdaN (𝟙_ Syn) n ≅ XModLambdaN X n)
    (X : Syn) (n : ℕ) :
    XModLambdaN (X⟦(1 : ℤ)⟧) n ≅ (XModLambdaN X n)⟦(1 : ℤ)⟧ := by
  letI := rightShift (XModLambdaN (𝟙_ Syn) n)
  exact (quotientIso (X⟦(1 : ℤ)⟧) n).symm ≪≫
    ((tensorRight (XModLambdaN (𝟙_ Syn) n)).commShiftIso (1 : ℤ)).app X ≪≫
    (shiftFunctor Syn (1 : ℤ)).mapIso (quotientIso X n)

/-- The actual left-tensor suspension comparison followed by the chosen
vertical quotient comparison. Naturality in X is a separate field below. -/
noncomputable def suspendedVerticalIso
    (leftShift : ∀ W : Syn, (tensorLeft W).CommShift ℤ)
    (verticalIso : ∀ (X : Syn) (i n : ℕ),
      X ⊗ (SyntheticCategory.biShift (0,-(i : ℤ))).obj
          (XModLambdaN (𝟙_ Syn) n) ≅
        (SyntheticCategory.biShift (0,-(i : ℤ))).obj (XModLambdaN X n))
    (X : Syn) (i n : ℕ) :
    X ⊗ ((SyntheticCategory.biShift (0,-(i : ℤ))).obj
        (XModLambdaN (𝟙_ Syn) n))⟦(1 : ℤ)⟧ ≅
      ((SyntheticCategory.biShift (0,-(i : ℤ))).obj
        (XModLambdaN X n))⟦(1 : ℤ)⟧ := by
  letI := leftShift X
  exact ((tensorLeft X).commShiftIso (1 : ℤ)).app
      ((SyntheticCategory.biShift (0,-(i : ℤ))).obj
        (XModLambdaN (𝟙_ Syn) n)) ≪≫
    (shiftFunctor Syn (1 : ℤ)).mapIso (verticalIso X i n)

/-- The directly sufficient structural comparison, parameterized by the
actual existing tensor shift choices. There is no MH conclusion or common
representative among the fields. -/
structure LambdaQuotientTensorCompatibility
    (Q : LambdaQuotientSystem Syn)
    (leftShift : ∀ W : Syn, (tensorLeft W).CommShift ℤ)
    (rightShift : ∀ W : Syn, (tensorRight W).CommShift ℤ) where
  quotientIso : ∀ (X : Syn) (n : ℕ),
    X ⊗ XModLambdaN (𝟙_ Syn) n ≅ XModLambdaN X n
  verticalIso : ∀ (X : Syn) (i n : ℕ),
    X ⊗ (SyntheticCategory.biShift (0,-(i : ℤ))).obj
        (XModLambdaN (𝟙_ Syn) n) ≅
      (SyntheticCategory.biShift (0,-(i : ℤ))).obj (XModLambdaN X n)
  quotient_natural : ∀ {X Y : Syn} (f : X ⟶ Y) (n : ℕ),
    (f ▷ XModLambdaN (𝟙_ Syn) n) ≫ (quotientIso Y n).hom =
      (quotientIso X n).hom ≫ XModLambdaN.map f n
  vertical_natural : ∀ {X Y : Syn} (f : X ⟶ Y) (i n : ℕ),
    (f ▷ (SyntheticCategory.biShift (0,-(i : ℤ))).obj
        (XModLambdaN (𝟙_ Syn) n)) ≫ (verticalIso Y i n).hom =
      (verticalIso X i n).hom ≫
        (SyntheticCategory.biShift (0,-(i : ℤ))).map (XModLambdaN.map f n)
  suspended_vertical_natural : ∀ {X Y : Syn} (f : X ⟶ Y) (i n : ℕ),
    (f ▷ ((SyntheticCategory.biShift (0,-(i : ℤ))).obj
        (XModLambdaN (𝟙_ Syn) n))⟦(1 : ℤ)⟧) ≫
          (suspendedVerticalIso leftShift verticalIso Y i n).hom =
      (suspendedVerticalIso leftShift verticalIso X i n).hom ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0,-(i : ℤ))).map (XModLambdaN.map f n))
  quotient_incl : ∀ (X : Syn) (n : ℕ),
    (X ◁ XModLambdaN.incl (𝟙_ Syn) n) ≫ (quotientIso X n).hom =
      (ρ_ X).hom ≫ XModLambdaN.incl X n
  lambda_triangle : ∀ (X : Syn) {i j : ℕ} (hi : 0 < i) (hij : i < j),
    (X ◁ ((Q.tower (𝟙_ Syn)).triangle hi hij).lambdaMap) ≫
        (quotientIso X j).hom =
      (verticalIso X i (j-i)).hom ≫ ((Q.tower X).triangle hi hij).lambdaMap
  rho_triangle : ∀ (X : Syn) {i j : ℕ} (hi : 0 < i) (hij : i < j),
    (X ◁ ((Q.tower (𝟙_ Syn)).triangle hi hij).rho) ≫
        (quotientIso X i).hom =
      (quotientIso X j).hom ≫ ((Q.tower X).triangle hi hij).rho
  delta_triangle : ∀ (X : Syn) {i j : ℕ} (hi : 0 < i) (hij : i < j),
    letI := leftShift X
    (X ◁ ((Q.tower (𝟙_ Syn)).triangle hi hij).delta) ≫
        ((tensorLeft X).commShiftIso (1 : ℤ)).hom.app
          ((SyntheticCategory.biShift (0,-(i : ℤ))).obj
            (XModLambdaN (𝟙_ Syn) (j-i))) ≫
        (shiftFunctor Syn (1 : ℤ)).map (verticalIso X i (j-i)).hom =
      (quotientIso X i).hom ≫ ((Q.tower X).triangle hi hij).delta
  suspension_incl : ∀ (X : Syn) (n : ℕ),
    XModLambdaN.incl (X⟦(1 : ℤ)⟧) n ≫
        (quotientSuspensionIso rightShift quotientIso X n).hom =
      (shiftFunctor Syn (1 : ℤ)).map (XModLambdaN.incl X n)

/-- A separate lower-level diagnostic condition on the existing chosen
sphere/tensor comparison, rather than a replacement comparison. This is a
possible producer-side route to the preceding record, not an extra MH
hypothesis. -/
def ExistingSphereTensorPreservesLambda : Prop :=
  ∀ (n : ℕ) (X : Syn),
    (biShift_eq_tensor_Smn 0 (-(n : ℤ)) X).hom ≫
        (lambdaPow n (𝟙_ Syn) ▷ X) ≫ (λ_ X).hom = lambdaPow n X

/-- The stronger May lifting input needed for arbitrary bigraded sphere
domains. The existing pushpull maps, squares, signs, and shift choices are
retained; only the quantified domain of the lift is enlarged. -/
def UniversalMayLift
    (B : KIP126.Literature.Route.MayContext Syn)
    (T U : HoCofiberSequence (C := Syn))
    (P : KIP126.Literature.Route.MayPushpullData Syn B T U) : Prop :=
  ∀ (W : Syn) (a : W ⟶ T.X ⊗ U.Z) (b : W ⟶ T.Y ⊗ U.Y),
    a ≫ (T.f ▷ U.Z) = b ≫ (T.Y ◁ U.g) →
    ∃ z : W ⟶ P.vertex, z ≫ P.j1 = a ∧ z ≫ P.j2 = b

/- Candidate fixed producer theorem types. These are type checks, with no
declaration or proof of either existence statement. -/
#check LambdaQuotientTensorCompatibility
#check quotientSuspensionIso
#check ExistingSphereTensorPreservesLambda
#check UniversalMayLift

/- Exact candidate producer types on the fixed project objects. `Type`
and `Prop` below only name the requested type, and assert no inhabitant. -/
def FixedCompatibilityType : Type 1 :=
  LambdaQuotientTensorCompatibility.{1,0}
    KIP126.AdamsSynthetic.Standard.quotients
    KIP126.Literature.Standard.may_leftShift
    KIP126.Literature.Standard.may_rightShift

def FixedUniversalMayType : Prop :=
  ∀ (T U : HoCofiberSequence (C := KIP126.AdamsSynthetic.Standard.SyntheticSpectrum)),
    ∃ P : KIP126.Literature.Route.MayPushpullData
        KIP126.AdamsSynthetic.Standard.SyntheticSpectrum
        KIP126.Literature.Standard.mayData T U,
      UniversalMayLift KIP126.Literature.Standard.mayData T U P

#check FixedCompatibilityType
#check FixedUniversalMayType

end KIP126.InterfaceReview.MHLambdaTensor
