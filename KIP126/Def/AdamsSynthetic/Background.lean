module

public import KIP126.Def.AdamsSynthetic.Context

/-! Additional background contracts on the same stable category. The chosen
closed structure and every shift comparison are explicit inputs; declaring
these records does not select an enhancement for an arbitrary category.
Source: KIPBase `StableHomotopy/TensorTriangulatedCategory.lean` and
`StableHomotopy/Basic.lean`, migration baseline 5aa845241533. -/

@[expose] section
namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits MonoidalCategory Pretriangulated

universe u v
variable (C : Type u) [StableHomotopyCategory.{u, v} C]

/-- Closed symmetric tensor triangulated structure on this very background.
The exactness statements use the supplied coherent shift comparisons, so a
consumer need not independently assume that tensor or internal hom commutes
with suspension. -/
public structure ClosedSymmetricTensorTriangulated where
  symmetric : SymmetricCategory C
  closed : MonoidalClosed C
  tensorShift : ∀ W : C, (tensorRight W).CommShift ℤ
  tensorExact : ∀ W : C,
    letI := tensorShift W
    (tensorRight W).IsTriangulated
  ihomShift : letI := closed
    ∀ W : C, (ihom W).CommShift ℤ
  ihomExact : letI := closed
    ∀ W : C,
    letI := ihomShift W
    (ihom W).IsTriangulated

variable {C}
namespace ClosedSymmetricTensorTriangulated

/-- Tensoring a shifted unit with an object is its actual integer shift.
This comparison is derived from the supplied tensor shift coherence. -/
public noncomputable def sphereTensorShift
    (B : ClosedSymmetricTensorTriangulated C) (n : ℤ) (X : C) :
    (Sphere n : C) ⊗ X ≅ (shiftFunctor C n).obj X := by
  letI := B.tensorShift X
  exact ((tensorRight X).commShiftIso n).app SphereSpectrum ≪≫
    (shiftFunctor C n).mapIso (λ_ X)

/-- The sphere product comparison determined by this background. -/
public noncomputable def smashSpheres
    (B : ClosedSymmetricTensorTriangulated C) (m n : ℤ) :
    (Sphere m : C) ⊗ Sphere n ≅ Sphere (m + n) :=
  B.sphereTensorShift m (Sphere n) ≪≫
    ((shiftFunctorAdd C n m).app SphereSpectrum).symm ≪≫
    eqToIso (congrArg (Sphere (C := C)) (add_comm n m))

end ClosedSymmetricTensorTriangulated

/-- The stable Koszul sign for the actual braiding and the sphere product
comparisons supplied by `B`. It is a separate proof input, since symmetry
alone does not imply the stable sign convention. -/
public structure SphereTwistSign (B : ClosedSymmetricTensorTriangulated C) : Prop where
  twist : letI := B.symmetric
    ∀ r s : ℤ,
      (β_ (Sphere r : C) (Sphere s)).hom ≫ (B.smashSpheres s r).hom ≫
        eqToHom (congrArg (Sphere (C := C)) (add_comm s r)) =
      if Even (r * s) then (B.smashSpheres r s).hom
      else -(B.smashSpheres r s).hom

end KIP126.StableHomotopy
