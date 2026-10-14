module

import KIP126.Def.AdamsSynthetic

/-! Consumer checks for the optional background and point-set realization
inputs. Every comparison stays attached to the supplied category and model. -/

open CategoryTheory CategoryTheory.Limits MonoidalCategory Pretriangulated
open HomotopicalAlgebra KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v w z
noncomputable section

section Background
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  (B : ClosedSymmetricTensorTriangulated C)

example (n : ℤ) (X : C) : (Sphere n : C) ⊗ X ≅ (shiftFunctor C n).obj X :=
  B.sphereTensorShift n X

example (W : C) (T : Triangle C) (hT : T ∈ distTriang C) :
    letI := B.tensorShift W
    (tensorRight W).mapTriangle.obj T ∈ distTriang C := by
  letI := B.tensorShift W
  letI := B.tensorExact W
  exact Functor.map_distinguished _ T hT

example (W : C) (T : Triangle C) (hT : T ∈ distTriang C) :
    letI := B.closed
    letI := B.ihomShift W
    (ihom W).mapTriangle.obj T ∈ distTriang C := by
  letI := B.closed
  letI := B.ihomShift W
  letI := B.ihomExact W
  exact Functor.map_distinguished _ T hT

example (H : SphereTwistSign B) (r s : ℤ) :
    letI := B.symmetric
    (β_ (Sphere r : C) (Sphere s)).hom ≫ (B.smashSpheres s r).hom ≫
      eqToHom (congrArg (Sphere (C := C)) (add_comm s r)) =
      if Even (r * s) then (B.smashSpheres r s).hom
      else -(B.smashSpheres r s).hom :=
  H.twist r s

-- A sign convention for another chosen closed background cannot be reused.
example (_B' : ClosedSymmetricTensorTriangulated C) (_H : SphereTwistSign B) : True := by
  fail_if_success have : SphereTwistSign _B' := _H
  trivial

-- Merely declaring the record does not select a closed structure for C.
example : True := by
  fail_if_success have : MonoidalClosed C := inferInstance
  trivial
end Background

section Realization
variable {C : Type w} [StableHomotopyCategory.{w,z} C]
  (R : SpectrumModelRealization.{u,v,w,z} C)

example :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    (weakEquivalences R.PointSet).Localization ≌ C :=
  R.toStableModelRealization.homotopyEquivalence

example :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    (weakEquivalences R.PointSet).Q ⋙
      R.toStableModelRealization.homotopyEquivalence.functor ≅ R.localization :=
  R.toStableModelRealization.localizationComparison

example (X : C) :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    IsIso (R.stable.suspensionLoop.unit.app X) := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  exact R.stable.unitIsIso X

example (X : C) :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    IsIso (R.stable.suspensionLoop.counit.app X) := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  exact R.stable.counitIsIso X

example :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    letI := R.monoidal
    ∀ {QI : R.PointSet} (q : QI ⟶ 𝟙_ R.PointSet),
      IsCofibrant QI → weakEquivalences R.PointSet q →
      (R.localization.obj QI ≅ SphereSpectrum (C := C)) :=
  R.unitComparison

-- The homotopy category is not silently supplied with a second model structure.
example : True := by
  fail_if_success have : ModelCategory C := inferInstance
  trivial
end Realization

section SyntheticRealization
variable {Syn : Type w} [SyntheticCategory.{w,z} Syn]
  (R : SyntheticModelRealization.{u,v,w,z} Syn)

example :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    (weakEquivalences R.PointSet).Localization ≌ Syn :=
  R.homotopyEquivalence
end SyntheticRealization

end
