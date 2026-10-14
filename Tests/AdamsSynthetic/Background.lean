module

import KIP126.Def.AdamsSynthetic

/-! Fixed categories, closed structure, recovery and point-set localization. -/
open CategoryTheory CategoryTheory.Limits MonoidalCategory Pretriangulated
open HomotopicalAlgebra KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic.Standard
noncomputable section

example (n : ℤ) (X : Spectrum) :
    (Sphere n : Spectrum) ⊗ X ≅ (shiftFunctor Spectrum n).obj X :=
  closedBackground.sphereTensorShift n X

example (W : Spectrum) (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum) :
    letI := closedBackground.tensorShift W
    (tensorRight W).mapTriangle.obj T ∈ distTriang Spectrum := by
  letI := closedBackground.tensorShift W
  letI := closedBackground.tensorExact W
  exact Functor.map_distinguished _ T hT

example (r s : ℤ) :
    letI := closedBackground.symmetric
    (β_ (Sphere r : Spectrum) (Sphere s)).hom ≫ (closedBackground.smashSpheres s r).hom ≫
      eqToHom (congrArg (Sphere (C := Spectrum)) (add_comm s r)) =
      if Even (r*s) then (closedBackground.smashSpheres r s).hom
      else -(closedBackground.smashSpheres r s).hom := sphere_twist r s

example : nu.functor ⋙ realization ≅ 𝟭 Spectrum := nuRealizationIso
example : realization ⊣ spectralYoneda := realizationAdjunction
example : spectralYoneda.FullyFaithful := spectralYonedaFullyFaithful

example :
    letI := spectrumRealization.pointSetCategory
    letI := spectrumRealization.pointSetModel
    (weakEquivalences spectrumRealization.PointSet).Localization ≌ Spectrum :=
  spectrumHomotopyEquivalence

example :
    letI := syntheticRealization.pointSetCategory
    letI := syntheticRealization.pointSetModel
    (weakEquivalences syntheticRealization.PointSet).Localization ≌ SyntheticSpectrum :=
  syntheticHomotopyEquivalence

-- A point-set model structure is not confused with the homotopy category.
example : True := by
  fail_if_success have : ModelCategory Spectrum := inferInstance
  trivial
-- The two fixed categories cannot be exchanged by definitional equality.
example : True := by
  fail_if_success have : Spectrum = SyntheticSpectrum := rfl
  trivial
end
