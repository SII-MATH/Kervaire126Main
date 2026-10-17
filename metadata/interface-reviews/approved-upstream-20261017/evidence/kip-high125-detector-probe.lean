import Mathlib.CategoryTheory.Preadditive.Basic
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {A S T D : C}
theorem high125_detector_probe
    (a : A ⟶ S) (unit : S ⟶ T) (detector : S ⟶ D)
    (e : T ≅ D) (hcomparison : unit ≫ e.hom = detector)
    (ha : a ≫ unit ≠ 0) : a ≫ detector ≠ 0 := by
  rw [←hcomparison,←Category.assoc]
  intro hz
  have hzero : a ≫ unit=0 := by
    apply (cancel_mono e.hom).mp
    simpa only [zero_comp] using hz
  exact ha hzero
