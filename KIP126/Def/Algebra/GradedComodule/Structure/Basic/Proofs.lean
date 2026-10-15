module

public import KIP126.Def.Algebra.GradedComodule.Structure.Basic.Data
public import Mathlib.CategoryTheory.Abelian.Basic

@[expose] public section

namespace KIP126.Algebra.GradedComodule

open CategoryTheory CategoryTheory.Limits GradedVectorSpace

universe u
variable {K : Type u} [Field K] (C : Comon (GrVect K))

/-- The actual coimage-to-image comparison in graded right comodules is an
isomorphism. Both objects are constructed by the finite (co)limits created
by the forgetful functor. This is a property obligation, not chosen data. -/
theorem coimageImageComparison_isIso {X Y : RightComodule C} (f : X ⟶ Y) :
    IsIso (Abelian.coimageImageComparison f) := by
  let F := Comonad.forget (rightTensorComonad C)
  letI : PreservesFiniteLimits F := ⟨fun J _ _ => inferInstance⟩
  haveI : IsIso (F.map (Abelian.coimageImageComparison f)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso (Abelian.PreservesCoimageImageComparison.iso F f).hom]
    infer_instance
  exact isIso_of_reflects_iso (Abelian.coimageImageComparison f) F

attribute [instance] coimageImageComparison_isIso

end KIP126.Algebra.GradedComodule
