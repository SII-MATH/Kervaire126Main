module

public import KIP126.Def.AdamsSynthetic.Standard.Background
public import KIP126.Def.AdamsSynthetic.ESSShift

/-! Compatibility of the fixed first-quotient comparison with the actual
positive weight shift and classical suspension. These are the two separately
authorized upstream proof responsibilities needed for the Mahowald labels.
The user authorized their addition on 2026-10-16; they are new compatibility
obligations, not proofs recovered from the migration baseline. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The first-quotient label commutes with the positive weight shift and
every quotient comparison satisfying the actual inclusion square. -/
public theorem firstQuotient_positive_shift
    (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (hε : XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ 1)) :
    homotopyRegrade (by simp) (by simp)
      (shiftHomotopyClass (0,1) (t-s,t)
        (homotopyRegrade rfl (by simp) ((model.firstQuotient X 0 s t).symm x) ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)) ≫ ε.inv =
        (model.firstQuotient X 1 s t).symm x := by
  sorry

/-- The first-quotient labels of a class and its actual classical suspension
agree after the fixed ν suspension and quotient comparisons. -/
public theorem firstQuotient_suspension
    (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (sx : (model.classical.obj ((ClassicalObject.shift 1 X).obj model.auxiliary)).Page 2 (s,t+1))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (hε : XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ 1))
    (hsx : (model.classicalSuspension X).DesuspendsClass s (t+1) sx (by simpa using x)) :
    (homotopyRegrade (w' := t+1) rfl (by simp)
        ((model.firstQuotient (.shift 1 X) 0 s (t+1)).symm sx) ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) ≫
      XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom 1 ≫ ε.hom =
    homotopyRegrade (by simp; omega) (by simp)
      (shiftHomotopyClass (1,1) (t-s,t)
        (homotopyRegrade rfl (by simp) ((model.firstQuotient X 0 s t).symm x) ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)) := by
  sorry

end
end KIP126.AdamsSynthetic.Standard
