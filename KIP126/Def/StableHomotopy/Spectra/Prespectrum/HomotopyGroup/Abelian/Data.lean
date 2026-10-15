module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.HomotopyGroup.Comparison
public import Mathlib.Algebra.Group.TransferInstance

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

universe u

/-- The original stable quotient is equivalent to the additive group obtained
from the actual level homotopy groups by their actual bonding maps. -/
noncomputable def stableHomotopyGroupEquiv (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy X d ≃ Additive (stableGroupColimit X d) where
  toFun x := Additive.ofMul (stableGroupCode X d x)
  invFun x := stableGroupRealize X d x.toMul
  left_inv := stableGroupRealize_code X d
  right_inv := stableGroupCode_realize X d

/-- Abelian group operations on the original cubical stable quotient. -/
noncomputable instance stableHomotopyAddCommGroup (X : Prespectrum.{u}) (d : ℤ) :
    AddCommGroup (StableHomotopy X d) :=
  (stableHomotopyGroupEquiv X d).addCommGroup

/-- The group comparison includes the proved compatibility of the operations. -/
noncomputable def stableHomotopyAddEquiv (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy X d ≃+ Additive (stableGroupColimit X d) where
  toEquiv := stableHomotopyGroupEquiv X d
  map_add' _ _ := (stableHomotopyGroupEquiv X d).apply_symm_apply _

end KIP126.StableHomotopy.Spectra.Prespectrum
