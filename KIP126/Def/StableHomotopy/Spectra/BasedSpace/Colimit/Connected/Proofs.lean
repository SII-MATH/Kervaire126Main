module

public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.Under.Data
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory CategoryTheory.Limits

universe u v w

/-- In a connected based diagram the basepoints already have a common
image, so its based colimit is also the actual topological colimit. -/
noncomputable instance forgetToTop_preservesConnectedColimits
    (J : Type w) [Category.{v} J] [IsConnected J] :
    PreservesColimitsOfShape J forgetToTop.{u} := by
  change PreservesColimitsOfShape J (underEquivalence.functor ⋙ Under.forget pointSpace)
  infer_instance

end KIP126.StableHomotopy.Spectra.BasedSpace
