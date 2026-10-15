module

public import KIP126.Def.SpectralSequence.Basic.Data
public import KIP126.Def.SpectralSequence.Convergence.Data
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section

namespace KIP126.Synthetic.PageExtension
open CategoryTheory CategoryTheory.Limits KIP126.SpectralSequence
universe v
noncomputable section

/-- An element as a map from the free rank-one module in the same universe. -/
def elementMap {A : ModuleCat.{v} ℤ} (x : A) :
    ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ A :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton ℤ A x).comp ULift.moduleEquiv.toLinearMap)

end
end KIP126.Synthetic.PageExtension
