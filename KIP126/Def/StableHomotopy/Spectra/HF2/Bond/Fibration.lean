module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Contraction
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.Tactic.FinCases
public import KIP126.Def.Algebra.SimplicialModule.Kernel.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
set_option backward.isDefEq.respectTransparency false

/-- Every degree of the actual path projection has the explicit degeneracy
section; no surjectivity hypothesis is supplied. -/
def decalageProjectionSplitEpi (A : SimplicialObject (ModuleCat.{0} (ZMod 2)))
    (a : SimplexCategoryᵒᵖ) : SplitEpi ((decalageProjection A).app a) where
  section_ := A.σ (0 : Fin (a.unop.len + 1))
  id := A.δ_comp_σ_self

/-- The path projection is onto in every actual simplicial degree. -/
theorem decalageProjection_app_surjective
    (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) (a : SimplexCategoryᵒᵖ) :
    Function.Surjective ((decalageProjection A).app a) := by
  intro x
  refine ⟨(decalageProjectionSplitEpi A a).section_ x, ?_⟩
  exact ConcreteCategory.congr_hom (decalageProjectionSplitEpi A a).id x

end KIP126.StableHomotopy.Spectra.HF2Bond
