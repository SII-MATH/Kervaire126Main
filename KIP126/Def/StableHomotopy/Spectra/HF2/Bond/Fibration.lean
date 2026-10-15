module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Contraction
public import KIP126.Def.Algebra.SimplicialModule.Kan.Fibration

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

instance decalageProjection_app_isSplitEpi
    (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) (a : SimplexCategoryᵒᵖ) :
    IsSplitEpi ((decalageProjection A).app a) := ⟨⟨decalageProjectionSplitEpi A a⟩⟩

/-- The path projection is onto in every actual simplicial degree. -/
theorem decalageProjection_app_surjective
    (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) (a : SimplexCategoryᵒᵖ) :
    Function.Surjective ((decalageProjection A).app a) := by
  intro x
  refine ⟨(decalageProjectionSplitEpi A a).section_ x, ?_⟩
  exact ConcreteCategory.congr_hom (decalageProjectionSplitEpi A a).id x

instance coefficient_isKanComplex (n : ℕ) : SSet.KanComplex (hf2SimplicialSet n) :=
  KIP126.Algebra.SimplicialModule.underlying_isKanComplex (hf2SimplicialModule n)

instance loopSet_isKanComplex (n : ℕ) : SSet.KanComplex (loopSet n) :=
  KIP126.Algebra.SimplicialModule.underlying_isKanComplex (loopModule n)

instance decalage_isKanComplex (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) :
    SSet.KanComplex (decalage (A ⋙ forget (ModuleCat (ZMod 2)))) :=
  KIP126.Algebra.SimplicialModule.underlying_isKanComplex (decalage A)

open SSet.modelCategoryQuillen in
/-- The actual simplicial path projection is a Kan fibration, by its
explicit degreewise degeneracy sections and the proved horn-lifting theorem. -/
instance decalageProjection_fibration
    (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) :
    HomotopicalAlgebra.Fibration (decalageProjection (A ⋙ forget (ModuleCat (ZMod 2)))) :=
  KIP126.Algebra.SimplicialModule.underlying_fibration_of_degreewise_surjective
    (decalageProjection A) (fun r => decalageProjection_app_surjective A (op ⦋r⦌))

open SSet.modelCategoryQuillen in
/-- The displayed endpoint projection for the actual fixed coefficient path
object is a simplicial Kan fibration. -/
theorem hf2PathProjection_fibration (n : ℕ) :
    HomotopicalAlgebra.Fibration (decalageProjection (hf2SimplicialSet (n + 1))) :=
  decalageProjection_fibration (hf2SimplicialModule (n + 1))

end KIP126.StableHomotopy.Spectra.HF2Bond
