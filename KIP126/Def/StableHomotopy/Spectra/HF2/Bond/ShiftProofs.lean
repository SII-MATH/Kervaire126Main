module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Shift

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
set_option backward.isDefEq.respectTransparency false

instance coefficientSimplex_mono (n : ℕ) : Mono (coefficientSimplex n) := by
  unfold coefficientSimplex
  infer_instance

@[reassoc (attr := simp)]
theorem coefficientLoop_inclusion (n : ℕ) :
    coefficientLoop n ≫ (loopInclusion n).app (op ⦋n⦌) = coefficientSimplex n := by
  unfold coefficientLoop
  rw [Category.assoc]
  change _ ≫ (PreservesKernel.iso ((evaluation _ _).obj (op ⦋n⦌))
      (decalageProjection (hf2SimplicialModule (n + 1)))).inv ≫
    ((evaluation _ _).obj (op ⦋n⦌)).map
      (kernel.ι (decalageProjection (hf2SimplicialModule (n + 1)))) = _
  rw [PreservesKernel.iso_inv_ι]
  exact kernel.lift_ι _ _ _

instance coefficientLoop_mono (n : ℕ) : Mono (coefficientLoop n) :=
  mono_of_mono_fac (coefficientLoop_inclusion n)

@[reassoc (attr := simp)]
theorem coefficientNormalizedLoop_arrow (n : ℕ) :
    coefficientNormalizedLoop n ≫ (NormalizedMooreComplex.objX (loopModule n) n).arrow =
      coefficientLoop n := Subobject.factorThru_arrow _ _ _

instance coefficientNormalizedLoop_mono (n : ℕ) : Mono (coefficientNormalizedLoop n) :=
  mono_of_mono_fac (coefficientNormalizedLoop_arrow n)

instance coefficientLoopChainMap_mono (n : ℕ) : Mono (coefficientLoopChainMap n) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  by_cases hi : i = n
  · subst i
    dsimp only [coefficientLoopChainMap]
    rw [HomologicalComplex.mkHomFromSingle_f]
    infer_instance
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) n
      (ModuleCat.of (ZMod 2) (ZMod 2)) i hi).mono _

/-- The simplicial map used to construct the spectrum bonds is injective in
each degree; it is not a zero placeholder. -/
instance coefficientToLoop_mono (n : ℕ) : Mono (coefficientToLoop n) := by
  change Mono (Abelian.DoldKan.equivalence.inverse.map (coefficientLoopChainMap n) ≫
    (Abelian.DoldKan.equivalence.unitIso.app (loopModule n)).inv)
  infer_instance

/-- Actual degreewise injectivity of the coefficient-to-loop map. -/
theorem coefficientToLoop_injective (n r : ℕ) :
    Function.Injective ((coefficientToLoop n).app (op ⦋r⦌)) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

end KIP126.StableHomotopy.Spectra.HF2Bond
