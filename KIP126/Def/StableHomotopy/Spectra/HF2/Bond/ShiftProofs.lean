module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Shift

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
set_option backward.isDefEq.respectTransparency false

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

@[reassoc (attr := simp)]
theorem coefficientNormalizedLoop_arrow (n : ℕ) :
    coefficientNormalizedLoop n ≫ (NormalizedMooreComplex.objX (loopModule n) n).arrow =
      coefficientLoop n := Subobject.factorThru_arrow _ _ _

end KIP126.StableHomotopy.Spectra.HF2Bond
