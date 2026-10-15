module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Full.Basic.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Steenrod.Milnor

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- In every nonzero degree the actual counit vanishes, so every
cooperation is already reduced. The underlying inclusion is unchanged. -/
def cooperationReducedEquivOfNe (n : ℤ) (hn : n ≠ 0) :
    letI := mod2HomologyModule H R n H.HF2
    letI := mod2HF2HomotopyModule H R n
    mod2HomologyF2 H R n H.HF2 ≃ₗ[ZMod 2] LinearMap.ker (cooperationCounitF2 H R n) :=
  letI := mod2HomologyModule H R n H.HF2
  letI := mod2HF2HomotopyModule H R n
  ((LinearEquiv.ofEq _ _ (cooperationCounitF2_ker_of_ne H R n hn)).trans
    (Submodule.topEquiv)).symm

variable (B : Mod2ReducedMilnorBasis H R)

/-- Complete the given reduced basis with the actual unit in degree zero.
Only the reduced basis, ring unit, and Eilenberg--Mac Lane coefficients
are used. This is a graded vector-space comparison, not an algebra or
coalgebra comparison, and there is no new existence input. -/
def cooperationMilnorEquiv (n : ℤ) :
    mod2HomologyF2 H R n H.HF2 ≃ₗ[ZMod 2] (MilnorMonomial n →₀ ZMod 2) := by
  classical
  by_cases hn : n = 0
  · subst n
    letI := mod2HomologyModule H R 0 H.HF2
    letI := mod2HF2HomotopyModule H R 0
    exact ((LinearEquiv.ofBijective (cooperationCounitF2 H R 0)
      (cooperationCounitF2_zero_bijective H R B)).trans (mod2Pi0LinearEquiv H R)).trans
        milnorZeroCoefficientsEquiv.symm
  · letI := mod2HomologyModule H R n H.HF2
    letI := mod2HF2HomotopyModule H R n
    exact (cooperationReducedEquivOfNe H R n hn).trans
      ((B.basis n).repr.trans (Finsupp.domLCongr (milnorMonomialEquivPositive n hn).symm))

end

end KIP126.StableHomotopy.Cohomology
