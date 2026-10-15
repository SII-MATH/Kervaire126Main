module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Data
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Unit.Proofs
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Full.Equiv.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory KIP126.Steenrod.Milnor

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)

include B in
/-- A reduced Milnor basis has no vectors in degree zero, so the actual
degree-zero counit kernel vanishes. -/
theorem reducedCooperations_zero_subsingleton :
    letI := mod2HomologyModule H R 0 H.HF2
    letI := mod2HF2HomotopyModule H R 0
    Subsingleton (LinearMap.ker (cooperationCounitF2 H R 0)) := by
  letI := mod2HomologyModule H R 0 H.HF2
  letI := mod2HF2HomotopyModule H R 0
  letI : IsEmpty (PositiveMonomial 0) := ⟨fun d => (lt_irrefl 0) (positiveMonomial_degree_pos d)⟩
  exact (B.basis 0).repr.injective.subsingleton

include B in
theorem cooperationCounitF2_zero_bijective :
    Function.Bijective (cooperationCounitF2 H R 0) := by
  letI := mod2HomologyModule H R 0 H.HF2
  letI := mod2HF2HomotopyModule H R 0
  letI := reducedCooperations_zero_subsingleton H R B
  have hk : LinearMap.ker (cooperationCounitF2 H R 0) = ⊥ := by
    apply bot_unique
    intro x hx
    change x = 0
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker
      (cooperationCounitF2 H R 0)) 0)
  exact ⟨LinearMap.ker_eq_bot.mp hk, cooperationCounit_surjective H R 0⟩

omit B in
theorem cooperationCounitF2_ker_of_ne (n : ℤ) (hn : n ≠ 0) :
    letI := mod2HomologyModule H R n H.HF2
    letI := mod2HF2HomotopyModule H R n
    LinearMap.ker (cooperationCounitF2 H R n) = ⊤ := by
  letI := mod2HomologyModule H R n H.HF2
  letI := mod2HF2HomotopyModule H R n
  rw [cooperationCounitF2_eq_zero_of_ne H R n hn, LinearMap.ker_zero]

end KIP126.StableHomotopy.Cohomology
