module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Reduced.Data
public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Equiv.Data

@[expose] public section

/-! A below-page Milnor basis input, and the algebraic tensor conversion it
supports. No value for the fixed sphere foundation is postulated. A basis
alone does not assert the coproduct formula or differential compatibility. -/

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Steenrod.Milnor

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- A monomial-indexed basis on genuine reduced cooperations, not on Adams
pages. Its existence is an explicit remaining lower-level input. -/
structure Mod2ReducedMilnorBasis where
  basis : ∀ n : ℤ,
    letI := mod2HomologyModule H R n H.HF2
    letI := mod2HF2HomotopyModule H R n
    Module.Basis (PositiveMonomial n) (ZMod 2) (LinearMap.ker (cooperationCounitF2 H R n))

/-- Convert one genuine reduced tensor step into one additional Milnor word
slot, using only the reduced-cooperation basis and the remaining factor's coordinates. -/
def reducedTensorMilnorWordEquiv (B : Mod2ReducedMilnorBasis H R)
    (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
    (s : ℕ) (e : ∀ i, V i ≃ₗ[ZMod 2] (MilnorWord s (i + s) →₀ ZMod 2)) (n : ℤ) :
    reducedCooperationTensor H R V (n + 1) ≃ₗ[ZMod 2]
      (MilnorWord (s + 1) (n + (s + 1 : ℕ)) →₀ ZMod 2) :=
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) := fun i =>
    mod2HF2HomotopyModule H R i
  (DirectSum.congrLinearEquiv fun i =>
    TensorProduct.congr (B.basis i).repr ((e (n + 1 - i)).trans
      (LinearEquiv.cast (R := ZMod 2) (M := fun t => MilnorWord s t →₀ ZMod 2)
        (show n + 1 - i + s = n + (s + 1 : ℕ) - i by omega)))).trans
    (wordTensorEquiv s (n + (s + 1 : ℕ)))

end

end KIP126.StableHomotopy.Cohomology
