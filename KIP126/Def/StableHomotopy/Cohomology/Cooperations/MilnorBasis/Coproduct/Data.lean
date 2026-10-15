module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Full.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Kunneth.Diagonal.Data
public import Mathlib.Algebra.Algebra.Bilinear

@[expose] public section

/-! Polynomial coordinates for actual cooperations and their tensor square.
These maps do not assert the Milnor coproduct formula. -/

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Steenrod.Milnor KIP126.Algebra
open scoped TensorProduct DirectSum

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)

/-- Place a single-slot exponent vector in the existing polynomial model. -/
def milnorMonomialPolynomial {n : ℤ} (d : MilnorMonomial n) : TensorPower 1 :=
  MvPolynomial.monomial (d.val.mapDomain fun j => ((0 : Fin 1), j)) 1

/-- The full linear coordinate map followed by monomial realization. -/
def cooperationMilnorPolynomial (n : ℤ) :
    mod2HomologyF2 H R n H.HF2 →ₗ[F2] TensorPower 1 :=
  (Finsupp.linearCombination F2 milnorMonomialPolynomial).comp
    (cooperationMilnorEquiv H R B n).toLinearMap

/-- Realize the two factors in adjacent polynomial slots. No Künneth
comparison, Adams page, or differential is needed to define this map. -/
def cooperationTensorMilnorPolynomial (n : ℤ) :
    cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n →ₗ[F2]
      TensorPower 2 := by
  letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  let left : TensorPower 1 →ₗ[F2] TensorPower 2 :=
    (MvPolynomial.rename fun a : Fin 1 × ℕ => (a.1.castAdd 1, a.2)).toLinearMap
  let right : TensorPower 1 →ₗ[F2] TensorPower 2 :=
    (MvPolynomial.rename fun a : Fin 1 × ℕ => (a.1.natAdd 1, a.2)).toLinearMap
  exact DirectSum.toModule F2 ℤ _ fun i =>
    (LinearMap.mul' F2 (TensorPower 2)).comp
      (TensorProduct.map (left.comp (cooperationMilnorPolynomial H R B i))
        (right.comp (cooperationMilnorPolynomial H R B (n - i))))

end

end KIP126.StableHomotopy.Cohomology
