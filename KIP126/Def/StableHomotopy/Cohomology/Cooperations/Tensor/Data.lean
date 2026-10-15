module

public import KIP126.Def.Algebra.Graded.Tensor.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Coefficients.Proofs
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

/-! Genuine graded cooperations and their reduced tensor products. These use
the represented groups and derived F₂ scalars, not Milnor coordinates. -/

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Algebra
open scoped TensorProduct DirectSum

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

variable (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]

/-- The total-degree part of cooperations tensored with a graded module. -/
abbrev cooperationTensor (n : ℤ) :=
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
  gradedTensor (ZMod 2) (Mod2Cooperations H) V n

/-- The tensor product with the actual coefficient groups `π_* H`. -/
abbrev coefficientTensor (n : ℤ) :=
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) := fun i =>
    mod2HF2HomotopyModule H R i
  gradedTensor (ZMod 2) (fun i => HomotopyGroup i H.HF2) V n

/-- Tensor the actual multiplication-induced counit with the identity. -/
def cooperationTensorCounit (n : ℤ) :
    cooperationTensor H R V n →ₗ[ZMod 2] coefficientTensor H R V n :=
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) := fun i =>
    mod2HF2HomotopyModule H R i
  gradedTensorMap (cooperationCounitF2 H R) V n

/-- The reduced cooperation tensor product, with reduction in each degree. -/
abbrev reducedCooperationTensor (n : ℤ) :=
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) := fun i =>
    mod2HF2HomotopyModule H R i
  gradedTensor (ZMod 2) (fun i => LinearMap.ker (cooperationCounitF2 H R i)) V n

/-- The reduced tensor product is the kernel of the tensor counit.
Flatness is derived from the coefficient field, not supplied as extra data. -/
def reducedCooperationTensorEquiv (n : ℤ) :
    reducedCooperationTensor H R V n ≃ₗ[ZMod 2]
      LinearMap.ker (cooperationTensorCounit H R V n) :=
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) := fun i =>
    mod2HF2HomotopyModule H R i
  gradedTensorKernelEquiv (cooperationCounitF2 H R) V n

/-- Since `π_* H` is concentrated in degree zero, its tensor product is `V`.
This is constructed from the specified π₀ coordinate and vanishing, not postulated. -/
def coefficientTensorEquiv (n : ℤ) : coefficientTensor H R V n ≃ₗ[ZMod 2] V n :=
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) := fun i =>
    mod2HF2HomotopyModule H R i
  (directSumConcentratedEquiv
    (fun i => HomotopyGroup i H.HF2 ⊗[ZMod 2] V (n - i)) 0 (fun i hi => by
      letI := H.homotopy_vanishes i hi
      infer_instance)).trans
    ((TensorProduct.congr (mod2Pi0LinearEquiv H R) (LinearEquiv.refl (ZMod 2) _)).trans
      ((TensorProduct.lid (ZMod 2) (V (n - 0))).trans
        (LinearEquiv.cast (M := V) (sub_zero n))))

/-- The graded tensor counit with its coefficient factor canonically removed. -/
def cooperationTensorAugmentation (n : ℤ) : cooperationTensor H R V n →ₗ[ZMod 2] V n :=
  (coefficientTensorEquiv H R V n).toLinearMap.comp (cooperationTensorCounit H R V n)

/-- The map of tensor products induced by a map of the remaining graded module. -/
def cooperationTensorMap {W : ℤ → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 2) (W i)]
    (g : ∀ i, V i →ₗ[ZMod 2] W i) (n : ℤ) :
    cooperationTensor H R V n →ₗ[ZMod 2] cooperationTensor H R W n :=
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
  gradedTensorMapRight (Mod2Cooperations H) g n

end

end KIP126.StableHomotopy.Cohomology
