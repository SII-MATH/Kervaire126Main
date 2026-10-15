module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Tensor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory KIP126.Algebra
open scoped TensorProduct DirectSum

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]

/-- Removing the coefficient factor does not change the kernel. -/
theorem cooperationTensorAugmentation_ker (n : ℤ) :
    LinearMap.ker (cooperationTensorAugmentation H R V n) =
      LinearMap.ker (cooperationTensorCounit H R V n) := by
  ext x
  change coefficientTensorEquiv H R V n (cooperationTensorCounit H R V n x) = 0 ↔ _
  exact (coefficientTensorEquiv H R V n).map_eq_zero_iff

/-- The coefficient identification uses exactly the prescribed π₀ coordinate. -/
theorem coefficientTensorEquiv_zero_tmul (n : ℤ) (a : HomotopyGroup 0 H.HF2)
    (v : V (n - 0)) :
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) := fun i =>
      mod2HF2HomotopyModule H R i
    coefficientTensorEquiv H R V n
      (DirectSum.lof (ZMod 2) ℤ _ 0 (a ⊗ₜ[ZMod 2] v)) =
      LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero n) (H.pi0Equiv a • v) := by
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) := fun i =>
    mod2HF2HomotopyModule H R i
  change LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero n)
    (TensorProduct.lid (ZMod 2) (V (n - 0))
      (TensorProduct.congr (mod2Pi0LinearEquiv H R) (LinearEquiv.refl (ZMod 2) _)
        (a ⊗ₜ[ZMod 2] v))) = _
  rw [TensorProduct.congr_tmul, TensorProduct.lid_tmul]
  rfl

/-- Away from degree zero the actual cooperation counit is zero. -/
theorem cooperationCounitF2_eq_zero_of_ne (n : ℤ) (hn : n ≠ 0) :
    cooperationCounitF2 H R n = 0 := by
  letI := H.homotopy_vanishes n hn
  exact Subsingleton.elim _ _

section MapComposition

variable {W U : ℤ → Type*}
  [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 2) (W i)]
  [∀ i, AddCommGroup (U i)] [∀ i, Module (ZMod 2) (U i)]

theorem cooperationTensorMap_comp (f : ∀ i, V i →ₗ[ZMod 2] W i)
    (g : ∀ i, W i →ₗ[ZMod 2] U i) (n : ℤ) :
    (cooperationTensorMap H R W g n).comp (cooperationTensorMap H R V f n) =
      cooperationTensorMap H R V (fun i => (g i).comp (f i)) n := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  ext i a x
  simp [cooperationTensorMap, KIP126.Algebra.gradedTensorMapRight]

end MapComposition

end

end KIP126.StableHomotopy.Cohomology
