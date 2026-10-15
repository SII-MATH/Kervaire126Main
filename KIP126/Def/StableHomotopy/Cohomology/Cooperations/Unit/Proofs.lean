module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Unit.Data
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Tensor.Proofs
public import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

noncomputable section

open CategoryTheory MonoidalCategory KIP126.Classical.Adams KIP126.Algebra
open scoped TensorProduct DirectSum

universe u v w

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

theorem cooperationCounit_unit :
    cooperationCounit H R 0 (cooperationUnit H) = H.pi0Equiv.symm 1 := by
  change (H.pi0Equiv.symm 1 ≫ adamsUnit H.unit H.HF2) ≫ R.monoid.mul = _
  rw [Category.assoc, adamsUnit_mul, Category.comp_id]

/-- The actual multiplication counit is split by the actual unit, in
every homotopy degree. -/
theorem cooperationCounit_surjective (n : ℤ) :
    Function.Surjective (cooperationCounit H R n) := by
  intro x
  refine ⟨inducedMap (adamsUnit H.unit H.HF2) n x, ?_⟩
  change (x ≫ adamsUnit H.unit H.HF2) ≫ R.monoid.mul = x
  rw [Category.assoc, adamsUnit_mul, Category.comp_id]

variable [MonoidalPreadditive C]
  (V : ℤ → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]

theorem cooperationTensorUnit_apply (n : ℤ) (x : V n) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    cooperationTensorUnit H R V n x =
      DirectSum.lof (ZMod 2) ℤ _ 0 (cooperationUnit H ⊗ₜ[ZMod 2]
        (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero n).symm) x) := rfl

/-- The coefficient counit retracts the actual elementary unit tensor. -/
theorem cooperationTensorUnit_augmentation (n : ℤ) (x : V n) :
    cooperationTensorAugmentation H R V n (cooperationTensorUnit H R V n x) = x := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  simp only [cooperationTensorAugmentation, LinearMap.comp_apply,
    cooperationTensorUnit_apply, cooperationTensorCounit, gradedTensorMap_lof_tmul,
    LinearEquiv.coe_coe]
  rw [coefficientTensorEquiv_zero_tmul, cooperationCounitF2_apply, cooperationCounit_unit]
  simp

end

end KIP126.StableHomotopy.Cohomology
