module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

/-! Kernel preservation needed for the normalized Adams tensor comparison. -/

namespace KIP126.Algebra

open scoped TensorProduct DirectSum

variable {R : Type*} [CommRing R]

theorem rTensor_kernel_range {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (f : A →ₗ[R] B)
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Flat R V] :
    LinearMap.range ((LinearMap.ker f).subtype.rTensor V) =
      LinearMap.ker (f.rTensor V) :=
  (Module.Flat.rTensor_exact V f.exact_subtype_ker_map).linearMap_ker_eq.symm

theorem directSum_kernel_range {ι : Type*} {A B : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module R (A i)] [∀ i, Module R (B i)] (f : ∀ i, A i →ₗ[R] B i) :
    LinearMap.range (DirectSum.lmap fun i => (LinearMap.ker (f i)).subtype) =
      LinearMap.ker (DirectSum.lmap f) := by
  rw [DirectSum.range_lmap, DirectSum.ker_lmap]
  simp only [Submodule.range_subtype]

end KIP126.Algebra
