module

public import KIP126.Def.Algebra.Graded.Tensor.Data

@[expose] public section

namespace KIP126.Algebra

noncomputable section

open scoped TensorProduct DirectSum

variable {R : Type*} [CommRing R]

variable {A B : ℤ → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
  [∀ i, Module R (A i)] [∀ i, Module R (B i)]
  (f : ∀ i, A i →ₗ[R] B i) (V : ℤ → Type*)
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

@[simp]
theorem gradedTensorMap_lof_tmul (n i : ℤ) (a : A i) (v : V (n - i)) :
    gradedTensorMap f V n (DirectSum.lof R ℤ _ i (a ⊗ₜ[R] v)) =
      DirectSum.lof R ℤ _ i (f i a ⊗ₜ[R] v) := by
  simp [gradedTensorMap]

variable [∀ i, Module.Flat R (V i)]

end

end KIP126.Algebra
