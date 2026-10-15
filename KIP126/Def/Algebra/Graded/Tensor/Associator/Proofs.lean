module

public import KIP126.Def.Algebra.Graded.Tensor.Associator.Data

@[expose] public section

namespace KIP126.Algebra

open scoped TensorProduct DirectSum

variable {R : Type*} [CommRing R]
  (A B V : ℤ → Type*)
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

@[simp]
theorem gradedTensorAssoc_lof_tmul (n k i : ℤ)
    (a : A i) (b : B (k - i)) (x : V (n - k)) :
    gradedTensorAssoc A B V n
      (DirectSum.lof R ℤ _ k ((DirectSum.lof R ℤ _ i (a ⊗ₜ[R] b)) ⊗ₜ[R] x)) =
      DirectSum.lof R ℤ _ i (a ⊗ₜ[R] (DirectSum.lof R ℤ _ (k - i)
        (b ⊗ₜ[R] (LinearEquiv.cast (R := R) (M := V)
          (show n - k = (n - i) - (k - i) by omega)) x))) := by
  simp [gradedTensorAssoc]

end KIP126.Algebra
