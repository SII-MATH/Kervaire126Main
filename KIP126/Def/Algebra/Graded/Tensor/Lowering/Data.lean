module

public import KIP126.Def.Algebra.Graded.Tensor.Data

@[expose] public section

namespace KIP126.Algebra

noncomputable section

variable {R : Type*} [CommRing R]
  (A : ℤ → Type*) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  {V W : ℤ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, AddCommGroup (W i)]
  [∀ i, Module R (V i)] [∀ i, Module R (W i)]

/-- Tensor a degree-minus-one map on the right with the identity on the left.
The cast records the equality `(n-i)-1 = (n-1)-i` of actual degrees. -/
def gradedTensorLowerMap (g : ∀ i, V i →ₗ[R] W (i - 1)) (n : ℤ) :
    gradedTensor R A V n →ₗ[R] gradedTensor R A W (n - 1) :=
  DirectSum.lmap fun i =>
    (((LinearEquiv.cast (R := R) (M := W) (show n - i - 1 = n - 1 - i by omega)).toLinearMap).comp
      (g (n - i))).lTensor (A i)

end

end KIP126.Algebra
