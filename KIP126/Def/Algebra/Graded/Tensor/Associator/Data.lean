module

public import KIP126.Def.Algebra.Graded.Tensor.Data
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

@[expose] public section

namespace KIP126.Algebra

noncomputable section

open scoped TensorProduct DirectSum

variable {R : Type*} [CommRing R]
  (A B V : ℤ → Type*)
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- Reassociate the finite-support graded tensor product, retaining the
integer degrees. This is the forward map needed to apply a coproduct to
the first factor; it is not a chosen coordinate equivalence. -/
def gradedTensorAssoc (n : ℤ) :
    gradedTensor R (gradedTensor R A B) V n →ₗ[R]
      gradedTensor R A (gradedTensor R B V) n :=
  DirectSum.toModule R ℤ _ fun k =>
    (DirectSum.toModule R ℤ _ fun i =>
      (DirectSum.lof R ℤ (fun i => A i ⊗[R] gradedTensor R B V (n - i)) i).comp
        ((((DirectSum.lof R ℤ (fun j => B j ⊗[R] V ((n - i) - j)) (k - i)).comp
          ((LinearEquiv.cast (R := R) (M := V)
            (show n - k = (n - i) - (k - i) by omega)).toLinearMap.lTensor (B (k - i))))
          |>.lTensor (A i)).comp
          (TensorProduct.assoc R (A i) (B (k - i)) (V (n - k))).toLinearMap)).comp
      (TensorProduct.directSumLeft R R (fun i => A i ⊗[R] B (k - i))
        (V (n - k))).toLinearMap

end

end KIP126.Algebra
