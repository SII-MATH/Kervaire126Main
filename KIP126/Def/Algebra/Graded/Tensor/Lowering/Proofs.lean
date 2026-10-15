module

public import KIP126.Def.Algebra.Graded.Tensor.Lowering.Data

@[expose] public section

namespace KIP126.Algebra

noncomputable section

open scoped TensorProduct DirectSum

variable {R : Type*} [CommRing R]
  (A : ℤ → Type*) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  {V W U : ℤ → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, AddCommGroup (W i)] [∀ i, AddCommGroup (U i)]
  [∀ i, Module R (V i)] [∀ i, Module R (W i)] [∀ i, Module R (U i)]

theorem gradedTensorLowerMap_lof_tmul (g : ∀ i, V i →ₗ[R] W (i - 1))
    (n i : ℤ) (a : A i) (x : V (n - i)) :
    gradedTensorLowerMap A g n (DirectSum.lof R ℤ _ i (a ⊗ₜ[R] x)) =
      DirectSum.lof R ℤ _ i (a ⊗ₜ[R]
        LinearEquiv.cast (R := R) (M := W) (show n - i - 1 = n - 1 - i by omega)
          (g (n - i) x)) := by
  simp [gradedTensorLowerMap]

/-- A degree-preserving map followed by a lowering map can be tensored in
one step or in two steps; no tensor exactness is needed. -/
theorem gradedTensorLowerMap_comp (f : ∀ i, V i →ₗ[R] W i)
    (g : ∀ i, W i →ₗ[R] U (i - 1)) (n : ℤ) :
    (gradedTensorLowerMap A g n).comp (gradedTensorMapRight A f n) =
      gradedTensorLowerMap A (fun i => (g i).comp (f i)) n := by
  ext i a x
  simp [gradedTensorLowerMap, gradedTensorMapRight]

end

end KIP126.Algebra
