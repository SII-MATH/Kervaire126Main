module

public import KIP126.Def.Algebra.Graded.Tensor.Data

@[expose] public section

namespace KIP126.Algebra

noncomputable section

open scoped TensorProduct DirectSum

variable {R : Type*} [CommRing R]

@[simp]
theorem rTensorKernelEquiv_coe {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (f : A →ₗ[R] B)
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Flat R V]
    (x : (LinearMap.ker f) ⊗[R] V) :
    (rTensorKernelEquiv f V x : A ⊗[R] V) = (LinearMap.ker f).subtype.rTensor V x := rfl

@[simp]
theorem directSumKernelEquiv_coe {ι : Type*} {A B : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module R (A i)] [∀ i, Module R (B i)] (f : ∀ i, A i →ₗ[R] B i)
    (x : ⨁ i, LinearMap.ker (f i)) :
    (directSumKernelEquiv f x : ⨁ i, A i) =
      DirectSum.lmap (fun i => (LinearMap.ker (f i)).subtype) x := rfl

variable {A B : ℤ → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
  [∀ i, Module R (A i)] [∀ i, Module R (B i)]
  (f : ∀ i, A i →ₗ[R] B i) (V : ℤ → Type*)
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

@[simp]
theorem gradedTensorMap_apply (n i : ℤ) (x : gradedTensor R A V n) :
    gradedTensorMap f V n x i = (f i).rTensor (V (n - i)) (x i) := rfl

@[simp]
theorem gradedTensorMap_lof_tmul (n i : ℤ) (a : A i) (v : V (n - i)) :
    gradedTensorMap f V n (DirectSum.lof R ℤ _ i (a ⊗ₜ[R] v)) =
      DirectSum.lof R ℤ _ i (f i a ⊗ₜ[R] v) := by
  simp [gradedTensorMap]

variable [∀ i, Module.Flat R (V i)]

/-- The kernel equivalence keeps the ordinary tensor representatives. -/
theorem gradedTensorKernelEquiv_coe (n : ℤ)
    (x : gradedTensor R (fun i => LinearMap.ker (f i)) V n) :
    (gradedTensorKernelEquiv f V n x : gradedTensor R A V n) =
      gradedTensorMap (fun i => (LinearMap.ker (f i)).subtype) V n x := by
  ext i
  rfl

end

end KIP126.Algebra
