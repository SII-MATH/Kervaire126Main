module

public import KIP126.Def.Algebra.Graded.Tensor.Basic.Proofs

@[expose] public section

namespace KIP126.Algebra

noncomputable section

open scoped TensorProduct DirectSum

variable {R : Type*} [CommRing R]

/-- Evaluation at the sole possibly nonzero summand. -/
def directSumConcentratedEquiv {ι : Type*} [DecidableEq ι] (A : ι → Type*)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → Subsingleton (A i)) : (⨁ i, A i) ≃ₗ[R] A i₀ :=
  { DFinsupp.lapply (R := R) (M := A) i₀ with
    invFun := DFinsupp.lsingle (R := R) i₀
    left_inv := fun x => by
      ext i
      by_cases hi : i = i₀
      · subst i
        simp
      · letI := h i hi
        exact Subsingleton.elim _ _
    right_inv := fun x => by simp }

/-- Tensoring a kernel with a flat module preserves its actual inclusion. -/
def rTensorKernelEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (f : A →ₗ[R] B)
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Flat R V] :
    (LinearMap.ker f) ⊗[R] V ≃ₗ[R] LinearMap.ker (f.rTensor V) :=
  (LinearEquiv.ofInjective ((LinearMap.ker f).subtype.rTensor V)
    (Module.Flat.rTensor_preserves_injective_linearMap _ (LinearMap.ker f).injective_subtype)).trans
      (LinearEquiv.ofEq _ _ (rTensor_kernel_range f V))

/-- A direct sum of kernels is the kernel of the componentwise map. -/
def directSumKernelEquiv {ι : Type*} {A B : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module R (A i)] [∀ i, Module R (B i)] (f : ∀ i, A i →ₗ[R] B i) :
    (⨁ i, LinearMap.ker (f i)) ≃ₗ[R] LinearMap.ker (DirectSum.lmap f) :=
  (LinearEquiv.ofInjective (DirectSum.lmap fun i => (LinearMap.ker (f i)).subtype)
    ((DirectSum.lmap_injective _).mpr fun i => (LinearMap.ker (f i)).injective_subtype)).trans
      (LinearEquiv.ofEq _ _ (directSum_kernel_range f))

/-- The degree `n` part of the ordinary graded tensor product, using finite support. -/
abbrev gradedTensor (R : Type*) [CommRing R] (A V : ℤ → Type*)
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (A i)] [∀ i, Module R (V i)] (n : ℤ) :=
  ⨁ i : ℤ, A i ⊗[R] V (n - i)

/-- A map on the first factor of a graded tensor product. -/
def gradedTensorMap {A B : ℤ → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module R (A i)] [∀ i, Module R (B i)]
    (f : ∀ i, A i →ₗ[R] B i) (V : ℤ → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (n : ℤ) :
    gradedTensor R A V n →ₗ[R] gradedTensor R B V n :=
  DirectSum.lmap fun i => (f i).rTensor (V (n - i))

/-- A map on the second factor of a graded tensor product. -/
def gradedTensorMapRight (A : ℤ → Type*)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    {V W : ℤ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, AddCommGroup (W i)]
    [∀ i, Module R (V i)] [∀ i, Module R (W i)]
    (g : ∀ i, V i →ₗ[R] W i) (n : ℤ) :
    gradedTensor R A V n →ₗ[R] gradedTensor R A W n :=
  DirectSum.lmap fun i => (g (n - i)).lTensor (A i)

/-- Degreewise kernel preservation for the graded tensor product. -/
def gradedTensorKernelEquiv {A B : ℤ → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module R (A i)] [∀ i, Module R (B i)]
    (f : ∀ i, A i →ₗ[R] B i) (V : ℤ → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, Module.Flat R (V i)] (n : ℤ) :
    gradedTensor R (fun i => LinearMap.ker (f i)) V n ≃ₗ[R]
      LinearMap.ker (gradedTensorMap f V n) :=
  (DirectSum.congrLinearEquiv fun i => rTensorKernelEquiv (f i) (V (n - i))).trans
    (directSumKernelEquiv fun i => (f i).rTensor (V (n - i)))

end

end KIP126.Algebra
