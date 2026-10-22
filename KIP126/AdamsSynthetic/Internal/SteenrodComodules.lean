module

public import KIP126.AdamsSynthetic.Context
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.TensorProduct.Basic

/-! The fixed Milnor source for the coefficient-Ext comparison.

The objects are actual graded comodules for the displayed polynomial
coproduct. Neither an Adams page nor a synthetic quotient occurs in their
definition. Recognition of this source and its exact structure is separate.
-/

namespace KIP126.AdamsSynthetic.Internal.SteenrodComodules
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Localization
open scoped BigOperators TensorProduct
noncomputable section

abbrev F2 := ZMod 2
abbrev DualSteenrod := MvPolynomial ℕ F2

def xi : ℕ → DualSteenrod
  | 0 => 1
  | j+1 => MvPolynomial.X j

def milnorCounit : DualSteenrod →ₐ[F2] F2 :=
  MvPolynomial.aeval (fun _ => 0)

def milnorCoproduct : DualSteenrod →ₐ[F2] DualSteenrod ⊗[F2] DualSteenrod :=
  MvPolynomial.aeval fun j =>
    ∑ i ∈ Finset.range (j+2),
      ((xi (j+1-i)) ^ (2^i)) ⊗ₜ[F2] xi i

def milnorWeight (j : ℕ) : ℕ := 2^(j+1)-1

/-- Degree `n` of the actual convolution tensor `A_* ⊗ M`. -/
def tensorGrade (M : ModuleCat.{0} F2) (grade : ℤ → Submodule F2 M)
    (n : ℤ) : Submodule F2 (DualSteenrod ⊗[F2] M) :=
  Submodule.span F2 {z | ∃ (d : ℕ) (a : DualSteenrod) (m : M),
    MvPolynomial.IsWeightedHomogeneous milnorWeight a d ∧
      m ∈ grade (n-d) ∧ z=a ⊗ₜ[F2] m}

/-- A genuine internally graded left comodule over the fixed Milnor
polynomial coalgebra. Every element has a finite homogeneous decomposition. -/
structure GradedSteenrodComodule where
  carrier : ModuleCat.{0} F2
  grade : ℤ → Submodule F2 carrier
  internal : DirectSum.IsInternal grade
  rho : carrier →ₗ[F2] DualSteenrod ⊗[F2] carrier
  counit :
    (TensorProduct.lid F2 carrier).toLinearMap ∘ₗ
      milnorCounit.toLinearMap.rTensor carrier ∘ₗ rho = LinearMap.id
  coassoc :
    (TensorProduct.assoc F2 DualSteenrod DualSteenrod carrier).toLinearMap ∘ₗ
      milnorCoproduct.toLinearMap.rTensor carrier ∘ₗ rho =
        rho.lTensor DualSteenrod ∘ₗ rho
  graded : ∀ (n : ℤ) (m : carrier), m ∈ grade n →
    rho m ∈ tensorGrade carrier grade n

namespace GradedSteenrodComodule

/-- A degree-zero linear map preserving the actual coaction. -/
structure Hom (M N : GradedSteenrodComodule) where
  linearMap : M.carrier →ₗ[F2] N.carrier
  graded : ∀ (n : ℤ) (m : M.carrier), m ∈ M.grade n →
    linearMap m ∈ N.grade n
  coaction : linearMap.lTensor DualSteenrod ∘ₗ M.rho =
    N.rho ∘ₗ linearMap

@[ext] theorem Hom.ext {M N : GradedSteenrodComodule}
    {f g : Hom M N} (h : f.linearMap=g.linearMap) : f=g := by
  cases f; cases g; cases h; rfl

def Hom.id (M : GradedSteenrodComodule) : Hom M M where
  linearMap := LinearMap.id
  graded _ _ hm := hm
  coaction := by simp only [LinearMap.lTensor_id, LinearMap.id_comp, LinearMap.comp_id]

def Hom.comp {M N P : GradedSteenrodComodule} (f : Hom M N) (g : Hom N P) :
    Hom M P where
  linearMap := g.linearMap ∘ₗ f.linearMap
  graded n m hm := g.graded n _ (f.graded n m hm)
  coaction := by
    rw [LinearMap.lTensor_comp, LinearMap.comp_assoc, f.coaction,
      ← LinearMap.comp_assoc, g.coaction, LinearMap.comp_assoc]

instance : Category GradedSteenrodComodule where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (by simp [Hom.id, Hom.comp])
  comp_id f := Hom.ext (by simp [Hom.id, Hom.comp])
  assoc f g h := Hom.ext (by simp [Hom.comp, LinearMap.comp_assoc])

def Hom.subgroup (M N : GradedSteenrodComodule) :
    AddSubgroup (M.carrier →ₗ[F2] N.carrier) where
  carrier := {f | (∀ (n : ℤ) (m : M.carrier), m ∈ M.grade n → f m ∈ N.grade n) ∧
    f.lTensor DualSteenrod ∘ₗ M.rho = N.rho ∘ₗ f}
  zero_mem' := by
    constructor
    · intro n m hm; exact (N.grade n).zero_mem
    · simp
  add_mem' := by
    rintro f g ⟨hfg,hfc⟩ ⟨hgg,hgc⟩
    constructor
    · intro n m hm; exact (N.grade n).add_mem (hfg n m hm) (hgg n m hm)
    · simp only [LinearMap.lTensor_add, LinearMap.add_comp, LinearMap.comp_add,
        hfc,hgc]
  neg_mem' := by
    rintro f ⟨hfg,hfc⟩
    constructor
    · intro n m hm; exact (N.grade n).neg_mem (hfg n m hm)
    · simp only [LinearMap.lTensor_neg, LinearMap.neg_comp, LinearMap.comp_neg, hfc]

def Hom.subgroupEquiv (M N : GradedSteenrodComodule) :
    (M ⟶ N) ≃ Hom.subgroup M N where
  toFun f := ⟨f.linearMap,f.graded,f.coaction⟩
  invFun f := ⟨f.val,f.property.1,f.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (M N : GradedSteenrodComodule) : AddCommGroup (M ⟶ N) :=
  (Hom.subgroupEquiv M N).addCommGroup

instance : Preadditive GradedSteenrodComodule where
  add_comp M N P f f' g := by
    apply Hom.ext
    change g.linearMap ∘ₗ (f.linearMap+f'.linearMap) =
      (g.linearMap ∘ₗ f.linearMap)+(g.linearMap ∘ₗ f'.linearMap)
    exact LinearMap.comp_add ..
  comp_add M N P f g g' := by
    apply Hom.ext
    change (g.linearMap+g'.linearMap) ∘ₗ f.linearMap =
      (g.linearMap ∘ₗ f.linearMap)+(g'.linearMap ∘ₗ f.linearMap)
    exact LinearMap.add_comp ..

def forget : GradedSteenrodComodule ⥤ ModuleCat.{0} F2 where
  obj M := M.carrier
  map f := ModuleCat.ofHom f.linearMap

instance : forget.Additive where
  map_add := by intros; rfl

/-- The actual degree-`n` homogeneous component and the restriction of
the same underlying comodule morphism. -/
def gradeForget (n : ℤ) : GradedSteenrodComodule ⥤ ModuleCat.{0} F2 where
  obj M := ModuleCat.of F2 (M.grade n)
  map {M N} f := ModuleCat.ofHom
    ((f.linearMap.comp (M.grade n).subtype).codRestrict (N.grade n)
      (fun m => f.graded n m m.property))

instance (n : ℤ) : (gradeForget n).Additive where
  map_add := by intros; rfl

end GradedSteenrodComodule

section Derived
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
local instance : HasExt.{max u v} C := HasExt.standard C

/-- Actual integer-graded derived Ext, not an `s.toNat` replacement. -/
def IntExt (X Y : C) (s : ℤ) : Type (max u v) :=
  SmallShiftedHom
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((CochainComplex.singleFunctor C 0).obj X)
    ((CochainComplex.singleFunctor C 0).obj Y) s

instance IntExt.instAddCommGroup (X Y : C) (s : ℤ) :
    AddCommGroup (IntExt X Y s) :=
  letI := HasDerivedCategory.standard C
  (SmallShiftedHom.equiv
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) DerivedCategory.Q).addCommGroup

instance IntExt.instIntModule (X Y : C) (s : ℤ) :
    Module ℤ (IntExt X Y s) := inferInstance

theorem IntExt_nat (X Y : C) (s : ℕ) :
    IntExt X Y (s : ℤ) = Ext.{max u v} X Y s := rfl

/-- Covariance in the same target comodule, induced by its actual map. -/
def IntExt.map {L Y Z : C} (f : Y ⟶ Z) (s : ℤ) :
    IntExt L Y s → IntExt L Z s := fun x =>
  SmallShiftedHom.comp x
    (SmallShiftedHom.mk₀
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) 0 rfl
      ((CochainComplex.singleFunctor C 0).map f)) (by omega)

/-- Composition with the actual extension class of this same short
exact sequence. This construction has no synthetic or Adams input. -/
def IntExt.sesBoundary (S : ShortComplex C) (hS : S.ShortExact)
    (L : C) (s : ℤ) :
    IntExt L S.X₃ s → IntExt L S.X₁ (s+1) := fun x =>
  SmallShiftedHom.comp x hS.extClass (by omega)

end Derived
end
end KIP126.AdamsSynthetic.Internal.SteenrodComodules
