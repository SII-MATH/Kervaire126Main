module

public import KIP126.Def.Synthetic.QuotientTower.Predicates
public import KIP126.Def.ClassicalAdams.MapFiltration.Predicates

@[expose] public section

/-! Normalized maps are explicit lifts of the same classical map. The
normalizing exponent uses the actual Adams tower, not a freely chosen AF. -/

namespace KIP126.Synthetic.Context

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams

universe u v u' v'
noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]

/-- The paper's e(f): one for positive actual Adams filtration, zero otherwise. -/
def normalizedExponent (H : Mod2EilenbergMacLane (C := C))
    {X Y : C} (f : X ⟶ Y) : ℕ := by
  classical
  exact if AdamsFiltrationAtLeast H f 1 then 1 else 0

/-- Multiplication by λᵏ with its positive-shift target, using exactly the
specified bigraded suspension comparisons. -/
def lambdaToPositivePow (k : ℕ) (X : Syn) :
    X ⟶ (SyntheticCategory.biShift (0, (k : ℤ))).obj X := by
  have h : ((0 : ℤ), (k : ℤ)) + ((0 : ℤ), -(k : ℤ)) = (0, 0) := by
    ext <;> simp
  exact SyntheticCategory.biShift_zero.inv.app X ≫
    eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj X) h.symm) ≫
    (SyntheticCategory.biShift_comp (0, (k : ℤ)) (0, -(k : ℤ))).inv.app X ≫
    lambdaPow k ((SyntheticCategory.biShift (0, (k : ℤ))).obj X)

/-- A fixed normalized lift; no global choice or literature axiom constructs it. -/
structure NormalizedSyntheticMap (H : Mod2EilenbergMacLane (C := C))
    (N : NuFunctorData C Syn) {X Y : C} (f : X ⟶ Y) where
  map : (SyntheticCategory.biShift (0, (normalizedExponent H f : ℤ))).obj
      (N.functor.obj X) ⟶ N.functor.obj Y
  factorization : lambdaToPositivePow (normalizedExponent H f) (N.functor.obj X) ≫
    map = N.functor.map f

end
end KIP126.Synthetic.Context
