module

public import KIP126.Def.ClassicalAdams.TowerHomology.Normalized.Proofs

@[expose] public section

/-! Explicit splitting and normalization of the actual smashed unit sequence.
These are constructions from its proved exactness, not Künneth inputs. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- Remove the unit-action summand from a homology class. -/
def adamsHomologyNormalize (X : C) (n : ℤ) :
    Mod2Homology H n (H.HF2 ⊗ X) →ₗ[ℤ] Mod2Homology H n (H.HF2 ⊗ X) :=
  LinearMap.id - (adamsHomologyUnit H X n).comp (adamsHomologyAction H R X n)

variable [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- Split a class into its multiplication component and its actual tower boundary.
The inverse uses the uniquely normalized boundary lift. -/
def adamsHomologySplitEquiv (X : C) (n : ℤ) :
    Mod2Homology H n (H.HF2 ⊗ X) ≃ₗ[ℤ]
      Mod2Homology H n X × Mod2Homology H (n - 1) (fiber (adamsUnit H.unit X)) :=
  { (adamsHomologyAction H R X n).prod (adamsHomologyBoundary H X n) with
    invFun := fun p => adamsHomologyUnit H X n p.1 +
      ((adamsHomologyKernelEquiv H R X n).symm p.2).val
    left_inv := fun x => by
      change adamsHomologyUnit H X n (adamsHomologyAction H R X n x) +
        ((adamsHomologyKernelEquiv H R X n).symm (adamsHomologyBoundary H X n x)).val = x
      rw [adamsHomologyKernelEquiv_symm_boundary]
      abel
    right_inv := fun p => by
      apply Prod.ext
      · change adamsHomologyAction H R X n (_ + _) = p.1
        rw [map_add, adamsHomologyAction_unit,
          ((adamsHomologyKernelEquiv H R X n).symm p.2).property, add_zero]
      · change adamsHomologyBoundary H X n (_ + _) = p.2
        rw [map_add, adamsHomologyBoundary_unit, zero_add]
        exact (adamsHomologyKernelEquiv H R X n).apply_symm_apply p.2 }

end

end KIP126.Classical.Adams
