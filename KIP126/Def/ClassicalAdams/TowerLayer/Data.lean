module

public import KIP126.Def.ClassicalAdams.TowerLayer.Basic.Proofs

@[expose] public section

/-! Constructed layer and first-page comparisons. No Milnor coordinates,
Lin presentation, ring structure, or convergence assumption is used here. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- Complete the first two isomorphisms of distinguished triangles.
The negative identity reconciles `fiberι` with inverse rotation. -/
def cofiberFiberTriangleIso {X Y : C} (f : X ⟶ Y) :
    Triangle.mk (fiberι f) (HasFunctorialCofiber.cofibι (fiberι f))
      (HasFunctorialCofiber.cofibδ (fiberι f)) ≅ adamsFiberTriangle f :=
  isoTriangleOfIso₁₂ _ _ (HasFunctorialCofiber.cofib_distinguished (fiberι f))
    (adamsFiberTriangle_distinguished f) (-(Iso.refl _)) (Iso.refl _)
    (by simp [Triangle.mk, adamsFiberTriangle_mor₁])

/-- The chosen cofiber of the positive fiber inclusion is isomorphic to its target. -/
def cofiberFiberIso {X Y : C} (f : X ⟶ Y) :
    HasFunctorialCofiber.cofib (fiberι f) ≅ Y :=
  Triangle.π₃.mapIso (cofiberFiberTriangleIso f)

variable {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Compare the actual integer-indexed layer triangle with the inverse-rotated
unit triangle. This transports maps, not just the third objects. -/
def adamsLayerTriangleIso (s : ℕ) :
    adamsLayerTriangle unit X (s : ℤ) ≅
      adamsFiberTriangle (adamsUnit unit (adamsTower unit X s)) :=
  isoTriangleOfIso₁₂ _ _ (adamsLayerTriangle_distinguished unit X s)
    (adamsFiberTriangle_distinguished _) (-(Iso.refl _)) (Iso.refl _)
    (by simp [adamsLayerTriangle, Triangle.mk, adamsFiberTriangle_mor₁,
      adamsTowerMapAt_nat_succ, adamsTowerStep])

/-- In nonnegative filtration the layer is `H ⊗ Tₛ`. -/
def adamsLayerIso (s : ℕ) : adamsLayerAt unit X s ≅ H ⊗ adamsTower unit X s :=
  Triangle.π₃.mapIso (adamsLayerTriangleIso unit X s)

/-- The exact-couple first group is the `H`-homology of the tower term.
We retain integer-linear structure; no extra scalar structure is assumed. -/
def adamsE1HomologyEquiv (s : ℕ) (t : ℤ) :
    adamsE1 unit X s t ≃ₗ[ℤ] HomotopyGroup (t - s) (H ⊗ adamsTower unit X s) :=
  ((homotopyGroupFunctor (t - s)).mapIso
    (adamsLayerIso unit X s)).addCommGroupIsoToAddEquiv.toIntLinearEquiv

/-- On page one every first-group element is a cycle. -/
def adamsCyclesOneEquiv (s t : ℤ) :
    adamsCycles unit X 1 (by decide) s t ≃ₗ[ℤ] adamsE1 unit X s t where
  toFun := Subtype.val
  invFun x := ⟨x, by rw [adamsCycles_one]; trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual first quotient page equals the exact-couple first group. -/
def adamsPageOneEquiv (s t : ℤ) :
    adamsPage unit X 1 (by decide) s t ≃ₗ[ℤ] adamsE1 unit X s t :=
  ((adamsCycleBoundaries unit X 1 (by decide) s t).quotEquivOfEqBot
    (adamsCycleBoundaries_one unit X s t)).trans (adamsCyclesOneEquiv unit X s t)

/-- The tower's actual first quotient page, not the internal sequence's
out-of-range `Page 1`, is the `H`-homology of the tower term. -/
def adamsPageOneHomologyEquiv (s : ℕ) (t : ℤ) :
    adamsPage unit X 1 (by decide) s t ≃ₗ[ℤ]
      HomotopyGroup (t - s) (H ⊗ adamsTower unit X s) :=
  (adamsPageOneEquiv unit X s t).trans (adamsE1HomologyEquiv unit X s t)

end

end KIP126.Classical.Adams
