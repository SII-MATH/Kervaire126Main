module

public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.Suspension.Cell

@[expose] public section

section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory KIP126.Topology.HomotopyLifting

universe u

/-- The actual attaching map on the full boundary of the suspended cube,
glued from its original side map and its two constant end faces. -/
noncomputable def suspensionCellBoundary (n : ℕ) (A : BasedSpace.{u})
    (a : cubeBoundaryObject n ⟶ A.space) :
    cubeBoundaryObject (n+1) ⟶ A.suspension.space :=
  (cubeBoundaryProduct_isPushout n).desc (suspensionCellEnds n A)
    (suspensionCellSide n A a) (suspensionCell_boundary_comm n A a)

end KIP126.StableHomotopy.Spectra.BasedSpace

end

section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

theorem suspensionCellBoundary_ends (n : ℕ) (A : BasedSpace.{u})
    (a : cubeBoundaryObject n ⟶ A.space) (x : cubeBoundaryProductEnds n) :
    suspensionCellBoundary n A a (cubeBoundaryProductEndInclusion n x) =
      A.suspension.point :=
  ConcreteCategory.congr_hom ((cubeBoundaryProduct_isPushout n).inl_desc
    (suspensionCellEnds n A) (suspensionCellSide n A a)
    (suspensionCell_boundary_comm n A a)) x

theorem suspensionCellBoundary_side (n : ℕ) (A : BasedSpace.{u})
    (a : cubeBoundaryObject n ⟶ A.space) (x : cubeBoundaryProductSide n) :
    suspensionCellBoundary n A a (cubeBoundaryProductSideInclusion n x) =
      suspensionProjection A (a x.2, x.1) :=
  ConcreteCategory.congr_hom ((cubeBoundaryProduct_isPushout n).inr_desc
    (suspensionCellEnds n A) (suspensionCellSide n A a)
    (suspensionCell_boundary_comm n A a)) x

/-- Suspending the original attaching square retains its original based
map as the map between the old and new suspended spaces. -/
theorem suspensionCell_square (n : ℕ) {A B : BasedSpace.{u}}
    (a : cubeBoundaryObject n ⟶ A.space) (c : cubeObject n ⟶ B.space)
    (f : A ⟶ B) (h : cubeBoundaryInclusion n ≫ c = a ≫ TopCat.ofHom f.map) :
    cubeBoundaryInclusion (n+1) ≫ suspensionCellCharacteristic n B c =
      suspensionCellBoundary n A a ≫ TopCat.ofHom (suspendMap f).map := by
  apply (cubeBoundaryProduct_isPushout n).hom_ext
  · ext x
    change suspensionProjection B (c x.2, x.1.val) =
      (suspendMap f).map
        (suspensionCellBoundary n A a (cubeBoundaryProductEndInclusion n x))
    rw [suspensionCellBoundary_ends, (suspendMap f).point]
    exact suspensionProjection_collapsed _ _ (Or.inr x.1.property)
  · ext x
    change suspensionProjection B (c (cubeBoundaryInclusion n x.2), x.1) =
      (suspendMap f).map
        (suspensionCellBoundary n A a (cubeBoundaryProductSideInclusion n x))
    rw [suspensionCellBoundary_side]
    change suspensionProjection B (c (cubeBoundaryInclusion n x.2), x.1) =
      suspensionProjection B (f.map (a x.2), x.1)
    exact congrArg (fun b => suspensionProjection B (b,x.1))
      (ConcreteCategory.congr_hom h x.2)

end KIP126.StableHomotopy.Spectra.BasedSpace

end
