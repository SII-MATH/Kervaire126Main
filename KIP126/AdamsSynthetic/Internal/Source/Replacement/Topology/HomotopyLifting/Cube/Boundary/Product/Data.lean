module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Product.Data
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] section

namespace KIP126.Topology.HomotopyLifting

open CategoryTheory
open scoped unitInterval

universe u

/-- The two actual endpoints of the unit interval. -/
def intervalBoundaryObject : TopCat := TopCat.of {t : I // t = 0 ∨ t = 1}

/-- The intersection of the end faces and the side boundary. -/
def cubeBoundaryProductCorner (n : ℕ) : TopCat.{u} :=
  TopCat.of (intervalBoundaryObject × cubeBoundaryObject.{u} n)

/-- The two end faces of the successor cube. -/
def cubeBoundaryProductEnds (n : ℕ) : TopCat.{u} :=
  TopCat.of (intervalBoundaryObject × cubeObject.{u} n)

/-- The side boundary of the successor cube. -/
def cubeBoundaryProductSide (n : ℕ) : TopCat.{u} :=
  TopCat.of (I × cubeBoundaryObject.{u} n)

/-- The intersection included in the end faces. -/
def cubeBoundaryProductTop (n : ℕ) :
    cubeBoundaryProductCorner.{u} n ⟶ cubeBoundaryProductEnds.{u} n :=
  TopCat.ofHom ⟨fun x => (x.1, cubeBoundaryInclusion n x.2),
    continuous_fst.prodMk ((cubeBoundaryInclusion n).hom.continuous.comp continuous_snd)⟩

/-- The intersection included in the side boundary. -/
def cubeBoundaryProductLeft (n : ℕ) :
    cubeBoundaryProductCorner.{u} n ⟶ cubeBoundaryProductSide.{u} n :=
  TopCat.ofHom ⟨fun x => (x.1.val, x.2),
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd⟩

/-- End-face inclusion into the original successor cube boundary. -/
def cubeBoundaryProductEndInclusion (n : ℕ) :
    cubeBoundaryProductEnds.{u} n ⟶ cubeBoundaryObject.{u} (n+1) :=
  TopCat.ofHom ⟨fun x => ULift.up ⟨(Fin.cases x.1.val x.2.down : Fin (n+1) → I), by
      exact ⟨0, x.1.property⟩⟩,
    continuous_uliftUp.comp ((continuous_pi (fun j => Fin.cases
      (continuous_subtype_val.comp continuous_fst)
      (fun k => (continuous_apply k).comp (continuous_uliftDown.comp continuous_snd)) j)).subtype_mk _)⟩

/-- Side-boundary inclusion into the original successor cube boundary. -/
def cubeBoundaryProductSideInclusion (n : ℕ) :
    cubeBoundaryProductSide.{u} n ⟶ cubeBoundaryObject.{u} (n+1) :=
  TopCat.ofHom ⟨fun x => ULift.up ⟨Fin.cases x.1 x.2.down.val, by
      obtain ⟨j,hj⟩ := x.2.down.property
      exact ⟨j.succ,hj⟩⟩,
    continuous_uliftUp.comp ((continuous_pi (fun j => Fin.cases continuous_fst
      (fun k => (continuous_apply k).comp
        (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd))) j)).subtype_mk _)⟩

end KIP126.Topology.HomotopyLifting
