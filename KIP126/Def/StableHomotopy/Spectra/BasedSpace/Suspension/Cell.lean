module

public import KIP126.Def.StableHomotopy.Spectra.Generators
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Product.Proofs
public import KIP126.Def.Topology.Pushout.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory KIP126.Topology.HomotopyLifting
open scoped unitInterval

universe u

/-- Suspend an actual cubical characteristic map using the original successor
cube coordinates and the original reduced suspension quotient. -/
def suspensionCellCharacteristic (n : ℕ) (B : BasedSpace.{u})
    (c : cubeObject n ⟶ B.space) : cubeObject (n+1) ⟶ B.suspension.space :=
  TopCat.ofHom ((suspensionProjection B).comp
    ⟨fun x => (c (cubeObjectSuccHomeomorph n x).2,
      (cubeObjectSuccHomeomorph n x).1),
      (c.hom.continuous.comp (cubeObjectSuccHomeomorph n).continuous.snd).prodMk
        (cubeObjectSuccHomeomorph n).continuous.fst⟩)

/-- The side boundary of the suspended characteristic cube retains the
original attaching map and the full suspension parameter. -/
def suspensionCellSide (n : ℕ) (A : BasedSpace.{u})
    (a : cubeBoundaryObject n ⟶ A.space) :
    cubeBoundaryProductSide n ⟶ A.suspension.space :=
  TopCat.ofHom ((suspensionProjection A).comp
    ⟨fun x => (a x.2, x.1),
      (a.hom.continuous.comp continuous_snd).prodMk continuous_fst⟩)

/-- On both end faces the suspended characteristic cube maps to the actual
suspension basepoint. -/
def suspensionCellEnds (n : ℕ) (A : BasedSpace.{u}) :
    cubeBoundaryProductEnds n ⟶ A.suspension.space :=
  TopCat.ofHom (ContinuousMap.const _ A.suspension.point)

end KIP126.StableHomotopy.Spectra.BasedSpace

end

section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory CategoryTheory.Limits KIP126.Topology.HomotopyLifting
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The prescribed end faces and side boundary agree on their actual
intersection, including the empty zero-dimensional boundary. -/
theorem suspensionCell_boundary_comm (n : ℕ) (A : BasedSpace.{u})
    (a : cubeBoundaryObject n ⟶ A.space) :
    cubeBoundaryProductTop n ≫ suspensionCellEnds n A =
      cubeBoundaryProductLeft n ≫ suspensionCellSide n A a := by
  ext x
  exact (suspensionProjection_collapsed A _ (Or.inr x.1.property)).symm

end KIP126.StableHomotopy.Spectra.BasedSpace

end
