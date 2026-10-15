module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Topology.Homotopy.Equiv
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Cubical.Proofs

@[expose] public section

section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory Simplicial
universe u

/-- A specified order-realization model of an actual space. -/
structure OrderRealizationModel (X : TopCat.{u}) where
  order : PartOrd.{u}
  equivalence : ContinuousMap.HomotopyEquiv |nerve order| X

/-- A model of the next space, retaining both comparisons with the old
space through the same order embedding. -/
structure OrderRealizationExtension {X Y : TopCat.{u}} (f : X ⟶ Y)
    (M : OrderRealizationModel X) where
  model : OrderRealizationModel Y
  embedding : M.order ↪o model.order
  forward : ∀ x : |nerve M.order|,
    model.equivalence (SSet.toTop.map (nerveMap embedding.monotone.functor) x) =
      f (M.equivalence x)
  backward : ∀ x : X,
    model.equivalence.invFun (f x) =
      SSet.toTop.map (nerveMap embedding.monotone.functor) (M.equivalence.invFun x)

end KIP126.Topology.SimplicialRealization

end

section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory HomotopicalAlgebra
open KIP126.Topology.HomotopyLifting
universe u

/-- The actual cube attachment theorem constructs the entire compatible
extension package; none of its comparison properties is an input. -/
theorem nonempty_orderRealizationExtension_of_cube_attachCells
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hc : Nonempty (AttachCells.{u} cubeBoundaryInclusion.{u} f))
    (M : OrderRealizationModel X) : Nonempty (OrderRealizationExtension f M) := by
  obtain ⟨c⟩ := hc
  obtain ⟨R,hR,j,E,hE,hEinv⟩ := exists_order_model_of_cube_attachCells c M.order M.equivalence
  letI := hR
  exact ⟨⟨⟨PartOrd.of R,E⟩,j,hE,hEinv⟩⟩

end KIP126.Topology.SimplicialRealization

end
