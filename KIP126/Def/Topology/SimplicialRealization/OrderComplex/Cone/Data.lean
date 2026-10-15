module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Cone.Coordinates.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped unitInterval Classical

universe u

/-- The actual order cone parametrized by a base point and its apex weight. -/
noncomputable def orderConeParameter (P : Type u) [PartialOrder P] [Fintype P] :
    C(I × |nerve P|, |nerve (WithTop P)|) :=
  let e := (exists_orderComplexCoordinates_homeomorph (WithTop P)).choose
  { toFun := fun z => e.symm ⟨orderConeCoordinates z.1 (orderComplexCoordinates P z.2),
      orderConeCoordinates_hasChainSupport z.1 _ (orderComplexCoordinates_hasChainSupport P z.2)⟩
    continuous_toFun := e.symm.continuous.comp
      ((continuous_orderConeCoordinates.comp
        (continuous_fst.prodMk ((orderComplexCoordinates P).continuous.comp continuous_snd))).subtype_mk _) }

end KIP126.Topology.SimplicialRealization
