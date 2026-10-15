module

public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.Under.Data
public import Mathlib.CategoryTheory.WithTerminal.Cone
public import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
public import Mathlib.Topology.Category.TopCat.Limits.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory CategoryTheory.Limits

universe u

/-- Actual based spaces have all small colimits, including the common
basepoint identifications in coproducts and pushouts. -/
noncomputable instance hasColimits : HasColimitsOfSize.{u,u} BasedSpace.{u} :=
  Adjunction.has_colimits_of_equivalence underEquivalence.functor

end KIP126.StableHomotopy.Spectra.BasedSpace
