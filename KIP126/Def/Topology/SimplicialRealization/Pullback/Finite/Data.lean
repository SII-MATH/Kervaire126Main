module

public import KIP126.Def.Topology.SimplicialRealization.Pullback.Identification.Data
public import KIP126.Def.Topology.SimplicialRealization.Product.LocallyCompact.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual product comparison with a finite simplicial set. -/
noncomputable def realizationFiniteProductHomeomorph (X Y : SSet.{u}) [Y.Finite] :
    |X ⊗ Y| ≃ₜ (|X| × |Y|) := by
  letI := productComparison_isIso_of_finite_right X Y
  exact TopCat.homeoOfIso (asIso (CartesianMonoidalCategory.prodComparison SSet.toTop X Y))

/-- Actual realization preserves pullback along every map from a finite
simplicial set, with the literal topological fiber-product topology. -/
noncomputable def finitePullbackHomeomorph {X Y Z : SSet.{u}} [Y.Finite]
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    |pullback f g| ≃ₜ {xy : |X| × |Y| // SSet.toTop.map f xy.1 = SSet.toTop.map g xy.2} :=
  pullbackRealizationHomeomorph f g (realizationFiniteProductHomeomorph X Y)
    (fun _ => rfl) (fun _ => rfl)


end KIP126.Topology.SimplicialRealization
