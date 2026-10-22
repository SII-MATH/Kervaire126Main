module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Pullback.Identification.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Product.Compact.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual product comparison with a standard simplex, as a homeomorphism. -/
noncomputable def realizationStandardSimplexProductHomeomorph (X : SSet.{u}) (n : ℕ) :
    |X ⊗ Δ[n]| ≃ₜ (|X| × |(Δ[n] : SSet.{u})|) := by
  letI := stdSimplex_right_productComparison_isIso X n
  exact TopCat.homeoOfIso (asIso (CartesianMonoidalCategory.prodComparison SSet.toTop X Δ[n]))

/-- Actual realization preserves the pullback of any simplicial map along
any standard simplex, with the literal topological pullback topology. -/
noncomputable def standardSimplexPullbackHomeomorph {X Y : SSet.{u}}
    (f : X ⟶ Y) (n : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ Y) :
    |pullback f b| ≃ₜ
      {xt : |X| × |(Δ[n] : SSet.{u})| // SSet.toTop.map f xt.1 = SSet.toTop.map b xt.2} :=
  pullbackRealizationHomeomorph f b (realizationStandardSimplexProductHomeomorph X n)
    (fun _ => rfl) (fun _ => rfl)


end KIP126.Topology.SimplicialRealization
