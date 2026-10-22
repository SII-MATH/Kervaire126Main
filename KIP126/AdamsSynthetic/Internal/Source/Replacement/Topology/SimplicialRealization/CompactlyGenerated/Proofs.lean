module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Proofs
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial

universe u v

set_option backward.isDefEq.respectTransparency false

/-- The topology of the actual realization is final for its actual
simplex maps, with no CW or separation premise. -/
theorem continuous_iff_simplex (X : SSet.{u}) {Y : Type v} [TopologicalSpace Y]
    (f : |X| → Y) :
    Continuous f ↔ ∀ (n : ℕ) (σ : (Δ[n] : SSet.{u}) ⟶ X),
      Continuous (f ∘ SSet.toTop.map σ) := by
  let c := SSet.toTop.mapCocone (Presheaf.tautologicalCocone' X)
  have hc : IsColimit c :=
    isColimitOfPreserves SSet.toTop (Presheaf.isColimitTautologicalCocone' X)
  rw [TopCat.continuous_iff_of_isColimit c hc]
  constructor
  · intro h n σ
    exact h (CostructuredArrow.mk σ)
  · intro h j
    exact h j.left.len j.hom

/-- Every actual simplicial realization is compactly generated: its
simplex maps already form a family of compact Hausdorff tests. -/
theorem realization_uCompactlyGeneratedSpace (X : SSet.{u}) :
    UCompactlyGeneratedSpace.{u} |X| := by
  apply uCompactlyGeneratedSpace_of_continuous_maps
  intro Y _ f hf
  apply (continuous_iff_simplex X f).mpr
  intro n σ
  letI := compactSpace_stdSimplex.{u} n
  letI : T2Space |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
  exact hf (CompHaus.of |(Δ[n] : SSet.{u})|) (SSet.toTop.map σ).hom

end KIP126.Topology.SimplicialRealization
