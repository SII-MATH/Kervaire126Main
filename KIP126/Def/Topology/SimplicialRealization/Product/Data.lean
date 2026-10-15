module

public import KIP126.Def.Topology.SimplicialRealization.Classical.Proofs
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CartesianMonoidalCategory MonoidalCategory Simplicial

universe u

/-- The actual comparison map from a realized simplicial product to the
product of realizations, given by its two realized projections. -/
noncomputable def productComparison (X Y : SSet.{u}) : C(|X ⊗ Y|, |X| × |Y|) :=
  ⟨fun z => (SSet.toTop.map (fst X Y) z,SSet.toTop.map (snd X Y) z),
    (SSet.toTop.map (fst X Y)).hom.continuous.prodMk
      (SSet.toTop.map (snd X Y)).hom.continuous⟩

/-- The comparison for two standard simplices in their barycentric
coordinates; no inverse is presumed in this definition. -/
noncomputable def stdSimplexProductComparison (p q : ℕ) :
    C(|(Δ[p] ⊗ Δ[q] : SSet.{u})|,
      stdSimplex ℝ (Fin (p+1)) × stdSimplex ℝ (Fin (q+1))) :=
  ⟨fun z => (SimplexCategory.toTopHomeo ⦋p⦌ (productComparison Δ[p] Δ[q] z).1,
      SimplexCategory.toTopHomeo ⦋q⦌ (productComparison Δ[p] Δ[q] z).2),
    ((SimplexCategory.toTopHomeo ⦋p⦌).continuous.comp
      (continuous_fst.comp (productComparison Δ[p] Δ[q]).continuous)).prodMk
      ((SimplexCategory.toTopHomeo ⦋q⦌).continuous.comp
        (continuous_snd.comp (productComparison Δ[p] Δ[q]).continuous))⟩

end KIP126.Topology.SimplicialRealization
