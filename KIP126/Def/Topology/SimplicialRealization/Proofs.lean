module

public import KIP126.Def.Topology.SimplicialRealization.Data
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesColimit
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.Topology.Category.TopCat.EpiMono

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- The realization of a standard simplex is genuinely compact. -/
theorem compactSpace_stdSimplex (n : ℕ) : CompactSpace |(Δ[n] : SSet.{u})| :=
  (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace

/-- Every realization point lies in the image of an actual nondegenerate
simplex, using the proved colimit over simplex-generated subcomplexes. -/
theorem exists_nondegenerate_simplex (X : SSet.{u}) (x : |X|) :
    ∃ s : X.N, ∃ t : |(Δ[s.dim] : SSet.{u})|,
      SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex) t = x := by
  let c := (SSet.toTop ⋙ forget TopCat).mapCocone X.coconeN
  have hc : IsColimit c := isColimitOfPreserves _ X.isColimitCoconeN
  obtain ⟨s,y,hy⟩ := Types.jointly_surjective_of_isColimit hc x
  let f := SSet.toTop.map (SSet.Subcomplex.toOfSimplex s.simplex)
  obtain ⟨t,ht⟩ := ((TopCat.epi_iff_surjective f).mp inferInstance) y
  refine ⟨s,t,?_⟩
  have hcomp := congrArg SSet.toTop.map (SSet.Subcomplex.toOfSimplex_ι s.simplex)
  rw [Functor.map_comp] at hcomp
  rw [← hcomp]
  exact (congrArg (fun z => SSet.toTop.map s.subcomplex.ι z) ht).trans hy

/-- A finite simplicial set has compact geometric realization. Finiteness
refers to actual nondegenerate simplices, not a supplied CW structure. -/
theorem compactSpace_of_finite (X : SSet.{u}) [X.Finite] : CompactSpace |X| := by
  letI (s : X.N) : CompactSpace |(Δ[s.dim] : SSet.{u})| := compactSpace_stdSimplex s.dim
  let f : (Σ s : X.N, |(Δ[s.dim] : SSet.{u})|) → |X| :=
    fun p => SSet.toTop.map (SSet.yonedaEquiv.symm p.1.simplex) p.2
  have hf : Continuous f := continuous_sigma fun s =>
    (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom.continuous
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨s,t,ht⟩ := exists_nondegenerate_simplex X x
    exact ⟨⟨s,t⟩,ht⟩
  exact hs.compactSpace hf

end KIP126.Topology.SimplicialRealization
