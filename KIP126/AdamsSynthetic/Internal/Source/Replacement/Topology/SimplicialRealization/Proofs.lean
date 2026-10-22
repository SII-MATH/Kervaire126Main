module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Data
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesColimit
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.Topology.Category.TopCat.EpiMono

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- The realization of a standard simplex is genuinely compact. -/
theorem compactSpace_stdSimplex (n : ℕ) : CompactSpace |(Δ[n] : SSet.{u})| :=
  (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace

/-- The actual realization of a simplex-generated subcomplex is a
continuous image of the corresponding compact standard simplex. -/
theorem compactSpace_ofSimplex (X : SSet.{u}) {n : ℕ} (x : X.obj (op ⦋n⦌)) :
    CompactSpace |(SSet.Subcomplex.ofSimplex x).toSSet| := by
  letI := compactSpace_stdSimplex.{u} n
  let f := SSet.toTop.map (SSet.Subcomplex.toOfSimplex x)
  exact ((TopCat.epi_iff_surjective f).mp inferInstance).compactSpace f.hom.continuous

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

/-- Degreewise finite simplices give a genuinely finite simplicial skeleton. -/
theorem finite_skeleton (X : SSet.{u}) (n : ℕ)
    (hX : ∀ d : ℕ, Finite (X.obj (op ⦋d⦌))) :
    SSet.Finite (X.skeleton n).toSSet := by
  letI (d : ℕ) := hX d
  change SSet.Finite (⨆ (i : Fin n) (x : X.nonDegenerate i),
    SSet.Subcomplex.ofSimplex x.1).toSSet
  apply (SSet.finite_iSup_iff _).mpr
  intro i
  apply (SSet.finite_iSup_iff _).mpr
  intro x
  exact SSet.finite_of_epi (SSet.Subcomplex.toOfSimplex x.1)

/-- Every realized skeleton of a degreewise finite simplicial set is compact. -/
theorem compactSpace_skeleton (X : SSet.{u}) (n : ℕ)
    (hX : ∀ d : ℕ, Finite (X.obj (op ⦋d⦌))) : CompactSpace (skeleton X n) := by
  letI := finite_skeleton X n hX
  exact compactSpace_of_finite (X.skeleton n).toSSet

end KIP126.Topology.SimplicialRealization
