module

public import KIP126.Def.Topology.SimplicialRealization.Classical.Structure.Data
public import KIP126.Def.Topology.CWComplex.FiniteSupport.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite Set _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every compact subset of an actual simplicial realization is contained
in the realization of an actual finite simplicial subcomplex. -/
theorem compact_subset_finite_simplicial_subcomplex (X : SSet.{u})
    (K : Set |X|) (hK : IsCompact K) :
    ∃ A : X.Subcomplex, A.toSSet.Finite ∧ K ⊆ Set.range (SSet.toTop.map A.ι) := by
  classical
  letI := realization_t2Space X
  letI := realizationClassicalCWComplex X
  obtain ⟨F,hF⟩ := cw_compact_subset_finite_closedCells (C := (Set.univ : Set |X|))
    K hK (Set.subset_univ _)
  change Finset (Σ n, X.nonDegenerate n) at F
  let A : X.Subcomplex := ⨆ a : F, SSet.Subcomplex.ofSimplex a.1.2.1
  have hA : A.toSSet.Finite := by
    apply (SSet.finite_iSup_iff _).mpr
    intro a
    exact SSet.finite_of_epi (SSet.Subcomplex.toOfSimplex a.1.2.1)
  refine ⟨A,hA,?_⟩
  intro x hx
  obtain ⟨a,ha,hxa⟩ := Set.mem_iUnion₂.mp (hF hx)
  change x ∈ simplexCharacteristicExtension X a.1 a.2 '' Metric.closedBall 0 1 at hxa
  rw [simplexCharacteristicExtension_closedCell] at hxa
  obtain ⟨t,rfl⟩ := hxa
  let g := SSet.Subcomplex.toOfSimplex a.2.1 ≫
    SSet.Subcomplex.homOfLE (le_iSup (fun b : F => SSet.Subcomplex.ofSimplex b.1.2.1) ⟨a,ha⟩)
  refine ⟨SSet.toTop.map g t,?_⟩
  have hg : g ≫ A.ι = SSet.yonedaEquiv.symm a.2.1 := by
    change (SSet.Subcomplex.toOfSimplex a.2.1 ≫
      SSet.Subcomplex.homOfLE _) ≫ (⨆ b : F, SSet.Subcomplex.ofSimplex b.1.2.1).ι = _
    rw [Category.assoc,SSet.Subcomplex.homOfLE_ι,SSet.Subcomplex.toOfSimplex_ι]
  exact ConcreteCategory.congr_hom
    ((SSet.toTop.map_comp g A.ι).symm.trans (congrArg SSet.toTop.map hg)) t

/-- Every continuous map from a compact space to an actual realization
factors continuously through a finite simplicial subcomplex. -/
theorem continuousMap_factor_finite_simplicial_subcomplex (X : SSet.{u})
    {D : Type*} [TopologicalSpace D] [CompactSpace D] (f : C(D,|X|)) :
    ∃ A : X.Subcomplex, A.toSSet.Finite ∧
      ∃ g : C(D,|A.toSSet|), ∀ d, SSet.toTop.map A.ι (g d) = f d := by
  obtain ⟨A,hA,hf⟩ := compact_subset_finite_simplicial_subcomplex X
    (Set.range f) (isCompact_range f.continuous)
  choose g hg using (fun d => hf (Set.mem_range_self d))
  have he := realization_mono_isClosedEmbedding A.ι
  have hgc : Continuous g := he.isEmbedding.isInducing.continuous_iff.mpr (by
    have h : (SSet.toTop.map A.ι) ∘ g = f := funext hg
    rw [h]
    exact f.continuous)
  exact ⟨A,hA,⟨g,hgc⟩,hg⟩

end KIP126.Topology.SimplicialRealization
