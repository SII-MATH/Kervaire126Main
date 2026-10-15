module

public import KIP126.Def.Topology.SimplicialRealization.Classical.Charts.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite Set _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- The chart inverse is continuous on its actual open-cell image. -/
theorem simplexCellChart_continuousOn_symm (X : SSet.{u}) (n : ℕ)
    (s : X.nonDegenerate n) :
    ContinuousOn (simplexCellChart X n s).symm (simplexCellChart X n s).target := by
  let p := simplexCellChart X n s
  have he : IsEmbedding (fun x : Metric.ball (0 : Fin n → ℝ) 1 =>
      simplexCharacteristicExtension X n s x.1) := by
    have hf : (fun x : Metric.ball (0 : Fin n → ℝ) 1 =>
        simplexCharacteristicExtension X n s x.1) =
        (fun x : Metric.ball (0 : Fin n → ℝ) 1 =>
          simplexCharacteristic X n s ⟨x.1,Metric.ball_subset_closedBall x.2⟩) := by
      funext x
      exact simplexCharacteristicExtension_apply X n s ⟨x.1,Metric.ball_subset_closedBall x.2⟩
    rw [hf]
    exact simplexCharacteristic_interior_isEmbedding X n s
  let g : p.target → Metric.ball (0 : Fin n → ℝ) 1 := fun y => ⟨p.symm y.1,p.map_target y.2⟩
  have hg : Continuous g := by
    apply he.isInducing.continuous_iff.mpr
    have hfg : (fun x : Metric.ball (0 : Fin n → ℝ) 1 =>
        simplexCharacteristicExtension X n s x.1) ∘ g = Subtype.val := by
      funext y
      exact p.right_inv y.2
    rw [hfg]
    exact continuous_subtype_val
  exact continuousOn_iff_continuous_restrict.mpr (continuous_subtype_val.comp hg)

/-- Distinct actual nondegenerate simplex interiors form disjoint open cells. -/
theorem simplexCellChart_pairwiseDisjoint (X : SSet.{u}) :
    (Set.univ : Set (Σ n, X.nonDegenerate n)).PairwiseDisjoint
      (fun s => simplexCellChart X s.1 s.2 '' Metric.ball 0 1) := by
  intro a _ b _ hab
  apply Set.disjoint_left.mpr
  intro z hza hzb
  change z ∈ simplexCharacteristicExtension X a.1 a.2 '' Metric.ball 0 1 at hza
  change z ∈ simplexCharacteristicExtension X b.1 b.2 '' Metric.ball 0 1 at hzb
  rw [simplexCharacteristicExtension_openCell] at hza hzb
  obtain ⟨t,ht,htz⟩ := hza
  obtain ⟨t',ht',htz'⟩ := hzb
  obtain ⟨hn,hs,_⟩ := nondegenerate_interior_unique X a.2 b.2 t t' ht ht' (htz.trans htz'.symm)
  exact hab (Sigma.ext hn hs)

/-- The entire boundary of a characteristic disk lands in finitely many
lower-dimensional closed cells. -/
theorem simplexCellChart_boundary (X : SSet.{u}) (n : ℕ) (s : X.nonDegenerate n) :
    ∃ I : ∀ m, Finset (X.nonDegenerate m),
      Set.MapsTo (simplexCellChart X n s) (Metric.sphere 0 1)
        (⋃ (m < n) (j ∈ I m), simplexCellChart X m j '' Metric.closedBall 0 1) := by
  obtain ⟨I,hI⟩ := simplex_boundary_finite_cells X n s
  refine ⟨I,?_⟩
  intro x hx
  let z : Metric.closedBall (0 : Fin n → ℝ) 1 := ⟨x,Metric.sphere_subset_closedBall hx⟩
  let t := (SimplexCategory.toTopHomeo ⦋n⦌).symm ((simplexDiskHomeomorph n).symm z)
  have hb : t ∈ Set.range (SSet.toTop.map ∂Δ[n].ι) := by
    rw [simplex_mem_boundary_iff]
    change ∃ i, (SimplexCategory.toTopHomeo ⦋n⦌
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm ((simplexDiskHomeomorph n).symm z))).1 i = 0
    rw [Homeomorph.apply_symm_apply,simplexDiskHomeomorph_boundary,Homeomorph.apply_symm_apply]
    simpa only [Metric.mem_sphere,dist_zero_right] using hx
  obtain ⟨b,hb⟩ := hb
  obtain ⟨m,hm,j,hj,t',ht'⟩ := hI b
  refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,
    Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,?_⟩⟩⟩⟩
  change simplexCharacteristicExtension X n s x ∈
    simplexCharacteristicExtension X m j '' Metric.closedBall 0 1
  rw [simplexCharacteristicExtension_closedCell]
  refine ⟨t',?_⟩
  rw [ht',hb]
  exact (simplexCharacteristicExtension_apply X n s z).symm

/-- The closed cell images detect all closed subsets of the realization. -/
theorem simplexCellChart_closed (X : SSet.{u}) (A : Set |X|)
    (hA : ∀ n (s : X.nonDegenerate n),
      IsClosed (A ∩ simplexCellChart X n s '' Metric.closedBall 0 1)) : IsClosed A := by
  apply realization_isClosed_of_simplex_preimages X A
  intro n s
  have hc := hA n s
  change IsClosed (A ∩ simplexCharacteristicExtension X n s '' Metric.closedBall 0 1) at hc
  rw [simplexCharacteristicExtension_closedCell] at hc
  have hpre := hc.preimage (SSet.toTop.map (SSet.yonedaEquiv.symm s.1)).hom.continuous
  simpa only [Set.preimage_inter,Set.preimage_range,Set.inter_univ] using hpre

/-- The closed cells cover every point of the actual realization. -/
theorem simplexCellChart_union (X : SSet.{u}) :
    (⋃ (n : ℕ) (s : X.nonDegenerate n), simplexCellChart X n s '' Metric.closedBall 0 1) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨s,t,ht⟩ := exists_nondegenerate_simplex X x
  refine Set.mem_iUnion.mpr ⟨s.dim,Set.mem_iUnion.mpr ⟨⟨s.simplex,s.nonDegenerate⟩,?_⟩⟩
  change x ∈ simplexCharacteristicExtension X s.dim ⟨s.simplex,s.nonDegenerate⟩ '' Metric.closedBall 0 1
  rw [simplexCharacteristicExtension_closedCell]
  exact ⟨t,ht⟩

/-- Every actual simplicial realization has a classical CW structure with
one cell for each nondegenerate simplex. All chart, closure-finiteness and
weak-topology obligations are proved from the concrete realization. -/
theorem realization_nonempty_classicalCWComplex (X : SSet.{u}) :
    Nonempty (_root_.Topology.CWComplex (Set.univ : Set |X|)) := by
  exact ⟨{
    cell := fun n => X.nonDegenerate n
    map := simplexCellChart X
    source_eq := fun _ _ => rfl
    continuousOn := simplexCharacteristicExtension_continuousOn X
    continuousOn_symm := simplexCellChart_continuousOn_symm X
    pairwiseDisjoint' := simplexCellChart_pairwiseDisjoint X
    mapsTo' := simplexCellChart_boundary X
    closed' := fun A _ => simplexCellChart_closed X A
    union' := simplexCellChart_union X }⟩

end KIP126.Topology.SimplicialRealization
