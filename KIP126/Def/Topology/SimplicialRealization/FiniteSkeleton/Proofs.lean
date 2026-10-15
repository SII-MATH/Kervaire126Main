module

public import KIP126.Def.Topology.SimplicialRealization.CWComplex.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Classical.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
universe u
set_option backward.isDefEq.respectTransparency false

/-- Above a genuine dimension bound, the actual simplicial skeleton is
the entire simplicial set. -/
theorem skeleton_eq_top_of_dimension (X : SSet.{u}) (d : ℕ) [X.HasDimensionLT d] :
    X.skeleton d = ⊤ := by
  apply top_unique
  rw [SSet.Subcomplex.le_iff_contains_nonDegenerate]
  intro n x _
  have hn : n < d := by
    by_contra! hn
    have hx := x.property
    simpa only [X.nonDegenerate_eq_empty_of_hasDimensionLT d n hn,Set.mem_empty_iff_false] using hx
  exact X.mem_skeleton x.val hn

/-- The actual inclusion from the terminal finite skeleton is an
isomorphism, not merely a homotopy equivalence. -/
theorem skeleton_inclusion_isIso_of_dimension (X : SSet.{u}) (d : ℕ)
    [X.HasDimensionLT d] : IsIso (SSet.toTop.map (X.skeleton d).ι) := by
  rw [skeleton_eq_top_of_dimension X d]
  infer_instance

/-- The specified simplex-attachment filtration reaches the actual
target at every dimension bound. -/
theorem cellComplex_inclusion_isIso_of_dimension (X : SSet.{u}) (d : ℕ)
    [X.HasDimensionLT d] : IsIso ((cellComplex X).incl.app d) := by
  change IsIso (SSet.toTop.map (SSet.Subcomplex.ι
    (SSet.skeletonOfMono (SSet.Subcomplex.ι (⊥ : X.Subcomplex)) d)))
  have h : SSet.skeletonOfMono (SSet.Subcomplex.ι (⊥ : X.Subcomplex)) d = ⊤ := by
    simp [SSet.skeletonOfMono,skeleton_eq_top_of_dimension X d]
  rw [h]
  infer_instance

/-- A finite simplicial realization is already one of its actual finite
attachment stages. -/
theorem finite_cellComplex_exists_terminal_stage (X : SSet.{u}) [X.Finite] :
    ∃ d : ℕ, IsIso ((cellComplex X).incl.app d) := by
  obtain ⟨d,hd⟩ := X.hasDimensionLT_of_finite
  letI := hd
  exact ⟨d,cellComplex_inclusion_isIso_of_dimension X d⟩

/-- The actual zeroth attachment stage is empty. -/
theorem cellComplex_stage_zero_isEmpty (X : SSet.{u}) :
    IsEmpty ((cellComplex X).F.obj 0) := by
  have h0 := (SSet.Subcomplex.isInitialBot (X := X)).isInitialObj SSet.toTop
  letI : IsEmpty |(⊥ : X.Subcomplex).toSSet| :=
    Function.isEmpty (h0.to (TopCat.of PEmpty.{u+1}))
  exact Function.isEmpty (cellComplex X).isoBot.hom

/-- The finite source filtration has genuinely compact intermediate spaces. -/
theorem finite_cellComplex_stage_compact (X : SSet.{u}) [X.Finite] (n : ℕ) :
    CompactSpace ((cellComplex X).F.obj n) := by
  change CompactSpace |(SSet.skeletonOfMono (SSet.Subcomplex.ι (⊥ : X.Subcomplex)) n).toSSet|
  exact compactSpace_of_finite _

theorem cellComplex_stage_t2Space (X : SSet.{u}) (n : ℕ) :
    T2Space ((cellComplex X).F.obj n) := by
  change T2Space |(SSet.skeletonOfMono (SSet.Subcomplex.ι (⊥ : X.Subcomplex)) n).toSSet|
  exact realization_t2Space _

/-- Each actual attachment layer has finitely many cells for a finite
simplicial target. -/
theorem finite_cellComplex_stage_cells (X : SSet.{u}) [X.Finite] (n : ℕ) :
    Finite ((cellComplex X).attachCells n (by simp)).ι := by
  change Finite (SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : X.Subcomplex)) n)
  exact Finite.of_injective (fun c => c.simplex) (by intro a b h; cases a; cases b; cases h; rfl)

/-- The complete coproduct of newly attached simplex cells is compact. -/
theorem finite_cellComplex_cell_coproduct_compact (X : SSet.{u}) [X.Finite] (n : ℕ) :
    CompactSpace ((cellComplex X).attachCells n (by simp)).cofan₂.pt := by
  let c := (cellComplex X).attachCells n (by simp)
  letI : Finite c.ι := finite_cellComplex_stage_cells X n
  letI : CompactSpace |(Δ[n] : SSet.{u})| := compactSpace_stdSimplex n
  let e := c.isColimit₂.coconePointUniqueUpToIso
    (TopCat.sigmaCofanIsColimit (fun _ : c.ι => SSet.toTop.obj (Δ[n])))
  letI : CompactSpace (TopCat.sigmaCofan (fun _ : c.ι => SSet.toTop.obj (Δ[n]))).pt :=
    inferInstanceAs (CompactSpace (Σ _ : c.ι, |(Δ[n] : SSet.{u})|))
  exact (TopCat.homeoOfIso e).symm.compactSpace

theorem cellComplex_step_inclusion (X : SSet.{u}) (n : ℕ) :
    (cellComplex X).F.map (homOfLE (Nat.le_succ n)) ≫ (cellComplex X).incl.app (n+1) =
      (cellComplex X).incl.app n := by
  exact ((cellComplex X).incl.naturality (homOfLE (Nat.le_succ n))).trans
    (Category.comp_id _)

/-- The exact map of each attached cell into the target is its original
Yoneda simplex, for the unchanged actual cell index. -/
theorem cellComplex_cell_characteristic (X : SSet.{u}) (n : ℕ)
    (c : ((cellComplex X).attachCells n (by simp)).ι) :
    ((cellComplex X).attachCells n (by simp)).cell c ≫ (cellComplex X).incl.app (n+1) =
      SSet.toTop.map (SSet.yonedaEquiv.symm c.simplex) := by
  change (SSet.toTop.map _) ≫ (SSet.toTop.map _) ≫ (SSet.toTop.map _) = _
  rw [← Functor.map_comp,← Functor.map_comp]
  exact congrArg SSet.toTop.map (SSet.relativeCellComplexOfMono.Cell.ι_b_ι c)

theorem cellComplex_boundary_coproduct_isClosedEmbedding (X : SSet.{u}) (n : ℕ) :
    _root_.Topology.IsClosedEmbedding ((cellComplex X).attachCells n (by simp)).m := by
  let c := (cellComplex X).attachCells n (by simp)
  exact isClosedEmbedding_of_coproduct (fun _ : c.ι => SSet.toTop.map (∂Δ[n].ι))
    (fun _ => realization_mono_isClosedEmbedding _) c.cofan₁ c.cofan₂
    c.isColimit₁ c.isColimit₂ c.m c.hm

end KIP126.Topology.SimplicialRealization
