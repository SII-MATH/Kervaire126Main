module

public import KIP126.Def.Topology.SimplicialRealization.Classical.Data
public import KIP126.Def.Topology.CWComplex.Cells.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Relative.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite Set _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- The disk chart takes precisely the geometric simplex boundary to the sphere. -/
theorem simplexDiskHomeomorph_boundary (n : ℕ) (x : stdSimplex ℝ (Fin (n+1))) :
    (∃ i, x.1 i = 0) ↔ ‖(simplexDiskHomeomorph n x).1‖ = 1 :=
  (Simplex.exists_stdSimplex_closedBall_homeomorph n).choose_spec x

/-- The characteristic cell map in the pushout construction is the realized
Yoneda simplex, including its exact map into the total space. -/
theorem simplexCellIndex_characteristic (X : SSet.{u}) (n : ℕ) (s : X.nonDegenerate n) :
    ((cellComplex X).attachCells n (by simp)).cell (simplexCellIndex X n s) ≫
      (cellComplex X).incl.app (n+1) = SSet.toTop.map (SSet.yonedaEquiv.symm s.1) := by
  change (SSet.toTop.map _) ≫ (SSet.toTop.map _) ≫ (SSet.toTop.map _) = _
  rw [← Functor.map_comp,← Functor.map_comp]
  exact congrArg SSet.toTop.map
    (SSet.relativeCellComplexOfMono.Cell.ι_b_ι (simplexCellIndex X n s))

/-- Actual filtration stages embed as closed subspaces of the realization. -/
theorem cellComplex_inclusion_isClosedEmbedding (X : SSet.{u}) (n : ℕ) :
    IsClosedEmbedding ((cellComplex X).incl.app n) := by
  change IsClosedEmbedding (SSet.toTop.map
    (SSet.skeletonOfMono (SSet.Subcomplex.ι (⊥ : X.Subcomplex)) n).ι)
  exact realization_mono_isClosedEmbedding _

/-- The coproduct of actual simplex cells has the separation properties
used in the explicit pushout interior charts. -/
theorem simplexCellCoproduct_separation (X : SSet.{u}) (n : ℕ) :
    NormalSpace ((cellComplex X).attachCells n (by simp)).cofan₂.pt ∧
    T2Space ((cellComplex X).attachCells n (by simp)).cofan₂.pt := by
  let a := (cellComplex X).attachCells n (by simp)
  letI : NormalSpace |(Δ[n] : SSet.{u})| :=
    (SimplexCategory.toTopHomeo ⦋n⦌).isClosedEmbedding.normalSpace
  letI : T2Space |(Δ[n] : SSet.{u})| :=
    (SimplexCategory.toTopHomeo ⦋n⦌).isEmbedding.t2Space
  letI : NormalSpace (Σ _ : a.ι, |(Δ[n] : SSet.{u})|) := normalSpace_sigma _
  letI : NormalSpace (TopCat.sigmaCofan (fun _ : a.ι => SSet.toTop.obj (Δ[n]))).pt :=
    inferInstanceAs (NormalSpace (Σ _ : a.ι, |(Δ[n] : SSet.{u})|))
  letI : T2Space (TopCat.sigmaCofan (fun _ : a.ι => SSet.toTop.obj (Δ[n]))).pt :=
    inferInstanceAs (T2Space (Σ _ : a.ι, |(Δ[n] : SSet.{u})|))
  let e := a.isColimit₂.coconePointUniqueUpToIso
    (TopCat.sigmaCofanIsColimit (fun _ : a.ι => SSet.toTop.obj (Δ[n])))
  letI : NormalSpace a.cofan₂.pt := (TopCat.homeoOfIso e).isClosedEmbedding.normalSpace
  letI : T2Space a.cofan₂.pt := (TopCat.homeoOfIso e).isEmbedding.t2Space
  exact ⟨inferInstance,inferInstance⟩

/-- Simplex interiors embed in the actual realization; this follows from
pushout interior charts and closed embeddings of the actual skeleta. -/
theorem simplex_interior_isEmbedding (X : SSet.{u}) (n : ℕ) (s : X.nonDegenerate n) :
    IsEmbedding (fun x : {x : |(Δ[n] : SSet.{u})| //
      x ∉ Set.range (SSet.toTop.map ∂Δ[n].ι)} =>
        SSet.toTop.map (SSet.yonedaEquiv.symm s.1) x.1) := by
  let a := (cellComplex X).attachCells n (by simp)
  letI : NormalSpace a.cofan₂.pt := (simplexCellCoproduct_separation X n).1
  letI : T2Space a.cofan₂.pt := (simplexCellCoproduct_separation X n).2
  have hcell := (isOpenEmbedding_attachCells_boundary_complement a
    (fun _ => realization_mono_isClosedEmbedding ∂Δ[n].ι) (simplexCellIndex X n s)).isEmbedding
  have hstage : IsEmbedding ((cellComplex X).incl.app (n+1)) :=
    (cellComplex_inclusion_isClosedEmbedding X (n+1)).isEmbedding
  have he := hstage.comp hcell
  have hfun : (fun x : {x : |(Δ[n] : SSet.{u})| //
      x ∉ Set.range (SSet.toTop.map ∂Δ[n].ι)} =>
        SSet.toTop.map (SSet.yonedaEquiv.symm s.1) x.1) =
      ((cellComplex X).incl.app (n+1)) ∘
        (fun x : {x : |(Δ[n] : SSet.{u})| //
          x ∉ Set.range (SSet.toTop.map ∂Δ[n].ι)} => a.cell (simplexCellIndex X n s) x.1) := by
    funext x
    exact (ConcreteCategory.congr_hom (simplexCellIndex_characteristic X n s) x.1).symm
  rw [hfun]
  exact he

/-- Every point of a realized skeleton is represented by a nondegenerate
simplex whose dimension is strictly smaller than that skeleton index. -/
theorem exists_nondegenerate_of_skeleton_point (X : SSet.{u}) (n : ℕ)
    (y : (cellComplex X).F.obj n) :
    ∃ (m : ℕ) (s : X.nonDegenerate m) (t : |(Δ[m] : SSet.{u})|),
      m < n ∧ SSet.toTop.map (SSet.yonedaEquiv.symm s.1) t =
        (cellComplex X).incl.app n y := by
  let A := SSet.skeletonOfMono (SSet.Subcomplex.ι (⊥ : X.Subcomplex)) n
  obtain ⟨s,t,ht⟩ := exists_nondegenerate_simplex A.toSSet y
  have hs : s.simplex.1 ∈ X.nonDegenerate s.dim := by
    exact (A.mem_nonDegenerate_iff s.simplex).mp s.nonDegenerate
  let sX : X.nonDegenerate s.dim := ⟨s.simplex.1,hs⟩
  have hmem : sX.1 ∈ (X.skeleton n).obj (op ⦋s.dim⦌) := by
    have h := s.simplex.2
    simpa [A,SSet.skeletonOfMono] using h
  refine ⟨s.dim,sX,t,(X.mem_skeleton_obj_iff_of_nonDegenerate sX n).mp hmem,?_⟩
  have hcomp : SSet.yonedaEquiv.symm s.simplex ≫ A.ι = SSet.yonedaEquiv.symm sX.1 :=
    SSet.yonedaEquiv_symm_comp s.simplex A.ι
  have h := congrArg SSet.toTop.map hcomp
  rw [Functor.map_comp] at h
  exact (ConcreteCategory.congr_hom h t).symm.trans (congrArg (SSet.toTop.map A.ι) ht)

/-- The realized boundary of an actual cell is in the preceding skeleton. -/
theorem simplex_boundary_mem_skeleton (X : SSet.{u}) (n : ℕ) (s : X.nonDegenerate n)
    (b : |(∂Δ[n] : SSet.{u})|) :
    SSet.toTop.map (SSet.yonedaEquiv.symm s.1) (SSet.toTop.map ∂Δ[n].ι b) ∈
      Set.range ((cellComplex X).incl.app n) := by
  let c := cellComplex X
  let a := c.attachCells n (by simp)
  let k := simplexCellIndex X n s
  refine ⟨a.g₁ (a.cofan₁.inj k b),?_⟩
  have hn : c.F.map (homOfLE (Nat.le_succ n)) ≫ c.incl.app (n+1) = c.incl.app n := by
    exact (c.incl.naturality (homOfLE (Nat.le_succ n))).trans (Category.comp_id _)
  have he : a.g₁ ≫ c.incl.app n = a.m ≫ a.g₂ ≫ c.incl.app (n+1) := by
    rw [← hn,← Category.assoc, a.isPushout.w,Category.assoc]
  have he' := congrArg (fun f => a.cofan₁.inj k ≫ f) he
  rw [a.hm_assoc] at he'
  have hchar := simplexCellIndex_characteristic X n s
  change a.cofan₂.inj k ≫ a.g₂ ≫ c.incl.app (n+1) = _ at hchar
  rw [hchar] at he'
  exact ConcreteCategory.congr_hom he' b

/-- Every point has a representative in the interior of a nondegenerate
simplex: boundaries strictly decrease the dimension. -/
theorem exists_nondegenerate_interior (X : SSet.{u}) (x : |X|) :
    ∃ (n : ℕ) (s : X.nonDegenerate n) (t : |(Δ[n] : SSet.{u})|),
      t ∉ Set.range (SSet.toTop.map ∂Δ[n].ι) ∧
      SSet.toTop.map (SSet.yonedaEquiv.symm s.1) t = x := by
  classical
  have hex : ∃ n, ∃ (s : X.nonDegenerate n) (t : |(Δ[n] : SSet.{u})|),
      SSet.toTop.map (SSet.yonedaEquiv.symm s.1) t = x := by
    obtain ⟨s,t,ht⟩ := exists_nondegenerate_simplex X x
    exact ⟨s.dim,⟨s.simplex,s.nonDegenerate⟩,t,ht⟩
  obtain ⟨s,t,ht⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex,s,t,?_,ht⟩
  rintro ⟨b,hb⟩
  obtain ⟨y,hy⟩ := simplex_boundary_mem_skeleton X (Nat.find hex) s b
  obtain ⟨m,s',t',hm,ht'⟩ := exists_nondegenerate_of_skeleton_point X _ y
  exact Nat.find_min hex hm ⟨s',t',ht'.trans (hy.trans (by rw [hb,ht]))⟩

/-- A nondegenerate simplex interior is disjoint from all lower-dimensional
cells, expressed by the actual preceding skeleton inclusion. -/
theorem simplex_interior_not_mem_skeleton (X : SSet.{u}) (n : ℕ) (s : X.nonDegenerate n)
    (t : |(Δ[n] : SSet.{u})|) (ht : t ∉ Set.range (SSet.toTop.map ∂Δ[n].ι)) :
    SSet.toTop.map (SSet.yonedaEquiv.symm s.1) t ∉
      Set.range ((cellComplex X).incl.app n) := by
  let c := cellComplex X
  let a := c.attachCells n (by simp)
  rintro ⟨y,hy⟩
  apply attachCells_interior_not_mem_range a
    (fun _ => realization_mono_isClosedEmbedding ∂Δ[n].ι) (simplexCellIndex X n s) t ht
  refine ⟨y,?_⟩
  apply (cellComplex_inclusion_isClosedEmbedding X (n+1)).injective
  have hn : c.F.map (homOfLE (Nat.le_succ n)) ≫ c.incl.app (n+1) = c.incl.app n := by
    exact (c.incl.naturality (homOfLE (Nat.le_succ n))).trans (Category.comp_id _)
  exact (ConcreteCategory.congr_hom hn y).trans
    (hy.trans (ConcreteCategory.congr_hom (simplexCellIndex_characteristic X n s) t).symm)

/-- Every point of a lower-dimensional closed cell is in a later skeleton. -/
theorem simplex_mem_skeleton_of_dim_lt (X : SSet.{u}) {n m : ℕ} (h : n < m)
    (s : X.nonDegenerate n) (t : |(Δ[n] : SSet.{u})|) :
    SSet.toTop.map (SSet.yonedaEquiv.symm s.1) t ∈
      Set.range ((cellComplex X).incl.app m) := by
  let c := cellComplex X
  let a := c.attachCells n (by simp)
  refine ⟨c.F.map (homOfLE (Nat.succ_le_of_lt h))
    (a.cell (simplexCellIndex X n s) t),?_⟩
  have hn : c.F.map (homOfLE (Nat.succ_le_of_lt h)) ≫ c.incl.app m = c.incl.app (n+1) := by
    exact (c.incl.naturality (homOfLE (Nat.succ_le_of_lt h))).trans (Category.comp_id _)
  exact (ConcreteCategory.congr_hom hn _).trans
    (ConcreteCategory.congr_hom (simplexCellIndex_characteristic X n s) t)

/-- Interior representatives have unique dimension, nondegenerate simplex,
and simplex coordinate; the statement includes actual equality of points. -/
theorem nondegenerate_interior_unique (X : SSet.{u}) {n m : ℕ}
    (s : X.nonDegenerate n) (s' : X.nonDegenerate m)
    (t : |(Δ[n] : SSet.{u})|) (t' : |(Δ[m] : SSet.{u})|)
    (ht : t ∉ Set.range (SSet.toTop.map ∂Δ[n].ι))
    (ht' : t' ∉ Set.range (SSet.toTop.map ∂Δ[m].ι))
    (h : SSet.toTop.map (SSet.yonedaEquiv.symm s.1) t =
      SSet.toTop.map (SSet.yonedaEquiv.symm s'.1) t') :
    n = m ∧ HEq s s' ∧ HEq t t' := by
  have hnm : n = m := by
    rcases lt_trichotomy n m with hnm | hnm | hnm
    · exact False.elim (simplex_interior_not_mem_skeleton X m s' t' ht'
        (h ▸ simplex_mem_skeleton_of_dim_lt X hnm s t))
    · exact hnm
    · exact False.elim (simplex_interior_not_mem_skeleton X n s t ht
        (h.symm ▸ simplex_mem_skeleton_of_dim_lt X hnm s' t'))
  subst m
  let a := (cellComplex X).attachCells n (by simp)
  letI : NormalSpace a.cofan₂.pt := (simplexCellCoproduct_separation X n).1
  letI : T2Space a.cofan₂.pt := (simplexCellCoproduct_separation X n).2
  have he : a.cell (simplexCellIndex X n s) t = a.cell (simplexCellIndex X n s') t' := by
    apply (cellComplex_inclusion_isClosedEmbedding X (n+1)).injective
    exact (ConcreteCategory.congr_hom (simplexCellIndex_characteristic X n s) t).trans
      (h.trans (ConcreteCategory.congr_hom (simplexCellIndex_characteristic X n s') t').symm)
  have he' := (attachCells_interior_eq_iff a
    (fun _ => realization_mono_isClosedEmbedding ∂Δ[n].ι) ht).mp he
  have hs : s = s' := by
    apply Subtype.ext
    exact congrArg (fun k => k.simplex) (congrArg Sigma.fst he')
  subst s'
  have htt : t = t' := congrArg Subtype.val
    ((simplex_interior_isEmbedding X n s).injective (show
      SSet.toTop.map (SSet.yonedaEquiv.symm s.1) (⟨t,ht⟩ : {t : |(Δ[n] : SSet.{u})| //
        t ∉ Set.range (SSet.toTop.map ∂Δ[n].ι)}).1 =
      SSet.toTop.map (SSet.yonedaEquiv.symm s.1) (⟨t',ht'⟩ : {t : |(Δ[n] : SSet.{u})| //
        t ∉ Set.range (SSet.toTop.map ∂Δ[n].ι)}).1 from h))
  exact ⟨rfl,HEq.rfl,heq_of_eq htt⟩

/-- The geometric boundary criterion expressed directly in realization
coordinates, without changing the actual simplex map. -/
theorem simplex_mem_boundary_iff (n : ℕ) (t : |(Δ[n] : SSet.{u})|) :
    t ∈ Set.range (SSet.toTop.map ∂Δ[n].ι) ↔
      ∃ i, (SimplexCategory.toTopHomeo ⦋n⦌ t).1 i = 0 := by
  have h := boundary_realization_range.{u} n (SimplexCategory.toTopHomeo ⦋n⦌ t)
  constructor
  · rintro ⟨b,rfl⟩
    exact h.mp ⟨b,rfl⟩
  · intro ht
    obtain ⟨b,hb⟩ := h.mpr ht
    exact ⟨b,(SimplexCategory.toTopHomeo ⦋n⦌).injective hb⟩

/-- The characteristic disk restricts to an embedding on the open ball. -/
theorem simplexCharacteristic_interior_isEmbedding (X : SSet.{u}) (n : ℕ)
    (s : X.nonDegenerate n) :
    IsEmbedding (fun x : Metric.ball (0 : Fin n → ℝ) 1 =>
      simplexCharacteristic X n s ⟨x.1,Metric.ball_subset_closedBall x.2⟩) := by
  let e : Metric.closedBall (0 : Fin n → ℝ) 1 ≃ₜ |(Δ[n] : SSet.{u})| :=
    (simplexDiskHomeomorph n).symm.trans (SimplexCategory.toTopHomeo ⦋n⦌).symm
  let j : Metric.ball (0 : Fin n → ℝ) 1 → |(Δ[n] : SSet.{u})| :=
    fun x => e ⟨x.1,Metric.ball_subset_closedBall x.2⟩
  have hj : IsEmbedding j := e.isEmbedding.comp (IsEmbedding.inclusion Metric.ball_subset_closedBall)
  have hb (x : Metric.ball (0 : Fin n → ℝ) 1) :
      j x ∉ Set.range (SSet.toTop.map ∂Δ[n].ι) := by
    rw [simplex_mem_boundary_iff]
    change ¬ ∃ i, (SimplexCategory.toTopHomeo ⦋n⦌
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm ((simplexDiskHomeomorph n).symm
        ⟨x.1,Metric.ball_subset_closedBall x.2⟩))).1 i = 0
    rw [Homeomorph.apply_symm_apply, simplexDiskHomeomorph_boundary,
      Homeomorph.apply_symm_apply]
    exact ne_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using x.2)
  exact (simplex_interior_isEmbedding X n s).comp
    (hj.codRestrict _ hb)

/-- Closedness in realization is detected by its actual nondegenerate
simplex maps, as follows from the genuine colimit topology. -/
theorem realization_isClosed_of_simplex_preimages (X : SSet.{u}) (A : Set |X|)
    (hA : ∀ n (s : X.nonDegenerate n),
      IsClosed ((SSet.toTop.map (SSet.yonedaEquiv.symm s.1)) ⁻¹' A)) : IsClosed A := by
  let c := SSet.toTop.mapCocone X.coconeN
  have hc : IsColimit c := isColimitOfPreserves SSet.toTop X.isColimitCoconeN
  apply (TopCat.isClosed_iff_of_isColimit c hc A).mpr
  intro s
  let f := SSet.toTop.map (SSet.Subcomplex.toOfSimplex s.simplex)
  letI := compactSpace_stdSimplex.{u} s.dim
  letI := realization_t2Space s.subcomplex.toSSet
  have hf : IsQuotientMap f := IsQuotientMap.of_surjective_continuous
    ((TopCat.epi_iff_surjective f).mp inferInstance) f.hom.continuous
  apply hf.isClosed_preimage.mp
  have he : f ≫ SSet.toTop.map s.subcomplex.ι =
      SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex) := by
    rw [← Functor.map_comp]
    exact congrArg SSet.toTop.map (SSet.Subcomplex.toOfSimplex_ι s.simplex)
  have he' : f ⁻¹' (c.ι.app s ⁻¹' A) =
      (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)) ⁻¹' A := by
    change (fun x => SSet.toTop.map s.subcomplex.ι (f x)) ⁻¹' A = _
    rw [← he]
    rfl
  rw [he']
  exact hA s.dim ⟨s.simplex,s.nonDegenerate⟩

/-- Only finitely many lower-dimensional nondegenerate cells occur on the
boundary of each actual simplex. The finite set comes from its simplicial
boundary image, not an added closure-finiteness hypothesis. -/
theorem simplex_boundary_finite_cells (X : SSet.{u}) (n : ℕ) (s : X.nonDegenerate n) :
    ∃ I : ∀ m, Finset (X.nonDegenerate m),
      ∀ b : |(∂Δ[n] : SSet.{u})|,
        ∃ (m : ℕ) (_ : m < n) (j : X.nonDegenerate m) (_ : j ∈ I m)
          (t : |(Δ[m] : SSet.{u})|),
          SSet.toTop.map (SSet.yonedaEquiv.symm j.1) t =
            SSet.toTop.map (SSet.yonedaEquiv.symm s.1) (SSet.toTop.map ∂Δ[n].ι b) := by
  classical
  let f : (∂Δ[n] : SSet.{u}) ⟶ X := ∂Δ[n].ι ≫ SSet.yonedaEquiv.symm s.1
  let B := SSet.Subcomplex.range f
  letI : SSet.Finite B.toSSet := SSet.finite_of_epi (SSet.Subcomplex.toRange f)
  letI : SSet.HasDimensionLT B.toSSet n := inferInstanceAs (SSet.HasDimensionLT (SSet.Subcomplex.range f) n)
  let lift (m : ℕ) (j : B.toSSet.nonDegenerate m) : X.nonDegenerate m :=
    ⟨j.1.1,(B.mem_nonDegenerate_iff j.1).mp j.2⟩
  let I (m : ℕ) : Finset (X.nonDegenerate m) :=
    (Set.finite_range (lift m)).toFinset
  refine ⟨I,?_⟩
  intro b
  obtain ⟨j,t,ht⟩ := exists_nondegenerate_simplex B.toSSet
    (SSet.toTop.map (SSet.Subcomplex.toRange f) b)
  let j' : B.toSSet.nonDegenerate j.dim := ⟨j.simplex,j.nonDegenerate⟩
  have hdim : j.dim < n := B.toSSet.dim_lt_of_nonDegenerate j' n
  refine ⟨j.dim,hdim,lift j.dim j',?_,t,?_⟩
  · exact ((Set.finite_range (lift j.dim)).mem_toFinset).mpr ⟨j',rfl⟩
  · have he : SSet.yonedaEquiv.symm j.simplex ≫ B.ι =
        SSet.yonedaEquiv.symm (lift j.dim j').1 :=
      SSet.yonedaEquiv_symm_comp j.simplex B.ι
    have he' := congrArg SSet.toTop.map he
    rw [Functor.map_comp] at he'
    calc
      SSet.toTop.map (SSet.yonedaEquiv.symm (lift j.dim j').1) t =
          SSet.toTop.map B.ι (SSet.toTop.map (SSet.yonedaEquiv.symm j.simplex) t) :=
        (ConcreteCategory.congr_hom he' t).symm
      _ = SSet.toTop.map B.ι (SSet.toTop.map (SSet.Subcomplex.toRange f) b) := congrArg _ ht
      _ = SSet.toTop.map (SSet.yonedaEquiv.symm s.1) (SSet.toTop.map ∂Δ[n].ι b) := by
        change (SSet.toTop.map (SSet.Subcomplex.toRange f) ≫ SSet.toTop.map B.ι) b = _
        rw [← Functor.map_comp, SSet.Subcomplex.toRange_ι]
        change SSet.toTop.map (∂Δ[n].ι ≫ SSet.yonedaEquiv.symm s.1) b = _
        rw [Functor.map_comp]
        rfl

/-- On the disk the total characteristic map is the actual continuous
simplex parametrization. -/
@[simp] theorem simplexCharacteristicExtension_apply (X : SSet.{u}) (n : ℕ)
    (s : X.nonDegenerate n) (x : Metric.closedBall (0 : Fin n → ℝ) 1) :
    simplexCharacteristicExtension X n s x.1 = simplexCharacteristic X n s x := by
  simp only [simplexCharacteristicExtension,dif_pos x.2]

/-- The total representative retains continuity on the whole closed cell. -/
theorem simplexCharacteristicExtension_continuousOn (X : SSet.{u}) (n : ℕ)
    (s : X.nonDegenerate n) :
    ContinuousOn (simplexCharacteristicExtension X n s) (Metric.closedBall 0 1) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have h : (Metric.closedBall (0 : Fin n → ℝ) 1).restrict
      (simplexCharacteristicExtension X n s) = simplexCharacteristic X n s := by
    funext x
    exact simplexCharacteristicExtension_apply X n s x
  rw [h]
  exact (simplexCharacteristic X n s).continuous

/-- The total representative is injective on the actual open cell. -/
theorem simplexCharacteristicExtension_injOn (X : SSet.{u}) (n : ℕ)
    (s : X.nonDegenerate n) :
    Set.InjOn (simplexCharacteristicExtension X n s) (Metric.ball 0 1) := by
  intro x hx y hy he
  have hxy : (⟨x,hx⟩ : Metric.ball (0 : Fin n → ℝ) 1) = ⟨y,hy⟩ := by
    apply (simplexCharacteristic_interior_isEmbedding X n s).injective
    change simplexCharacteristic X n s ⟨x,Metric.ball_subset_closedBall hx⟩ =
      simplexCharacteristic X n s ⟨y,Metric.ball_subset_closedBall hy⟩
    simpa only [← simplexCharacteristicExtension_apply] using he
  exact congrArg Subtype.val hxy

/-- The closed-cell image is exactly the image of the realized simplex. -/
theorem simplexCharacteristicExtension_closedCell (X : SSet.{u}) (n : ℕ)
    (s : X.nonDegenerate n) :
    simplexCharacteristicExtension X n s '' Metric.closedBall 0 1 =
      Set.range (SSet.toTop.map (SSet.yonedaEquiv.symm s.1)) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [show simplexCharacteristicExtension X n s x =
      simplexCharacteristic X n s ⟨x,hx⟩ from simplexCharacteristicExtension_apply X n s ⟨x,hx⟩]
    exact ⟨_,rfl⟩
  · rintro ⟨t,rfl⟩
    let x := simplexDiskHomeomorph n (SimplexCategory.toTopHomeo ⦋n⦌ t)
    refine ⟨x.1,x.2,?_⟩
    rw [simplexCharacteristicExtension_apply]
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.1)
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm ((simplexDiskHomeomorph n).symm
        (simplexDiskHomeomorph n (SimplexCategory.toTopHomeo ⦋n⦌ t)))) = _
    rw [Homeomorph.symm_apply_apply,Homeomorph.symm_apply_apply]

/-- In disk coordinates the open cell is precisely the nondegenerate
simplex interior, with its proved boundary complement. -/
theorem simplexCharacteristicExtension_openCell (X : SSet.{u}) (n : ℕ)
    (s : X.nonDegenerate n) :
    simplexCharacteristicExtension X n s '' Metric.ball 0 1 =
      (SSet.toTop.map (SSet.yonedaEquiv.symm s.1)) ''
        (Set.range (SSet.toTop.map ∂Δ[n].ι))ᶜ := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    let z : Metric.closedBall (0 : Fin n → ℝ) 1 := ⟨x,Metric.ball_subset_closedBall hx⟩
    let t := (SimplexCategory.toTopHomeo ⦋n⦌).symm ((simplexDiskHomeomorph n).symm z)
    refine ⟨t,?_,(simplexCharacteristicExtension_apply X n s z).symm⟩
    rw [Set.mem_compl_iff,simplex_mem_boundary_iff]
    change ¬ ∃ i, (SimplexCategory.toTopHomeo ⦋n⦌
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm ((simplexDiskHomeomorph n).symm z))).1 i = 0
    rw [Homeomorph.apply_symm_apply,simplexDiskHomeomorph_boundary,Homeomorph.apply_symm_apply]
    exact ne_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hx)
  · rintro ⟨t,ht,rfl⟩
    let x := simplexDiskHomeomorph n (SimplexCategory.toTopHomeo ⦋n⦌ t)
    have hx : x.1 ∈ Metric.ball (0 : Fin n → ℝ) 1 := by
      have hn : ‖x.1‖ ≠ 1 := by
        intro hn
        exact ht ((simplex_mem_boundary_iff n t).mpr
          ((simplexDiskHomeomorph_boundary n _).mpr hn))
      have hle : ‖x.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using x.2
      simpa only [Metric.mem_ball,dist_zero_right] using lt_of_le_of_ne hle hn
    refine ⟨x.1,hx,?_⟩
    rw [simplexCharacteristicExtension_apply]
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.1)
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm ((simplexDiskHomeomorph n).symm
        (simplexDiskHomeomorph n (SimplexCategory.toTopHomeo ⦋n⦌ t)))) = _
    rw [Homeomorph.symm_apply_apply,Homeomorph.symm_apply_apply]

end KIP126.Topology.SimplicialRealization
