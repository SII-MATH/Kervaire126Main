module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import Mathlib.Topology.DiscreteSubset

@[expose] public section

namespace KIP126.Topology

open Set _root_.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  {C : Set X} [CWComplex C]

/-- A compact subset of a Hausdorff CW complex meets only finitely many
open cells, and hence is covered by finitely many closed cells. -/
theorem cw_compact_subset_finite_closedCells (K : Set X)
    (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ F : Finset (Σ n : ℕ, RelCWComplex.cell C n),
      K ⊆ ⋃ a ∈ F, RelCWComplex.closedCell a.1 a.2 := by
  classical
  let Cells := Σ n : ℕ, RelCWComplex.cell C n
  let J : Set Cells := {a | (K ∩ RelCWComplex.openCell a.1 a.2).Nonempty}
  choose p hp using (fun a : J => a.2)
  have hlabel (a : J) (b : Cells) (h : p a ∈ RelCWComplex.openCell b.1 b.2) :
      a.1 = b := by
    by_contra hn
    exact Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne hn) (hp a).2 h
  have hinj : Function.Injective p := by
    intro a b h
    apply Subtype.ext
    apply hlabel a b.1
    rw [h]
    exact (hp b).2
  have hclosed (T : Set X) (hT : T ⊆ Set.range p) : IsClosed T := by
    have hTC : T ⊆ C := by
      rintro x hx
      obtain ⟨a, rfl⟩ := hT hx
      exact hKC (hp a).1
    apply CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
      hTC
    intro n hn i
    left
    have hs : (T ∩ RelCWComplex.openCell n i).Subsingleton := by
      intro x hx y hy
      obtain ⟨a, rfl⟩ := hT hx.1
      obtain ⟨b, rfl⟩ := hT hy.1
      have hab : a = b := Subtype.ext ((hlabel a ⟨n,i⟩ hx.2).trans
        (hlabel b ⟨n,i⟩ hy.2).symm)
      exact congrArg p hab
    exact hs.finite.isClosed
  have hcompact : IsCompact (Set.range p) :=
    hK.of_isClosed_subset (hclosed _ Set.Subset.rfl) (by
      rintro _ ⟨a,rfl⟩
      exact (hp a).1)
  have hdiscrete : IsDiscrete (Set.range p) :=
    isDiscrete_iff_forall_mem_exists_isClosed.mpr (by
      intro T hT
      exact ⟨T,hclosed T hT,Set.inter_eq_left.mpr hT⟩)
  have hfinite : Finite J := (Set.finite_range_iff hinj).mp (hcompact.finite hdiscrete)
  have hJ : J.Finite := Set.finite_coe_iff.mp hfinite
  refine ⟨hJ.toFinset, ?_⟩
  intro x hx
  have hcover : x ∈ ⋃ n : ℕ, ⋃ i : RelCWComplex.cell C n,
      RelCWComplex.openCell n i := by
    rw [CWComplex.iUnion_openCell_eq_complex]
    exact hKC hx
  obtain ⟨n,i,hi⟩ := by simpa only [Set.mem_iUnion] using hcover
  refine Set.mem_iUnion.mpr ⟨⟨n,i⟩,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
  · exact hJ.mem_toFinset.mpr ⟨x,hx,hi⟩
  · exact RelCWComplex.openCell_subset_closedCell n i hi

omit [T2Space X] in
/-- Closure-finiteness extends one closed cell to a finite collection of
cells that contains the closure of each of its own open cells. -/
theorem cw_closedCell_subset_finite_saturated_cells (n : ℕ)
    (i : RelCWComplex.cell C n) :
    ∃ F : Finset (Σ m : ℕ, RelCWComplex.cell C m),
      (⟨n,i⟩ ∈ F) ∧
      ∀ a ∈ F, RelCWComplex.closedCell a.1 a.2 ⊆
        ⋃ b ∈ F, RelCWComplex.openCell b.1 b.2 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨J, hJ⟩ := CWComplex.cellFrontier_subset_finite_closedCell n i
    let B : Finset (Σ m : ℕ, RelCWComplex.cell C m) :=
      (Finset.range n).biUnion (fun m => (J m).map
        ⟨Sigma.mk m, fun _ _ h => eq_of_heq (Sigma.mk.inj h).2⟩)
    have memB (b : Σ m : ℕ, RelCWComplex.cell C m) :
        b ∈ B ↔ b.1 < n ∧ b.2 ∈ J b.1 := by
      rcases b with ⟨m,j⟩
      simp only [B, Finset.mem_biUnion, Finset.mem_range, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨k,hk,l,hl,he⟩
        cases he
        exact ⟨hk,hl⟩
      · rintro ⟨hm,hj⟩
        exact ⟨m,hm,j,hj,rfl⟩
    choose F hmem hclosed using (fun b : B => ih b.1.1 ((memB b.1).mp b.2).1 b.1.2)
    let G := insert (⟨n,i⟩ : Σ m : ℕ, RelCWComplex.cell C m)
      (Finset.univ.biUnion F)
    have hsub (b : B) : F b ⊆ G := by
      intro a ha
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, ha⟩)
    have hmono (b : B) :
        (⋃ a ∈ F b, RelCWComplex.openCell a.1 a.2) ⊆
          ⋃ a ∈ G, RelCWComplex.openCell a.1 a.2 := by
      exact Set.iUnion₂_mono' fun a ha => ⟨a, hsub b ha, Set.Subset.rfl⟩
    refine ⟨G, Finset.mem_insert_self _ _, ?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell]
      apply Set.union_subset
      · intro x hx
        obtain ⟨m, hmn, j, hj, hxj⟩ := by
          simpa only [Set.mem_iUnion, exists_prop] using hJ hx
        let b : B := ⟨⟨m,j⟩, (memB ⟨m,j⟩).mpr ⟨hmn,hj⟩⟩
        exact hmono b (hclosed b b.1 (hmem b) hxj)
      · exact Set.subset_iUnion₂_of_subset _ (Finset.mem_insert_self _ _) Set.Subset.rfl
    · obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp ha
      exact (hclosed b a hb).trans (hmono b)

/-- Every compact subset of a Hausdorff CW complex is contained in an
actual finite subcomplex, with its inherited characteristic maps. -/
theorem cw_compact_subset_finite_subcomplex (K : Set X)
    (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ E : CWComplex.Subcomplex C,
      CWComplex.Finite (E : Set X) ∧ K ⊆ E := by
  classical
  obtain ⟨F₀, hF₀⟩ := cw_compact_subset_finite_closedCells K hK hKC
  choose F hmem hclosed using
    (fun a : F₀ => cw_closedCell_subset_finite_saturated_cells a.1.1 a.1.2)
  let G := Finset.univ.biUnion F
  have hsub (a : F₀) : F a ⊆ G :=
    fun _ hb => Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hb⟩
  have hmono (a : F₀) :
      (⋃ b ∈ F a, RelCWComplex.openCell b.1 b.2) ⊆
        ⋃ b ∈ G, RelCWComplex.openCell b.1 b.2 :=
    Set.iUnion₂_mono' fun b hb => ⟨b, hsub a hb, Set.Subset.rfl⟩
  have hG (b) (hb : b ∈ G) : RelCWComplex.closedCell b.1 b.2 ⊆
      ⋃ a ∈ G, RelCWComplex.openCell a.1 a.2 := by
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hb
    exact (hclosed a b ha).trans (hmono a)
  let E : CWComplex.Subcomplex C := CWComplex.Subcomplex.mk' C
    (⋃ a ∈ G, RelCWComplex.openCell a.1 a.2)
    (fun n => {i | (⟨n,i⟩ : Σ m : ℕ, RelCWComplex.cell C m) ∈ G})
    (fun n i => hG ⟨n,i.1⟩ i.2) (by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨n,i,hx⟩
        exact ⟨⟨n,i.1⟩,i.2,hx⟩
      · rintro ⟨⟨n,i⟩,hi,hx⟩
        exact ⟨n,⟨i,hi⟩,hx⟩)
  have hfinite : Finite (Σ n, RelCWComplex.cell (E : Set X) n) := by
    let f : (Σ n, RelCWComplex.cell (E : Set X) n) → G :=
      fun a => ⟨⟨a.1,a.2.1⟩,a.2.2⟩
    apply Finite.of_injective f
    rintro ⟨n,i,hi⟩ ⟨m,j,hj⟩ h
    have he : (⟨n,i⟩ : Σ m : ℕ, RelCWComplex.cell C m) = ⟨m,j⟩ :=
      congrArg Subtype.val h
    cases he
    rfl
  refine ⟨E, RelCWComplex.finite_of_finite_cells (C := (E : Set X)) hfinite, ?_⟩
  intro x hx
  obtain ⟨a,ha,hxa⟩ := by simpa only [Set.mem_iUnion] using hF₀ hx
  exact hmono ⟨a,ha⟩ (hclosed ⟨a,ha⟩ a (hmem ⟨a,ha⟩) hxa)

/-- A continuous map from a compact space factors through a finite
subcomplex of its Hausdorff CW target. -/
theorem continuousMap_factor_finite_subcomplex
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (f : C(A,X)) (hf : Set.range f ⊆ C) :
    ∃ E : CWComplex.Subcomplex C, CWComplex.Finite (E : Set X) ∧
      ∃ g : C(A,E), ∀ a, (g a).1 = f a := by
  obtain ⟨E,hE,he⟩ := cw_compact_subset_finite_subcomplex (Set.range f)
    (isCompact_range f.continuous) hf
  refine ⟨E,hE,⟨fun a => ⟨f a,he ⟨a,rfl⟩⟩,
    f.continuous.subtype_mk _⟩,fun _ => rfl⟩

omit [T2Space X] in
/-- The underlying space of an actual finite CW complex is compact. -/
theorem cw_finite_isCompact [CWComplex.Finite C] : IsCompact C := by
  letI := RelCWComplex.finite_cells_of_finite (C := C)
  have h : IsCompact (⋃ a : Σ n, RelCWComplex.cell C n,
      RelCWComplex.closedCell a.1 a.2) :=
    isCompact_iUnion fun _ => RelCWComplex.isCompact_closedCell
  simpa only [Set.iUnion_sigma, CWComplex.union] using h

/-- Two actual finite subcomplexes are contained in a third. Thus finite
subcomplex approximation is directed, rather than an unrelated collection
of finite supports for individual maps. -/
theorem cw_finite_subcomplex_directed
    (E F : CWComplex.Subcomplex C)
    [CWComplex.Finite (E : Set X)] [CWComplex.Finite (F : Set X)] :
    ∃ G : CWComplex.Subcomplex C,
      CWComplex.Finite (G : Set X) ∧ E ≤ G ∧ F ≤ G := by
  obtain ⟨G,hG,h⟩ := cw_compact_subset_finite_subcomplex ((E : Set X) ∪ F)
    (cw_finite_isCompact.union cw_finite_isCompact)
    (Set.union_subset E.subset_complex F.subset_complex)
  exact ⟨G,hG,fun _ hx => h (Or.inl hx),fun _ hx => h (Or.inr hx)⟩

/-- The actual CW topology is detected on its finite subcomplexes. This is
the topological finality assertion for finite subcomplex approximation. -/
theorem cw_isClosed_iff_finite_subcomplex (S : Set X) (hSC : S ⊆ C) :
    IsClosed S ↔ ∀ E : CWComplex.Subcomplex C,
      CWComplex.Finite (E : Set X) → IsClosed (S ∩ E) := by
  constructor
  · intro hS E _
    exact hS.inter E.closed
  · intro h
    apply CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hSC
    intro n _ i
    right
    obtain ⟨E,hE,he⟩ := cw_compact_subset_finite_subcomplex
      (RelCWComplex.closedCell n i) RelCWComplex.isCompact_closedCell
      (RelCWComplex.closedCell_subset_complex n i)
    have hi : S ∩ RelCWComplex.closedCell n i =
        (S ∩ E) ∩ RelCWComplex.closedCell n i := by
      rw [Set.inter_assoc, Set.inter_eq_right.mpr he]
    rw [hi]
    exact (h E hE).inter RelCWComplex.isClosed_closedCell

end KIP126.Topology
