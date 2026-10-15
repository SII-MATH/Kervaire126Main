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

end KIP126.Topology
