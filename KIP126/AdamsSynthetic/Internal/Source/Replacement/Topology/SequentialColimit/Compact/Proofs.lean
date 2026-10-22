module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Proofs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homotopy.Basic

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology Set
open scoped unitInterval

universe u v

set_option backward.isDefEq.respectTransparency false

variable (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)

/-- The actual stage images of a sequential colimit form an increasing family. -/
theorem range_nat_colimit_mono :
    Monotone (fun n : ℕ => (Set.range (c.ι.app n) : Set c.pt)) := by
  intro n m h
  rintro _ ⟨x, rfl⟩
  exact ⟨F.map (homOfLE h) x, ConcreteCategory.congr_hom (c.w (homOfLE h)) x⟩

include hc

/-- Every finite subset of an actual sequential colimit lies in one stage. -/
theorem finite_subset_range_nat_colimit (K : Set c.pt) (hK : K.Finite) :
    ∃ n, K ⊆ Set.range (c.ι.app n) := by
  have hc' := isColimitOfPreserves (forget TopCat) hc
  classical
  induction K, hK using Set.Finite.induction_on with
  | empty => exact ⟨0, Set.empty_subset _⟩
  | @insert x K hx hK ih =>
      obtain ⟨n, y, hy⟩ := Types.jointly_surjective_of_isColimit hc' x
      obtain ⟨m, hm⟩ := ih
      refine ⟨max n m, ?_⟩
      rintro z (rfl | hz)
      · exact range_nat_colimit_mono F c (le_max_left n m) ⟨y, hy⟩
      · exact range_nat_colimit_mono F c (le_max_right n m) (hm hz)

/-- A compact subset of a sequential colimit of closed embeddings of T1 spaces
lies in an actual finite stage. The colimit topology prevents an escaping
sequence from accumulating across infinitely many stages. -/
theorem isCompact_subset_range_nat_colimit
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    (K : Set c.pt) (hK : IsCompact K) :
    ∃ n, K ⊆ Set.range (c.ι.app n) := by
  classical
  by_contra hn
  have hx : ∀ n, ∃ x : c.pt, x ∈ K ∧ x ∉ Set.range (c.ι.app n) := by
    intro n
    by_contra h
    apply hn
    refine ⟨n, ?_⟩
    intro x hx
    by_contra hr
    exact h ⟨x, hx, hr⟩
  choose x hxK hxout using hx
  have hι (n : ℕ) : Function.Injective (c.ι.app n) :=
    (isClosedEmbedding_nat_colimit F c hc hF n).injective
  have hclosed (S : Set c.pt) (hS : S ⊆ Set.range x) : IsClosed S := by
    apply (TopCat.isClosed_iff_of_isColimit c hc S).mpr
    intro n
    have hfinite : (c.ι.app n ⁻¹' S).Finite := by
      apply Set.Finite.subset
        (Set.Finite.preimage (hι n).injOn (Set.finite_range (fun i : Fin n => x i)))
      intro y hy
      obtain ⟨m, hm⟩ := hS hy
      have hmn : m < n := by
        by_contra hh
        exact hxout m (range_nat_colimit_mono F c (Nat.le_of_not_gt hh)
          ⟨y, hm.symm⟩)
      exact ⟨⟨m, hmn⟩, hm⟩
    exact hfinite.isClosed
  have hsub : Set.range x ⊆ K := by rintro _ ⟨n, rfl⟩; exact hxK n
  have hdis : IsDiscrete (Set.range x) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro S hS
    exact ⟨S, hclosed S hS, Set.inter_eq_left.mpr hS⟩
  have hfinite : (Set.range x).Finite :=
    (hK.of_isClosed_subset (hclosed _ (Set.Subset.refl _)) hsub).finite hdis
  obtain ⟨n, hn⟩ := finite_subset_range_nat_colimit F c hc _ hfinite
  exact hxout n (hn ⟨n, rfl⟩)

/-- Every continuous map from a compact space factors continuously through
one of the actual closed embedded stages. -/
theorem continuousMap_factor_nat_colimit
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    {A : Type v} [TopologicalSpace A] [CompactSpace A] (f : C(A, c.pt)) :
    ∃ (n : ℕ) (g : C(A, F.obj n)), ∀ x, c.ι.app n (g x) = f x := by
  obtain ⟨n, hn⟩ := isCompact_subset_range_nat_colimit F c hc hF
    (Set.range f) (isCompact_range f.continuous)
  choose g hg using fun x => hn (Set.mem_range_self x)
  have hcG : Continuous g := by
    apply (isClosedEmbedding_nat_colimit F c hc hF n).isEmbedding.continuous_iff.mpr
    have he : (c.ι.app n) ∘ g = f := funext hg
    rw [he]
    exact f.continuous
  exact ⟨n, ⟨g, hcG⟩, hg⟩

/-- The finite stage of a compact map may be required to lie beyond any
already specified stage. -/
theorem continuousMap_factor_nat_colimit_after
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    {A : Type v} [TopologicalSpace A] [CompactSpace A] (f : C(A, c.pt)) (n : ℕ) :
    ∃ (m : ℕ) (_ : n ≤ m) (g : C(A, F.obj m)), ∀ x, c.ι.app m (g x) = f x := by
  obtain ⟨k, g, hg⟩ := continuousMap_factor_nat_colimit F c hc hF f
  refine ⟨max k n, le_max_right _ _,
    (F.map (homOfLE (le_max_left k n))).hom.comp g, ?_⟩
  intro x
  exact (ConcreteCategory.congr_hom (c.w (homOfLE (le_max_left k n))) (g x)).trans (hg x)

/-- A relative homotopy between maps from one stage is already a relative
homotopy in some later stage, with the original homotopy retained exactly. -/
theorem homotopyRel_factor_nat_colimit
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    {A : Type v} [TopologicalSpace A] [CompactSpace A] (n : ℕ)
    (f g : C(A, F.obj n)) (S : Set A)
    (H : ((c.ι.app n).hom.comp f).HomotopyRel ((c.ι.app n).hom.comp g) S) :
    ∃ (m : ℕ) (h : n ≤ m)
      (G : ((F.map (homOfLE h)).hom.comp f).HomotopyRel
        ((F.map (homOfLE h)).hom.comp g) S),
      ∀ z, c.ι.app m (G z) = H z := by
  obtain ⟨m, h, G, hG⟩ := continuousMap_factor_nat_colimit_after F c hc hF
    H.toHomotopy.toContinuousMap n
  have hι := (isClosedEmbedding_nat_colimit F c hc hF m).injective
  have hw (x : F.obj n) : c.ι.app m (F.map (homOfLE h) x) = c.ι.app n x :=
    ConcreteCategory.congr_hom (c.w (homOfLE h)) x
  refine ⟨m, h, { toContinuousMap := G, map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }, hG⟩
  · intro x
    apply hι
    exact (hG (0, x)).trans ((H.apply_zero x).trans (hw (f x)).symm)
  · intro x
    apply hι
    exact (hG (1, x)).trans ((H.apply_one x).trans (hw (g x)).symm)
  · intro t x hx
    apply hι
    exact (hG (t, x)).trans ((H.eq_fst t hx).trans (hw (f x)).symm)

/-- Relative homotopy in the genuine sequential colimit is equivalent to
relative homotopy after a finite transition. This includes based cubical
homotopies by taking the relative set to be the cube boundary. -/
theorem homotopicRel_nat_colimit_iff
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    {A : Type v} [TopologicalSpace A] [CompactSpace A] (n : ℕ)
    (f g : C(A, F.obj n)) (S : Set A) :
    ((c.ι.app n).hom.comp f).HomotopicRel ((c.ι.app n).hom.comp g) S ↔
      ∃ (m : ℕ) (h : n ≤ m),
        ((F.map (homOfLE h)).hom.comp f).HomotopicRel
          ((F.map (homOfLE h)).hom.comp g) S := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨m, h, G, _⟩ := homotopyRel_factor_nat_colimit F c hc hF n f g S H
    exact ⟨m, h, ⟨G⟩⟩
  · rintro ⟨m, h, ⟨G⟩⟩
    refine ⟨(G.compContinuousMap (c.ι.app m).hom).cast ?_ ?_⟩
    · apply ContinuousMap.ext
      intro x
      exact ConcreteCategory.congr_hom (c.w (homOfLE h)) (f x)
    · apply ContinuousMap.ext
      intro x
      exact ConcreteCategory.congr_hom (c.w (homOfLE h)) (g x)

end KIP126.Topology
