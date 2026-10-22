module

import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Data.Fintype.Option

@[expose] section

namespace KIP126.Topology.ClosedCover

variable {X E B ι : Type*} [TopologicalSpace X] [TopologicalSpace E]

/-- Compatible continuous maps on a finite closed cover glue continuously. -/
theorem exists_gluing [Finite ι] (C : ι → Set X)
    (hC : ∀ i, IsClosed (C i)) (hcover : ⋃ i, C i = Set.univ)
    (L : ∀ i, C(C i, E))
    (hagree : ∀ i j x (hi : x ∈ C i) (hj : x ∈ C j),
      L i ⟨x, hi⟩ = L j ⟨x, hj⟩) :
    ∃ G : C(X, E), ∀ i (x : C i), G x.val = L i x := by
  let G := Set.liftCover C (fun i => L i) hagree hcover
  have hG : Continuous G := by
    apply (locallyFinite_of_finite C).continuous hcover hC
    intro i
    rw [continuousOn_iff_continuous_restrict]
    convert (L i).continuous using 1
    funext x
    exact Set.liftCover_coe (f := fun i => L i) (hf := hagree) (hS := hcover) x
  exact ⟨⟨G, hG⟩, fun i x =>
    Set.liftCover_coe (f := fun i => L i) (hf := hagree) (hS := hcover) x⟩

/-- Add finitely many closed cells whose mutual intersections lie in the old
closed domain, preserving both its map and every prescribed cell map. -/
theorem exists_extension [Finite ι] (S : Set X) (C : ι → Set X)
    (hS : IsClosed S) (hC : ∀ i, IsClosed (C i))
    (hinter : ∀ i j, i ≠ j → C i ∩ C j ⊆ S)
    (g : C(S, E)) (L : ∀ i, C(C i, E))
    (hagree : ∀ i (x : C i) (hx : x.val ∈ S), L i x = g ⟨x.val, hx⟩) :
    ∃ G : C(↥(S ∪ ⋃ i, C i), E),
      (∀ x : S, G ⟨x.val, Or.inl x.property⟩ = g x) ∧
      (∀ i (x : C i),
        G ⟨x.val, Or.inr (Set.mem_iUnion.mpr ⟨i, x.property⟩)⟩ = L i x) := by
  classical
  let U := S ∪ ⋃ i, C i
  let A : Option ι → Set X := fun i => i.elim S C
  let F : ∀ i, C(A i, E) := fun i => by
    cases i with
    | none => exact g
    | some i => exact L i
  have hA : ∀ i, IsClosed (A i) := by
    intro i
    cases i with
    | none => exact hS
    | some i => exact hC i
  have hF : ∀ i j x (hi : x ∈ A i) (hj : x ∈ A j),
      F i ⟨x, hi⟩ = F j ⟨x, hj⟩ := by
    intro i j x hi hj
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact (hagree j ⟨x, hj⟩ hi).symm
    | some i =>
      cases j with
      | none => exact hagree i ⟨x, hi⟩ hj
      | some j =>
        by_cases hij : i = j
        · subst j
          rfl
        · have hx := hinter i j hij ⟨hi, hj⟩
          exact (hagree i ⟨x, hi⟩ hx).trans (hagree j ⟨x, hj⟩ hx).symm
  let D : Option ι → Set U := fun i => Subtype.val ⁻¹' A i
  let M : ∀ i, C(D i, E) := fun i =>
    (F i).comp ⟨fun x => ⟨x.val.val, x.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  have hD : ∀ i, IsClosed (D i) := fun i => (hA i).preimage continuous_subtype_val
  have hcover : ⋃ i, D i = Set.univ := by
    apply Set.iUnion_eq_univ_iff.mpr
    intro x
    rcases x.property with hx | hx
    · exact ⟨none, hx⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact ⟨some i, hi⟩
  obtain ⟨G, hG⟩ := exists_gluing D hD hcover M
    (fun i j x hi hj => hF i j x.val hi hj)
  refine ⟨G, ?_, ?_⟩
  · intro x
    exact hG none ⟨⟨x.val, Or.inl x.property⟩, x.property⟩
  · intro i x
    exact hG (some i)
      ⟨⟨x.val, Or.inr (Set.mem_iUnion.mpr ⟨i, x.property⟩)⟩, x.property⟩

/-- Closed-cell gluing preserves an equation with a fixed projection. -/
theorem exists_extension_over [Finite ι] [TopologicalSpace B]
    (S : Set X) (C : ι → Set X) (hS : IsClosed S) (hC : ∀ i, IsClosed (C i))
    (hinter : ∀ i j, i ≠ j → C i ∩ C j ⊆ S)
    (f : C(E, B)) (H : C(X, B)) (g : C(S, E)) (L : ∀ i, C(C i, E))
    (hg : ∀ x, f (g x) = H x.val) (hL : ∀ i x, f (L i x) = H x.val)
    (hagree : ∀ i (x : C i) (hx : x.val ∈ S), L i x = g ⟨x.val, hx⟩) :
    ∃ G : C(↥(S ∪ ⋃ i, C i), E),
      (∀ x, f (G x) = H x.val) ∧
      (∀ x : S, G ⟨x.val, Or.inl x.property⟩ = g x) ∧
      (∀ i (x : C i),
        G ⟨x.val, Or.inr (Set.mem_iUnion.mpr ⟨i, x.property⟩)⟩ = L i x) := by
  obtain ⟨G, hGg, hGL⟩ := exists_extension S C hS hC hinter g L hagree
  refine ⟨G, ?_, hGg, hGL⟩
  intro x
  rcases x.property with hx | hx
  · rw [hGg ⟨x.val, hx⟩]
    exact hg ⟨x.val, hx⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rw [hGL i ⟨x.val, hi⟩]
    exact hL i ⟨x.val, hi⟩

end KIP126.Topology.ClosedCover
