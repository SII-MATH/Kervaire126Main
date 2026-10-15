module

public import KIP126.Def.Topology.Simplex.MonotoneCoupling.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Boundary.Proofs
public import Mathlib.Order.Hom.Set

@[expose] public section

namespace KIP126.Topology.Simplex

open Set

/-- A chain-supported barycentric distribution is represented by the
strictly positive coordinates of one ordered simplex. -/
theorem exists_ordered_simplex_representation {A : Type*} [Fintype A] [PartialOrder A]
    (w : stdSimplex ℝ A) (hw : IsChain (· ≤ ·) {a | 0 < w a}) :
    ∃ (n : ℕ) (f : Fin (n+1) →o A) (_ : Function.Injective f)
      (v : stdSimplex ℝ (Fin (n+1))),
      (∀ i, 0 < v i) ∧ stdSimplex.map f v = w := by
  classical
  let S : Set A := {a | 0 < w a}
  letI : Fintype S := Fintype.ofFinite S
  letI : LinearOrder S := hw.linearOrder
  have hnonempty : Nonempty S := by
    obtain ⟨a,ha⟩ := SimplicialRealization.simplex_exists_positive w
    exact ⟨⟨a,ha⟩⟩
  letI := hnonempty
  let n := Fintype.card S - 1
  have hn : Fintype.card S = n+1 := (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr hnonempty)).symm
  let e : Fin (n+1) ≃o S := Fintype.orderIsoFinOfCardEq S hn
  let f : Fin (n+1) →o A := (OrderHom.Subtype.val S).comp e.toOrderEmbedding.toOrderHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hz (a : A) (ha : a ∉ Set.range f) : w a = 0 := by
    apply le_antisymm _ (stdSimplex.zero_le w a)
    by_contra h
    have hp : 0 < w a := lt_of_not_ge h
    obtain ⟨i,hi⟩ := e.surjective ⟨a,hp⟩
    exact ha ⟨i,congrArg Subtype.val hi⟩
  obtain ⟨v,hv⟩ := (SimplicialRealization.simplex_map_range_iff f hf w).mpr hz
  refine ⟨n,f,hf,v,?_,hv⟩
  intro i
  have h := SimplicialRealization.simplex_map_apply_injective f hf v i
  rw [hv] at h
  rw [← h]
  exact (e i).2

/-- Injectively mapping a strictly positive barycentric point has support
exactly the image of its vertex map. -/
theorem positive_support_map_of_injective {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (v : stdSimplex ℝ A) (hv : ∀ i, 0 < v i) :
    {a | 0 < stdSimplex.map f v a} = Set.range f := by
  ext a
  constructor
  · intro ha
    by_contra hn
    have hz := SimplicialRealization.simplex_map_apply_not_range f v a hn
    change 0 < stdSimplex.map f v a at ha
    rw [hz] at ha
    exact (lt_irrefl _ ha)
  · rintro ⟨i,rfl⟩
    change 0 < stdSimplex.map f v (f i)
    rw [SimplicialRealization.simplex_map_apply_injective f hf]
    exact hv i

/-- The representation by an injective ordered vertex sequence and
strictly positive barycentric coordinates is unique. -/
theorem ordered_simplex_representation_unique {A : Type*} [Fintype A] [PartialOrder A]
    {n m : ℕ} (f : Fin (n+1) →o A) (g : Fin (m+1) →o A)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (v : stdSimplex ℝ (Fin (n+1))) (w : stdSimplex ℝ (Fin (m+1)))
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (h : stdSimplex.map f v = stdSimplex.map g w) :
    n = m ∧ HEq f g ∧ HEq v w := by
  classical
  have hr : Set.range f = Set.range g := by
    rw [← positive_support_map_of_injective f hf v hv,
      ← positive_support_map_of_injective g hg w hw,h]
  have hf' : StrictMono f := f.monotone.strictMono_of_injective hf
  have hg' : StrictMono g := g.monotone.strictMono_of_injective hg
  let e : Fin (n+1) ≃o Fin (m+1) := (hf'.orderIso f).trans
    ((OrderIso.setCongr _ _ hr).trans (hg'.orderIso g).symm)
  have hnm : n = m := by
    have hc := Fintype.card_congr e.toEquiv
    simpa only [Fintype.card_fin,Nat.add_right_cancel_iff] using hc
  subst m
  have hfg : f = g := DFunLike.coe_injective ((hf'.range_inj hg').mp hr)
  subst g
  have hvw := SimplicialRealization.simplex_map_injective f hf h
  exact ⟨rfl,HEq.rfl,heq_of_eq hvw⟩

end KIP126.Topology.Simplex
