module

public import KIP126.Def.Topology.HomotopyFiber.Contraction.Data
public import KIP126.Def.Topology.HomotopyLifting.Proofs
public import KIP126.Def.Topology.Cube.Square.Proofs

@[expose] public section

namespace KIP126.Topology

open scoped unitInterval
open HomotopyLifting
universe u v w
variable {E : Type u} {B : Type v} {Z : Type w}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Z]

@[simp] theorem contractionFiberLoop_point (f : C(E,B)) (e : E)
    (c : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (hc : ∀ t, c (t,e) = e) :
    contractionFiberLoop f e c ⟨e,rfl⟩ = Path.refl (f e) := by
  apply Path.ext
  funext t
  change f (c (t,e)) = f e
  rw [hc]

/-- Relative homotopy lifting produces an actual fiber family whose
projected contraction paths represent any prescribed family of based loops. -/
theorem contractionFiberLoop_homotopy_surjective
    (f : C(E,B)) (e : E)
    (c : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (hc : ∀ t, c (t,e) = e) (S : Set Z)
    (hf : HasRelativeLifting f Z S)
    (β : C(Z,Path (f e) (f e))) (hβ : ∀ z ∈ S, β z = Path.refl (f e)) :
    ∃ α : C(Z,{x : E // f x = f e}),
      (∀ z ∈ S, α z = ⟨e,rfl⟩) ∧
      β.HomotopicRel ((contractionFiberLoop f e c).comp α) S := by
  let H : C(I × Z,B) := ⟨fun z => β z.2 z.1, by fun_prop⟩
  obtain ⟨L,hL,hL0⟩ := hf.exists_lift (ContinuousMap.const (I × Z) e) H (by
    intro t z hz
    rcases hz with rfl | hz
    · exact (β z).source.symm
    · change f e = β z t
      rw [hβ z hz]
      rfl)
  have hLstart (z : Z) : L (0,z) = e := hL0 0 z (Or.inl rfl)
  have hLside (t : I) (z : Z) (hz : z ∈ S) : L (t,z) = e := hL0 t z (Or.inr hz)
  let α : C(Z,{x : E // f x = f e}) := {
    toFun := fun z => ⟨L (1,z),(hL (1,z)).trans (β z).target⟩
    continuous_toFun := (L.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _ }
  have hα (z : Z) (hz : z ∈ S) : α z = ⟨e,rfl⟩ :=
    Subtype.ext (hLside 1 z hz)
  refine ⟨α,hα,?_⟩
  let F : C((I × I) × Z,B) := ⟨fun z => f (c (z.1.2,L (z.1.1,z.2))),by fun_prop⟩
  apply Cube.square_edges_homotopicRel F β ((contractionFiberLoop f e c).comp α) S
  · intro t z
    change f (c (t,L (0,z))) = f e
    rw [hLstart,hc]
  · intro t z
    change f (c (0,L (t,z))) = f e
    rw [c.apply_zero]
    rfl
  · intro t z
    change f (c (1,L (t,z))) = β z t
    rw [c.apply_one]
    exact hL (t,z)
  · intro t z
    rfl
  · intro s t z hz
    change f (c (t,L (s,z))) = f e
    rw [hLside s z hz,hc]

/-- Relative lifting in one more parameter reflects based homotopies under
the actual contraction comparison from the fiber to the loop space. -/
theorem contractionFiberLoop_homotopy_injective
    (f : C(E,B)) (e : E)
    (c : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (hc : ∀ t, c (t,e) = e) (S : Set Z)
    (hf : HasRelativeLifting f (I × Z) (cylinderBoundary S))
    (α β : C(Z,{x : E // f x = f e}))
    (hα : ∀ z ∈ S, α z = ⟨e,rfl⟩) (hβ : ∀ z ∈ S, β z = ⟨e,rfl⟩)
    (h : ((contractionFiberLoop f e c).comp α).HomotopicRel
      ((contractionFiberLoop f e c).comp β) S) : α.HomotopicRel β S := by
  let a : C(Z,E) := ⟨fun z => (α z).val,continuous_subtype_val.comp α.continuous⟩
  let b : C(Z,E) := ⟨fun z => (β z).val,continuous_subtype_val.comp β.continuous⟩
  have ha (z : Z) (hz : z ∈ S) : a z = e := congrArg Subtype.val (hα z hz)
  have hb (z : Z) (hz : z ∈ S) : b z = e := congrArg Subtype.val (hβ z hz)
  let ca : ContinuousMap.HomotopyRel (ContinuousMap.const Z e) a S := {
    toFun := fun z => c (z.1,a z.2)
    continuous_toFun := by fun_prop
    map_zero_left := fun z => c.apply_zero (a z)
    map_one_left := fun z => c.apply_one (a z)
    prop' := fun t z hz => by change c (t,a z) = e; rw [ha z hz,hc] }
  let cb : ContinuousMap.HomotopyRel (ContinuousMap.const Z e) b S := {
    toFun := fun z => c (z.1,b z.2)
    continuous_toFun := by fun_prop
    map_zero_left := fun z => c.apply_zero (b z)
    map_one_left := fun z => c.apply_one (b z)
    prop' := fun t z hz => by change c (t,b z) = e; rw [hb z hz,hc] }
  let g := ca.symm.trans cb
  obtain ⟨K⟩ := h
  let G : C(I × (I × Z),E) := ⟨fun z => c (z.1,g z.2),by fun_prop⟩
  let H : C(I × (I × Z),B) := ⟨fun z => K z.2 z.1,by fun_prop⟩
  obtain ⟨L,hL,hLG⟩ := hf.exists_lift G H (by
    intro t z hz
    rcases hz with rfl | hz
    · change f (c (0,g z)) = K z 0
      rw [c.apply_zero,Path.source]
      rfl
    · rcases hz with hz | hz | hz
      · obtain ⟨s,z⟩ := z
        change s = 0 at hz
        subst s
        change f (c (t,g (0,z))) = K (0,z) t
        rw [g.apply_zero,K.apply_zero]
        rfl
      · obtain ⟨s,z⟩ := z
        change s = 1 at hz
        subst s
        change f (c (t,g (1,z))) = K (1,z) t
        rw [g.apply_one,K.apply_one]
        rfl
      · change f (c (t,g z)) = K z t
        rw [g.eq_fst z.1 hz,ha z.2 hz,hc,K.eq_fst z.1 hz]
        change f e = contractionFiberLoop f e c (α z.2) t
        rw [hα z.2 hz,contractionFiberLoop_point f e c hc]
        rfl)
  refine ⟨{
    toFun := fun z => ⟨L (1,z),(hL (1,z)).trans (K z).target⟩
    continuous_toFun := (L.continuous.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro z
    apply Subtype.ext
    change L (1,(0,z)) = a z
    rw [hLG 1 (0,z) (Or.inr (Or.inl rfl))]
    change c (1,g (0,z)) = a z
    rw [c.apply_one,g.apply_zero]
    rfl
  · intro z
    apply Subtype.ext
    change L (1,(1,z)) = b z
    rw [hLG 1 (1,z) (Or.inr (Or.inr (Or.inl rfl)))]
    change c (1,g (1,z)) = b z
    rw [c.apply_one,g.apply_one]
    rfl
  · intro s z hz
    apply Subtype.ext
    change L (1,(s,z)) = a z
    rw [hLG 1 (s,z) (Or.inr (Or.inr (Or.inr hz)))]
    change c (1,g (s,z)) = a z
    rw [c.apply_one]
    exact g.eq_fst s hz

end KIP126.Topology
