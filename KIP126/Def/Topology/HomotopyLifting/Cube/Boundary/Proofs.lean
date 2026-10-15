module

public import KIP126.Def.Topology.HomotopyLifting.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Predicates
public import KIP126.Def.Topology.HomotopyGroup.ContinuousMap.Data
public import Mathlib.Topology.Piecewise

@[expose] public section

namespace KIP126.Topology.HomotopyLifting

open Set
open scoped unitInterval Topology.Homotopy

universe u v

set_option backward.isDefEq.respectTransparency false

/-- Two based cubical loops prescribe a genuine continuous map on the
entire boundary of their homotopy cylinder, constant on every side. -/
theorem exists_cylinderBoundary_genLoop_map {E : Type u} [TopologicalSpace E]
    (n : ℕ) (e : E) (p q : GenLoop (Fin n) E e) :
    ∃ g : C({z : I × (Fin n → I) // z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n))},E),
      (∀ x, g ⟨(0,x),Or.inl rfl⟩ = p x) ∧
      (∀ x, g ⟨(1,x),Or.inr (Or.inl rfl)⟩ = q x) ∧
      ∀ (t : I) (x : Fin n → I) (hx : x ∈ _root_.Cube.boundary (Fin n)),
        g ⟨(t,x),Or.inr (Or.inr hx)⟩ = e := by
  classical
  let g : I × (Fin n → I) → E := fun z => if z.1 = 0 then p z.2 else
    if z.1 = 1 then q z.2 else e
  let S₀ : Set (I × (Fin n → I)) := {z | z.1 = 0}
  let S₁ : Set (I × (Fin n → I)) := {z | z.1 = 1}
  let S₂ : Set (I × (Fin n → I)) := {z | z.2 ∈ _root_.Cube.boundary (Fin n)}
  have hS₀ : IsClosed S₀ := isClosed_eq continuous_fst continuous_const
  have hS₁ : IsClosed S₁ := isClosed_eq continuous_fst continuous_const
  have hS₂ : IsClosed S₂ := by
    have hb : IsClosed (_root_.Cube.boundary (Fin n)) := by
      simpa only [_root_.Cube.boundary,Set.setOf_exists,Set.setOf_or] using
        isClosed_iUnion_of_finite (fun i : Fin n =>
          (isClosed_eq (continuous_apply i) continuous_const).union
            (isClosed_eq (continuous_apply i) continuous_const))
    exact hb.preimage continuous_snd
  have hg₀ : ContinuousOn g S₀ :=
    (p.val.continuous.comp continuous_snd).continuousOn.congr (by
      intro z hz
      simp [g,show z.1 = 0 from hz])
  have hg₁ : ContinuousOn g S₁ :=
    (q.val.continuous.comp continuous_snd).continuousOn.congr (by
      intro z hz
      have hz' : z.1 = 1 := hz
      simp [g,hz'])
  have hside (z : I × (Fin n → I)) (hz : z.2 ∈ _root_.Cube.boundary (Fin n)) : g z = e := by
    dsimp only [g]
    split_ifs
    · exact p.property _ hz
    · exact q.property _ hz
    · rfl
  have hg₂ : ContinuousOn g S₂ := continuousOn_const.congr hside
  have hg : ContinuousOn g (cylinderBoundary (_root_.Cube.boundary (Fin n))) :=
    hg₀.union_of_isClosed (hg₁.union_of_isClosed hg₂ hS₁ hS₂) hS₀ (hS₁.union hS₂)
  refine ⟨⟨fun z => g z.val,hg.restrict⟩,?_,?_,?_⟩
  · intro x
    simp [g]
  · intro x
    simp [g]
  · intro t x hx
    exact hside (t,x) hx

/-- The actual boundary lifting property lifts every based cubical loop
exactly, with its entire boundary fixed at the chosen source point. -/
theorem HasCubeBoundaryLifting.exists_genLoop_lift
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {f : C(E,B)} (hf : HasCubeBoundaryLifting f) (e : E) (n : ℕ)
    (p : GenLoop (Fin n) B (f e)) :
    ∃ q : GenLoop (Fin n) E e, ∀ x, f (q x) = p x := by
  obtain ⟨L,hL,hb⟩ := hf n (ContinuousMap.const _ e) p.val
    (fun z => (p.property z.val z.property).symm)
  exact ⟨⟨L,fun x hx => hb ⟨x,hx⟩⟩,hL⟩

/-- Cube-boundary lifting applies to a full homotopy cylinder boundary
through its actual product-to-cube homeomorphism. -/
theorem HasCubeBoundaryLifting.lift_cylinderBoundary
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {f : C(E,B)} (hf : HasCubeBoundaryLifting f) (n : ℕ)
    (g : C({z : I × (Fin n → I) // z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n))},E))
    (H : C(I × (Fin n → I),B)) (hcomm : ∀ z, f (g z) = H z.val) :
    ∃ L : C(I × (Fin n → I),E), (∀ z, f (L z) = H z) ∧ (∀ z, L z.val = g z) := by
  let e := cubeCylinderHomeomorph n
  have he (z : ↥(_root_.Cube.boundary (Fin (n+1)))) :
      e.symm z.val ∈ cylinderBoundary (_root_.Cube.boundary (Fin n)) := by
    apply (cubeCylinderHomeomorph_boundary n _).mpr
    simpa only [e,Homeomorph.apply_symm_apply] using z.property
  let b : C(↥(_root_.Cube.boundary (Fin (n+1))),E) :=
    ⟨fun z => g ⟨e.symm z.val,he z⟩,
      g.continuous.comp ((e.symm.continuous.comp continuous_subtype_val).subtype_mk he)⟩
  obtain ⟨L,hL,hb⟩ := hf (n+1) b (H.comp ⟨e.symm,e.symm.continuous⟩)
    (fun z => hcomm ⟨e.symm z.val,he z⟩)
  refine ⟨L.comp ⟨e,e.continuous⟩,?_,?_⟩
  · intro z
    exact (hL (e z)).trans (congrArg H (e.symm_apply_apply z))
  · intro z
    have hz : e z.val ∈ _root_.Cube.boundary (Fin (n+1)) :=
      (cubeCylinderHomeomorph_boundary n z.val).mp z.property
    exact (hb ⟨e z.val,hz⟩).trans (congrArg g (Subtype.ext (e.symm_apply_apply z.val)))

/-- Every specified homotopy between images of two based cubical loops
lifts to a based homotopy between the original loops, retaining all
parameter values under the comparison map. -/
theorem HasCubeBoundaryLifting.lift_genLoop_homotopy
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {f : C(E,B)} (hf : HasCubeBoundaryLifting f) (e : E) (n : ℕ)
    (p q : GenLoop (Fin n) E e)
    (H : (f.comp p.val).HomotopyRel (f.comp q.val) (_root_.Cube.boundary (Fin n))) :
    ∃ G : p.val.HomotopyRel q.val (_root_.Cube.boundary (Fin n)),
      ∀ z, f (G z) = H z := by
  obtain ⟨g,hg₀,hg₁,hgs⟩ := exists_cylinderBoundary_genLoop_map n e p q
  have hg : ∀ z, f (g z) = H z.val := by
    rintro ⟨⟨t,x⟩,ht | ht | hx⟩
    · change t = 0 at ht
      subst t
      rw [hg₀]
      exact (H.apply_zero x).symm
    · change t = 1 at ht
      subst t
      rw [hg₁]
      exact (H.apply_one x).symm
    · rw [hgs t x hx]
      exact ((H.eq_fst t hx).trans (congrArg f (p.property x hx))).symm
  obtain ⟨L,hL,hb⟩ := hf.lift_cylinderBoundary n g H.toContinuousMap hg
  refine ⟨{
    toContinuousMap := L
    map_zero_left := fun x => (hb ⟨(0,x),Or.inl rfl⟩).trans (hg₀ x)
    map_one_left := fun x => (hb ⟨(1,x),Or.inr (Or.inl rfl)⟩).trans (hg₁ x)
    prop' := ?_ },hL⟩
  intro t x hx
  exact (hb ⟨(t,x),Or.inr (Or.inr hx)⟩).trans ((hgs t x hx).trans (p.property x hx).symm)

/-- Full cube-boundary lifting induces a bijection on each actual based
cubical homotopy quotient, including degree zero. -/
theorem HasCubeBoundaryLifting.continuousHomotopyMap_bijective
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {f : C(E,B)} (hf : HasCubeBoundaryLifting f) (e : E) (b : B)
    (he : f e = b) (n : ℕ) :
    Function.Bijective (continuousHomotopyMap f e b he n) := by
  subst b
  constructor
  · intro p q
    induction p using Quotient.inductionOn with
    | h p =>
      induction q using Quotient.inductionOn with
      | h q =>
        intro hpq
        obtain ⟨H⟩ := Quotient.exact hpq
        obtain ⟨G,_⟩ := hf.lift_genLoop_homotopy e n p q H
        exact Quotient.sound ⟨G⟩
  · intro p
    induction p using Quotient.inductionOn with
    | h p =>
      obtain ⟨q,hq⟩ := hf.exists_genLoop_lift e n p
      refine ⟨⟦q⟧,?_⟩
      exact congrArg Quotient.mk' (GenLoop.ext _ _ hq)

end KIP126.Topology.HomotopyLifting
