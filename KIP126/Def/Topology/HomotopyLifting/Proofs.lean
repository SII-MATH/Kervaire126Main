module

public import KIP126.Def.Topology.HomotopyLifting.Predicates

@[expose] public section

namespace KIP126.Topology.HomotopyLifting

open scoped unitInterval
set_option backward.isDefEq.respectTransparency false
universe u v w
variable {E : Type u} {B : Type v} {Z : Type w}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Z]

/-- Restrict a prescribed source homotopy to the actual cylinder horn and
lift while retaining exactly that bottom and side. -/
theorem HasRelativeLifting.exists_lift {f : C(E,B)} {S : Set Z}
    (hf : HasRelativeLifting f Z S) (g : C(I × Z,E)) (H : C(I × Z,B))
    (h : ∀ t z, t = 0 ∨ z ∈ S → f (g (t,z)) = H (t,z)) :
    ∃ L : C(I × Z,E), (∀ z, f (L z) = H z) ∧
      (∀ t z, t = 0 ∨ z ∈ S → L (t,z) = g (t,z)) := by
  let g' : C(CylinderHorn Z S,E) := ⟨fun z => g z.val,
    g.continuous.comp continuous_subtype_val⟩
  obtain ⟨L,hL,hLg⟩ := hf g' H (fun z => h z.val.1 z.val.2 z.property)
  exact ⟨L,hL,fun t z hz => hLg ⟨(t,z),hz⟩⟩

/-- Relative lifting is invariant under an actual homeomorphism of pairs. -/
theorem HasRelativeLifting.of_homeomorph {W : Type*} [TopologicalSpace W]
    {f : C(E,B)} {S : Set Z} {T : Set W}
    (hf : HasRelativeLifting f W T) (h : Z ≃ₜ W)
    (hST : ∀ z, z ∈ S ↔ h z ∈ T) : HasRelativeLifting f Z S := by
  intro g H hcomm
  let g' : C(CylinderHorn W T,E) := {
    toFun := fun z => g ⟨(z.val.1,h.symm z.val.2),z.property.elim
      Or.inl (fun hz => Or.inr ((hST _).mpr (by simpa using hz)))⟩
    continuous_toFun := g.continuous.comp
      (((continuous_fst.comp continuous_subtype_val).prodMk
        (h.symm.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _) }
  let H' : C(I × W,B) := ⟨fun z => H (z.1,h.symm z.2),by fun_prop⟩
  obtain ⟨L,hL,hLg⟩ := hf g' H' (fun z => hcomm _)
  let L' : C(I × Z,E) := ⟨fun z => L (z.1,h z.2),by fun_prop⟩
  refine ⟨L',?_,?_⟩
  · intro z
    change f (L (z.1,h z.2)) = H z
    simpa only [H',ContinuousMap.coe_mk,Homeomorph.symm_apply_apply] using hL (z.1,h z.2)
  · intro z
    rcases z with ⟨⟨t,z⟩,hz0⟩
    have hz : t = 0 ∨ h z ∈ T :=
      hz0.elim Or.inl (fun hz => Or.inr ((hST _).mp hz))
    change L (t,h z) = g ⟨(t,z),hz0⟩
    simpa only [g',ContinuousMap.coe_mk,Homeomorph.symm_apply_apply] using
      hLg ⟨(t,h z),hz⟩

theorem cubeCylinderHomeomorph_boundary (n : ℕ) (z : I × (Fin n → I)) :
    z ∈ cylinderBoundary (_root_.Cube.boundary (Fin n)) ↔
      cubeCylinderHomeomorph n z ∈ _root_.Cube.boundary (Fin (n + 1)) := by
  constructor
  · rintro (h | h | ⟨i,hi⟩)
    · exact ⟨0,Or.inl h⟩
    · exact ⟨0,Or.inr h⟩
    · exact ⟨i.succ,hi⟩
  · rintro ⟨i,hi⟩
    induction i using Fin.cases with
    | zero => exact hi.elim Or.inl (fun h => Or.inr (Or.inl h))
    | succ i => exact Or.inr (Or.inr ⟨i,hi⟩)

/-- Cubical lifting includes the extra parameter and its two endpoint faces. -/
theorem HasCubicalLifting.cylinder {f : C(E,B)} (hf : HasCubicalLifting f) (n : ℕ) :
    HasRelativeLifting f (I × (Fin n → I))
      (cylinderBoundary (_root_.Cube.boundary (Fin n))) :=
  (hf (n + 1)).of_homeomorph (cubeCylinderHomeomorph n) (cubeCylinderHomeomorph_boundary n)

end KIP126.Topology.HomotopyLifting
