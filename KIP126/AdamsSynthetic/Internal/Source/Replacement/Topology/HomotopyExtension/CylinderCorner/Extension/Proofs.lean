module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.CylinderCorner.Proofs

@[expose] section

namespace KIP126.Topology.HomotopyExtension
open CategoryTheory Set _root_.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- A homotopy on the original image cylinder extends while preserving both
ambient endpoint maps exactly. The extension uses the actual closed
cylinder corner and a continuous map glued over its closed cover. -/
theorem HasHomotopyExtension.exists_endpoint_extension {A B : TopCat.{u}}
    {i : A ⟶ B} (hH : HasHomotopyExtension i) (hi : IsClosedEmbedding i)
    (Y : TopCat.{u}) (q : C(B × I,Y)) (a : C((A × I) × I,Y))
    (ha : ∀ x t, a ((x,t),0) = q (i x,t))
    (ha0 : ∀ x s, a ((x,0),s) = q (i x,0))
    (ha1 : ∀ x s, a ((x,1),s) = q (i x,1)) :
    ∃ E : C((B × I) × I,Y),
      (∀ x t, E ((x,t),0) = q (x,t)) ∧
      (∀ x t s, E ((i x,t),s) = a ((x,t),s)) ∧
      (∀ x s, E ((x,0),s) = q (x,0)) ∧
      (∀ x s, E ((x,1),s) = q (x,1)) := by
  classical
  have hK := hH.cylinderCorner hi
  let K := {z : B × I // z.1 ∈ range i ∨ z.2 = 0 ∨ z.2 = 1}
  let e := hi.isEmbedding.toHomeomorph
  let U : Set (K × I) := {z | z.1.val.2 = 0 ∨ z.1.val.2 = 1}
  let V : Set (K × I) := {z | z.1.val.1 ∈ range i}
  have hU : IsClosed U := (isClosed_eq continuous_fst.subtype_val.snd continuous_const).union
    (isClosed_eq continuous_fst.subtype_val.snd continuous_const)
  have hV : IsClosed V := hi.isClosed_range.preimage continuous_fst.subtype_val.fst
  have hUV : U ∪ V = univ := Set.eq_univ_of_forall (fun z => z.1.property.symm)
  let av : C(V,Y) := ⟨fun z => a ((e.symm ⟨z.val.1.val.1,z.property⟩,z.val.1.val.2),z.val.2),
    a.continuous.comp (((e.symm.continuous.comp
      (continuous_subtype_val.fst.subtype_val.fst.subtype_mk _)).prodMk
      continuous_subtype_val.fst.subtype_val.snd).prodMk continuous_subtype_val.snd)⟩
  let Q : C(K × I,Y) := q.comp ⟨fun z => z.1.val,continuous_fst.subtype_val⟩
  let P : K × I → Y := fun z => if h : z ∈ V then av ⟨z,h⟩ else Q z
  have pv : ContinuousOn P V := continuousOn_iff_continuous_restrict.mpr
    (av.continuous.congr (by intro z; dsimp [P]; rw [dif_pos z.property]))
  have htransport (z : K × I) (h : z ∈ V) : i (e.symm ⟨z.1.val.1,h⟩) = z.1.val.1 :=
    congrArg Subtype.val (e.apply_symm_apply ⟨z.1.val.1,h⟩)
  have pu : ContinuousOn P U := Q.continuous.continuousOn.congr (by
    intro z hz
    dsimp only [P]
    split_ifs with h
    · change a ((e.symm ⟨z.1.val.1,h⟩,z.1.val.2),z.2) = q z.1.val
      rcases hz with hz | hz
      · rw [hz,ha0,htransport]
        exact congrArg q (Prod.ext rfl hz.symm)
      · rw [hz,ha1,htransport]
        exact congrArg q (Prod.ext rfl hz.symm)
    · rfl)
  let p : C(K × I,Y) := ⟨P,continuousOn_univ.mp (hUV ▸ pu.union_of_isClosed pv hU hV)⟩
  have hp (z : K) : p (z,0) = q z.val := by
    change P (z,0) = q z.val
    dsimp only [P]
    split_ifs with h
    · change a ((e.symm ⟨z.val.1,h⟩,z.val.2),0) = q z.val
      rw [ha,htransport (z,0) h]
    · rfl
  obtain ⟨E,hE,hEp⟩ := hK Y q p hp
  refine ⟨E,fun x t => hE (x,t),?_,?_,?_⟩
  · intro x t s
    let z : K := ⟨(i x,t),Or.inl ⟨x,rfl⟩⟩
    have hx : e.symm ⟨i x,(show i x ∈ range i from ⟨x,rfl⟩)⟩ = x := by
      apply e.injective
      exact e.apply_symm_apply _
    calc
      E ((i x,t),s) = p (z,s) := hEp z s
      _ = a ((x,t),s) := by
        change P (z,s) = _
        dsimp only [P]
        rw [dif_pos (show (z,s) ∈ V from ⟨x,rfl⟩)]
        change a ((e.symm ⟨i x,_⟩,t),s) = _
        rw [hx]
  · intro x s
    let z : K := ⟨(x,0),Or.inr (Or.inl rfl)⟩
    calc
      E ((x,0),s) = p (z,s) := hEp z s
      _ = q (x,0) := by
        change P (z,s) = _
        dsimp only [P]
        split_ifs with h
        · change a ((e.symm ⟨x,h⟩,0),s) = q (x,0)
          rw [ha0,htransport (z,s) h]
        · rfl
  · intro x s
    let z : K := ⟨(x,1),Or.inr (Or.inr rfl)⟩
    calc
      E ((x,1),s) = p (z,s) := hEp z s
      _ = q (x,1) := by
        change P (z,s) = _
        dsimp only [P]
        split_ifs with h
        · change a ((e.symm ⟨x,h⟩,1),s) = q (x,1)
          rw [ha1,htransport (z,s) h]
        · rfl

end KIP126.Topology.HomotopyExtension
