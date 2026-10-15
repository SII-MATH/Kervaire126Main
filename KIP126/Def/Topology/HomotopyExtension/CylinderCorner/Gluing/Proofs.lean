module

public import KIP126.Def.Topology.HomotopyExtension.CylinderCorner.Proofs
public import KIP126.Def.Topology.ClosedCover.Proofs

@[expose] public section

namespace KIP126.Topology.HomotopyExtension
open CategoryTheory Set _root_.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Compatible maps on the three actual faces of a closed cylinder corner
glue continuously with exact values on every face. -/
theorem exists_cylinderCorner_desc {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : IsClosedEmbedding i) {Y : TopCat.{u}} (a : C(A × I,Y)) (f₀ f₁ : C(B,Y))
    (ha₀ : ∀ x, a (x,0) = f₀ (i x)) (ha₁ : ∀ x, a (x,1) = f₁ (i x)) :
    ∃ d : C(cylinderCorner i,Y),
      (∀ x t, d ⟨(i x,t),Or.inl ⟨x,rfl⟩⟩ = a (x,t)) ∧
      (∀ b, d ⟨(b,0),Or.inr (Or.inl rfl)⟩ = f₀ b) ∧
      (∀ b, d ⟨(b,1),Or.inr (Or.inr rfl)⟩ = f₁ b) := by
  let K := cylinderCorner i
  let e := hi.isEmbedding.toHomeomorph
  let C : Fin 3 → Set K := ![{z | z.val.1 ∈ range i},{z | z.val.2 = 0},{z | z.val.2 = 1}]
  let M : ∀ j, C(C j,Y)
    | 0 => ⟨fun z => a (e.symm ⟨z.val.val.1,z.property⟩,z.val.val.2),
        a.continuous.comp ((e.symm.continuous.comp
          (continuous_subtype_val.subtype_val.fst.subtype_mk _)).prodMk
            continuous_subtype_val.subtype_val.snd)⟩
    | 1 => ⟨fun z => f₀ z.val.val.1,f₀.continuous.comp continuous_subtype_val.subtype_val.fst⟩
    | 2 => ⟨fun z => f₁ z.val.val.1,f₁.continuous.comp continuous_subtype_val.subtype_val.fst⟩
  have hC : ∀ j, IsClosed (C j) := by
    intro j
    fin_cases j
    · exact hi.isClosed_range.preimage continuous_subtype_val.fst
    · exact isClosed_eq continuous_subtype_val.snd continuous_const
    · exact isClosed_eq continuous_subtype_val.snd continuous_const
  have hcover : ⋃ j, C j = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro z
    rcases z.property with h | h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  have h01 (z : K) (h : z ∈ C 0) (h' : z ∈ C 1) : M 0 ⟨z,h⟩ = M 1 ⟨z,h'⟩ := by
    change a (e.symm ⟨z.val.1,h⟩,z.val.2) = f₀ z.val.1
    rw [show z.val.2 = 0 from h',ha₀]
    exact congrArg f₀ (congrArg Subtype.val (e.apply_symm_apply _))
  have h02 (z : K) (h : z ∈ C 0) (h' : z ∈ C 2) : M 0 ⟨z,h⟩ = M 2 ⟨z,h'⟩ := by
    change a (e.symm ⟨z.val.1,h⟩,z.val.2) = f₁ z.val.1
    rw [show z.val.2 = 1 from h',ha₁]
    exact congrArg f₁ (congrArg Subtype.val (e.apply_symm_apply _))
  have h12 (z : K) (h : z ∈ C 1) (h' : z ∈ C 2) : False := by
    have h0 : z.val.2 = 0 := h
    have h1 : z.val.2 = 1 := h'
    exact zero_ne_one (h0.symm.trans h1)
  obtain ⟨d,hd⟩ := ClosedCover.exists_gluing C hC hcover M (by
    intro j k z hj hk
    fin_cases j <;> fin_cases k
    · rfl
    · exact h01 z hj hk
    · exact h02 z hj hk
    · exact (h01 z hk hj).symm
    · rfl
    · exact (h12 z hj hk).elim
    · exact (h02 z hk hj).symm
    · exact (h12 z hk hj).elim
    · rfl)
  refine ⟨d,?_,?_,?_⟩
  · intro x t
    have h := hd 0 ⟨⟨(i x,t),Or.inl ⟨x,rfl⟩⟩,⟨x,rfl⟩⟩
    refine h.trans ?_
    change a (e.symm ⟨i x,_⟩,t) = a (x,t)
    have hx : e.symm ⟨i x,(show i x ∈ range i from ⟨x,rfl⟩)⟩ = x := by
      apply e.injective
      exact e.apply_symm_apply _
    rw [hx]
  · intro b
    exact hd 1 ⟨⟨(b,0),Or.inr (Or.inl rfl)⟩,rfl⟩
  · intro b
    exact hd 2 ⟨⟨(b,1),Or.inr (Or.inr rfl)⟩,rfl⟩

end KIP126.Topology.HomotopyExtension
