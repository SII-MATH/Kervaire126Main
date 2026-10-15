module

public import KIP126.Def.Topology.FiberBundle.Pullback.Data

@[expose] public section

namespace KIP126.Topology

variable {E E' A B P F : Type*}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace P] [TopologicalSpace F]
set_option backward.isDefEq.respectTransparency false

@[simp] theorem iteratedPullbackHomeomorph_snd (p : C(E,P)) (a : C(A,P)) (b : C(B,A))
    (z : {z : {z : E × A // p z.1 = a z.2} × B // pullbackSndMap p a z.1 = b z.2}) :
    (iteratedPullbackHomeomorph p a b z).val.2 = z.val.2 := rfl

/-- Local charts transfer across an actual homeomorphism of total spaces
commuting strictly with their projections. -/
theorem localTriviality_of_total_homeomorph (p : C(E,B)) (q : C(E',B))
    (e : E' ≃ₜ E) (he : ∀ x, p (e x) = q x)
    (hp : ∀ b, ∃ T : Bundle.Trivialization F p, b ∈ T.baseSet) :
    ∀ b, ∃ T : Bundle.Trivialization F q, b ∈ T.baseSet := by
  intro b
  obtain ⟨T,hT⟩ := hp b
  have h : (p : E → B) ∘ e = q := funext he
  change ∃ T : Bundle.Trivialization F (q : E' → B), b ∈ T.baseSet
  rw [← h]
  exact ⟨T.compHomeomorph e,hT⟩

/-- Local charts transfer across an actual homeomorphism of base spaces. -/
theorem localTriviality_of_base_homeomorph (p : C(E,B)) (q : C(E,P))
    (e : B ≃ₜ P) (he : ∀ x, e (p x) = q x)
    (hp : ∀ b, ∃ T : Bundle.Trivialization F p, b ∈ T.baseSet) :
    ∀ b, ∃ T : Bundle.Trivialization F q, b ∈ T.baseSet := by
  intro b
  obtain ⟨T,hT⟩ := hp (e.symm b)
  have h : e ∘ (p : E → B) = q := funext he
  change ∃ T : Bundle.Trivialization F (q : E → P), b ∈ T.baseSet
  rw [← h]
  exact ⟨T.homeomorphComp e,hT⟩

/-- Local triviality over the final homeomorphic skeleton is local
triviality over the original base. -/
theorem localTriviality_of_pullback_base_homeomorph (p : C(E,P)) (a : A ≃ₜ P)
    (hp : ∀ x, ∃ T : Bundle.Trivialization F (pullbackSndMap p ⟨a,a.continuous⟩),
      x ∈ T.baseSet) : ∀ x, ∃ T : Bundle.Trivialization F p, x ∈ T.baseSet := by
  let q : C({z : E × A // p z.1 = a z.2},P) :=
    ⟨fun z => p z.val.1,p.continuous.comp (continuous_fst.comp continuous_subtype_val)⟩
  have hq : ∀ x, ∃ T : Bundle.Trivialization F q, x ∈ T.baseSet :=
    localTriviality_of_base_homeomorph _ q a (fun z => z.property.symm) hp
  exact localTriviality_of_total_homeomorph q p (pullbackBaseHomeomorph p a).symm (fun _ => rfl) hq

end KIP126.Topology
