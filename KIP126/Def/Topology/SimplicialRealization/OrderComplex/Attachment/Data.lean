module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Data
public import Mathlib.Order.UpperLower.Basic

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]

/-- The order obtained by adjoining a target to an actual order along
an order map defined on a lower induced suborder. -/
def OrderAttachment (i : P ↪o R) (_hi : IsLowerSet (Set.range i)) (_f : P →o Q) := R ⊕ Q

/-- Cross relations are precisely those from a source-suborder vertex
to a target vertex lying above its assigned image. -/
def orderAttachmentLE (i : P ↪o R) (hi : IsLowerSet (Set.range i)) (f : P →o Q) :
    OrderAttachment i hi f → OrderAttachment i hi f → Prop
  | Sum.inl r, Sum.inl r' => r ≤ r'
  | Sum.inl r, Sum.inr q => ∃ p, i p = r ∧ f p ≤ q
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr q, Sum.inr q' => q ≤ q'

instance orderAttachment_partialOrder (i : P ↪o R) (hi : IsLowerSet (Set.range i)) (f : P →o Q) :
    PartialOrder (OrderAttachment i hi f) where
  le := orderAttachmentLE i hi f
  le_refl := by rintro (r | q) <;> exact le_rfl
  le_trans := by
    rintro (r | q) (r' | q') (r'' | q'') h h'
    · exact h.trans h'
    · obtain ⟨p',hp',hf'⟩ := h'
      obtain ⟨p,hp⟩ := hi h ⟨p',hp'⟩
      refine ⟨p,hp,?_⟩
      have hh : p ≤ p' := i.le_iff_le.mp (by rw [hp,hp']; exact h)
      exact (f.monotone hh).trans hf'
    · exact h'.elim
    · obtain ⟨p,hp,hf⟩ := h
      exact ⟨p,hp,hf.trans h'⟩
    · exact h.elim
    · exact h.elim
    · exact h'.elim
    · exact h.trans h'
  le_antisymm := by
    rintro (r | q) (r' | q') h h'
    · exact congrArg Sum.inl (le_antisymm h h')
    · exact h'.elim
    · exact h.elim
    · exact congrArg Sum.inr (le_antisymm h h')

/-- The original order is an induced suborder of the attachment. -/
def orderAttachmentPieceEmbedding (i : P ↪o R) (hi : IsLowerSet (Set.range i)) (f : P →o Q) :
    R ↪o OrderAttachment i hi f where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

/-- The mapping cylinder of the attaching map is an induced suborder
of the attachment. -/
def orderAttachmentCylinderEmbedding (i : P ↪o R) (hi : IsLowerSet (Set.range i)) (f : P →o Q) :
    OrderMappingCylinder f ↪o OrderAttachment i hi f where
  toFun := Sum.map i id
  inj' := Sum.map_injective.mpr ⟨i.injective,Function.injective_id⟩
  map_rel_iff' := by
    rintro (p | q) (p' | q')
    · exact i.le_iff_le
    · change (∃ p', i p' = i p ∧ f p' ≤ q') ↔ f p ≤ q'
      constructor
      · rintro ⟨p',hp',hf⟩
        exact i.injective hp' ▸ hf
      · intro hf
        exact ⟨p,rfl,hf⟩
    · rfl
    · rfl

/-- The original piece's actual nerve inclusion. -/
def orderAttachmentPieceInclusion (i : P ↪o R) (hi : IsLowerSet (Set.range i)) (f : P →o Q) :
    nerve R ⟶ nerve (OrderAttachment i hi f) :=
  nerveMap (orderAttachmentPieceEmbedding i hi f).monotone.functor

/-- The mapping cylinder's actual nerve inclusion. -/
def orderAttachmentCylinderInclusion (i : P ↪o R) (hi : IsLowerSet (Set.range i)) (f : P →o Q) :
    nerve (OrderMappingCylinder f) ⟶ nerve (OrderAttachment i hi f) :=
  nerveMap (orderAttachmentCylinderEmbedding i hi f).monotone.functor

end KIP126.Topology.SimplicialRealization
