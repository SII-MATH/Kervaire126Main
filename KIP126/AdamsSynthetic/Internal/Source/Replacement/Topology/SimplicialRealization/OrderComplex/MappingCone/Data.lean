module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Data
import Mathlib.Order.WithBot
import Mathlib.Data.Fintype.WithTopBot

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- Attach a cone on the source end of the actual order mapping cylinder. -/
def OrderMappingCone (f : P →o Q) := OrderMappingCylinder f ⊕ Unit

/-- The new apex lies above exactly the source vertices and itself. -/
def orderMappingConeLE (f : P →o Q) : OrderMappingCone f → OrderMappingCone f → Prop
  | Sum.inl x, Sum.inl y => x ≤ y
  | Sum.inl (Sum.inl _), Sum.inr _ => True
  | Sum.inl (Sum.inr _), Sum.inr _ => False
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr _, Sum.inr _ => True

instance orderMappingCone_partialOrder (f : P →o Q) : PartialOrder (OrderMappingCone f) where
  le := orderMappingConeLE f
  le_refl := by rintro (x | t); exact le_rfl; trivial
  le_trans := by
    rintro (x | t) (y | t') (z | t'') h h'
    · exact h.trans h'
    · rcases x with p | q <;> rcases y with p' | q'
      · trivial
      · exact h'.elim
      · exact h.elim
      · exact h'.elim
    · exact h'.elim
    · exact h
    · exact h.elim
    · exact h.elim
    · exact h'.elim
    · trivial
  le_antisymm := by
    rintro (x | t) (y | t') h h'
    · exact congrArg Sum.inl (le_antisymm h h')
    · exact h'.elim
    · exact h.elim
    · exact congrArg Sum.inr (Subsingleton.elim _ _)

instance orderMappingCone_fintype (f : P →o Q) [Fintype P] [Fintype Q] :
    Fintype (OrderMappingCone f) := inferInstanceAs (Fintype (OrderMappingCylinder f ⊕ Unit))

instance orderMappingCone_finite (f : P →o Q) [Finite P] [Finite Q] :
    Finite (OrderMappingCone f) := inferInstanceAs (Finite (OrderMappingCylinder f ⊕ Unit))

/-- The actual mapping cylinder is an induced suborder of the mapping cone. -/
def orderMappingConeCylinderEmbedding (f : P →o Q) : OrderMappingCylinder f ↪o OrderMappingCone f where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

/-- The source with an added maximum is an induced suborder of the mapping cone. -/
def orderMappingConeTopEmbedding (f : P →o Q) : WithTop P ↪o OrderMappingCone f where
  toFun := fun x => match x with
    | none => Sum.inr ()
    | some p => Sum.inl (Sum.inl p)
  inj' := by
    rintro (_ | p) (_ | p') h
    · rfl
    · cases h
    · cases h
    · exact congrArg some (Sum.inl_injective (Sum.inl_injective h))
  map_rel_iff' := by
    rintro (_ | p) (_ | p')
    · change True ↔ (⊤ : WithTop P) ≤ ⊤
      simp
    · change False ↔ (⊤ : WithTop P) ≤ (p' : WithTop P)
      simp
    · change True ↔ (p : WithTop P) ≤ ⊤
      simp
    · change p ≤ p' ↔ (p : WithTop P) ≤ (p' : WithTop P)
      exact WithTop.coe_le_coe.symm

/-- The source inclusion into its actual cone order. -/
def orderMappingConeSourceTopEmbedding (P : Type u) [PartialOrder P] : P ↪o WithTop P where
  toFun := fun p => p
  inj' := WithTop.coe_injective
  map_rel_iff' := WithTop.coe_le_coe

/-- The source inclusion into its simplicial cone. -/
def orderMappingConeSourceTopInclusion (P : Type u) [PartialOrder P] :
    nerve P ⟶ nerve (WithTop P) :=
  nerveMap (orderMappingConeSourceTopEmbedding P).monotone.functor

/-- The actual mapping cylinder inclusion into the simplicial mapping cone. -/
def orderMappingConeCylinderInclusion (f : P →o Q) :
    nerve (OrderMappingCylinder f) ⟶ nerve (OrderMappingCone f) :=
  nerveMap (orderMappingConeCylinderEmbedding f).monotone.functor

/-- The actual source cone inclusion into the simplicial mapping cone. -/
def orderMappingConeTopInclusion (f : P →o Q) :
    nerve (WithTop P) ⟶ nerve (OrderMappingCone f) :=
  nerveMap (orderMappingConeTopEmbedding f).monotone.functor

end KIP126.Topology.SimplicialRealization
