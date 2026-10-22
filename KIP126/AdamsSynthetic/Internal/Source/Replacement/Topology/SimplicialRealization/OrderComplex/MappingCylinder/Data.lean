module

import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finite.Sum

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- The actual order mapping cylinder has disjoint source and target vertices. -/
def OrderMappingCylinder (_f : P →o Q) := P ⊕ Q

/-- The mapping-cylinder relation has one-way cross relations given by the map. -/
def orderMappingCylinderLE (f : P →o Q) : OrderMappingCylinder f → OrderMappingCylinder f → Prop
  | Sum.inl p, Sum.inl p' => p ≤ p'
  | Sum.inl p, Sum.inr q => f p ≤ q
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr q, Sum.inr q' => q ≤ q'

instance orderMappingCylinder_partialOrder (f : P →o Q) : PartialOrder (OrderMappingCylinder f) where
  le := orderMappingCylinderLE f
  le_refl := by rintro (p | q) <;> exact le_rfl
  le_trans := by
    rintro (p | q) (p' | q') (p'' | q'') h h'
    · exact h.trans h'
    · exact (f.monotone h).trans h'
    · exact h'.elim
    · exact h.trans h'
    · exact h.elim
    · exact h.elim
    · exact h'.elim
    · exact h.trans h'
  le_antisymm := by
    rintro (p | q) (p' | q') h h'
    · exact congrArg Sum.inl (le_antisymm h h')
    · exact h'.elim
    · exact h.elim
    · exact congrArg Sum.inr (le_antisymm h h')

instance orderMappingCylinder_fintype (f : P →o Q) [Fintype P] [Fintype Q] :
    Fintype (OrderMappingCylinder f) := inferInstanceAs (Fintype (P ⊕ Q))

instance orderMappingCylinder_finite (f : P →o Q) [Finite P] [Finite Q] :
    Finite (OrderMappingCylinder f) := inferInstanceAs (Finite (P ⊕ Q))

/-- The actual source end of the order mapping cylinder. -/
def orderMappingCylinderInl (f : P →o Q) : P →o OrderMappingCylinder f where
  toFun := Sum.inl
  monotone' := fun _ _ h => h

/-- The actual target end of the order mapping cylinder. -/
def orderMappingCylinderInr (f : P →o Q) : Q →o OrderMappingCylinder f where
  toFun := Sum.inr
  monotone' := fun _ _ h => h

/-- The actual mapping-cylinder retraction equals the given map on
the source end and the identity on the target end. -/
def orderMappingCylinderRetraction (f : P →o Q) : OrderMappingCylinder f →o Q where
  toFun := Sum.elim f id
  monotone' := by
    rintro (p | q) (p' | q') h
    · exact f.monotone h
    · exact h
    · exact h.elim
    · exact h

/-- The actual source inclusion of the nerve mapping cylinder. -/
def orderMappingCylinderSourceInclusion (f : P →o Q) :
    nerve P ⟶ nerve (OrderMappingCylinder f) :=
  nerveMap (orderMappingCylinderInl f).monotone.functor

/-- The actual target inclusion of the nerve mapping cylinder. -/
def orderMappingCylinderTargetInclusion (f : P →o Q) :
    nerve Q ⟶ nerve (OrderMappingCylinder f) :=
  nerveMap (orderMappingCylinderInr f).monotone.functor

/-- The actual simplicial retraction of the nerve mapping cylinder. -/
def orderMappingCylinderProjection (f : P →o Q) :
    nerve (OrderMappingCylinder f) ⟶ nerve Q :=
  nerveMap (orderMappingCylinderRetraction f).monotone.functor

end KIP126.Topology.SimplicialRealization
