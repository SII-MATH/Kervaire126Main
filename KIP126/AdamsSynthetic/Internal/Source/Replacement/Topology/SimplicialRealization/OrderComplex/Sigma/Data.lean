module

import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Data.Sigma.Order
import Mathlib.Order.WithBot

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

variable {ι : Type u} (P : ι → Type u) [∀ j, PartialOrder (P j)]

/-- Each summand is an actual induced suborder of the disjoint union. -/
def orderSigmaEmbedding (j : ι) : P j ↪o (Σ k, P k) where
  toFun := Sigma.mk j
  inj' := sigma_mk_injective
  map_rel_iff' := Sigma.mk_le_mk_iff


/-- The nerve inclusion of an actual order summand. -/
def orderSigmaInclusion (j : ι) : nerve (P j) ⟶ nerve (Σ k, P k) :=
  nerveMap (orderSigmaEmbedding P j).monotone.functor


/-- The actual family of order-nerve summand inclusions. -/
def orderSigmaCofan : Cofan (fun j => nerve (P j)) :=
  Cofan.mk (nerve (Σ k, P k)) (orderSigmaInclusion P)


/-- The realized inclusions of all disjoint order summands. -/
noncomputable def orderSigmaRealizationCofan : Cofan (fun j => SSet.toTop.obj (nerve (P j))) :=
  Cofan.mk (SSet.toTop.obj (nerve (Σ k, P k))) (fun j => SSet.toTop.map (orderSigmaInclusion P j))


/-- The disjoint family of actual cone bases embeds in the disjoint family of cones. -/
def orderSigmaConeEmbedding : (Σ j, P j) ↪o (Σ j, WithTop (P j)) where
  toFun := fun x => ⟨x.1,x.2⟩
  inj' := by
    rintro ⟨j,p⟩ ⟨k,q⟩ h
    have hjk : j = k := congrArg Sigma.fst h
    subst k
    have h' : (p : WithTop (P j)) = (q : WithTop (P j)) :=
      @sigma_mk_injective ι (fun j => WithTop (P j)) j _ _ h
    exact congrArg (Sigma.mk j) (WithTop.coe_injective h')
  map_rel_iff' := by
    rintro ⟨j,p⟩ ⟨k,q⟩
    constructor
    · intro h
      have hjk : j = k := (Sigma.le_def.mp h).choose
      subst k
      exact Sigma.LE.fiber _ _ _ (WithTop.coe_le_coe.mp (Sigma.mk_le_mk_iff.mp h))
    · intro h
      cases h with
      | fiber j p q hpq => exact Sigma.LE.fiber _ _ _ (WithTop.coe_le_coe.mpr hpq)


/-- A family of order maps assembles to an actual order map from the
disjoint union, without relations between distinct summands. -/
def orderSigmaMap {Q : Type u} [PartialOrder Q] (f : ∀ j, P j →o Q) : (Σ j, P j) →o Q where
  toFun := fun x => f x.1 x.2
  monotone' := by
    rintro _ _ ⟨j,p,q,hpq⟩
    exact (f j).monotone hpq


end KIP126.Topology.SimplicialRealization
