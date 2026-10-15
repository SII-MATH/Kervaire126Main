module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Boundary.Data
public import Mathlib.Order.Hom.WithTopBot

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial
open scoped Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- The full nonempty chain of a finite linear order. -/
def orderFullChain (P : Type u) [LinearOrder P] [Fintype P] [Nonempty P] :
    PartialOrder.NonemptyFiniteChains P where
  finset := Finset.univ
  nonempty := Finset.univ_nonempty
  comparable a b := le_total a b

/-- Adding an apex to the proper face chains recovers all face chains;
the apex is the full face. -/
noncomputable def orderBoundaryConeOrderIso (P : Type u)
    [LinearOrder P] [Fintype P] [Nonempty P] :
    WithTop (orderProperChains P) ≃o PartialOrder.NonemptyFiniteChains P where
  toFun := fun c => match c with
    | none => orderFullChain P
    | some c => c.val
  invFun := fun c => if h : c.finset = Finset.univ then none else some ⟨c,h⟩
  left_inv := by
    intro c
    cases c with
    | top => simp [orderFullChain]; rfl
    | coe c => simp [show c.val.finset ≠ Finset.univ from c.property]; rfl
  right_inv := by
    intro c
    dsimp only
    split_ifs with h
    · exact PartialOrder.NonemptyFiniteChains.ext h.symm
    · rfl
  map_rel_iff' := by
    intro c d
    cases c with
    | top =>
      cases d with
      | top => simp
      | coe d =>
        have hn : ¬ orderFullChain P ≤ d.val := by
          intro h
          exact d.property (Finset.univ_subset_iff.mp h)
        change orderFullChain P ≤ d.val ↔ (⊤ : WithTop (orderProperChains P)) ≤ ↑d
        simpa only [WithTop.top_le_iff,WithTop.coe_ne_top,iff_false] using hn
    | coe c =>
      cases d with
      | top =>
        exact iff_of_true (show c.val.finset ⊆ Finset.univ from Finset.subset_univ _)
          le_top
      | coe d =>
        change c ≤ d ↔ (c : WithTop (orderProperChains P)) ≤ ↑d
        exact WithTop.coe_le_coe.symm

/-- The corresponding actual simplicial isomorphism identifies the
poset cone with the original subdivided simplex. -/
noncomputable def orderBoundaryConeIso (P : Type u)
    [LinearOrder P] [Fintype P] [Nonempty P] :
    nerve (WithTop (orderProperChains P)) ≅ nerve (PartialOrder.NonemptyFiniteChains P) :=
  PartOrd.nerveFunctor.mapIso {
    hom := PartOrd.ofHom (⟨orderBoundaryConeOrderIso P,(orderBoundaryConeOrderIso P).monotone⟩)
    inv := PartOrd.ofHom (⟨(orderBoundaryConeOrderIso P).symm,(orderBoundaryConeOrderIso P).symm.monotone⟩)
    hom_inv_id := by apply PartOrd.ext; intro c; exact (orderBoundaryConeOrderIso P).symm_apply_apply c
    inv_hom_id := by apply PartOrd.ext; intro c; exact (orderBoundaryConeOrderIso P).apply_symm_apply c }

end KIP126.Topology.SimplicialRealization
