module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Comparison.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Barycentric subdivision is an actual homeomorphism between the
realizations of a finite order and its order of nonempty finite chains. -/
theorem exists_orderSubdivision_homeomorph (P : Type u) [PartialOrder P] [Fintype P] :
    ∃ h : |nerve (PartialOrder.NonemptyFiniteChains P)| ≃ₜ |nerve P|,
      ∀ x, orderComplexCoordinates P (h x) = orderSubdivisionCoordinates P x := by
  obtain ⟨a,ha⟩ := exists_orderSubdivisionCoordinates_homeomorph P
  obtain ⟨b,hb⟩ := exists_orderComplexCoordinates_homeomorph P
  refine ⟨a.trans b.symm,?_⟩
  intro x
  have h := hb (b.symm (a x))
  rw [b.apply_symm_apply] at h
  exact h.symm.trans (ha x)

/-- The genuine finite-order subdivision homeomorphism is homotopic
to the actual simplicial last-vertex map. Throughout the homotopy every
zero coordinate of its geometric image stays zero. -/
theorem exists_orderSubdivision_homeomorph_homotopy (P : Type u)
    [PartialOrder P] [Fintype P] :
    ∃ h : |nerve (PartialOrder.NonemptyFiniteChains P)| ≃ₜ |nerve P|,
      (∀ x, orderComplexCoordinates P (h x) = orderSubdivisionCoordinates P x) ∧
      ∃ H : (⟨h,h.continuous⟩ :
          C(|nerve (PartialOrder.NonemptyFiniteChains P)|,|nerve P|)).Homotopy
            (SSet.toTop.map (orderSubdivisionLastVertex P)).hom,
        ∀ (t : I) (x : |nerve (PartialOrder.NonemptyFiniteChains P)|) (p : P),
          orderSubdivisionCoordinates P x p = 0 → orderComplexCoordinates P (H (t,x)) p = 0 := by
  obtain ⟨h,hh⟩ := exists_orderSubdivision_homeomorph P
  obtain ⟨b,hb⟩ := exists_orderComplexCoordinates_homeomorph P
  obtain ⟨G,hchain,hzero⟩ := exists_orderSubdivisionCoordinates_homotopy P
  have hbi (y : {y : stdSimplex ℝ P // HasChainSupport y}) :
      orderComplexCoordinates P (b.symm y) = y.val := by
    have h := hb (b.symm y)
    rw [b.apply_symm_apply] at h
    exact h.symm
  let H : (⟨h,h.continuous⟩ :
      C(|nerve (PartialOrder.NonemptyFiniteChains P)|,|nerve P|)).Homotopy
        (SSet.toTop.map (orderSubdivisionLastVertex P)).hom := {
    toFun := fun z => b.symm ⟨G z,hchain z.1 z.2⟩
    continuous_toFun := b.symm.continuous.comp (G.continuous.subtype_mk _)
    map_zero_left := by
      intro x
      apply orderComplexCoordinates_injective P
      rw [hbi]
      exact (G.apply_zero x).trans (hh x).symm
    map_one_left := by
      intro x
      apply orderComplexCoordinates_injective P
      rw [hbi]
      exact G.apply_one x }
  refine ⟨h,hh,H,?_⟩
  intro t x p hx
  change orderComplexCoordinates P (b.symm ⟨G (t,x),hchain t x⟩) p = 0
  rw [hbi]
  exact hzero t x p hx

end KIP126.Topology.SimplicialRealization
