module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Approximation.ArbitraryTarget.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial

universe u

set_option backward.isDefEq.respectTransparency false

/-- Each finite order summand may be subdivided independently. The
resulting actual homeomorphism transports an arbitrary continuous map
to one homotopic to a single genuine order map into the arbitrary target. -/
theorem exists_orderSigma_order_approximation
    {ι : Type u} (P : ι → Type u) [∀ j, PartialOrder (P j)] [∀ j, Fintype (P j)]
    (Q : Type u) [PartialOrder Q]
    (a : C(|nerve (Σ j, P j)|,|nerve Q|)) :
    ∃ (n : ι → ℕ)
      (f : (Σ j, iteratedOrderSubdivision (P j) (n j + 1)) →o Q)
      (e : |nerve (Σ j, iteratedOrderSubdivision (P j) (n j + 1))| ≃ₜ |nerve (Σ j, P j)|),
      (∀ j (x : |nerve (iteratedOrderSubdivision (P j) (n j + 1))|),
        e (SSet.toTop.map (orderSigmaInclusion
          (fun k => iteratedOrderSubdivision (P k) (n k + 1)) j) x) =
        SSet.toTop.map (orderSigmaInclusion P j)
          (iteratedOrderSubdivisionHomeomorph (P j) (n j + 1) x)) ∧
      (a.comp ⟨e,e.continuous⟩).Homotopic
        (SSet.toTop.map (nerveMap f.monotone.functor)).hom := by
  classical
  have h (j : ι) := exists_iteratedOrderSubdivision_order_approximation_arbitrary_target
    (P j) Q (a.comp (SSet.toTop.map (orderSigmaInclusion P j)).hom)
  choose n f hf using h
  let D : ι → Type u := fun j => iteratedOrderSubdivision (P j) (n j + 1)
  obtain ⟨e,he⟩ := exists_orderSigmaRealization_homeomorph_of_family D P
    (fun j => iteratedOrderSubdivisionHomeomorph (P j) (n j + 1))
  refine ⟨n,orderSigmaMap D f,e,he,?_⟩
  apply orderSigmaRealization_homotopic D
  intro j
  have hleft : (a.comp ⟨e,e.continuous⟩).comp
      (SSet.toTop.map (orderSigmaInclusion D j)).hom =
      (a.comp (SSet.toTop.map (orderSigmaInclusion P j)).hom).comp
        ⟨iteratedOrderSubdivisionHomeomorph (P j) (n j + 1),
          (iteratedOrderSubdivisionHomeomorph (P j) (n j + 1)).continuous⟩ := by
    ext x
    exact congrArg a (he j x)
  have hright : (SSet.toTop.map (nerveMap (orderSigmaMap D f).monotone.functor)).hom.comp
      (SSet.toTop.map (orderSigmaInclusion D j)).hom =
        (SSet.toTop.map (nerveMap (f j).monotone.functor)).hom := by
    change (SSet.toTop.map (orderSigmaInclusion D j) ≫
      SSet.toTop.map (nerveMap (orderSigmaMap D f).monotone.functor)).hom = _
    rw [← CategoryTheory.Functor.map_comp,orderSigmaInclusion_map]
  rw [hleft,hright]
  exact hf j

end KIP126.Topology.SimplicialRealization
