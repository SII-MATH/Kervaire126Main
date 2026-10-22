module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Data
import Mathlib.Data.Fintype.WithTopBot
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Simplex.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.Vertices

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial
open scoped Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- The cone's base inclusion is exactly the original proper-chain
boundary inclusion under the displayed simplicial isomorphism. -/
theorem orderBoundaryConeIso_base (P : Type u)
    [LinearOrder P] [Fintype P] [Nonempty P] :
    nerveMap (WithTop.coeOrderHom.toOrderHom : orderProperChains P →o WithTop (orderProperChains P)).monotone.functor ≫
      (orderBoundaryConeIso P).hom = orderBoundaryInclusion P := rfl

/-- Actual order-complex vertices commute with every order map. -/
theorem orderVertex_natural {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    [Fintype P] [Fintype Q] (f : P →o Q) (p : P) :
    SSet.toTop.map (nerveMap f.monotone.functor) (orderVertex P p) = orderVertex Q (f p) := by
  apply orderComplexCoordinates_injective Q
  rw [orderComplexCoordinates_natural,orderComplexCoordinates_vertex,stdSimplex.map_vertex,
    orderComplexCoordinates_vertex]

/-- The full face's geometric barycenter is the standard simplex barycenter. -/
theorem orderChainBarycenter_full (P : Type u) [LinearOrder P] [Fintype P] [Nonempty P] :
    orderChainBarycenter P (orderFullChain P) = stdSimplex.barycenter := by
  apply stdSimplex.ext
  funext p
  simp [orderChainBarycenter_apply,orderFullChain,stdSimplex.barycenter]
  rfl

/-- The actual order cone on the proper-chain boundary is a genuine
standard simplex. Its base is the original geometric boundary, and
its apex maps to the interior barycenter. -/
theorem exists_orderBoundaryCone_stdSimplex_homeomorph (P : Type u)
    [LinearOrder P] [Fintype P] [Nonempty P] :
    ∃ h : |nerve (WithTop (orderProperChains P))| ≃ₜ stdSimplex ℝ P,
      (∀ x, h x = orderSubdivisionCoordinates P
        (SSet.toTop.map (orderBoundaryConeIso P).hom x)) ∧
      (∀ x : |nerve (orderProperChains P)|,
        h (SSet.toTop.map (nerveMap (WithTop.coeOrderHom.toOrderHom :
          orderProperChains P →o WithTop (orderProperChains P)).monotone.functor) x) =
          orderSubdivisionCoordinates P (SSet.toTop.map (orderBoundaryInclusion P) x)) ∧
      h (orderVertex _ (⊤ : WithTop (orderProperChains P))) = stdSimplex.barycenter := by
  letI := finite_nonemptyFiniteChains P
  letI : Fintype (PartialOrder.NonemptyFiniteChains P) := Fintype.ofFinite _
  letI : Fintype (orderProperChains P) := Fintype.ofFinite _
  obtain ⟨e,he⟩ := exists_linearOrderCoordinates_homeomorph P
  let h := (TopCat.homeoOfIso (SSet.toTop.mapIso (orderBoundaryConeIso P))).trans
    ((orderSubdivisionHomeomorph P).trans e)
  have hh (x : |nerve (WithTop (orderProperChains P))|) :
      h x = orderSubdivisionCoordinates P (SSet.toTop.map (orderBoundaryConeIso P).hom x) := by
    change e (orderSubdivisionHomeomorph P _) = _
    rw [he,orderSubdivisionHomeomorph_coordinates]
    rfl
  refine ⟨h,hh,?_,?_⟩
  · intro x
    rw [hh,← TopCat.comp_app,← Functor.map_comp,orderBoundaryConeIso_base]
  · rw [hh]
    have hv : SSet.toTop.map (orderBoundaryConeIso P).hom
        (orderVertex _ (⊤ : WithTop (orderProperChains P))) =
        orderVertex _ (orderFullChain P) :=
      orderVertex_natural ⟨orderBoundaryConeOrderIso P,(orderBoundaryConeOrderIso P).monotone⟩ ⊤
    rw [hv,← orderSubdivisionHomeomorph_coordinates,orderSubdivisionHomeomorph_vertex,
      orderChainBarycenter_full]

end KIP126.Topology.SimplicialRealization
