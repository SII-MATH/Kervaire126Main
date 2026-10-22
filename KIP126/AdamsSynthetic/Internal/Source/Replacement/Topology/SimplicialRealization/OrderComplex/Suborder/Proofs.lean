module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Suborder.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual suborder inclusion is injective in every simplicial degree. -/
theorem orderSuborderInclusion_app_injective (P : Type u) [PartialOrder P]
    (S : Set P) (d : SimplexCategoryᵒᵖ) :
    Function.Injective ((orderSuborderInclusion P S).app d) := by
  intro s t h
  exact CategoryTheory.Functor.ext (fun k =>
    Subtype.ext (congrArg (fun z : (nerve P).obj d => z.obj k) h))

/-- The suborder inclusion is an actual simplicial monomorphism. -/
instance orderSuborderInclusion_mono (P : Type u) [PartialOrder P] (S : Set P) :
    Mono (orderSuborderInclusion P S) := by
  letI (d : SimplexCategoryᵒᵖ) : Mono ((orderSuborderInclusion P S).app d) :=
    (CategoryTheory.mono_iff_injective _).mpr (orderSuborderInclusion_app_injective P S d)
  exact NatTrans.mono_of_mono_app _

/-- Coordinates of the actual suborder inclusion are precisely the
pushforward along the underlying vertex inclusion. -/
theorem orderSuborderInclusion_coordinates (P : Type u) [PartialOrder P] [Fintype P]
    (S : Set P) [Fintype S] (x : |nerve S|) :
    orderComplexCoordinates P (SSet.toTop.map (orderSuborderInclusion P S) x) =
      stdSimplex.map (fun p : S => p.val) (orderComplexCoordinates S x) :=
  orderComplexCoordinates_natural (OrderHom.Subtype.val (· ∈ S)) x

/-- The actual realization of a suborder is exactly the coordinate
face cut out by vanishing at every vertex outside that suborder. -/
theorem orderSuborderInclusion_range_iff (P : Type u) [PartialOrder P] [Fintype P]
    (S : Set P) (x : |nerve P|) :
    x ∈ Set.range (SSet.toTop.map (orderSuborderInclusion P S)) ↔
      ∀ p, p ∉ S → orderComplexCoordinates P x p = 0 := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  constructor
  · rintro ⟨y,rfl⟩ p hp
    rw [orderSuborderInclusion_coordinates]
    exact simplex_map_apply_not_range (fun p : S => p.val) _ p
      (by rintro ⟨q,rfl⟩; exact hp q.property)
  · intro hx
    have hy : orderComplexCoordinates P x ∈
        Set.range (stdSimplex.map (S := ℝ) (fun p : S => p.val)) := by
      apply (simplex_map_range_iff _ Subtype.val_injective _).mpr
      intro p hp
      apply hx p
      intro hS
      exact hp ⟨⟨p,hS⟩,rfl⟩
    obtain ⟨y,hy⟩ := hy
    have hchain : HasChainSupport y := by
      intro p q hp hq
      apply orderComplexCoordinates_hasChainSupport P x p.val q.val
      · rw [← hy,simplex_map_apply_injective _ Subtype.val_injective]
        exact hp
      · rw [← hy,simplex_map_apply_injective _ Subtype.val_injective]
        exact hq
    obtain ⟨z,hz⟩ := orderComplexCoordinates_preimage S y hchain
    refine ⟨z,?_⟩
    apply orderComplexCoordinates_injective P
    rw [orderSuborderInclusion_coordinates,hz,hy]

/-- The actual suborder realization inclusion is injective. -/
theorem orderSuborderInclusion_realization_injective (P : Type u)
    [PartialOrder P] [Fintype P] (S : Set P) :
    Function.Injective (SSet.toTop.map (orderSuborderInclusion P S)) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  intro x y hxy
  apply orderComplexCoordinates_injective S
  apply simplex_map_injective (fun p : S => p.val) Subtype.val_injective
  rw [← orderSuborderInclusion_coordinates,← orderSuborderInclusion_coordinates,hxy]

end KIP126.Topology.SimplicialRealization
