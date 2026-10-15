module

public import KIP126.Def.Topology.Cylinder.Endpoints.Data

@[expose] public section

namespace KIP126.Topology
open CategoryTheory Set _root_.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Both ends of a cylinder form a closed embedded subspace without any
separation condition on the original space. -/
theorem cylinderEndpointInclusion_isClosedEmbedding (A : TopCat.{u}) :
    IsClosedEmbedding (cylinderEndpointInclusion A) := by
  have h (t : I) : IsClosedEmbedding (fun a : A => (a,t)) := by
    refine ⟨isEmbedding_prodMkLeft t,?_⟩
    have hr : range (fun a : A => (a,t)) = {z : A × I | z.2 = t} := by
      ext z
      constructor
      · rintro ⟨a,rfl⟩; rfl
      · intro hz; exact ⟨z.1,Prod.ext rfl hz.symm⟩
    rw [hr]
    exact isClosed_eq continuous_snd continuous_const
  apply (h 0).sumElim (h 1)
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (congrArg Prod.fst hxy)
    | inr y => exact (zero_ne_one (congrArg Prod.snd hxy)).elim
  | inr x =>
    cases y with
    | inl y => exact (zero_ne_one (congrArg Prod.snd hxy).symm).elim
    | inr y => exact congrArg Sum.inr (congrArg Prod.fst hxy)

/-- Both-end cylinder inclusion has actual homotopy extension for every
original space. -/
theorem cylinderEndpointInclusion_hasHomotopyExtension (A : TopCat.{u}) :
    HomotopyExtension.HasHomotopyExtension (cylinderEndpointInclusion A) := by
  obtain ⟨r,h0,hL,hR,hr⟩ := HomotopyExtension.exists_interval_boundary_retraction
  let R : C((A × I) × I,(A × I) × I) := ⟨fun z => ((z.1.1,(r (z.1.2,z.2)).1),(r (z.1.2,z.2)).2),
    (continuous_fst.fst.prodMk (r.continuous.comp (continuous_fst.snd.prodMk continuous_snd)).fst).prodMk
      (r.continuous.comp (continuous_fst.snd.prodMk continuous_snd)).snd⟩
  apply HomotopyExtension.hasHomotopyExtension_of_cylinder_retraction
    (cylinderEndpointInclusion A) (cylinderEndpointInclusion_isClosedEmbedding A) R
  · rintro ⟨a,t⟩
    change ((a,(r (t,0)).1),(r (t,0)).2) = ((a,t),0)
    rw [h0]
  · intro a s
    cases a with
    | inl a =>
      change ((a,(r (0,s)).1),(r (0,s)).2) = ((a,0),s)
      rw [hL]
    | inr a =>
      change ((a,(r (1,s)).1),(r (1,s)).2) = ((a,1),s)
      rw [hR]
  · rintro ⟨⟨a,t⟩,s⟩
    rcases hr (t,s) with hz | hz | hz
    · exact Or.inl hz
    · right
      refine ⟨Sum.inl a,?_⟩
      exact Prod.ext rfl hz.symm
    · right
      refine ⟨Sum.inr a,?_⟩
      exact Prod.ext rfl hz.symm

end KIP126.Topology
