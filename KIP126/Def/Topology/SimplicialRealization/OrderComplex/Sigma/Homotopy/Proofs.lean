module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Sigma.Proofs
public import KIP126.Def.Topology.Coproduct.Homotopy.Small.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Actual homotopies on all order summands assemble to a homotopy on
the realization of their disjoint union. -/
theorem orderSigmaRealization_homotopic
    {ι : Type u} (P : ι → Type u) [∀ j, PartialOrder (P j)]
    {Y : TopCat.{u}} (F G : C(|nerve (Σ j, P j)|,Y))
    (h : ∀ j, (F.comp (SSet.toTop.map (orderSigmaInclusion P j)).hom).Homotopic
      (G.comp (SSet.toTop.map (orderSigmaInclusion P j)).hom)) : F.Homotopic G := by
  classical
  obtain ⟨H,_⟩ := exists_homotopy_of_topological_cofan (orderSigmaRealizationCofan P)
    (orderSigmaRealizationCofan_isColimit P) F G (fun j => (h j).some)
  exact ⟨H⟩

/-- A family of actual homeomorphisms of order realizations induces a
homeomorphism of their realized disjoint unions with exact summand formulas. -/
theorem exists_orderSigmaRealization_homeomorph_of_family
    {ι : Type u} (P Q : ι → Type u) [∀ j, PartialOrder (P j)] [∀ j, PartialOrder (Q j)]
    (e : ∀ j, |nerve (P j)| ≃ₜ |nerve (Q j)|) :
    ∃ E : |nerve (Σ j, P j)| ≃ₜ |nerve (Σ j, Q j)|,
      ∀ j (x : |nerve (P j)|),
        E (SSet.toTop.map (orderSigmaInclusion P j) x) =
          SSet.toTop.map (orderSigmaInclusion Q j) (e j x) := by
  obtain ⟨p,hp⟩ := exists_orderSigmaRealization_homeomorph P
  obtain ⟨q,hq⟩ := exists_orderSigmaRealization_homeomorph Q
  let s : (Σ j, |nerve (P j)|) ≃ₜ (Σ j, |nerve (Q j)|) := {
    toEquiv := Equiv.sigmaCongrRight (fun j => (e j).toEquiv)
    continuous_toFun := continuous_sigma (fun j => continuous_sigmaMk.comp (e j).continuous)
    continuous_invFun := continuous_sigma (fun j => continuous_sigmaMk.comp (e j).symm.continuous) }
  refine ⟨p.trans (s.trans q.symm),?_⟩
  intro j x
  change q.symm (s (p (SSet.toTop.map (orderSigmaInclusion P j) x))) = _
  rw [hp]
  apply q.injective
  exact (q.apply_symm_apply _).trans (hq j (e j x)).symm

end KIP126.Topology.SimplicialRealization
