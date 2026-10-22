module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Sigma.Attachment.Model.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.OrderComplex.Boundary.Cone.Cube.Proofs
import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

@[expose] section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Simplicial HomotopicalAlgebra
open KIP126.Topology.HomotopyLifting
universe u v
set_option backward.isDefEq.respectTransparency false

/-- An actual attachment of a family of finite-order cone bases to
an old order homotopy model has a new actual order homotopy model.
Both comparisons strictly retain the original old-space map. -/
theorem exists_order_model_of_orderCone_attachCells
    {α : Type v} (P : α → Type u) [∀ i, PartialOrder (P i)] [∀ i, Fintype (P i)]
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (fun i => SSet.toTop.map (orderMappingConeSourceTopInclusion (P i))) f)
    (Q : Type u) [PartialOrder Q] (e : ContinuousMap.HomotopyEquiv |nerve Q| X) :
    ∃ (R : Type u) (_ : PartialOrder R) (j : Q ↪o R)
      (E : ContinuousMap.HomotopyEquiv |nerve R| Y),
      (∀ x : |nerve Q|, E (SSet.toTop.map (nerveMap j.monotone.functor) x) = f (e x)) ∧
      ∀ x : X, E.invFun (f x) = SSet.toTop.map (nerveMap j.monotone.functor) (e.invFun x) := by
  let D : c.ι → Type u := fun j => P (c.π j)
  let hc₁ := orderSigmaRealizationCofan_isColimit D
  let hc₂ := orderSigmaRealizationCofan_isColimit (fun j => WithTop (D j))
  let e₁ := hc₁.coconePointUniqueUpToIso c.isColimit₁
  let e₂ := hc₂.coconePointUniqueUpToIso c.isColimit₂
  have he₁ (j : c.ι) : SSet.toTop.map (orderSigmaInclusion D j) ≫ e₁.hom = c.cofan₁.inj j :=
    hc₁.fac c.cofan₁ ⟨j⟩
  have he₂ (j : c.ι) : SSet.toTop.map (orderSigmaInclusion (fun k => WithTop (D k)) j) ≫
      e₂.hom = c.cofan₂.inj j := hc₂.fac c.cofan₂ ⟨j⟩
  let m := SSet.toTop.map (nerveMap (orderSigmaConeEmbedding D).monotone.functor)
  have hm : e₁.hom ≫ c.m = m ≫ e₂.hom := by
    apply Cofan.IsColimit.hom_ext hc₁
    intro j
    change SSet.toTop.map (orderSigmaInclusion D j) ≫ (e₁.hom ≫ c.m) =
      SSet.toTop.map (orderSigmaInclusion D j) ≫ (m ≫ e₂.hom)
    rw [← Category.assoc,he₁,c.hm]
    have hs := congrArg SSet.toTop.map (orderSigmaConeEmbedding_inclusion D j)
    simp only [Functor.map_comp] at hs
    rw [← Category.assoc,hs,Category.assoc,he₂]
  have hp : IsPushout (e₁.hom ≫ c.g₁) m f (e₂.hom ≫ c.g₂) := by
    apply c.isPushout.of_iso' e₁ (Iso.refl X) e₂ (Iso.refl Y)
    · simp only [Iso.refl_hom,Category.comp_id]
    · exact hm
    · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
    · simp only [Iso.refl_hom,Category.comp_id]
  obtain ⟨n,a,E,hE,hEinv⟩ := exists_orderSigmaConeAttachment_homotopyEquiv_of_model
    D Q e (e₁.hom ≫ c.g₁) f (e₂.hom ≫ c.g₂) hp
  exact ⟨OrderSigmaConeAttachment (fun j => iteratedOrderSubdivision (D j) (n j+1)) a,
    inferInstance,orderSigmaConeAttachmentTargetEmbedding _ a,E,hE,hEinv⟩

/-- An attachment of the original whole cube boundaries admits an
actual order-realization model extending any actual old model. The
finite-order cell pair comparison includes zero-dimensional cells. -/
theorem exists_order_model_of_cube_attachCells
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} cubeBoundaryInclusion.{u} f)
    (Q : Type u) [PartialOrder Q] (e : ContinuousMap.HomotopyEquiv |nerve Q| X) :
    ∃ (R : Type u) (_ : PartialOrder R) (j : Q ↪o R)
      (E : ContinuousMap.HomotopyEquiv |nerve R| Y),
      (∀ x : |nerve Q|, E (SSet.toTop.map (nerveMap j.monotone.functor) x) = f (e x)) ∧
      ∀ x : X, E.invFun (f x) = SSet.toTop.map (nerveMap j.monotone.functor) (e.invFun x) := by
  classical
  let P : ℕ → Type u := fun n => orderProperChains (ULift.{u} (Fin (n+1)))
  letI (n : ℕ) : Fintype (P n) := Fintype.ofFinite _
  let c' := c.reindexCellTypes
    (fun n => SSet.toTop.map (orderMappingConeSourceTopInclusion (P n))) id
    (fun n => (orderBoundaryCubeArrowIso n).symm)
  exact exists_order_model_of_orderCone_attachCells P c' Q e

end KIP126.Topology.SimplicialRealization
