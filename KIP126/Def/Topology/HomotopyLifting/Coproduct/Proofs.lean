module

public import KIP126.Def.Topology.HomotopyLifting.Coproduct.Data
public import Mathlib.Topology.Category.TopCat.Limits.Products

@[expose] public section

namespace KIP126.Topology.HomotopyLifting

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

universe u v w

/-- Componentwise product coordinates preserve the actual point of the
coproduct base when every component preserves its base point. -/
theorem sigmaPullbackProductHomeomorph_snd
    {E P F ι : Type*} [TopologicalSpace E] [TopologicalSpace P] [TopologicalSpace F]
    (D : ι → Type*) [∀ i, TopologicalSpace (D i)]
    (p : C(E, P)) (a : C((Σ i, D i), P))
    (e : ∀ i, {z : E × D i // p z.1 = a ⟨i, z.2⟩} ≃ₜ F × D i)
    (he : ∀ i z, (e i z).2 = z.val.2)
    (z : {z : E × (Σ i, D i) // p z.1 = a z.2}) :
    (sigmaPullbackProductHomeomorph D p a e z).2 = z.val.2 := by
  change (⟨z.val.2.1, (e z.val.2.1 ⟨(z.val.1, z.val.2.2), z.property⟩).2⟩ : Σ i, D i) = _
  rw [he]

/-- Product coordinates on the pullback over each actual coproduct cell
assemble over any colimiting cofan, preserving its actual base coordinate. -/
theorem coproduct_pullback_product_homeomorph
    {ι : Type u} {D : ι → TopCat.{u}} (c : Cofan D) (hc : IsColimit c)
    {P : TopCat.{u}} {E : Type v} {F : Type w}
    [TopologicalSpace E] [TopologicalSpace F]
    (p : C(E, P)) (a : c.pt ⟶ P)
    (e : ∀ i, {z : E × D i // p z.1 = a (c.inj i z.2)} ≃ₜ F × D i)
    (he : ∀ i z, (e i z).2 = z.val.2) :
    ∃ eA : {z : E × c.pt // p z.1 = a z.2} ≃ₜ F × c.pt,
      ∀ z, (eA z).2 = z.val.2 := by
  let q := hc.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit D)
  let h := TopCat.homeoOfIso q
  have hinj (i : ι) (x : D i) : h.symm ⟨i, x⟩ = c.inj i x := by
    apply h.injective
    rw [Homeomorph.apply_symm_apply]
    exact (ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_hom hc
        (TopCat.sigmaCofanIsColimit D) (Discrete.mk i)) x).symm
  let a' : C((Σ i, D i), P) := a.hom.comp ⟨h.symm, h.symm.continuous⟩
  let e' (i : ι) : {z : E × D i // p z.1 = a' ⟨i, z.2⟩} ≃ₜ F × D i :=
    (Homeomorph.setCongr (by
      ext z
      change (p z.1 = a (h.symm ⟨i, z.2⟩)) ↔ p z.1 = a (c.inj i z.2)
      rw [hinj])).trans (e i)
  have he' (i : ι) (z : {z : E × D i // p z.1 = a' ⟨i, z.2⟩}) :
      (e' i z).2 = z.val.2 := he i _
  let b : {z : E × c.pt // p z.1 = a z.2} ≃ₜ
      {z : E × (Σ i, D i) // p z.1 = a' z.2} :=
    ((Homeomorph.refl E).prodCongr h).subtype (fun z => by
      change (p z.1 = a z.2) ↔ p z.1 = a (h.symm (h z.2))
      rw [Homeomorph.symm_apply_apply])
  let eA := b.trans ((sigmaPullbackProductHomeomorph (fun i => D i) p a' e').trans
    ((Homeomorph.refl F).prodCongr h.symm))
  refine ⟨eA, ?_⟩
  intro z
  change h.symm ((sigmaPullbackProductHomeomorph (fun i => D i) p a' e' (b z)).2) = z.val.2
  rw [sigmaPullbackProductHomeomorph_snd _ _ _ _ he']
  exact h.symm_apply_apply z.val.2

end KIP126.Topology.HomotopyLifting
