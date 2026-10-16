module

import all KIP126.SpectralSequence.ModuleQuotient.Data

@[expose] section

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R] {M : ModuleCat.{v} R}

/-- Inclusions preserve the specified concrete representatives. -/
@[reassoc] theorem submoduleUnderlyingIso_inv_ofLE (B Z : Submodule R M) (h : B ≤ Z) :
    (submoduleUnderlyingIso B).inv ≫
      Subobject.ofLE ((ModuleCat.subobjectModule M).symm B)
        ((ModuleCat.subobjectModule M).symm Z)
        ((ModuleCat.subobjectModule M).symm.monotone h) =
    ModuleCat.ofHom (Submodule.inclusion h) ≫ (submoduleUnderlyingIso Z).inv := by
  apply (cancel_mono (submoduleUnderlyingIso Z).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  unfold submoduleUnderlyingIso
  rw [submodule_ofLE_underlyingIso B Z h]
  exact Iso.inv_hom_id_assoc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel comparison sends each actual representative to its quotient class. -/
@[reassoc] theorem submoduleCokernelIso_π (B Z : Submodule R M) (h : B ≤ Z) :
    (Subobject.underlyingIso (ModuleCat.ofHom Z.subtype)).inv ≫
      cokernel.π (Subobject.ofLE ((ModuleCat.subobjectModule M).symm B)
        ((ModuleCat.subobjectModule M).symm Z)
        ((ModuleCat.subobjectModule M).symm.monotone h)) ≫
      (submoduleCokernelIso B Z h).hom =
        ModuleCat.ofHom (B.comap Z.subtype).mkQ := by
  simp only [submoduleCokernelIso, Iso.trans_hom, cokernel.mapIso_hom,
    cokernel.map, Category.assoc, cokernel.π_desc_assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  ext x
  exact Submodule.quotEquivOfEq_mk _ _ (Submodule.range_inclusion B Z h) x

/-- Inverse ambient maps with actual lifts preserve and reflect membership.
The subobjects are the existing ones; no alternate representative object is chosen. -/
theorem subobject_mem_iff_of_inverse {N : ModuleCat.{v} R}
    (e : M ≃ₗ[R] N) (S : Subobject M) (T : Subobject N)
    (hf : ∃ f : Subobject.underlying.obj S ⟶ Subobject.underlying.obj T,
      f ≫ T.arrow = S.arrow ≫ ModuleCat.ofHom e.toLinearMap)
    (hg : ∃ g : Subobject.underlying.obj T ⟶ Subobject.underlying.obj S,
      g ≫ S.arrow = T.arrow ≫ ModuleCat.ofHom e.symm.toLinearMap) (x : M) :
    e x ∈ (ModuleCat.subobjectModule N) T ↔ x ∈ (ModuleCat.subobjectModule M) S := by
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := hg
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨g a, ?_⟩
    have h := congrArg (fun k => k.hom a) hg
    change S.arrow (g a) = e.symm (T.arrow a) at h
    simpa only [ha, e.symm_apply_apply] using h
  · rintro ⟨a, ha⟩
    refine ⟨f a, ?_⟩
    have h := congrArg (fun k => k.hom a) hf
    change T.arrow (f a) = e (S.arrow a) at h
    simpa only [ha] using h

set_option backward.isDefEq.respectTransparency false in
/-- Descend an ambient linear equivalence through the existing cycle and
boundary subobjects. This adapts KIPBase's `quotientAddEquivOfAddEquiv` to
the canonical categorical quotient, and records its effect on representatives. -/
theorem subobject_quotient_iso_of_linearEquiv {N : ModuleCat.{v} R}
    (B Z : Subobject M) (B' Z' : Subobject N) (h : B ≤ Z) (h' : B' ≤ Z')
    (e : M ≃ₗ[R] N)
    (hB : ∀ x, e x ∈ (ModuleCat.subobjectModule N) B' ↔ x ∈ (ModuleCat.subobjectModule M) B)
    (hZ : ∀ x, e x ∈ (ModuleCat.subobjectModule N) Z' ↔ x ∈ (ModuleCat.subobjectModule M) Z) :
    ∃ q : cokernel (Subobject.ofLE B Z h) ≅ cokernel (Subobject.ofLE B' Z' h'),
      ∀ a : (Subobject.underlying.obj Z : ModuleCat R),
        ∃ b : (Subobject.underlying.obj Z' : ModuleCat R),
          Z'.arrow b = e (Z.arrow a) ∧
          q.hom (cokernel.π (Subobject.ofLE B Z h) a) =
            cokernel.π (Subobject.ofLE B' Z' h') b := by
  have restrict (S : Subobject M) (T : Subobject N)
      (he : ∀ x, e x ∈ (ModuleCat.subobjectModule N) T ↔ x ∈ (ModuleCat.subobjectModule M) S) :
      ∃ v : Subobject.underlying.obj S ≅ Subobject.underlying.obj T,
        ∀ a, T.arrow (v.hom a) = e (S.arrow a) := by
    let a := LinearEquiv.ofInjective S.arrow.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
    let b := LinearEquiv.ofInjective T.arrow.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
    have hm : ((ModuleCat.subobjectModule M) S).map e.toLinearMap =
        (ModuleCat.subobjectModule N) T := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (he x).2 hx
      · intro hy
        refine ⟨e.symm y, (he (e.symm y)).1 ?_, e.apply_symm_apply y⟩
        simpa only [e.apply_symm_apply] using hy
    let c := e.ofSubmodules ((ModuleCat.subobjectModule M) S) ((ModuleCat.subobjectModule N) T) hm
    refine ⟨((a.trans c).trans b.symm).toModuleIso, ?_⟩
    intro x
    exact congrArg Subtype.val (b.apply_symm_apply (c (a x)))
  obtain ⟨b, hb⟩ := restrict B B' hB
  obtain ⟨z, hz⟩ := restrict Z Z' hZ
  have comm : Subobject.ofLE B Z h ≫ z.hom = b.hom ≫ Subobject.ofLE B' Z' h' := by
    apply (cancel_mono Z'.arrow).1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Z'.arrow (z.hom (Subobject.ofLE B Z h x)) =
      Z'.arrow (Subobject.ofLE B' Z' h' (b.hom x))
    rw [hz]
    have hs := congrArg (fun f => f.hom x) (Subobject.ofLE_arrow h)
    have ht := congrArg (fun f => f.hom (b.hom x)) (Subobject.ofLE_arrow h')
    change Z.arrow (Subobject.ofLE B Z h x) = B.arrow x at hs
    change Z'.arrow (Subobject.ofLE B' Z' h' (b.hom x)) = B'.arrow (b.hom x) at ht
    rw [hs, ht, hb]
  let q := cokernel.mapIso (Subobject.ofLE B Z h) (Subobject.ofLE B' Z' h') b z comm
  refine ⟨q, fun a => ⟨z.hom a, hz a, ?_⟩⟩
  have hq : cokernel.π (Subobject.ofLE B Z h) ≫ q.hom =
      z.hom ≫ cokernel.π (Subobject.ofLE B' Z' h') := by
    simp only [q, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]
  exact congrArg (fun f => f.hom a) hq

end KIP126.Core.SpectralSequence
