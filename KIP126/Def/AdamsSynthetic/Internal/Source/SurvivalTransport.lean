module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
-/

import KIP126.Def.SpectralSequence

/-! Representative-level transport used by the fixed classical-source comparison.
An isomorphism here includes the ambient maps and preservation of every cycle
and boundary subobject, including infinity; an E₂ isomorphism alone is not used. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Internal.Source

open CategoryTheory KIP126.Core.SpectralSequence

universe v

private def NonzeroRepresentativeAt (D : SSData (ModuleCat.{v} ℤ))
    (n : WithTop ℕ) (x : D.page n) : Prop :=
  ∃ z : (Subobject.underlying.obj (D.Z ⊤) : ModuleCat ℤ),
    (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n) z = x ∧
      D.pageπ ⊤ z ≠ 0

private theorem nonzeroRepresentativeAt_regrade (D : SSData (ModuleCat.{v} ℤ))
    {n n' : WithTop ℕ} (h : n = n') (x : D.page n)
    (hx : NonzeroRepresentativeAt D n x) :
    NonzeroRepresentativeAt D n' (eqToHom (congrArg D.page h) x) := by
  subst n'
  simpa only [eqToHom_refl, ModuleCat.id_apply] using hx

private theorem nonzeroRepresentativeAt_map
    {D D' : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
    (f : SSDataMorphism (ℤ × ℤ) D D') (p : ℤ × ℤ) (n : WithTop ℕ)
    (hinj : Function.Injective (f.pageMap p ⊤)) (x : (D p).page n)
    (hx : NonzeroRepresentativeAt (D p) n x) :
    NonzeroRepresentativeAt (D' p) n (f.pageMap p n x) := by
  obtain ⟨z, hz, hnz⟩ := hx
  simp only [ModuleCat.comp_apply] at hz
  refine ⟨f.cycleMap p ⊤ z, ?_, ?_⟩
  · have h := congrArg (fun m => m z)
      (congrArg (fun m => m ≫ (D' p).pageπ n)
        (f.cycleMap_ofLE p (show n ≤ ⊤ from le_top)))
    simpa only [Category.assoc, ← f.pageπ_pageMap, ModuleCat.comp_apply, hz] using h.symm
  · have h := congrArg (fun m => m z) (f.pageπ_pageMap p ⊤)
    intro hzero
    apply hnz
    apply hinj
    simpa only [ModuleCat.comp_apply, hzero, map_zero] using h

private theorem nonzeroSurvival_map_of_injective
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    (f : E ⟶ E') (p : ℤ × ℤ)
    (hinj : Function.Injective (f.eInftyMap p)) (x : E.Page 2 p)
    (hx : NonzeroSurvival E p x) :
    NonzeroSurvival E' p (f.pageMap 2 p x) := by
  have h := nonzeroRepresentativeAt_map f.toSSDataMorphism p
    (↑(2 - E.r₀).toNat) hinj x hx
  change NonzeroRepresentativeAt (E'.ssData p) (↑(2 - E'.r₀).toNat)
    (f.toSSDataMorphism.pageMapAt f.r₀_eq 2 p x)
  unfold SSDataMorphism.pageMapAt
  have hn : (↑(2 - E.r₀).toNat : WithTop ℕ) = ↑(2 - E'.r₀).toNat := by rw [f.r₀_eq]
  simpa only [ModuleCat.comp_apply] using
    nonzeroRepresentativeAt_regrade (E'.ssData p) hn _ h

private theorem eInftyMap_iso_injective
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    (e : E ≅ E') (p : ℤ × ℤ) : Function.Injective (e.hom.eInftyMap p) := by
  intro x y h
  have hcomp := congrArg (fun f => f x)
    (congrArg (fun f : E ⟶ E => f.eInftyMap p) e.hom_inv_id)
  have hcomp' := congrArg (fun f => f y)
    (congrArg (fun f : E ⟶ E => f.eInftyMap p) e.hom_inv_id)
  simp only [SpectralSequenceMorphism.eInftyMap_comp,
    SpectralSequenceMorphism.eInftyMap_id, ModuleCat.comp_apply,
    ModuleCat.id_apply] at hcomp hcomp'
  exact hcomp.symm.trans ((congrArg (e.inv.eInftyMap p) h).trans hcomp')

private theorem nonzeroSurvival_iso_iff
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    (e : E ≅ E') (p : ℤ × ℤ) (x : E.Page 2 p) :
    NonzeroSurvival E' p (e.hom.pageMap 2 p x) ↔ NonzeroSurvival E p x := by
  constructor
  · intro hx
    have h := nonzeroSurvival_map_of_injective e.inv p
      (eInftyMap_iso_injective e.symm p) _ hx
    have hinverse := congrArg (fun f => f x)
      (congrArg (fun f : E ⟶ E => f.pageMap 2 p) e.hom_inv_id)
    simp only [SpectralSequenceMorphism.pageMap_comp,
      SpectralSequenceMorphism.pageMap_id, ModuleCat.comp_apply,
      ModuleCat.id_apply] at hinverse
    simpa only [hinverse] using h
  · exact nonzeroSurvival_map_of_injective e.hom p (eInftyMap_iso_injective e p) x

end KIP126.AdamsSynthetic.Internal.Source
