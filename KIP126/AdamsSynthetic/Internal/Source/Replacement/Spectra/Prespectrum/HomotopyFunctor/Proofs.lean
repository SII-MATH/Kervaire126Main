module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/HomotopyFunctor/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.HomotopyFunctor.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory TypeCat

universe u

@[simp] theorem sourceStableHomotopyFunctor_fac (d : ℤ) :
    sourceLocalization ⋙ sourceStableHomotopyFunctor.{u} d =
      Prespectrum.stableHomotopyFunctor d :=
  Localization.Construction.fac _ _

/-- On an actual point-set map, the descended functor is the originally
specified map of the cubical stable quotient. -/
@[simp] theorem sourceStableHomotopyFunctor_map
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) (d : ℤ) :
    (sourceStableHomotopyFunctor d).map (sourceLocalization.map f) =
      ofHom (Prespectrum.stableHomotopyMap f d) := by
  have h : ∀ (F G : Prespectrum.{u} ⥤ Type u), F = G → HEq (F.map f) (G.map f) := by
    intro F G h
    cases h
    rfl
  exact eq_of_heq (h _ _ (sourceStableHomotopyFunctor_fac d))

/-- The original definition of stable equivalence is saturated on
point-set maps by the specified ordinary localization. -/
theorem Prespectrum.stableEquivalence_iff_source_isIso
    {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences f ↔ IsIso (sourceLocalization.map f) := by
  constructor
  · exact stableEquivalences.Q_inverts f
  · intro hf d
    letI := hf
    have hi : IsIso ((sourceStableHomotopyFunctor d).map (sourceLocalization.map f)) :=
      inferInstance
    rw [sourceStableHomotopyFunctor_map] at hi
    exact (bijective_iff_isIso_ofHom _).mpr hi

/-- In particular, source isomorphisms preserve actual stable vanishing. -/
theorem Prespectrum.stableHomotopy_subsingleton_of_source_iso
    {X Y : Prespectrum.{u}} (e : sourceLocalization.obj X ≅ sourceLocalization.obj Y)
    (d : ℤ) [Subsingleton (X.StableHomotopy d)] : Subsingleton (Y.StableHomotopy d) :=
  (stableHomotopyEquivOfSourceIso e d).symm.injective.subsingleton

end KIP126.AdamsSynthetic.Source
