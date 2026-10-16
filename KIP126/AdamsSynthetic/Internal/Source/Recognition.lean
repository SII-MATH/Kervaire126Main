module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Sphere
import KIP126.AdamsSynthetic.Context

@[expose] section

/-!
# Recognition of the fixed classical background by its concrete source

This is a mathematical comparison with the ordinary stable localization of
the explicit sequential prespectra. It does not redefine that localization
as a completed category. Every comparison uses the same equivalence, actual
point-set maps, and the selected coefficient object and unit.

The record contains no Adams page, differential, named Adams class, survival
claim, cofiber comparison, or tensor comparison. The latter two require their
own actual source constructions.
-/

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory Topology KIP126.StableHomotopy
open scoped Topology

universe u v

/-- Recognition of one background by the explicit ordinary stable source,
including its sphere, shifts, integer stable homotopy, and mod-two unit. -/
structure SourceRecognition (C : Type u) [StableHomotopyCategory.{u,v} C]
    (H : ModTwoCoefficients C) where
  equivalence : SourceCategory.{0} ≌ C
  sphereIso : equivalence.functor.obj (sourceLocalization.obj Prespectrum.sphere) ≅
    SphereSpectrum
  suspensionIso : ∀ (X : Prespectrum.{0}), X.IsWellBased →
    (equivalence.functor.obj (sourceLocalization.obj X.suspension) ≅
      (shiftFunctor C (1 : ℤ)).obj
        (equivalence.functor.obj (sourceLocalization.obj X)))
  suspension_natural : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y)
      (hX : X.IsWellBased) (hY : Y.IsWellBased),
    equivalence.functor.map (sourceLocalization.map (Prespectrum.suspensionMap f)) ≫
      (suspensionIso Y hY).hom =
        (suspensionIso X hX).hom ≫ (shiftFunctor C (1 : ℤ)).map
          (equivalence.functor.map (sourceLocalization.map f))
  desuspensionIso : ∀ X : Prespectrum.{0},
    equivalence.functor.obj (sourceLocalization.obj X.desuspension) ≅
      (shiftFunctor C (-1 : ℤ)).obj
        (equivalence.functor.obj (sourceLocalization.obj X))
  desuspension_natural : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y),
    equivalence.functor.map (sourceLocalization.map (Prespectrum.desuspensionMap f)) ≫
      (desuspensionIso Y).hom =
        (desuspensionIso X).hom ≫ (shiftFunctor C (-1 : ℤ)).map
          (equivalence.functor.map (sourceLocalization.map f))
  homotopy : ∀ (X : Prespectrum.{0}) (d : ℤ),
    HomotopyGroup d (equivalence.functor.obj (sourceLocalization.obj X)) ≃
      Prespectrum.StableHomotopy X d
  homotopy_natural : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y) (d : ℤ)
      (a : HomotopyGroup d (equivalence.functor.obj (sourceLocalization.obj X))),
    homotopy Y d (a ≫ equivalence.functor.map (sourceLocalization.map f)) =
      Prespectrum.stableHomotopyMap f d (homotopy X d a)
  homotopy_zero : ∀ (X : Prespectrum.{0}) (d : ℤ) (n r : ℕ)
      (h : (r : ℤ) = d + n),
    homotopy X d 0 = Prespectrum.loopClass X d n r h GenLoop.const
  /-- Stable addition is the actual concatenation of cubical loops. Two
  coordinates ensure the displayed representative lies in the abelian range. -/
  homotopy_add : ∀ (X : Prespectrum.{0}) (d : ℤ) (n r : ℕ)
      (h : ((r + 2 : ℕ) : ℤ) = d + n)
      (p q : GenLoop (Fin (r + 2)) (X.level n) (X.level n).point),
    (homotopy X d).symm
        (Prespectrum.loopClass X d n (r + 2) h (GenLoop.transAt 0 p q)) =
      (homotopy X d).symm (Prespectrum.loopClass X d n (r + 2) h p) +
        (homotopy X d).symm (Prespectrum.loopClass X d n (r + 2) h q)
  /-- The identity of the selected sphere has the actual positive point-set
  generator, fixing the normalization of the source sphere comparison. -/
  sphere_identity : homotopy Prespectrum.sphere 0
      ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ sphereIso.inv) =
    Prespectrum.sphereGenerator
  sourceHF2 : Prespectrum.{0}
  sourceHF2Pi0 : Prespectrum.StableHomotopy sourceHF2 0 ≃ ZMod 2
  sourceHF2Vanishes : ∀ d : ℤ, d ≠ 0 →
    Subsingleton (Prespectrum.StableHomotopy sourceHF2 d)
  hf2Iso : equivalence.functor.obj (sourceLocalization.obj sourceHF2) ≅ H.object
  /-- The source coefficient coordinate is the selected target coordinate on
  the same homotopy comparison, not a separately named two-element set. -/
  hf2_pi0 : ∀ a : HomotopyGroup 0
      (equivalence.functor.obj (sourceLocalization.obj sourceHF2)),
    H.pi0Equiv (a ≫ hf2Iso.hom) = sourceHF2Pi0 (homotopy sourceHF2 0 a)
  sourceUnit : Prespectrum.sphere ⟶ sourceHF2
  /-- The actual point-set unit represents this same selected coefficient
  unit under the fixed sphere and coefficient comparisons. -/
  unit_compat : equivalence.functor.map (sourceLocalization.map sourceUnit) ≫
      hf2Iso.hom = sphereIso.hom ≫ H.unit

namespace SourceRecognition

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  {H : ModTwoCoefficients C} (R : SourceRecognition C H)

/-- The coefficient zero coordinate is forced by the same target zero and
the same homotopy comparison; it is not a further field to be supplied. -/
theorem sourceHF2Pi0_zero (n r : ℕ) (h : (r : ℤ) = (0 : ℤ) + n) :
    R.sourceHF2Pi0 (Prespectrum.loopClass R.sourceHF2 0 n r h GenLoop.const) = 0 := by
  rw [← R.homotopy_zero R.sourceHF2 0 n r h, ← R.hf2_pi0]
  simp

/-- The chosen actual source unit sends the actual positive sphere generator
to the coefficient one in the same specified coordinate. -/
theorem sourceUnit_pi0 :
    R.sourceHF2Pi0 (Prespectrum.stableHomotopyMap R.sourceUnit 0
      Prespectrum.sphereGenerator) = 1 := by
  let a : HomotopyGroup 0 (R.equivalence.functor.obj
      (sourceLocalization.obj Prespectrum.sphere)) :=
    (shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ R.sphereIso.inv
  have ha : R.homotopy Prespectrum.sphere 0 a = Prespectrum.sphereGenerator :=
    R.sphere_identity
  rw [← ha, ← R.homotopy_natural R.sourceUnit 0 a, ← R.hf2_pi0]
  simp [a, Category.assoc, R.unit_compat, ModTwoCoefficients.unit]
  rw [← Category.assoc]
  erw [Iso.hom_inv_id_app]
  rw [Category.id_comp]
  exact H.pi0Equiv.apply_symm_apply 1

end SourceRecognition

end KIP126.AdamsSynthetic.Source
