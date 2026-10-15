module

public import KIP126.Def.StableHomotopy.Spectra.Completion
public import KIP126.Def.StableHomotopy.Cohomology.Data

@[expose] public section

/-! Identification of the classical stable category with an explicit
point-set stable localization. The source sphere, suspension, cone and maps
are the constructions in `PointSet`; there is no `isActualSpectrum : Prop`
slot and no input differential, permanent cycle, or Kervaire conclusion. -/

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory MonoidalCategory
open KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]

/-- Comparison of the completed prespectrum category with the stable category. In addition to the
category equivalence, the selected shifts and cofibers must match the actual
point-set suspension and mapping-cone sequence, including both arrows.
The homotopy comparison is natural for the actual point-set maps.

`HF2` is identified via its supplied homotopy groups, this recognition of
integer stable homotopy of the specified local replacement, and its unit.
The sphere is the completion of the ordinary point-set sphere under the
specified reflection `Q`; every comparison uses this same reflection. -/
structure SourceComparison (Q : CompletionModel) (H : Mod2EilenbergMacLane (C := C)) where
  equivalence : CompletedSpectrum ≌ C
  sphere : equivalence.functor.obj (Q.localization.obj Prespectrum.sphere) ≅ SphereSpectrum
  suspension : ∀ X : Prespectrum.{0}, X.IsWellBased →
    (equivalence.functor.obj (Q.localization.obj X.suspension) ≅
      (shiftFunctor C (1 : ℤ)).obj (equivalence.functor.obj (Q.localization.obj X)))
  suspension_natural : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y)
      (hX : X.IsWellBased) (hY : Y.IsWellBased),
    equivalence.functor.map (Q.localization.map (Prespectrum.suspensionMap f)) ≫
      (suspension Y hY).hom =
        (suspension X hX).hom ≫
          (shiftFunctor C (1 : ℤ)).map (equivalence.functor.map (Q.localization.map f))
  cofiber : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y), X.IsWellBased → Y.IsWellBased →
    (equivalence.functor.obj (Q.localization.obj (Prespectrum.cone f)) ≅
      HasFunctorialCofiber.cofib (equivalence.functor.map (Q.localization.map f)))
  cofiber_inclusion : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y)
      (hX : X.IsWellBased) (hY : Y.IsWellBased),
    equivalence.functor.map (Q.localization.map (Prespectrum.coneInclusion f)) ≫
      (cofiber f hX hY).hom =
        HasFunctorialCofiber.cofibι (equivalence.functor.map (Q.localization.map f))
  cofiber_boundary : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y)
      (hX : X.IsWellBased) (hY : Y.IsWellBased),
    equivalence.functor.map (Q.localization.map (Prespectrum.coneBoundary f)) ≫
      (suspension X hX).hom =
        (cofiber f hX hY).hom ≫
          HasFunctorialCofiber.cofibδ (equivalence.functor.map (Q.localization.map f))
  homotopy : ∀ (X : Prespectrum.{0}) (d : ℤ),
    HomotopyGroup d (equivalence.functor.obj (Q.localization.obj X)) ≃
      Prespectrum.StableHomotopy (Q.replacement.obj X) d
  homotopy_natural : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y) (d : ℤ)
      (a : HomotopyGroup d (equivalence.functor.obj (Q.localization.obj X))),
    homotopy Y d (a ≫ equivalence.functor.map (Q.localization.map f)) =
      Prespectrum.stableHomotopyMap (Q.replacement.map f) d (homotopy X d a)
  /-- Addition is the actual loop concatenation in the local replacement. -/
  homotopy_add : ∀ (X : Prespectrum.{0}) (d : ℤ) (n r : ℕ)
      (h : ((r+1 : ℕ) : ℤ) = d + n)
      (p q : GenLoop (Fin (r+1)) ((Q.replacement.obj X).level n)
        ((Q.replacement.obj X).level n).point),
    (homotopy X d).symm (Prespectrum.loopClass _ d n (r+1) h
        (GenLoop.transAt 0 p q)) =
      (homotopy X d).symm (Prespectrum.loopClass _ d n (r+1) h p) +
      (homotopy X d).symm (Prespectrum.loopClass _ d n (r+1) h q)
  /-- The chosen sphere isomorphism sends its identity to the positive
  point-set generator followed by the actual completion unit. -/
  sphere_identity : homotopy Prespectrum.sphere 0
      ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ sphere.inv) =
    Prespectrum.stableHomotopyMap (Q.unit.app Prespectrum.sphere) 0
      Prespectrum.sphereGenerator
  hf2Iso : equivalence.functor.obj (Q.localization.obj sourceHF2.spectrum) ≅ H.HF2
  /-- The target's chosen π₀(HF₂) coordinate is the actual source F₂
  coordinate followed through completion and this same object comparison. -/
  hf2_pi0 : ∀ x : Prespectrum.StableHomotopy sourceHF2.spectrum 0,
    H.pi0Equiv ((homotopy sourceHF2.spectrum 0).symm
      (Prespectrum.stableHomotopyMap (Q.unit.app sourceHF2.spectrum) 0 x) ≫
        hf2Iso.hom) = sourceHF2.pi0 x
  unit : Q.localization.obj Prespectrum.sphere ⟶ Q.localization.obj sourceHF2.spectrum
  unit_eq : equivalence.functor.map unit ≫ hf2Iso.hom = sphere.hom ≫ H.unit

end KIP126.StableHomotopy.Spectra
