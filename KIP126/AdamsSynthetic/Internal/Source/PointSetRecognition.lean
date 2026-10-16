module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Recognition
import all KIP126.AdamsSynthetic.Internal.Source.PointSet

@[expose] section

/-!
# Recognition of the actual source cones and tensor generators

The tensor condition here concerns suspension spectra of actual good based
spaces, with the compactly generated reduced smash and its actual maps. It
does not claim an arbitrary-prespectrum derived smash or its descent through
stable equivalences. That full extension is a separate construction task.

The cofiber condition compares the selected cofiber with the explicit mapping
cone, including its actual inclusion and boundary. No freely chosen cone or
smash object is introduced as source data.
-/

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v

namespace SourceRecognition

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  {H : ModTwoCoefficients C} (R : SourceRecognition C H)

noncomputable def spaceObj (A : BasedSpace.{0}) : C :=
  R.equivalence.functor.obj (sourceLocalization.obj (Prespectrum.suspensionSpectrum A))

noncomputable def spaceMap {A B : BasedSpace.{0}} (f : A ⟶ B) : R.spaceObj A ⟶ R.spaceObj B :=
  R.equivalence.functor.map (sourceLocalization.map (Prespectrum.suspensionSpectrumMap f))

/-- The unit isomorphism uses the same actual suspension spectrum of the
discrete based two-point space and the fixed source sphere comparison. -/
noncomputable def spaceUnit : R.spaceObj BasedSpace.zeroSphere ≅ SphereSpectrum :=
  R.equivalence.functor.mapIso (sourceLocalization.mapIso
    (eqToIso Prespectrum.suspensionSpectrum_zeroSphere)) ≪≫ R.sphereIso

end SourceRecognition

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  {H : ModTwoCoefficients C}

/-- Recognition of the selected tensor on good suspension-spectrum
generators only. Full derived-smash extension is not asserted by this type. -/
structure SourceGeneratorTensorRecognition (R : SourceRecognition C H) where
  smash : ∀ (A B : BasedSpace.{0}), A.IsGood → B.IsGood →
    (R.spaceObj A ⊗ R.spaceObj B ≅ R.spaceObj (A.smash B))
  natural : ∀ {A B A' B' : BasedSpace.{0}} (f : A ⟶ A') (g : B ⟶ B')
      (hA : A.IsGood) (hB : B.IsGood) (hA' : A'.IsGood) (hB' : B'.IsGood),
    (R.spaceMap f ⊗ₘ R.spaceMap g) ≫ (smash A' B' hA' hB').hom =
      (smash A B hA hB).hom ≫ R.spaceMap (BasedSpace.smashMap f g)
  unit : ∀ (A : BasedSpace.{0}) (hA : A.IsGood),
    (smash BasedSpace.zeroSphere A BasedSpace.good_zeroSphere hA).hom ≫
      R.spaceMap (BasedSpace.smashUnit A hA) =
        (R.spaceUnit.hom ▷ R.spaceObj A) ≫ (λ_ (R.spaceObj A)).hom

/-- Recognition of the actual reduced mapping cone for well-based inputs,
including the same inclusion and connecting map as the fixed cofiber. -/
structure SourceCofiberRecognition [HasFunctorialCofiber (C := C)]
    (R : SourceRecognition C H) where
  cone : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y),
    X.IsWellBased → Y.IsWellBased →
      (R.equivalence.functor.obj (sourceLocalization.obj (Prespectrum.cone f)) ≅
        HasFunctorialCofiber.cofib
          (R.equivalence.functor.map (sourceLocalization.map f)))
  inclusion : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y)
      (hX : X.IsWellBased) (hY : Y.IsWellBased),
    R.equivalence.functor.map (sourceLocalization.map (Prespectrum.coneInclusion f)) ≫
      (cone f hX hY).hom =
        HasFunctorialCofiber.cofibι (R.equivalence.functor.map (sourceLocalization.map f))
  boundary : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y)
      (hX : X.IsWellBased) (hY : Y.IsWellBased),
    R.equivalence.functor.map (sourceLocalization.map (Prespectrum.coneBoundary f)) ≫
      (R.suspensionIso X hX).hom =
        (cone f hX hY).hom ≫
          HasFunctorialCofiber.cofibδ
            (R.equivalence.functor.map (sourceLocalization.map f))

end KIP126.AdamsSynthetic.Source
