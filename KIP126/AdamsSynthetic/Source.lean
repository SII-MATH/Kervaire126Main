module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

public import KIP126.AdamsSynthetic.Context
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Localization.Predicate

import all KIP126.AdamsSynthetic.Internal.Source.Recognition
import all KIP126.AdamsSynthetic.Internal.Source.PointSetRecognition
import all KIP126.AdamsSynthetic.Internal.Source.Completion
import all KIP126.AdamsSynthetic.Internal.Source.DerivedSmash
import all KIP126.AdamsSynthetic.Internal.Milnor.Cohomology

/-! Concrete mathematical sources for the fixed Adams interfaces.
The ordinary sequential-prespectrum source is kept distinct from completion.
Milnor cohomology is the quotient for the specified polynomial differential;
it is not an arbitrarily supplied graded object or a renamed Ext group.
Only the source names needed to state fixed-background recognition are public.
-/

@[expose] section
namespace KIP126.AdamsSynthetic
open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v

@[no_expose] public def ClassicalPrespectrum : Type 1 := Source.Prespectrum.{0}
@[no_expose] public noncomputable instance classicalPrespectrumCategory : Category ClassicalPrespectrum :=
  inferInstanceAs (Category Source.Prespectrum.{0})
@[no_expose] public def ClassicalSource : Type 1 := Source.SourceCategory.{0}
@[no_expose] public noncomputable instance classicalSourceCategory : Category ClassicalSource :=
  inferInstanceAs (Category Source.SourceCategory.{0})
@[no_expose] public noncomputable def classicalSourceLocalization : ClassicalPrespectrum ⥤ ClassicalSource :=
  Source.sourceLocalization
@[no_expose] public noncomputable def classicalSpherePrespectrum : ClassicalPrespectrum := Source.Prespectrum.sphere
public noncomputable def classicalSourceSphere : ClassicalSource :=
  classicalSourceLocalization.obj classicalSpherePrespectrum
@[no_expose] public def classicalStableHomotopy (X : ClassicalPrespectrum) (d : ℤ) : Type :=
  Source.Prespectrum.StableHomotopy X d

/-- Genuine source recognition, including the same sphere, integer homotopy,
actual cubical addition, HF₂ coordinate and its normalized unit. It contains
no Adams page, named class or paper conclusion. -/
@[no_expose] public def ClassicalSourceRecognition (C : Type u) [StableHomotopyCategory.{u,v} C]
    (H : ModTwoCoefficients C) : Type (max 1 (max u v)) := Source.SourceRecognition C H

@[no_expose] public def ClassicalSourceGeneratorTensorRecognition
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) : Type (max 1 v) :=
  Source.SourceGeneratorTensorRecognition R

@[no_expose] public def ClassicalSourceCofiberRecognition
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
    {H : ModTwoCoefficients C} (R : ClassicalSourceRecognition C H) :
    Type (max 1 v) := Source.SourceCofiberRecognition R

@[no_expose] public noncomputable def classicalStableHomotopyMap {X Y : ClassicalPrespectrum}
    (f : X ⟶ Y) (d : ℤ) : classicalStableHomotopy X d → classicalStableHomotopy Y d :=
  Source.Prespectrum.stableHomotopyMap f d

@[no_expose] public def classicalSphereGenerator :
    classicalStableHomotopy classicalSpherePrespectrum 0 := Source.Prespectrum.sphereGenerator

namespace ClassicalSourceRecognition

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  {H : ModTwoCoefficients C} (R : ClassicalSourceRecognition C H)

@[no_expose] public noncomputable def equivalence : ClassicalSource ≌ C :=
  Source.SourceRecognition.equivalence R

@[no_expose] public noncomputable def sphereIso :
    R.equivalence.functor.obj classicalSourceSphere ≅ SphereSpectrum :=
  Source.SourceRecognition.sphereIso R

@[no_expose] public noncomputable def homotopy (X : ClassicalPrespectrum) (d : ℤ) :
    HomotopyGroup d (R.equivalence.functor.obj (classicalSourceLocalization.obj X)) ≃
      classicalStableHomotopy X d := Source.SourceRecognition.homotopy R X d

public theorem homotopy_natural {X Y : ClassicalPrespectrum} (f : X ⟶ Y) (d : ℤ)
    (a : HomotopyGroup d (R.equivalence.functor.obj (classicalSourceLocalization.obj X))) :
    R.homotopy Y d (a ≫ R.equivalence.functor.map (classicalSourceLocalization.map f)) =
      classicalStableHomotopyMap f d (R.homotopy X d a) :=
  Source.SourceRecognition.homotopy_natural R f d a

public theorem sphere_identity : R.homotopy classicalSpherePrespectrum 0
    ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ R.sphereIso.inv) =
      classicalSphereGenerator := Source.SourceRecognition.sphere_identity R

@[no_expose] public noncomputable def coefficientPrespectrum : ClassicalPrespectrum :=
  Source.SourceRecognition.sourceHF2 R

@[no_expose] public noncomputable def coefficientPi0 :
    classicalStableHomotopy R.coefficientPrespectrum 0 ≃ ZMod 2 :=
  Source.SourceRecognition.sourceHF2Pi0 R

public theorem coefficientVanishing (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (classicalStableHomotopy R.coefficientPrespectrum d) :=
  Source.SourceRecognition.sourceHF2Vanishes R d hd

@[no_expose] public noncomputable def coefficientIso :
    R.equivalence.functor.obj (classicalSourceLocalization.obj R.coefficientPrespectrum) ≅
      H.object := Source.SourceRecognition.hf2Iso R

public theorem coefficient_pi0 (a : HomotopyGroup 0
    (R.equivalence.functor.obj (classicalSourceLocalization.obj R.coefficientPrespectrum))) :
    H.pi0Equiv (a ≫ R.coefficientIso.hom) =
      R.coefficientPi0 (R.homotopy R.coefficientPrespectrum 0 a) :=
  Source.SourceRecognition.hf2_pi0 R a

@[no_expose] public noncomputable def coefficientUnit :
    classicalSpherePrespectrum ⟶ R.coefficientPrespectrum :=
  Source.SourceRecognition.sourceUnit R

public theorem coefficientUnit_compat :
    R.equivalence.functor.map (classicalSourceLocalization.map R.coefficientUnit) ≫
      R.coefficientIso.hom = R.sphereIso.hom ≫ H.unit :=
  Source.SourceRecognition.unit_compat R

public theorem coefficientUnit_pi0 :
    R.coefficientPi0 (classicalStableHomotopyMap R.coefficientUnit 0 classicalSphereGenerator) = 1 :=
  Source.SourceRecognition.sourceUnit_pi0 R

@[no_expose] public noncomputable def shiftedCoefficient (d : ℤ) : ClassicalSource :=
  Source.shiftedHF2 R d

@[no_expose] public noncomputable def shiftedCoefficientIso (d : ℤ) :
    R.equivalence.functor.obj (R.shiftedCoefficient d) ≅
      (shiftFunctor C d).obj H.object := Source.shiftedHF2Iso R d

end ClassicalSourceRecognition

/-- Exactly the maps whose precomposition maps into every recognized integer
shift of the same HF₂ are bijective. -/
@[no_expose] public def classicalHF2Equivalences
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) : MorphismProperty ClassicalSource :=
  Source.HF2Equivalences R

public theorem classicalHF2Equivalences_iff
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) {X Y : ClassicalSource} (f : X ⟶ Y) :
    classicalHF2Equivalences R f ↔ ∀ d : ℤ,
      Function.Bijective (fun a : Y ⟶ R.shiftedCoefficient d => f ≫ a) := Iff.rfl

/-- The actual categorical localization at this explicit HF₂ cohomology
equivalence class. Identification with a completion model is a separate theorem. -/
@[no_expose] public def ClassicalHF2LocalizedSource
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) : Type 1 := Source.HF2LocalizedSource R

@[no_expose] public noncomputable instance classicalHF2LocalizedSourceCategory
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) : Category (ClassicalHF2LocalizedSource R) :=
  inferInstanceAs (Category (Source.HF2LocalizedSource R))

@[no_expose] public noncomputable def classicalHF2Localization
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) : ClassicalSource ⥤ ClassicalHF2LocalizedSource R :=
  Source.hf2Localization R

public theorem classicalHF2Localization_isLocalization
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) :
    (classicalHF2Localization R).IsLocalization (classicalHF2Equivalences R) := by
  change (Source.hf2Localization R).IsLocalization (Source.HF2Equivalences R)
  infer_instance

public noncomputable def classicalHF2LocalizedSphere
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) : ClassicalHF2LocalizedSource R :=
  (classicalHF2Localization R).obj classicalSourceSphere

@[no_expose] public def ClassicalSourceReplacementData : Type 1 := Source.SourceReplacementData

@[no_expose] public def ClassicalSourceReplacementFlatness
    (P : ClassicalSourceReplacementData) : Prop := Source.SourceReplacementFlatness P

@[no_expose] public def ClassicalSourceDerivedSmashRecognition
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) (P : ClassicalSourceReplacementData) :
    Type (max 1 v) := Source.SourceDerivedSmashRecognition R P

@[no_expose] public def classicalStableEquivalences : MorphismProperty ClassicalPrespectrum :=
  Source.Prespectrum.stableEquivalences

@[no_expose] public def classicalPrespectrumIsGood (X : ClassicalPrespectrum) : Prop :=
  Source.Prespectrum.IsGood X

public theorem classicalStableEquivalences_iff {X Y : ClassicalPrespectrum} (f : X ⟶ Y) :
    classicalStableEquivalences f ↔
      ∀ d : ℤ, Function.Bijective (classicalStableHomotopyMap f d) := Iff.rfl

@[no_expose] public noncomputable def classicalDerivedSmash
    (P : ClassicalSourceReplacementData) (X Y : ClassicalPrespectrum) : ClassicalPrespectrum :=
  Source.SourceReplacementData.derivedSmash P X Y

@[no_expose] public noncomputable def classicalDerivedSmashMap
    (P : ClassicalSourceReplacementData) {X Y X' Y' : ClassicalPrespectrum}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    classicalDerivedSmash P X Y ⟶ classicalDerivedSmash P X' Y' :=
  Source.SourceReplacementData.derivedSmashMap P f g

public theorem classicalSourceReplacementFlatness_apply (P : ClassicalSourceReplacementData)
    (hP : ClassicalSourceReplacementFlatness P) {X Y X' Y' : ClassicalPrespectrum}
    (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : classicalStableEquivalences f) (hg : classicalStableEquivalences g) :
    classicalStableEquivalences (classicalDerivedSmashMap P f g) := hP f g hf hg

namespace ClassicalSourceReplacementData

@[no_expose] public noncomputable def replacement (P : ClassicalSourceReplacementData) :
    ClassicalPrespectrum ⥤ ClassicalPrespectrum := Source.SourceReplacementData.replacement P

@[no_expose] public noncomputable def comparison (P : ClassicalSourceReplacementData) :
    P.replacement ⟶ 𝟭 ClassicalPrespectrum := Source.SourceReplacementData.comparison P

public theorem comparison_stable (P : ClassicalSourceReplacementData) (X : ClassicalPrespectrum) :
    classicalStableEquivalences (P.comparison.app X) := Source.SourceReplacementData.stable P X

public theorem replacement_good (P : ClassicalSourceReplacementData) (X : ClassicalPrespectrum) :
    classicalPrespectrumIsGood (P.replacement.obj X) := Source.SourceReplacementData.good P X

end ClassicalSourceReplacementData

namespace ClassicalSourceDerivedSmashRecognition

variable {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
  {R : ClassicalSourceRecognition C H} {P : ClassicalSourceReplacementData}
  (D : ClassicalSourceDerivedSmashRecognition R P)

@[no_expose] public noncomputable def comparison (X Y : ClassicalPrespectrum) :
    (R.equivalence.functor.obj (classicalSourceLocalization.obj X) ⊗
      R.equivalence.functor.obj (classicalSourceLocalization.obj Y) ≅
        R.equivalence.functor.obj
          (classicalSourceLocalization.obj (classicalDerivedSmash P X Y))) :=
  Source.SourceDerivedSmashRecognition.comparison D X Y

public theorem natural {X Y X' Y' : ClassicalPrespectrum} (f : X ⟶ X') (g : Y ⟶ Y') :
    (R.equivalence.functor.map (classicalSourceLocalization.map f) ⊗ₘ
        R.equivalence.functor.map (classicalSourceLocalization.map g)) ≫
      (D.comparison X' Y').hom =
        (D.comparison X Y).hom ≫ R.equivalence.functor.map
          (classicalSourceLocalization.map (classicalDerivedSmashMap P f g)) :=
  Source.SourceDerivedSmashRecognition.natural D f g

end ClassicalSourceDerivedSmashRecognition

@[no_expose] public def MilnorCochains (s t : ℕ) : Type := Milnor.cochains s t
@[no_expose] public def MilnorCohomology (s t : ℕ) : Type := Milnor.Cohomology s t

@[no_expose] public noncomputable instance milnorCochainsAddCommGroup (s t : ℕ) :
    AddCommGroup (MilnorCochains s t) := inferInstanceAs (AddCommGroup (Milnor.cochains s t))
@[no_expose] public noncomputable instance milnorCochainsIntModule (s t : ℕ) :
    Module ℤ (MilnorCochains s t) := inferInstanceAs (Module ℤ (Milnor.cochains s t))
@[no_expose] public noncomputable instance milnorCohomologyAddCommGroup (s t : ℕ) :
    AddCommGroup (MilnorCohomology s t) := inferInstanceAs (AddCommGroup (Milnor.Cohomology s t))
@[no_expose] public noncomputable instance milnorCohomologyIntModule (s t : ℕ) :
    Module ℤ (MilnorCohomology s t) := inferInstanceAs (Module ℤ (Milnor.Cohomology s t))

@[no_expose] public noncomputable def milnorDifferential (s t : ℕ) :
    MilnorCochains s t →ₗ[ℤ] MilnorCochains (s + 1) t :=
  (Milnor.differential s t).restrictScalars ℤ

public theorem milnorDifferential_squared (s t : ℕ) (x : MilnorCochains s t) :
    milnorDifferential (s + 1) t (milnorDifferential s t x) = 0 :=
  Milnor.differential_squared s t x

@[no_expose] public noncomputable def milnorClassOfCycle {s t : ℕ} (x : MilnorCochains s t)
    (hx : milnorDifferential s t x = 0) : MilnorCohomology s t :=
  Milnor.classOfCycle x hx

@[no_expose] public noncomputable def milnorHiClass (i : ℕ) : MilnorCohomology 1 (2 ^ i) :=
  Milnor.hiClass i
@[no_expose] public noncomputable def milnorHiSquareClass (i : ℕ) :
    MilnorCohomology 2 (2 ^ (i + 1)) := Milnor.hiSquareClass i
@[no_expose] public noncomputable def milnorUnitClass : MilnorCohomology 0 0 := Milnor.unitClass
@[no_expose] public noncomputable def milnorCup {s t s' t' : ℕ}
    (x : MilnorCohomology s t) (y : MilnorCohomology s' t') :
    MilnorCohomology (s + s') (t + t') := Milnor.cohomologyCup x y

end KIP126.AdamsSynthetic
