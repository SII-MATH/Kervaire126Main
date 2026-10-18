module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Recognition
import Mathlib.CategoryTheory.Localization.Construction

@[expose] section

/-!
# HF₂ cohomology localization of the same recognized ordinary source

Every detector is the inverse image of an integer shift of the same selected
HF₂ object under the same source equivalence. This uses the recognized stable
shift, without asserting that an unrestricted point-set reduced suspension is
a derived suspension. A morphism is inverted precisely when precomposition
induces a bijection into every one of these fixed integer detectors.

The category below is the actual categorical localization at that explicit
class of maps. Its definition does not identify this localization with a
reflective subcategory, Moore(2)-completion, or the paper's completion of
connective spectra of finite type; those require further comparison proofs.
-/

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory KIP126.StableHomotopy

universe u v

noncomputable section

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  {H : ModTwoCoefficients C}

/-- A fixed integer-shifted HF₂ detector in the actual ordinary source. -/
def shiftedHF2 (R : SourceRecognition C H) (d : ℤ) : SourceCategory.{0} :=
  R.equivalence.inverse.obj ((shiftFunctor C d).obj H.object)

def shiftedHF2Iso (R : SourceRecognition C H) (d : ℤ) :
    R.equivalence.functor.obj (shiftedHF2 R d) ≅ (shiftFunctor C d).obj H.object :=
  R.equivalence.counitIso.app _

/-- Equivalences detected by cohomology into every shift of the same HF₂. -/
def HF2Equivalences (R : SourceRecognition C H) : MorphismProperty SourceCategory.{0} :=
  fun _X Y f => ∀ d : ℤ,
    Function.Bijective (fun a : Y ⟶ shiftedHF2 R d => f ≫ a)

/-- The localization is a prescribed construction, not an arbitrary category
supplied with a completion label. -/
abbrev HF2LocalizedSource (R : SourceRecognition C H) := (HF2Equivalences R).Localization

abbrev hf2Localization (R : SourceRecognition C H) :
    SourceCategory.{0} ⥤ HF2LocalizedSource R := (HF2Equivalences R).Q

def completedSphere (R : SourceRecognition C H) : HF2LocalizedSource R :=
  (hf2Localization R).obj (sourceLocalization.obj Prespectrum.sphere)

end

end KIP126.AdamsSynthetic.Source
