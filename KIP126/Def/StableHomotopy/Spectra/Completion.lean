module

public import KIP126.Def.StableHomotopy.Spectra.Generators
public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Stability.Proofs
public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.StableHomotopy.Equivalence
public import KIP126.Def.StableHomotopy.Spectra.HF2.Simplicial.CW.Proofs
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! A concrete HF₂-local source. Ordinary sequential spectra and stable
weak equivalences are already fixed. An Eilenberg–Mac Lane spectrum is
specified by its actual stable homotopy groups, including loop addition.
Equivalences detected by all its integer cohomology groups define the
HF₂ localization. The reflection's existence is an explicit standard
background assumption for the Section 7 proof. The hopfAndDetector S[1/2]
construction separately defines the
Moore(2)-completeness predicate; no comparison between the two notions of
completion is established here. -/
namespace KIP126.StableHomotopy.Spectra
open CategoryTheory _root_.Topology
open scoped unitInterval




/-- Exact Eilenberg–Mac Lane characterization in the ordinary source.
The equivalence respects the actual cubical concatenation and zero, so it
is not an arbitrary two-element set identified with F₂. -/
structure SourceHF2Model where
  spectrum : Prespectrum.{0}
  good : ∀ n, (spectrum.level n).IsGood
  pi0 : Prespectrum.StableHomotopy spectrum 0 ≃ ZMod 2
  pi0_zero : pi0 (Prespectrum.loopClass spectrum 0 0 0 (by simp) GenLoop.const) = 0
  pi0_add : ∀ (n : ℕ)
      (p q : GenLoop (Fin (n+1)) (spectrum.level (n+1)) (spectrum.level (n+1)).point),
    pi0 (Prespectrum.loopClass spectrum 0 (n+1) (n+1) (by omega)
        (GenLoop.transAt 0 p q)) =
      pi0 (Prespectrum.loopClass spectrum 0 (n+1) (n+1) (by omega) p) +
      pi0 (Prespectrum.loopClass spectrum 0 (n+1) (n+1) (by omega) q)
  vanishes : ∀ d : ℤ, d ≠ 0 → Subsingleton (Prespectrum.StableHomotopy spectrum d)

/-- The fixed source coefficient is the actual Dold--Kan realization with
its proved geometric bonds and normalized stable coefficient equivalence. -/
noncomputable def sourceHF2 : SourceHF2Model where
  spectrum := hf2RealizationPrespectrum
  good := hf2RealizationLevel_isGood
  pi0 := HF2Bond.coefficientStableZeroEquiv HF2Bond.bondHomotopyMap_bijective
  pi0_zero := HF2Bond.coefficientStableZeroEquiv_zero HF2Bond.bondHomotopyMap_bijective
  pi0_add := HF2Bond.coefficientStableZeroEquiv_add HF2Bond.bondHomotopyMap_bijective
  vanishes := HF2Bond.coefficientStableHomotopy_subsingleton_of_ne
    HF2Bond.bondHomotopyMap_bijective

noncomputable def sourceHF2Shift (d : ℤ) : SourceCategory.{0} :=
  sourceLocalization.obj
    (if 0 ≤ d then (Prespectrum.suspension^[d.toNat]) sourceHF2.spectrum
     else (Prespectrum.desuspension^[(-d).toNat]) sourceHF2.spectrum)

/-- Mod-2 cohomology equivalences in all integer degrees. Over the field F₂,
cohomology detects exactly HF₂-homology equivalences, without a boundedness
restriction. The target HF₂ is the fixed Eilenberg–Mac Lane prespectrum. -/
def HF2Equivalences : MorphismProperty SourceCategory.{0} :=
  fun _X Y f => ∀ d : ℤ,
    Function.Bijective (fun a : Y ⟶ sourceHF2Shift d => f ≫ a)

namespace Prespectrum
/-- The actual right lifting/orthogonality property defining HF₂-local
objects in the ordinary stable category. This is not Moore-locality. -/
def IsHF2Local (X : Prespectrum.{0}) : Prop :=
  ∀ {A B : SourceCategory.{0}} (f : A ⟶ B), HF2Equivalences f →
    Function.Bijective (fun a : B ⟶ sourceLocalization.obj X => f ≫ a)
end Prespectrum

/-- The full subcategory of local objects, represented by point-set spectra. -/
structure CompletedSpectrum where
  spectrum : Prespectrum.{0}
  isLocal : spectrum.IsHF2Local

noncomputable instance : Category CompletedSpectrum where
  Hom X Y := sourceLocalization.obj X.spectrum ⟶ sourceLocalization.obj Y.spectrum
  id X := 𝟙 _
  comp f g := f ≫ g
  id_comp := by intros; apply Category.id_comp
  comp_id := by intros; apply Category.comp_id
  assoc := by intros; apply Category.assoc

/-- A functorial local replacement, including its reflection universal
property in the ordinary stable category. The unit is an actual point-set
map. This pins the completion and all induced maps up to unique isomorphism. -/
structure CompletionModel where
  replacement : Prespectrum.{0} ⥤ Prespectrum.{0}
  unit : 𝟭 _ ⟶ replacement
  isLocal : ∀ X, (replacement.obj X).IsHF2Local
  universal : ∀ (X : Prespectrum.{0}) (Y : CompletedSpectrum),
    Function.Bijective (fun f : sourceLocalization.obj (replacement.obj X) ⟶
        sourceLocalization.obj Y.spectrum => sourceLocalization.map (unit.app X) ≫ f)

/-- The localization functor determined by the specified HF₂-local reflection.
Its functor laws follow from those of the replacement and source localization. -/
noncomputable def CompletionModel.localization (Q : CompletionModel) : Prespectrum.{0} ⥤ CompletedSpectrum where
  obj X := ⟨Q.replacement.obj X, Q.isLocal X⟩
  map f := sourceLocalization.map (Q.replacement.map f)
  map_id X := by
    change sourceLocalization.map (Q.replacement.map (𝟙 X)) = 𝟙 _
    simp
  map_comp f g := by
    change sourceLocalization.map (Q.replacement.map (f ≫ g)) =
      sourceLocalization.map (Q.replacement.map f) ≫
      sourceLocalization.map (Q.replacement.map g)
    simp

end KIP126.StableHomotopy.Spectra
