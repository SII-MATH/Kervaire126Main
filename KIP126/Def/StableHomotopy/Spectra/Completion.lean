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

namespace BasedSpace

/-- Traverse the suspension coordinate twice. It is deliberately a raw
function: the jump from 1 to 0 is continuous only after reduced suspension. -/
noncomputable def doubleInterval (t : I) : I :=
  if h : (t : ℝ) ≤ 1/2 then
    ⟨2 * (t : ℝ), by constructor <;> nlinarith [t.property.1, t.property.2]⟩
  else
    ⟨2 * (t : ℝ) - 1, by constructor <;> nlinarith [t.property.1, t.property.2]⟩

/-- This is the degree-two pinch/fold map, fixed on quotient representatives.
Its source is a reduced suspension, so the two traversals add in homotopy. -/
theorem doubleSuspension_exists (A : BasedSpace.{0}) :
    ∃! f : A.suspension ⟶ A.suspension, ∀ a t,
      f.map (suspensionProjection A (a,t)) =
        suspensionProjection A (a,doubleInterval t) := by
  classical
  have hzero : doubleInterval 0 = 0 := by
    apply Subtype.ext
    norm_num [doubleInterval]
  have hone : doubleInterval 1 = 1 := by
    apply Subtype.ext
    norm_num [doubleInterval]
  let l (t : I) : I := Set.projIcc 0 1 zero_le_one (2 * (t:ℝ))
  let r (t : I) : I := Set.projIcc 0 1 zero_le_one (2 * (t:ℝ)-1)
  have hl : Continuous l := continuous_projIcc.comp (continuous_const.mul continuous_subtype_val)
  have hr : Continuous r := continuous_projIcc.comp
    ((continuous_const.mul continuous_subtype_val).sub continuous_const)
  have hglue : ∀ p : A × I, (p.2:ℝ) = 1/2 →
      suspensionProjection A (p.1,l p.2) = suspensionProjection A (p.1,r p.2) := by
    intro p hp
    have hpl : l p.2 = 1 := by
      dsimp [l]
      norm_num [hp]
    have hpr : r p.2 = 0 := by
      dsimp [r]
      norm_num [hp]
    rw [hpl,hpr]
    exact (suspensionProjection_collapsed A _ (Or.inr (Or.inr rfl))).trans
      (suspensionProjection_collapsed A _ (Or.inr (Or.inl rfl))).symm
  have hc : Continuous (fun p : A × I => suspensionProjection A (p.1,doubleInterval p.2)) := by
    have heq : (fun p : A × I => suspensionProjection A (p.1,doubleInterval p.2)) =
        (fun p : A × I => if (p.2:ℝ) ≤ 1/2 then
          suspensionProjection A (p.1,l p.2) else suspensionProjection A (p.1,r p.2)) := by
      funext p
      dsimp only [doubleInterval]
      split_ifs with h
      · have hm : 2*(p.2:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
          constructor <;> nlinarith [p.2.property.1,p.2.property.2]
        rw [show l p.2 = ⟨2*(p.2:ℝ),hm⟩ from Set.projIcc_of_mem _ hm]
      · have hm : 2*(p.2:ℝ)-1 ∈ Set.Icc (0:ℝ) 1 := by
          constructor <;> nlinarith [p.2.property.1,p.2.property.2]
        rw [show r p.2 = ⟨2*(p.2:ℝ)-1,hm⟩ from Set.projIcc_of_mem _ hm]
    rw [heq]
    exact continuous_if_le (continuous_subtype_val.comp continuous_snd) continuous_const
      ((suspensionProjection A).continuous.comp
        (continuous_fst.prodMk (hl.comp continuous_snd))).continuousOn
      ((suspensionProjection A).continuous.comp
        (continuous_fst.prodMk (hr.comp continuous_snd))).continuousOn hglue
  let raw : C(A × I,A.suspension) := ⟨_,hc⟩
  have collapsed (p : A × I) (hp : SuspensionCollapsed A p) : raw p = A.suspension.point := by
    apply suspensionProjection_collapsed
    rcases hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by rw [h,hzero]))
    · exact Or.inr (Or.inr (by rw [h,hone]))
  have respects : ∀ p q, SuspensionRelation A p q → raw p = raw q :=
    fun p q hpq => (collapsed p hpq.1).trans (collapsed q hpq.2).symm
  let f : A.suspension ⟶ A.suspension :=
    { map := ⟨Quot.lift raw respects,continuous_quot_lift respects raw.continuous⟩
      point := collapsed (A.point,0) (Or.inl rfl) }
  refine ⟨f,?_,?_⟩
  · intro a t
    rfl
  · intro g hg
    apply Hom.ext
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    intro p
    exact hg p.1 p.2

noncomputable def doubleSuspension (A : BasedSpace.{0}) :
    A.suspension ⟶ A.suspension := (doubleSuspension_exists A).exists.choose

end BasedSpace
namespace Prespectrum

/-- The prespectrum with sphere levels and doubled bonding maps. Its stable
homotopy groups are the sequential colimit under multiplication by 2; it is
therefore the ordinary sphere with 2 inverted, not the mod-2 Moore spectrum. -/
noncomputable def sphereInvertTwo : Prespectrum.{0} where
  level := sphereLevel
  bond n := (BasedSpace.doubleSuspension (sphereLevel n)).map.comp (sphere.bond n)
  bond_point n t := by
    change (BasedSpace.doubleSuspension _).map (sphere.bond n (_,t)) = _
    exact (congrArg (BasedSpace.doubleSuspension (sphereLevel n)).map
      (sphere.bond_point n t)).trans (BasedSpace.doubleSuspension _).point
  bond_zero n x := by
    change (BasedSpace.doubleSuspension _).map (sphere.bond n (x,0)) = _
    rw [sphere.bond_zero]
    exact (BasedSpace.doubleSuspension _).point
  bond_one n x := by
    change (BasedSpace.doubleSuspension _).map (sphere.bond n (x,1)) = _
    rw [sphere.bond_one]
    exact (BasedSpace.doubleSuspension _).point

/-- Orthogonality to every shift of S[1/2], expressed in the already defined
ordinary stable localization. Both nonnegative and nonpositive shifts occur. -/
def IsTwoComplete (X : Prespectrum.{0}) : Prop :=
  ∀ n : ℕ,
    Subsingleton (sourceLocalization.obj ((suspension^[n]) sphereInvertTwo) ⟶
      sourceLocalization.obj X) ∧
    Subsingleton (sourceLocalization.obj ((desuspension^[n]) sphereInvertTwo) ⟶
      sourceLocalization.obj X)

end Prespectrum

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
