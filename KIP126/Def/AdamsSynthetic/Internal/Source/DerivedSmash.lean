module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

import all KIP126.Def.AdamsSynthetic.Internal.Source.PointSetRecognition

@[expose] section

/-!
# The actual even-indexed prespectrum smash and its derived comparison boundary

The even level `2n` is `X_n ∧ Y_n`; the odd level is its suspension. The
paired bond is fixed by the actual two input bonds on quotient representatives
and its continuity is proved below. No tensor of the target category is used
in defining this source smash.

Good replacement, flatness, and identification with the selected target tensor
are separate mathematical conditions on this explicit construction.
-/

namespace KIP126.AdamsSynthetic.Source
open CategoryTheory Topology MonoidalCategory KIP126.StableHomotopy
open scoped unitInterval

namespace Prespectrum


def tail (X : Prespectrum.{0}) : Prespectrum.{0} where
  level n := X.level (n+1)
  bond n := X.bond (n+1)
  bond_point n := X.bond_point (n+1)
  bond_zero n := X.bond_zero (n+1)
  bond_one n := X.bond_one (n+1)

def tailMap {X Y : Prespectrum.{0}} (f : X ⟶ Y) : X.tail ⟶ Y.tail where
  level n := f.level (n+1)
  point n := f.point (n+1)
  bond n := f.bond (n+1)



/-- Two consecutive bonds, on their actual quotient representatives. -/
theorem pairedBond_exists (X Y : Prespectrum.{0}) :
    ∃! b : C((X.level 0 |>.smash (Y.level 0)).suspension × I,
        (X.level 1).smash (Y.level 1)),
      (∀ x y s t,
        b (BasedSpace.suspensionProjection _ (BasedSpace.smashPoint _ _ x y,s),t) =
          BasedSpace.smashPoint _ _ (X.bond 0 (x,s)) (Y.bond 0 (y,t))) ∧
      (∀ t, b (((X.level 0).smash (Y.level 0)).suspension.point,t) =
        ((X.level 1).smash (Y.level 1)).point) ∧
      (∀ a, b (a,0) = ((X.level 1).smash (Y.level 1)).point) ∧
      (∀ a, b (a,1) = ((X.level 1).smash (Y.level 1)).point) := by
  have kc (S : CompHaus.{0}) (k : C(S, X.level 1 × Y.level 1)) :
      Continuous (fun s : S => BasedSpace.smashPoint (X.level 1) (Y.level 1) (k s).1 (k s).2) := by
    let ev : (Σ i : (T : CompHaus.{0}) × C(T, X.level 1 × Y.level 1), i.fst) →
        X.level 1 × Y.level 1 := fun q => q.1.2 q.2
    have hi : Continuous (fun s : S => (⟨⟨S,k⟩,s⟩ :
        Σ i : (T : CompHaus.{0}) × C(T, X.level 1 × Y.level 1), i.fst)) :=
      @continuous_sigmaMk _ (fun i : (T : CompHaus.{0}) × C(T, X.level 1 × Y.level 1) => i.fst)
        (fun _ => inferInstance) ⟨S,k⟩
    letI : TopologicalSpace (X.level 1 × Y.level 1) := TopologicalSpace.coinduced ev inferInstance
    exact continuous_quot_mk.comp ((show Continuous ev from continuous_coinduced_rng).comp hi)
  let family (p : X.level 0 × Y.level 0) :
      C(I, C(I, (X.level 1).smash (Y.level 1))) :=
    (⟨fun st : I × I => BasedSpace.smashPoint _ _ (X.bond 0 (p.1,st.1)) (Y.bond 0 (p.2,st.2)),
      kc (CompHaus.of (I × I)) ⟨_,
        ((X.bond 0).continuous.comp (continuous_const.prodMk continuous_fst)).prodMk
          ((Y.bond 0).continuous.comp (continuous_const.prodMk continuous_snd))⟩⟩ :
      C(I × I, (X.level 1).smash (Y.level 1))).curry
  have hf : Continuous[TopologicalSpace.compactlyGenerated.{0} (X.level 0 × Y.level 0),
      inferInstance] family := by
    refine @continuous_from_compactlyGenerated (X.level 0 × Y.level 0) _ _ _ family ?_
    intro S k
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact kc (CompHaus.of ((S × I) × I)) ⟨fun p =>
      (X.bond 0 ((k p.1.1).1,p.1.2), Y.bond 0 ((k p.1.1).2,p.2)),
      ((X.bond 0).continuous.comp ((k.continuous.fst.comp continuous_fst.fst).prodMk
        continuous_fst.snd)).prodMk
      ((Y.bond 0).continuous.comp ((k.continuous.snd.comp continuous_fst.fst).prodMk
        continuous_snd))⟩
  let raw (p : (X.level 0 × Y.level 0) × (I × I)) : (X.level 1).smash (Y.level 1) :=
    BasedSpace.smashPoint _ _ (X.bond 0 (p.1.1,p.2.1)) (Y.bond 0 (p.1.2,p.2.2))
  have collapsed (p : X.level 0 × Y.level 0) (st : I × I)
      (hp : p.1 = (X.level 0).point ∨ p.2 = (Y.level 0).point) :
      raw (p,st) = ((X.level 1).smash (Y.level 1)).point := by
    rcases hp with h | h
    · dsimp [raw]
      rw [h, X.bond_point]
      exact BasedSpace.smashPoint_base_left _ _ _
    · dsimp [raw]
      rw [h, Y.bond_point]
      exact BasedSpace.smashPoint_base_right _ _ _
  have hr (st : I × I) : ∀ a b, BasedSpace.SmashRelation (X.level 0) (Y.level 0) a b →
      raw (a,st) = raw (b,st) :=
    fun a b h => (collapsed a st h.1).trans (collapsed b st h.2).symm
  let mid (p : (X.level 0).smash (Y.level 0) × (I × I)) :=
    Quot.lift (fun q => raw (q,p.2)) (hr p.2) p.1
  have hm : Continuous mid := by
    letI : TopologicalSpace (X.level 0 × Y.level 0) :=
      TopologicalSpace.compactlyGenerated.{0} (X.level 0 × Y.level 0)
    apply isQuotientMap_quot_mk.continuous_lift_prod_left
    exact ((⟨family,hf⟩ : C(X.level 0 × Y.level 0,
      C(I,C(I,(X.level 1).smash (Y.level 1))))).uncurry.uncurry.continuous).comp
      ((continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd)
  have mid_left (s t : I) : mid (((X.level 0).smash (Y.level 0)).point,(s,t)) =
      ((X.level 1).smash (Y.level 1)).point := collapsed _ _ (Or.inl rfl)
  have mid_zero (a : (X.level 0).smash (Y.level 0)) (t : I) :
      mid (a,(0,t)) = ((X.level 1).smash (Y.level 1)).point := by
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    change BasedSpace.smashPoint _ _ (X.bond 0 (x,0)) (Y.bond 0 (y,t)) = _
    rw [X.bond_zero]
    exact BasedSpace.smashPoint_base_left _ _ _
  have mid_one (a : (X.level 0).smash (Y.level 0)) (t : I) :
      mid (a,(1,t)) = ((X.level 1).smash (Y.level 1)).point := by
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    change BasedSpace.smashPoint _ _ (X.bond 0 (x,1)) (Y.bond 0 (y,t)) = _
    rw [X.bond_one]
    exact BasedSpace.smashPoint_base_left _ _ _
  have collapse_outer (p : (X.level 0).smash (Y.level 0) × I) (t : I)
      (hp : BasedSpace.SuspensionCollapsed ((X.level 0).smash (Y.level 0)) p) :
      mid (p.1,(p.2,t)) = ((X.level 1).smash (Y.level 1)).point := by
    rcases hp with h | h | h
    · rw [h, mid_left]
    · rw [h, mid_zero]
    · rw [h, mid_one]
  have hrout (t : I) : ∀ a b,
      BasedSpace.SuspensionRelation ((X.level 0).smash (Y.level 0)) a b →
      mid (a.1,(a.2,t)) = mid (b.1,(b.2,t)) :=
    fun a b h => (collapse_outer a t h.1).trans (collapse_outer b t h.2).symm
  let b : C(((X.level 0).smash (Y.level 0)).suspension × I,
      (X.level 1).smash (Y.level 1)) :=
    ⟨fun p => Quot.lift (fun q => mid (q.1,(q.2,p.2))) (hrout p.2) p.1, by
      apply isQuotientMap_quot_mk.continuous_lift_prod_left
      exact hm.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))⟩
  refine ⟨b, ⟨fun _ _ _ _ => rfl, fun t => mid_left 0 t, ?_, ?_⟩, ?_⟩
  · intro a
    refine Quot.inductionOn a ?_
    rintro ⟨a,s⟩
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    change BasedSpace.smashPoint _ _ (X.bond 0 (x,s)) (Y.bond 0 (y,0)) = _
    rw [Y.bond_zero]
    exact BasedSpace.smashPoint_base_right _ _ _
  · intro a
    refine Quot.inductionOn a ?_
    rintro ⟨a,s⟩
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    change BasedSpace.smashPoint _ _ (X.bond 0 (x,s)) (Y.bond 0 (y,1)) = _
    rw [Y.bond_one]
    exact BasedSpace.smashPoint_base_right _ _ _
  · intro c hc
    apply ContinuousMap.ext
    rintro ⟨a,t⟩
    refine Quot.inductionOn a ?_
    rintro ⟨a,s⟩
    refine Quot.inductionOn a ?_
    rintro ⟨x,y⟩
    exact hc.1 x y s t



noncomputable def pairedBond (X Y : Prespectrum.{0}) :
    C(((X.level 0).smash (Y.level 0)).suspension × I,
      (X.level 1).smash (Y.level 1)) := (pairedBond_exists X Y).exists.choose

def diagonalLevel (X Y : Prespectrum.{0}) : ℕ → BasedSpace.{0}
  | 0 => (X.level 0).smash (Y.level 0)
  | 1 => ((X.level 0).smash (Y.level 0)).suspension
  | n+2 => diagonalLevel X.tail Y.tail n

noncomputable def diagonalBond (X Y : Prespectrum.{0}) :
    ∀ n, C(diagonalLevel X Y n × I, diagonalLevel X Y (n+1))
  | 0 => BasedSpace.suspensionProjection _
  | 1 => pairedBond X Y
  | n+2 => diagonalBond X.tail Y.tail n



theorem diagonalBond_laws (X Y : Prespectrum.{0}) (n : ℕ) :
    (∀ t, diagonalBond X Y n ((diagonalLevel X Y n).point,t) =
      (diagonalLevel X Y (n+1)).point) ∧
    (∀ a, diagonalBond X Y n (a,0) = (diagonalLevel X Y (n+1)).point) ∧
    (∀ a, diagonalBond X Y n (a,1) = (diagonalLevel X Y (n+1)).point) := by
  induction n using Nat.twoStepInduction generalizing X Y with
  | zero =>
    exact ⟨fun _ => BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl),
      fun _ => BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl)),
      fun _ => BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))⟩
  | one => exact (pairedBond_exists X Y).exists.choose_spec.2
  | more n ih _ => exact ih X.tail Y.tail



noncomputable def diagonalSmash (X Y : Prespectrum.{0}) : Prespectrum.{0} where
  level := diagonalLevel X Y
  bond := diagonalBond X Y
  bond_point n := (diagonalBond_laws X Y n).1
  bond_zero n := (diagonalBond_laws X Y n).2.1
  bond_one n := (diagonalBond_laws X Y n).2.2

noncomputable def diagonalMapLevel {X Y X' Y' : Prespectrum.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    ∀ n, diagonalLevel X Y n ⟶ diagonalLevel X' Y' n
  | 0 => BasedSpace.smashMap ⟨f.level 0, f.point 0⟩ ⟨g.level 0, g.point 0⟩
  | 1 => BasedSpace.suspendMap
      (BasedSpace.smashMap ⟨f.level 0, f.point 0⟩ ⟨g.level 0, g.point 0⟩)
  | n+2 => diagonalMapLevel (tailMap f) (tailMap g) n



theorem diagonalMapLevel_bond {X Y X' Y' : Prespectrum.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) (a : diagonalLevel X Y n) (t : I) :
    (diagonalMapLevel f g (n+1)).map (diagonalBond X Y n (a,t)) =
      diagonalBond X' Y' n ((diagonalMapLevel f g n).map a,t) := by
  induction n using Nat.twoStepInduction generalizing X Y X' Y' with
  | zero => rfl
  | one =>
    refine Quot.inductionOn a ?_
    rintro ⟨b,s⟩
    refine Quot.inductionOn b ?_
    rintro ⟨x,y⟩
    have hsm {A B A' B' : BasedSpace.{0}} (p : A ⟶ A') (q : B ⟶ B') (x : A) (y : B) :
        (BasedSpace.smashMap p q).map (BasedSpace.smashPoint A B x y) =
          BasedSpace.smashPoint A' B' (p.map x) (q.map y) :=
      (BasedSpace.smashMap_exists p q).exists.choose_spec x y
    have hp (U V : Prespectrum.{0}) (x : U.level 0) (y : V.level 0) (s t : I) :
        pairedBond U V (BasedSpace.suspensionProjection _
          (BasedSpace.smashPoint _ _ x y,s),t) =
        BasedSpace.smashPoint _ _ (U.bond 0 (x,s)) (V.bond 0 (y,t)) :=
      (pairedBond_exists U V).exists.choose_spec.1 x y s t
    change (BasedSpace.smashMap ⟨f.level 1, f.point 1⟩ ⟨g.level 1, g.point 1⟩).map
        (pairedBond X Y (BasedSpace.suspensionProjection _
          (BasedSpace.smashPoint _ _ x y,s),t)) =
      pairedBond X' Y' (BasedSpace.suspensionProjection _
        ((BasedSpace.smashMap ⟨f.level 0, f.point 0⟩ ⟨g.level 0, g.point 0⟩).map
          (BasedSpace.smashPoint _ _ x y),s),t)
    rw [hp, hsm, hsm, hp]
    change BasedSpace.smashPoint _ _ (f.level 1 (X.bond 0 (x,s)))
        (g.level 1 (Y.bond 0 (y,t))) = _
    rw [f.bond, g.bond]
  | more n ih _ => exact ih (tailMap f) (tailMap g) a



noncomputable def diagonalSmashMap {X Y X' Y' : Prespectrum.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') : diagonalSmash X Y ⟶ diagonalSmash X' Y' where
  level n := (diagonalMapLevel f g n).map
  point n := (diagonalMapLevel f g n).point
  bond n := diagonalMapLevel_bond f g n


end Prespectrum

def Prespectrum.IsGood (X : Prespectrum.{0}) : Prop := ∀ n, (X.level n).IsGood

/-- A replacement is an actual point-set functor and actual stable comparison
map, with the precise levelwise CW-type hypotheses used by the smash. -/
structure SourceReplacementData where
  replacement : Prespectrum.{0} ⥤ Prespectrum.{0}
  comparison : replacement ⟶ 𝟭 _
  good : ∀ X, (replacement.obj X).IsGood
  stable : ∀ X, Prespectrum.stableEquivalences (comparison.app X)

/-- Flatness is requested for this specified replacement and this actual
two-variable map. It is not inferred merely from a replacement label. -/
def SourceReplacementFlatness (P : SourceReplacementData) : Prop :=
  ∀ {X Y X' Y' : Prespectrum.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
    Prespectrum.stableEquivalences f → Prespectrum.stableEquivalences g →
      Prespectrum.stableEquivalences
        (Prespectrum.diagonalSmashMap (P.replacement.map f) (P.replacement.map g))

namespace SourceReplacementData

noncomputable def derivedSmash (P : SourceReplacementData) (X Y : Prespectrum.{0}) :
    Prespectrum.{0} := Prespectrum.diagonalSmash (P.replacement.obj X) (P.replacement.obj Y)

noncomputable def derivedSmashMap (P : SourceReplacementData)
    {X Y X' Y' : Prespectrum.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    P.derivedSmash X Y ⟶ P.derivedSmash X' Y' :=
  Prespectrum.diagonalSmashMap (P.replacement.map f) (P.replacement.map g)

end SourceReplacementData

universe u v

/-- Full-object recognition against the independently constructed source
smash of the specified replacements. This extends the object comparison to
every prespectrum, rather than supplying a second freely chosen source tensor.

The source unitor and its agreement with the generator normalization are not
asserted here; they require an actual source unitor construction. -/
structure SourceDerivedSmashRecognition
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : SourceRecognition C H) (P : SourceReplacementData) where
  comparison : ∀ (X Y : Prespectrum.{0}),
    (R.equivalence.functor.obj (sourceLocalization.obj X) ⊗
      R.equivalence.functor.obj (sourceLocalization.obj Y) ≅
        R.equivalence.functor.obj (sourceLocalization.obj (P.derivedSmash X Y)))
  natural : ∀ {X Y X' Y' : Prespectrum.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
    (R.equivalence.functor.map (sourceLocalization.map f) ⊗ₘ
        R.equivalence.functor.map (sourceLocalization.map g)) ≫
      (comparison X' Y').hom =
        (comparison X Y).hom ≫
          R.equivalence.functor.map (sourceLocalization.map (P.derivedSmashMap f g))

end KIP126.AdamsSynthetic.Source
