module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Sphere
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Normed.Module.Connected

@[expose] section

/-!
# Concrete generators, smash maps, and cones in the ordinary source

The reduced smash below is the actual quotient of the compactly generated
product; suspension spectra use the fixed reduced suspensions, and mapping
cones use the explicit point-set cone quotient with its inclusion and boundary.
Only these constructions are claimed here. No arbitrary-prespectrum derived
smash or descent of such a smash to stable localization is supplied.

Adapted from `Implementation/Generators.lean` and `Implementation/PointSet.lean`,
SII-MATH/Kervaire126 develop commit
`8cb35dad5f75ecc095e474df6c765baec9b175bf`.
-/

namespace KIP126.AdamsSynthetic.Source

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace BasedSpace

@[ext] structure Hom (X Y : BasedSpace.{u}) where
  map : C(X,Y)
  point : map X.point = Y.point

instance : Category BasedSpace.{u} where
  Hom := Hom
  id X := ⟨ContinuousMap.id _, rfl⟩
  comp f g := ⟨g.map.comp f.map, by simp [f.point, g.point]⟩
  id_comp := by intros; ext; rfl
  comp_id := by intros; ext; rfl
  assoc := by intros; ext; rfl

def suspendMap {X Y : BasedSpace.{u}} (f : X ⟶ Y) : X.suspension ⟶ Y.suspension where
  map := suspensionMap X Y f.map f.point
  point := suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))

def iterateSuspension (X : BasedSpace.{u}) : ℕ → BasedSpace.{u}
  | 0 => X
  | n+1 => (iterateSuspension X n).suspension

def iterateSuspensionMap {X Y : BasedSpace.{u}} (f : X ⟶ Y) :
    ∀ n, iterateSuspension X n ⟶ iterateSuspension Y n
  | 0 => f
  | n+1 => suspendMap (iterateSuspensionMap f n)

def SmashRelation (X Y : BasedSpace.{u}) (p q : X × Y) : Prop :=
  (p.1 = X.point ∨ p.2 = Y.point) ∧ (q.1 = X.point ∨ q.2 = Y.point)

/-- Reduced smash in compactly generated spaces: k-ify the product before
collapsing its wedge. -/
def smash (X Y : BasedSpace.{u}) : BasedSpace.{u} where
  space := by
    letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
    exact TopCat.of (Quot (SmashRelation X Y))
  point := Quot.mk _ (X.point,Y.point)

def smashPoint (X Y : BasedSpace.{u}) (x : X) (y : Y) : X.smash Y := Quot.mk _ (x,y)

theorem smashPoint_base_left (X Y : BasedSpace.{u}) (y : Y) :
    smashPoint X Y X.point y = (X.smash Y).point := Quot.sound ⟨Or.inl rfl, Or.inl rfl⟩

theorem smashPoint_base_right (X Y : BasedSpace.{u}) (x : X) :
    smashPoint X Y x Y.point = (X.smash Y).point := Quot.sound ⟨Or.inr rfl, Or.inl rfl⟩

/-- The representative formulas uniquely determine the induced based maps.
Only their continuous quotient extension is a construction obligation. -/
theorem smashMap_exists {X Y X' Y' : BasedSpace.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    ∃! h : X.smash Y ⟶ X'.smash Y', ∀ x y,
      h.map (smashPoint X Y x y) = smashPoint X' Y' (f.map x) (g.map y) := by
  have hc : Continuous[TopologicalSpace.compactlyGenerated.{u} (X × Y),
      TopologicalSpace.compactlyGenerated.{u} (X' × Y')]
      (fun p : X × Y => (f.map p.1,g.map p.2)) := by
    refine @continuous_from_compactlyGenerated (X × Y) (X' × Y') _
      (TopologicalSpace.compactlyGenerated.{u} (X' × Y')) _ ?_
    intro S k
    let l : C(S, X' × Y') :=
      ⟨fun s => (f.map (k s).1,g.map (k s).2),
        (f.map.continuous.comp k.continuous.fst).prodMk
          (g.map.continuous.comp k.continuous.snd)⟩
    let ev : (Σ i : (T : CompHaus.{u}) × C(T, X' × Y'), i.fst) → X' × Y' :=
      fun q => q.1.2 q.2
    have hi : Continuous (fun s : S => (⟨⟨S,l⟩,s⟩ :
        Σ i : (T : CompHaus.{u}) × C(T, X' × Y'), i.fst)) :=
      @continuous_sigmaMk _ (fun i : (T : CompHaus.{u}) × C(T, X' × Y') => i.fst)
        (fun _ => inferInstance) ⟨S,l⟩
    letI : TopologicalSpace (X' × Y') := TopologicalSpace.coinduced ev inferInstance
    exact (show Continuous ev from continuous_coinduced_rng).comp hi
  let raw : X × Y → X'.smash Y' := fun p => smashPoint X' Y' (f.map p.1) (g.map p.2)
  have collapsed (p : X × Y) (hp : p.1 = X.point ∨ p.2 = Y.point) :
      raw p = (X'.smash Y').point := by
    rcases hp with h | h
    · dsimp [raw]
      rw [h, f.point]
      exact smashPoint_base_left _ _ _
    · dsimp [raw]
      rw [h, g.point]
      exact smashPoint_base_right _ _ _
  have hr : ∀ a b, SmashRelation X Y a b → raw a = raw b :=
    fun a b h => (collapsed a h.1).trans (collapsed b h.2).symm
  letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
  letI : TopologicalSpace (X' × Y') := TopologicalSpace.compactlyGenerated.{u} (X' × Y')
  let h : X.smash Y ⟶ X'.smash Y' :=
    { map := ⟨Quot.lift raw hr, continuous_quot_lift hr (continuous_quot_mk.comp hc)⟩
      point := collapsed _ (Or.inl rfl) }
  refine ⟨h, fun _ _ => rfl, ?_⟩
  intro h' hh'
  apply Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  intro p
  exact hh' p.1 p.2

noncomputable def smashMap {X Y X' Y' : BasedSpace.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    X.smash Y ⟶ X'.smash Y' := (smashMap_exists f g).exists.choose

/-- Actual based CW homotopy type, using characteristic cells and weak
CW topology from Mathlib, and homotopies fixed at the specified basepoint. -/
def HasCWType (A : BasedSpace.{u}) : Prop :=
  ∃ Y : BasedSpace.{u}, T2Space Y ∧
    Nonempty (Topology.CWComplex (Set.univ : Set Y)) ∧ Y.IsWellBased ∧
    ∃ (f : A ⟶ Y) (g : Y ⟶ A),
      (g.map.comp f.map).HomotopicRel (ContinuousMap.id A) {A.point} ∧
      (f.map.comp g.map).HomotopicRel (ContinuousMap.id Y) {Y.point}

/-- The derived-smash comparison is restricted to compactly generated,
well-based spaces of actual CW homotopy type. Merely being well-based does
not supply the flatness hypothesis used in MMSS, Proposition 11.7. -/
def IsGood (A : BasedSpace.{u}) : Prop :=
  UCompactlyGeneratedSpace.{u} A ∧ A.IsWellBased ∧ A.HasCWType

def zeroSphere : BasedSpace.{0} := Prespectrum.sphereLevel 0

set_option linter.unusedVariables false in
theorem smashUnit_exists (A : BasedSpace.{0}) (hA : A.IsGood) :
    ∃! f : zeroSphere.smash A ⟶ A,
      ∀ a, f.map (smashPoint zeroSphere A (show zeroSphere from (1 : Fin 2)) a) = a := by
  classical
  letI : DiscreteTopology zeroSphere := inferInstanceAs (DiscreteTopology (Fin 2))
  let raw : zeroSphere × A → A := fun p => if p.1 = zeroSphere.point then A.point else p.2
  have hc : Continuous raw := by
    apply continuous_prod_of_discrete_left.mpr
    intro x
    dsimp [raw]
    split_ifs
    · exact continuous_const
    · exact continuous_id
  have collapsed (p : zeroSphere × A)
      (hp : p.1 = zeroSphere.point ∨ p.2 = A.point) : raw p = A.point := by
    rcases hp with h | h
    · simp [raw, h]
    · simp [raw, h]
  have hr : ∀ a b, SmashRelation zeroSphere A a b → raw a = raw b :=
    fun a b h => (collapsed a h.1).trans (collapsed b h.2).symm
  have hck : Continuous[TopologicalSpace.compactlyGenerated.{0} (zeroSphere × A),
      inferInstance] raw :=
    continuous_from_compactlyGenerated raw (fun _ k => hc.comp k.continuous)
  letI : TopologicalSpace (zeroSphere × A) :=
    TopologicalSpace.compactlyGenerated.{0} (zeroSphere × A)
  let f : zeroSphere.smash A ⟶ A :=
    { map := ⟨Quot.lift raw hr, continuous_quot_lift hr hck⟩
      point := collapsed _ (Or.inl rfl) }
  refine ⟨f, ?_, ?_⟩
  · intro a
    change raw ((1 : Fin 2), a) = a
    simp [raw, zeroSphere, Prespectrum.sphereLevel]
  · intro g hg
    apply Hom.ext
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨x,a⟩
    change g.map (smashPoint zeroSphere A x a) = raw (x,a)
    change Fin 2 at x
    fin_cases x
    · change g.map (smashPoint zeroSphere A zeroSphere.point a) = raw (zeroSphere.point,a)
      rw [smashPoint_base_left, g.point]
      simp [raw]
    · simpa [raw, zeroSphere, Prespectrum.sphereLevel] using hg a

noncomputable def smashUnit (A : BasedSpace.{0}) (hA : A.IsGood) :
    zeroSphere.smash A ⟶ A := (smashUnit_exists A hA).exists.choose

theorem good_zeroSphere : zeroSphere.IsGood := by
  classical
  letI : DiscreteTopology zeroSphere := inferInstanceAs (DiscreteTopology (Fin 2))
  have hwb : zeroSphere.IsWellBased := by
    refine ⟨isClosed_singleton, ?_⟩
    intro Y f p hp
    let H : C(zeroSphere × I,Y) := ContinuousMap.uncurry
      ⟨fun x => if x = zeroSphere.point then p else ContinuousMap.const I (f x),
        continuous_of_discreteTopology⟩
    refine ⟨H, ?_, ?_⟩
    · intro x
      by_cases hx : x = zeroSphere.point
      · simpa [H, hx] using hp
      · simp [H, hx]
    · intro t
      simp [H]
  refine ⟨inferInstance, hwb, zeroSphere, inferInstance, ⟨inferInstance⟩, hwb,
    𝟙 _, 𝟙 _, ?_, ?_⟩
  all_goals exact ContinuousMap.HomotopicRel.refl _

end BasedSpace

namespace Prespectrum

def suspensionSpectrum (A : BasedSpace.{u}) : Prespectrum.{u} where
  level := A.iterateSuspension
  bond _n := BasedSpace.suspensionProjection _
  bond_point _ _ := BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)
  bond_zero _ _ := BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  bond_one _ _ := BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))

theorem suspensionSpectrum_zeroSphere :
    suspensionSpectrum BasedSpace.zeroSphere = sphere := by
  have h : BasedSpace.iterateSuspension BasedSpace.zeroSphere = sphereLevel := by
    funext n
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg BasedSpace.suspension ih
  have ext (X Y : Prespectrum.{0}) (hlevel : X.level = Y.level)
      (hbond : ∀ n, HEq (X.bond n) (Y.bond n)) : X = Y := by
    cases X
    cases Y
    cases hlevel
    have hb := funext fun n => eq_of_heq (hbond n)
    cases hb
    rfl
  apply ext _ _ h
  intro n
  have hp (A B : BasedSpace.{0}) (hab : A = B) :
      HEq A.suspensionProjection B.suspensionProjection := by
    cases hab
    rfl
  exact hp _ _ (congrFun h n)

def suspensionSpectrumMap {A B : BasedSpace.{u}} (f : A ⟶ B) :
    suspensionSpectrum A ⟶ suspensionSpectrum B where
  level n := (BasedSpace.iterateSuspensionMap f n).map
  point n := (BasedSpace.iterateSuspensionMap f n).point
  bond := by intros; rfl

/-- The reduced mapping-cone quotient at one level. -/
inductive ConeRelation {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    Y.level n ⊕ (X.level n × I) → Y.level n ⊕ (X.level n × I) → Prop
  | start (x : X.level n) : ConeRelation f n (.inr (x,0)) (.inl (f.level n x))
  | finish (x : X.level n) : ConeRelation f n (.inr (x,1)) (.inl (Y.level n).point)
  | point (t : I) : ConeRelation f n (.inr ((X.level n).point,t)) (.inl (Y.level n).point)

def coneLevel {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) : BasedSpace.{u} where
  space := TopCat.of (Quot (ConeRelation f n))
  point := Quot.mk _ (.inl (Y.level n).point)

def coneBondRepresentative {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (t : I) : Y.level n ⊕ (X.level n × I) → coneLevel f (n + 1)
  | .inl y => Quot.mk _ (.inl (Y.bond n (y,t)))
  | .inr (x,s) => Quot.mk _ (.inr (X.bond n (x,t),s))

theorem coneBondRepresentative_respects {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (t : I) (a b) (h : ConeRelation f n a b) :
    coneBondRepresentative f n t a = coneBondRepresentative f n t b := by
  cases h with
  | start x =>
    change Quot.mk (ConeRelation f (n+1)) (.inr (X.bond n (x,t),0)) =
      Quot.mk (ConeRelation f (n+1)) (.inl (Y.bond n (f.level n x,t)))
    rw [← f.bond]
    exact Quot.sound (ConeRelation.start _)
  | finish x =>
    change Quot.mk (ConeRelation f (n+1)) (.inr (X.bond n (x,t),1)) =
      Quot.mk (ConeRelation f (n+1)) (.inl (Y.bond n ((Y.level n).point,t)))
    rw [Y.bond_point]
    exact Quot.sound (ConeRelation.finish _)
  | point s =>
    change Quot.mk (ConeRelation f (n+1)) (.inr (X.bond n ((X.level n).point,t),s)) =
      Quot.mk (ConeRelation f (n+1)) (.inl (Y.bond n ((Y.level n).point,t)))
    rw [X.bond_point, Y.bond_point]
    exact Quot.sound (ConeRelation.point s)

def coneBond {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (p : coneLevel f n × I) : coneLevel f (n + 1) :=
  Quot.lift (coneBondRepresentative f n p.2)
    (coneBondRepresentative_respects f n p.2) p.1

theorem continuous_coneBond {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    Continuous (coneBond f n) := by
  apply isQuotientMap_quot_mk.continuous_lift_prod_left
  have hleft : Continuous (fun p : Y.level n × I =>
      Quot.mk (ConeRelation f (n+1)) (.inl (Y.bond n p))) :=
    continuous_quot_mk.comp (continuous_inl.comp (Y.bond n).continuous)
  have hright : Continuous (fun p : (X.level n × I) × I =>
      Quot.mk (ConeRelation f (n+1)) (.inr (X.bond n (p.1.1,p.2),p.1.2))) :=
    continuous_quot_mk.comp (continuous_inr.comp
      (((X.bond n).continuous.comp (continuous_fst.fst.prodMk continuous_snd)).prodMk
        continuous_fst.snd))
  have hcont := (hleft.sumElim hright).comp
    (Homeomorph.sumProdDistrib (X := Y.level n) (Y := X.level n × I) (Z := I)).continuous
  apply hcont.congr
  rintro ⟨p,t⟩
  cases p <;> rfl

def cone {X Y : Prespectrum.{u}} (f : X ⟶ Y) : Prespectrum.{u} where
  level := coneLevel f
  bond n := ⟨coneBond f n, continuous_coneBond f n⟩
  bond_point := by intro n t; change Quot.mk (ConeRelation f (n+1)) (Sum.inl (Y.bond n (_,t))) = _; rw [Y.bond_point]; rfl
  bond_zero := by
    intro n x
    refine Quot.inductionOn x ?_
    rintro (y | ⟨x,t⟩)
    · change Quot.mk (ConeRelation f (n+1)) (Sum.inl (Y.bond n (y,0))) = _
      rw [Y.bond_zero]; rfl
    · change Quot.mk (ConeRelation f (n+1)) (Sum.inr (X.bond n (x,0),t)) = _
      rw [X.bond_zero]
      exact Quot.sound (ConeRelation.point t)
  bond_one := by
    intro n x
    refine Quot.inductionOn x ?_
    rintro (y | ⟨x,t⟩)
    · change Quot.mk (ConeRelation f (n+1)) (Sum.inl (Y.bond n (y,1))) = _
      rw [Y.bond_one]; rfl
    · change Quot.mk (ConeRelation f (n+1)) (Sum.inr (X.bond n (x,1),t)) = _
      rw [X.bond_one]
      exact Quot.sound (ConeRelation.point t)

def coneInclusion {X Y : Prespectrum.{u}} (f : X ⟶ Y) : Y ⟶ cone f where
  level _n := ⟨fun y => Quot.mk _ (.inl y), continuous_quot_mk.comp continuous_inl⟩
  point := fun _ => rfl
  bond := fun _ _ _ => rfl

set_option linter.unusedVariables false in
def coneBoundaryRepresentative {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    Y.level n ⊕ (X.level n × I) → (X.level n).suspension
  | .inl _ => (X.level n).suspension.point
  | .inr p => BasedSpace.suspensionProjection _ p

theorem coneBoundaryRepresentative_respects {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (a b) (h : ConeRelation f n a b) :
    coneBoundaryRepresentative f n a = coneBoundaryRepresentative f n b := by
  cases h with
  | start x =>
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  | finish x =>
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))
  | point t =>
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)

def coneBoundaryLevel {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    coneLevel f n → (X.level n).suspension :=
  Quot.lift (coneBoundaryRepresentative f n) (coneBoundaryRepresentative_respects f n)

theorem continuous_coneBoundaryLevel {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    Continuous (coneBoundaryLevel f n) := by
  exact continuous_quot_lift _ (continuous_sum_dom.mpr
    ⟨continuous_const, (BasedSpace.suspensionProjection (X.level n)).continuous⟩)

def coneBoundary {X Y : Prespectrum.{u}} (f : X ⟶ Y) : cone f ⟶ X.suspension where
  level n := ⟨coneBoundaryLevel f n, continuous_coneBoundaryLevel f n⟩
  point := fun _ => rfl
  bond := by
    intro n x t
    refine Quot.inductionOn x ?_
    rintro (y | ⟨x,s⟩)
    · change (X.level (n+1)).suspension.point =
        BasedSpace.suspensionProjection _ (X.bond n ((X.level n).point,t),0)
      exact (BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))).symm
    · rfl

end Prespectrum

end KIP126.AdamsSynthetic.Source
