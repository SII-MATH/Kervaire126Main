module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum
public import Mathlib.Topology.Piecewise
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity

@[expose] public section

/-! Explicit point-set spheres, suspension, and mapping cones. All quotient
relations and maps are fixed below; unfinished obligations are continuity,
well-definedness, and compatibility proofs, not unspecified operations. -/

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace BasedSpace

/-- The actual basepoint inclusion is a closed Hurewicz cofibration: its
homotopy extension property is quantified over continuous maps of spaces.
This condition is needed when using the ordinary reduced cone as a derived
cofiber; arbitrary based spaces are not silently assumed cofibrant. -/
def IsWellBased (X : BasedSpace.{u}) : Prop :=
  IsClosed ({X.point} : Set X) ∧
    ∀ (Y : TopCat.{u}) (f : C(X,Y)) (p : C(I,Y)), p 0 = f X.point →
      ∃ H : C(X × I,Y), (∀ x, H (x,0) = f x) ∧ (∀ t, H (X.point,t) = p t)

def SuspensionCollapsed (X : BasedSpace.{u}) (p : X × I) : Prop :=
  p.1 = X.point ∨ p.2 = 0 ∨ p.2 = 1

def SuspensionRelation (X : BasedSpace.{u}) (p q : X × I) : Prop :=
  SuspensionCollapsed X p ∧ SuspensionCollapsed X q

def suspension (X : BasedSpace.{u}) : BasedSpace.{u} where
  space := TopCat.of (Quot (SuspensionRelation X))
  point := Quot.mk _ (X.point, 0)

def suspensionProjection (X : BasedSpace.{u}) : C(X × I, X.suspension) :=
  ⟨Quot.mk _, continuous_quot_mk⟩

theorem suspensionProjection_collapsed (X : BasedSpace.{u}) (p : X × I)
    (h : SuspensionCollapsed X p) : suspensionProjection X p = X.suspension.point :=
  Quot.sound ⟨h, Or.inl rfl⟩

/-- Pointwise suspension of a based continuous family of maps. -/
def suspensionFamily (X Y : BasedSpace.{u}) (f : C(X × I, Y))
    (hf : ∀ t, f (X.point,t) = Y.point) (p : X.suspension × I) : Y.suspension :=
  Quot.lift (fun q : X × I => suspensionProjection Y (f (q.1,p.2),q.2))
    (by
      intro a b hab
      apply Eq.trans _ (suspensionProjection_collapsed Y _ ?_).symm
      · apply suspensionProjection_collapsed
        rcases hab.1 with h | h | h
        · exact Or.inl (h ▸ hf p.2)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases hab.2 with h | h | h
        · exact Or.inl (h ▸ hf p.2)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)) p.1

theorem continuous_suspensionFamily (X Y : BasedSpace.{u}) (f : C(X × I, Y))
    (hf : ∀ t, f (X.point,t) = Y.point) : Continuous (suspensionFamily X Y f hf) := by
  apply isQuotientMap_quot_mk.continuous_lift_prod_left
  exact (suspensionProjection Y).continuous.comp
    ((f.continuous.comp ((continuous_fst.fst).prodMk continuous_snd)).prodMk
      continuous_fst.snd)

def suspensionMap (X Y : BasedSpace.{u}) (f : C(X,Y)) (hf : f X.point = Y.point) :
    C(X.suspension,Y.suspension) := by
  let raw : C(X × I,Y.suspension) :=
    (suspensionProjection Y).comp ⟨fun p => (f p.1,p.2),
      (f.continuous.comp continuous_fst).prodMk continuous_snd⟩
  have respects : ∀ a b, SuspensionRelation X a b → raw a = raw b := by
    intro a b hab
    have collapsed : ∀ p, SuspensionCollapsed X p → raw p = Y.suspension.point := by
      intro p hp
      apply suspensionProjection_collapsed
      rcases hp with h | h | h
      · left
        change f p.1 = Y.point
        rw [h]
        exact hf
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact (collapsed a hab.1).trans (collapsed b hab.2).symm
  exact ⟨Quot.lift raw respects, continuous_quot_lift respects raw.continuous⟩



end BasedSpace

namespace Prespectrum

def IsWellBased (X : Prespectrum.{u}) : Prop := ∀ n, (X.level n).IsWellBased

/-- The sphere prespectrum has level Sⁿ, formed by iterated actual reduced
suspension of the discrete based two-point space. -/
def sphereLevel : ℕ → BasedSpace
  | 0 => { space := TopCat.of (Fin 2), point := 0 }
  | n + 1 => (sphereLevel n).suspension

def sphere : Prespectrum where
  level := sphereLevel
  bond n := BasedSpace.suspensionProjection (sphereLevel n)
  bond_point _n _t := BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)
  bond_zero _n _x := BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  bond_one _n _x := BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))

/-- The positive generator of π₀ of the ordinary sphere: the non-basepoint
of S⁰, viewed as a zero-dimensional cubical loop. -/
def sphereGenerator : StableHomotopy sphere 0 :=
  loopClass sphere 0 0 0 (by norm_num)
    ⟨ContinuousMap.const _ (show sphere.level 0 from (1 : Fin 2)), by
      intro t ht
      obtain ⟨i, _⟩ := ht
      exact Fin.elim0 i⟩

/-- Levelwise reduced suspension with the displayed interchange of the two
interval variables. This is not an independently selected shift operation. -/
def suspension (X : Prespectrum.{u}) : Prespectrum.{u} where
  level n := (X.level n).suspension
  bond n := ⟨BasedSpace.suspensionFamily _ _ (X.bond n) (X.bond_point n),
    BasedSpace.continuous_suspensionFamily _ _ (X.bond n) (X.bond_point n)⟩
  bond_point := by
    intro n t
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  bond_zero := by
    intro n x
    refine Quot.inductionOn x ?_
    intro p
    change BasedSpace.suspensionProjection _ (X.bond n (p.1,0),p.2) = _
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl (X.bond_zero n _))
  bond_one := by
    intro n x
    refine Quot.inductionOn x ?_
    intro p
    change BasedSpace.suspensionProjection _ (X.bond n (p.1,1),p.2) = _
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl (X.bond_one n _))

def suspensionMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) : X.suspension ⟶ Y.suspension where
  level n := BasedSpace.suspensionMap _ _ (f.level n) (f.point n)
  point := by
    intro n
    change BasedSpace.suspensionProjection _ (f.level n (X.level n).point,0) = _
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  bond := by
    intro n x t
    refine Quot.inductionOn x ?_
    intro p
    change BasedSpace.suspensionProjection _ (f.level (n+1) (X.bond n (p.1,t)),p.2) =
      BasedSpace.suspensionProjection _ (Y.bond n (f.level n p.1,t),p.2)
    rw [f.bond]

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

-- Retain the named hypotheses in the statement of this theorem.
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

end KIP126.StableHomotopy.Spectra
