module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.CategoryTheory.Localization.Construction

@[expose] public section

/-!
# Point-set prespectra for the classical stable category

Sequential prespectra are sequences of based spaces with continuous maps
`X n × I → X (n+1)` constant on the basepoint cylinder and both ends.
The stable homotopy sets below are the quotient of actual cubical based maps
by based homotopy and these structure maps. Stable equivalences are precisely
the maps inducing bijections in every integer stable degree. In particular,
neither the category nor its weak equivalences are unspecified inputs.

This is the ordinary, uncompleted stable homotopy source. Identification of a
completed model must use an additional localization, not rename this sphere.
-/

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u

/-- A space with a specified basepoint; the topology is part of `TopCat`. -/
structure BasedSpace where
  space : TopCat.{u}
  point : space

instance : CoeSort BasedSpace (Type u) := ⟨fun X => X.space⟩
instance (X : BasedSpace) : TopologicalSpace X := X.space.str

/-- Adjoint structure maps are written without choosing a loop-space model. -/
structure Prespectrum where
  level : ℕ → BasedSpace.{u}
  bond : ∀ n, C(level n × I, level (n + 1))
  bond_point : ∀ n t, bond n ((level n).point, t) = (level (n + 1)).point
  bond_zero : ∀ n x, bond n (x, 0) = (level (n + 1)).point
  bond_one : ∀ n x, bond n (x, 1) = (level (n + 1)).point

namespace Prespectrum

/-- A levelwise continuous based map commuting with the actual bonds. -/
@[ext]
structure Hom (X Y : Prespectrum.{u}) where
  level : ∀ n, C(X.level n, Y.level n)
  point : ∀ n, level n (X.level n).point = (Y.level n).point
  bond : ∀ n x t, level (n + 1) (X.bond n (x,t)) = Y.bond n (level n x,t)

instance : Category Prespectrum.{u} where
  Hom := Hom
  id X :=
    { level := fun _ => ContinuousMap.id _
      point := fun _ => rfl
      bond := fun _ _ _ => rfl }
  comp f g :=
    { level := fun n => (g.level n).comp (f.level n)
      point := by intro n; simp [f.point, g.point]
      bond := by intro n x t; simp only [ContinuousMap.comp_apply, f.bond, g.bond] }
  id_comp := by intros; ext; rfl
  comp_id := by intros; ext; rfl
  assoc := by intros; ext; rfl

/-- An actual cubical representative in degree `d`, at a sufficiently high
level. No homotopy group or stable stem is supplied as independent data. -/
structure Representative (X : Prespectrum.{u}) (d : ℤ) where
  stage : ℕ
  dimension : ℕ
  degree : (dimension : ℤ) = d + stage
  loop : GenLoop (Fin dimension) (X.level stage) (X.level stage).point

/-- Stabilization of a cubical loop by the displayed prespectrum bond.
The new first coordinate is the structure-map interval. -/
def stabilizeLoop (X : Prespectrum.{u}) (n r : ℕ)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
    GenLoop (Fin (r + 1)) (X.level (n + 1)) (X.level (n + 1)).point := by
  refine ⟨⟨fun t => X.bond n (p (fun i => t i.succ), t 0), ?_⟩, ?_⟩
  · exact (X.bond n).continuous.comp
      ((p.val.continuous.comp (continuous_pi fun i => continuous_apply i.succ)).prodMk
        (continuous_apply 0))
  · intro t ht
    obtain ⟨i, hi⟩ := ht
    induction i using Fin.cases with
    | zero =>
      rcases hi with h | h
      · simpa [h] using X.bond_zero n (p (fun i => t i.succ))
      · simpa [h] using X.bond_one n (p (fun i => t i.succ))
    | succ j =>
      have hp : p (fun i => t i.succ) = (X.level n).point := p.property _ ⟨j, hi⟩
      simpa [hp] using X.bond_point n (t 0)

def Representative.next {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) : Representative X d where
  stage := a.stage + 1
  dimension := a.dimension + 1
  degree := by have := a.degree; omega
  loop := stabilizeLoop X a.stage a.dimension a.loop

/-- Relations generating the colimit of the based homotopy sets. -/
inductive StableRelation (X : Prespectrum.{u}) (d : ℤ) :
    Representative X d → Representative X d → Prop
  | homotopy (a : Representative X d)
      (p : GenLoop (Fin a.dimension) (X.level a.stage) (X.level a.stage).point)
      (h : GenLoop.Homotopic a.loop p) : StableRelation X d a { a with loop := p }
  | stabilization (a : Representative X d) : StableRelation X d a a.next

-- Keep the established public declaration name.
set_option linter.dupNamespace false in
/-- The set underlying the usual integer-graded stable homotopy group. -/
def StableHomotopy (X : Prespectrum.{u}) (d : ℤ) := Quot (StableRelation X d)

def Representative.map {X Y : Prespectrum.{u}} (f : X ⟶ Y) {d : ℤ}
    (a : Representative X d) : Representative Y d where
  stage := a.stage
  dimension := a.dimension
  degree := a.degree
  loop := ⟨(f.level a.stage).comp a.loop.val, by
    intro t ht
    change f.level a.stage (a.loop t) = _
    exact (congrArg (fun x => f.level a.stage x) (a.loop.property t ht)).trans
      (f.point a.stage)⟩

/-- Based homotopies and stabilization are respected by the actual maps.
This proof obligation does not choose a new induced map. -/
theorem Representative.map_relation {X Y : Prespectrum.{u}} (f : X ⟶ Y) {d : ℤ}
    {a b : Representative X d} (h : StableRelation X d a b) :
    StableRelation Y d (a.map f) (b.map f) := by
  cases h with
  | homotopy p h =>
    exact StableRelation.homotopy (a.map f) _
      (h.comp_continuousMap (f.level a.stage))
  | stabilization =>
    have hm : a.next.map f = (a.map f).next := by
      unfold Representative.next Representative.map
      congr 1
      apply Subtype.ext
      ext t
      exact f.bond a.stage _ _
    rw [hm]
    exact StableRelation.stabilization (a.map f)

def stableHomotopyMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) (d : ℤ) :
    StableHomotopy X d → StableHomotopy Y d :=
  Quot.map (Representative.map f) (fun _ _ h => Representative.map_relation f h)

/-- Quotient class of a displayed cubical loop. -/
def loopClass (X : Prespectrum.{u}) (d : ℤ) (n r : ℕ)
    (h : (r : ℤ) = d + n)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point) : StableHomotopy X d :=
  Quot.mk _ ⟨n,r,h,p⟩

/-- Stable weak equivalences, defined using the actual point-set system. -/
def stableEquivalences : MorphismProperty Prespectrum.{u} :=
  fun _ _ f => ∀ d : ℤ, Function.Bijective (stableHomotopyMap f d)

end Prespectrum

/-- The uncompleted stable homotopy category presented by sequential spectra.
This is the explicit localization construction, not a supplied category. -/
abbrev SourceCategory := Prespectrum.stableEquivalences.{u}.Localization

abbrev sourceLocalization : Prespectrum.{u} ⥤ SourceCategory.{u} :=
  Prespectrum.stableEquivalences.Q

end KIP126.StableHomotopy.Spectra
