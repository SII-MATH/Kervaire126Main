module

public import KIP126.Computation.LinCoordinates.Interpretation.Near126.Classes.Data
public import KIP126.Main.Computation.LinCoordinates.Interpretation.Classes.Data
public import KIP126.Def.SpectralSequence.Computation.Predicates

@[expose] public section

/-! All predicates below concern the *fixed* tower-derived internal sphere
sequence, via its existing Lin comparison. None asserts an external fact. -/
namespace KIP126.Computation.Near126.Sphere
open CategoryTheory KIP126.LinE2 KIP126.Classical.Adams
open KIP126.SpectralSequence

def Differential {s t u v : Nat} (r : ℤ) (x : E2At s t) (y : E2At u v) : Prop :=
  ∃ (hx : t ≤ 261) (hy : v ≤ 261),
    HasNonzeroDifferential sphereAdamsData r (s, t) (u, v)
      (linToSphereE2 s t hx x) (linToSphereE2 u v hy y)

def Survival {s t : Nat} (r : ℤ) (x : E2At s t) : Prop :=
  ∃ h : t ≤ 261, SurvivesTo sphereAdamsData r (s, t) (linToSphereE2 s t h x)

def NotHit {s t : Nat} (x : E2At s t) : Prop :=
  ∃ h : t ≤ 261, NeverHit sphereAdamsData (s, t) (linToSphereE2 s t h x)

def Permanent {s t : Nat} (x : E2At s t) : Prop :=
  ∃ h : t ≤ 261, NonzeroSurvival sphereAdamsData (s, t) (linToSphereE2 s t h x)

def NoOutgoing {s t : Nat} (x : E2At s t) : Prop :=
  ∃ h : t ≤ 261, ∀ (r : ℤ) (_ : 2 ≤ r) (y : sphereAdamsData.Page r (s, t)),
    RepresentsOnPage sphereAdamsData r (s, t) (linToSphereE2 s t h x) y →
      sphereAdamsData.d r (s, t) y = 0

/-- Exhaustion of incoming possibilities, including the specified sources.
It asserts neither that d₆(W) vanishes nor that d₁₂(h₆²) is nonzero. -/
def OnlyIncomingT : Prop :=
  ∀ (r : ℤ), HitOnPage sphereAdamsData r (14, 139)
      (linToSphereE2 14 139 (by decide) T) →
    (r = 6 ∧ Differential 6 W T) ∨ (r = 12 ∧ Differential 12 dataH6Sq T)

/-- The indicated E₅ component has exactly the zero class and this class.
This is a statement about the whole group, not just the listed table rows. -/
def HighComponentExhaustion : Prop :=
  ∃ y : sphereAdamsData.Page 5 (25, 150),
    RepresentsOnPage sphereAdamsData 5 (25, 150)
      (linToSphereE2 25 150 (by decide) highClass) y ∧
      y ≠ 0 ∧ ∀ z : sphereAdamsData.Page 5 (25, 150), z = 0 ∨ z = y

/-- All E₆ continuations of W have differential zero or represented by T. -/
def D6WTargets : Prop :=
  DifferentialTargets sphereAdamsData 6 (8, 134)
    (linToSphereE2 8 134 (by decide) W)
    (linToSphereE2 14 139 (by decide) T)

end KIP126.Computation.Near126.Sphere
