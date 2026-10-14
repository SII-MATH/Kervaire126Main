module

public import KIP126.Def.SpectralSequence.Permanence.Predicates
import all KIP126.Def.SpectralSequence.Permanence.Predicates

@[expose] section

namespace KIP126.Core.SpectralSequence
open CategoryTheory
universe u v

/-- Kernel membership for an actual page element, with no survival claim. -/
public def IsPageCycle {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p : ℤ × ℤ) (x : E.Page r p) : Prop := E.d r p x = 0

/-- Membership in the image of the actual page differential with source
degree `p`. The target degree is `p + E.diffDeg r`. Zero is allowed: this is
boundary membership, not the assertion of a nonzero incoming hit. -/
public def IsPageBoundary {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p : ℤ × ℤ) (y : E.Page r (p + E.diffDeg r)) : Prop :=
  ∃ x : E.Page r p, E.d r p x = y

/-- A later-page class represented by the given E₂ class. This is not a map
from all of E₂ to Eᵣ. A common cycle representative is required. -/
public def RepresentsOnPage {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) (y : E.Page r p) : Prop :=
  ∃ hr : 2 ≤ r,
    let D := E.ssData p
    let n : WithTop ℕ := ↑(2 - E.r₀).toNat
    let m : WithTop ℕ := ↑(r - E.r₀).toNat
    ∃ z : (Subobject.underlying.obj (D.Z m) : ModuleCat R),
      (Subobject.ofLE (D.Z m) (D.Z n) (D.Z_anti (by
        change (↑(2 - E.r₀).toNat : WithTop ℕ) ≤ ↑(r - E.r₀).toNat
        exact_mod_cast (show (2 - E.r₀).toNat ≤ (r - E.r₀).toNat by omega))) ≫
        D.pageπ n) z = x ∧ D.pageπ m z = y

/-- Survival *to* Eᵣ means a nonzero class there, not that dᵣ vanishes. -/
public def SurvivesTo {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  ∃ y : E.Page r p, RepresentsOnPage E r p x y ∧ y ≠ 0

/-- No nonzero continuation is an incoming differential target. This alone
does not exclude an outgoing differential on x. -/
public def NeverHit {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  ∀ (r : ℤ) (_ : 2 ≤ r) (q : ℤ × ℤ) (h : q + E.diffDeg r = p)
    (y : E.Page r p), RepresentsOnPage E r p x y → y ≠ 0 →
    ∀ z : E.Page r q, (E.d r q ≫ eqToHom (congrArg (E.Page r) h)) z ≠ y

/-- Vanishing on all continuations of a fixed E₂ class on one page.
This predicate alone does not assert that any continuation exists. -/
public def DifferentialVanishesOn {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  ∀ xr : E.Page r p, RepresentsOnPage E r p x xr → E.d r p xr = 0

/-- Every differential on a continuation is zero or represented by the
specified target. The nonzero alternative is not assumed to occur. -/
public def DifferentialTargets {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p)
    (y : E.Page 2 (p + E.diffDeg r)) : Prop :=
  ∀ xr : E.Page r p, RepresentsOnPage E r p x xr →
    E.d r p xr = 0 ∨
      ∃ yr : E.Page r (p + E.diffDeg r),
        RepresentsOnPage E r (p + E.diffDeg r) y yr ∧ E.d r p xr = yr

/-- An equation for the existing differential between specified E₂ labels.
Both labels must admit a common-cycle representative on page r. Zero targets
are allowed; later-page nonvanishing is the stronger predicate below.
Ported from the useful local-differential interface in KIPBase. -/
public def HasDifferential {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p q : ℤ × ℤ) (x : E.Page 2 p) (y : E.Page 2 q) : Prop :=
  ∃ h : p + E.diffDeg r = q,
    ∃ (xr : E.Page r p) (yr : E.Page r q),
      RepresentsOnPage E r p x xr ∧ RepresentsOnPage E r q y yr ∧
        (E.d r p ≫ eqToHom (congrArg (E.Page r) h)) xr = yr

/-- A nonzero differential between specified E₂ representatives, with both
classes lifted to the actual r-th page and the degree transport made explicit. -/
public def HasNonzeroDifferential {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p q : ℤ × ℤ) (x : E.Page 2 p) (y : E.Page 2 q) : Prop :=
  ∃ h : p + E.diffDeg r = q,
    ∃ (xr : E.Page r p) (yr : E.Page r q),
      RepresentsOnPage E r p x xr ∧ RepresentsOnPage E r q y yr ∧
        (E.d r p ≫ eqToHom (congrArg (E.Page r) h)) xr = yr ∧ yr ≠ 0

/-- Some differential hits a nonzero r-page continuation of x. -/
public def HitOnPage {R : Type u} [Ring R]
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  ∃ (q : ℤ × ℤ) (h : q + E.diffDeg r = p) (z : E.Page r q)
    (y : E.Page r p), RepresentsOnPage E r p x y ∧ y ≠ 0 ∧
      (E.d r q ≫ eqToHom (congrArg (E.Page r) h)) z = y

end KIP126.Core.SpectralSequence
