module

public import KIP126.Def.SpectralSequence.Computation.Predicates

@[expose] public section

/-!
# Page representatives, boundaries and survival

These predicates only use the actual internal spectral sequence and its
common representatives. They do not interpret a raw program row. In
particular, unknown program values are not mathematical assertions, and
permanent-cycle membership does not require a nonzero E∞ class.
-/

namespace KIP126.SpectralSequence

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

/-- A label has a representative on the stated page; its class there may
be zero. This is the cycle information stored by an unresolved outgoing
staircase entry, not nonzero survival. -/
def ReachesPage
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  ∃ xr : E.Page r p, RepresentsOnPage E r p x xr

/-- The E₂ label is in the boundary subobject after page `r`. This
allows an earlier hit, a sum of boundaries, and zero; an unresolved
incoming staircase entry does not specify one nonzero differential. -/
def IsBoundaryBy
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (r : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  2 ≤ r ∧
    let D := E.ssData p
    let n : WithTop ℕ := ↑(2 - E.r₀).toNat
    let m : WithTop ℕ := ↑(r + 1 - E.r₀).toNat
    ∃ b : (Subobject.underlying.obj (D.B m) : ModuleCat R),
      (Subobject.ofLE (D.B m) (D.B ⊤) (D.B_mono le_top) ≫
        Subobject.ofLE (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) ≫
        Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n) b = x

/-- A common permanent-cycle representative of the given E₂ class.
Its E∞ image may be zero. This deliberately omits the nonvanishing
condition in `NonzeroSurvival`. -/
def IsPermanentCycle
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2 - E.r₀).toNat
  ∃ z : (Subobject.underlying.obj (D.Z ⊤) : ModuleCat R),
    (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ D.pageπ n) z = x

/-- No nonzero incoming hit in the specified nonempty window. This
does not assert existence of continuations or absence of outgoing
differentials, and is not an unrestricted permanence claim. -/
def NeverHitOnWindow
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (first last : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) : Prop :=
  2 ≤ first ∧ first ≤ last ∧
    ∀ r : ℤ, first ≤ r → r ≤ last → ¬ HitOnPage E r p x

/-- Every outgoing differential at this bidegree is zero on every page
from E₂ onward. This permits a zero page and does not assert survival of a label. -/
def NoOutgoingAt
    (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)) (s t : ℤ) : Prop :=
  ∀ r : ℤ, 2 ≤ r → ∀ x : E.Page r (s, t), E.d r (s, t) x = 0

end KIP126.SpectralSequence
