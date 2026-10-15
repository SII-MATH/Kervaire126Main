module

public import KIP126.Def.Synthetic.AdamsSequence.Data

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory
universe v

/-- A genuine common cycle representative; no coercion of arbitrary E₂
classes to later synthetic pages is provided. -/
def RepresentsOnPage (A : SyntheticAdamsSS.{v}) (r : ℤ) (i : Tridegree)
    (x : A.E₂ i) (y : A.Page r i) : Prop :=
  2 ≤ r ∧ ∃ z : (Subobject.underlying.obj
      ((A.sequence.ssData i).Z (↑(r - 2).toNat : WithTop ℕ)) : ModuleCat ℤ),
    (Subobject.ofLE _ _ ((A.sequence.ssData i).Z_anti bot_le) ≫
      (A.sequence.ssData i).pageπ 0) z = x ∧
    (A.sequence.ssData i).pageπ (↑(r - 2).toNat : WithTop ℕ) z = y

/-- An equation for this family's existing differential, with its exact
tridegree and both representatives visible. A nonzero assertion is separate. -/
def HasDifferential (A : SyntheticAdamsSS.{v}) (r : ℤ) (i j : Tridegree)
    (x : A.E₂ i) (y : A.E₂ j) : Prop :=
  ∃ h : syntheticAdamsDifferentialTarget r i = j,
    ∃ (xr : A.Page r i) (yr : A.Page r j),
      RepresentsOnPage A r i x xr ∧ RepresentsOnPage A r j y yr ∧
        (A.d r i ≫ eqToHom (congrArg (A.Page r) h)) xr = yr
end KIP126.Synthetic.SpectralSequence
