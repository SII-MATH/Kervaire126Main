module

public import KIP126.Def.AdamsSynthetic.Families

/-! Operations now consumed by the literature contracts. Suspension uses
the specified fully faithful shift; finite-page equations retain common
representatives in the actual trigraded sequence. Adapted from
Def/Synthetic/Sphere/Data and AdamsSequence at bbac1fc05843 (Apache-2.0). -/

@[expose] section
namespace KIP126.Synthetic.Context
open CategoryTheory
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]

public noncomputable def susp_invariance (m n k l : ℤ) (X : Syn) :
    BiHom m n X ≃ BiHom (m+k) (n+l) ((SyntheticCategory.biShift (k,l)).obj X) := by
  refine ((SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (k,l)).homEquiv).trans ?_
  exact Iso.homCongr ((SyntheticCategory.biShift_comp (m,n) (k,l)).app S_0_0) (Iso.refl _)
end KIP126.Synthetic.Context

namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.Synthetic.SpectralSequence
universe v

public def SyntheticRepresentsOnPage (E : SyntheticAdamsSS.{v}) (r : ℤ)
    (p : Tridegree) (x : E.E₂ p) (y : E.Page r p) : Prop :=
  ∃ hr : 2 ≤ r,
    let A := E.sequence.ssData p
    let n : WithTop ℕ := ↑(2-E.sequence.r₀).toNat
    let m : WithTop ℕ := ↑(r-E.sequence.r₀).toNat
    ∃ z : (Subobject.underlying.obj (A.Z m) : ModuleCat ℤ),
      (Subobject.ofLE _ _ (A.Z_anti (by
        dsimp [n,m]; exact_mod_cast (show (2-E.sequence.r₀).toNat ≤
          (r-E.sequence.r₀).toNat by omega))) ≫ A.pageπ n) z = x ∧ A.pageπ m z = y

public def SyntheticHasDifferential (E : SyntheticAdamsSS.{v}) (r : ℤ)
    (p q : Tridegree) (x : E.E₂ p) (y : E.E₂ q) : Prop :=
  ∃ h : p+E.sequence.diffDeg r = q,
    ∃ (xr : E.Page r p) (yr : E.Page r q),
      SyntheticRepresentsOnPage E r p x xr ∧ SyntheticRepresentsOnPage E r q y yr ∧
      (E.sequence.d r p ≫ eqToHom (congrArg (E.Page r) h)) xr = yr
end KIP126.AdamsSynthetic
