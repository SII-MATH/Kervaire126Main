module

public import KIP126.Def.Synthetic.Context.Data

@[expose] public section

/-! Natural-transformation presentation of the existing pointwise λ powers. -/

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The same recursive λ powers, constructed as natural transformations.
Their components are proved equal to the existing `lambdaPow` separately. -/
noncomputable def lambdaPowNatTrans : (n : ℕ) →
    SyntheticCategory.biShift (0, -(n : ℤ)) ⟶ 𝟭 Syn
  | 0 => SyntheticCategory.biShift_zero.hom
  | n + 1 => by
      have step : SyntheticCategory.biShift ((0 : ℤ), -1) ⋙
          SyntheticCategory.biShift ((0 : ℤ), -(n : ℤ)) ⟶ 𝟭 Syn :=
        Functor.whiskerRight SyntheticCategory.lam
            (SyntheticCategory.biShift ((0 : ℤ), -(n : ℤ))) ≫
          lambdaPowNatTrans n
      have result : SyntheticCategory.biShift ((0, -1) + (0, -(n : ℤ))) ⟶ 𝟭 Syn :=
        (SyntheticCategory.biShift_comp (0, -1) (0, -(n : ℤ))).inv ≫ step
      have heq : ((0 : ℤ), (-1 : ℤ)) + ((0 : ℤ), -(n : ℤ)) =
          ((0 : ℤ), -(↑(n + 1) : ℤ)) := by simp
      exact heq ▸ result

end KIP126.Synthetic.Context
