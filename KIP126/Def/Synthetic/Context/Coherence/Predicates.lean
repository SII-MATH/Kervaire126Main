module

public import KIP126.Def.Synthetic.Context.Coherence.Data

@[expose] public section

/-! Exact coherence conditions on the *specified* `biShift`, comparisons,
and deformation transformation. The record supplies no replacement data. -/

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

variable (Syn : Type u) [SyntheticCategory.{u, v} Syn]

/-- Associativity, units, and centrality of λ for the existing suspension
comparisons. The named intermediate and final degrees only make every
transport explicit; their equalities determine them uniquely. -/
structure BiShiftCoherence : Prop where
  associativity : ∀ (a b c ab bc total : ℤ × ℤ)
      (hab : a + b = ab) (hbc : b + c = bc)
      (habc : ab + c = total) (habc' : a + bc = total) (X : Syn),
    (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).hom.app X) ≫
        (biShiftAddIso ab c total habc).hom.app X =
      (biShiftAddIso b c bc hbc).hom.app ((SyntheticCategory.biShift a).obj X) ≫
        (biShiftAddIso a bc total habc').hom.app X
  left_unit : ∀ (a : ℤ × ℤ) (X : Syn),
    (biShiftAddIso 0 a a (zero_add a)).hom.app X =
      (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app X)
  right_unit : ∀ (a : ℤ × ℤ) (X : Syn),
    (biShiftAddIso a 0 a (add_zero a)).hom.app X =
      SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj X)
  lambda_comm : ∀ (a : ℤ × ℤ) (X : Syn),
    SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj X) =
      (biShiftAddIso a (0, -1) (a + (0, -1)) rfl).hom.app X ≫
        (biShiftAddIso (0, -1) a (a + (0, -1)) (add_comm _ _)).inv.app X ≫
        (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app X)

end KIP126.Synthetic.Context
