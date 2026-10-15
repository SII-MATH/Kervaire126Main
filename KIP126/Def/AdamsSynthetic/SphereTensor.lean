module
public import KIP126.Def.AdamsSynthetic.Sphere
/-! The tensor presentation of a bigraded suspension, derived from the
existing category fields. Source: Def/Synthetic/Sphere/Data.lean:40–43,
bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Synthetic.Context
open CategoryTheory MonoidalCategory
universe u v
public noncomputable def biShift_eq_tensor_Smn {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    (m n : ℤ) (X : Syn) :
    (SyntheticCategory.biShift (m,n)).obj X ≅ Smn m n ⊗ X :=
  (SyntheticCategory.biShift (m,n)).mapIso (λ_ X).symm ≪≫
    SyntheticCategory.biShift_tensor_comm (m,n) (𝟙_ Syn) X
end KIP126.Synthetic.Context
