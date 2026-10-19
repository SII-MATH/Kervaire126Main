module

import KIP126.AdamsSynthetic.Context
import KIP126.AdamsSynthetic.Quotients

/- A narrow independence diagnostic: the current SyntheticCategory record
accepts an arbitrary replacement tensor comparison without any further
equation. This is not an actual HF₂-synthetic countermodel. -/

open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v

namespace KIP126.InterfaceReview.MHLambdaTensor

variable {Syn : Type u} [S : SyntheticCategory.{u,v} Syn]

@[implicit_reducible] def rechooseTensorComparison
    (χ : ∀ (p : ℤ × ℤ) (X Y : Syn),
      (SyntheticCategory.biShift p).obj (MonoidalCategory.tensorObj X Y) ≅
        MonoidalCategory.tensorObj ((SyntheticCategory.biShift p).obj X) Y) :
    SyntheticCategory.{u,v} Syn :=
  { S with biShift_tensor_comm := χ }

theorem rechoose_preserves_lam
    (χ : ∀ (p : ℤ × ℤ) (X Y : Syn),
      (SyntheticCategory.biShift p).obj (MonoidalCategory.tensorObj X Y) ≅
        MonoidalCategory.tensorObj ((SyntheticCategory.biShift p).obj X) Y) :
    (rechooseTensorComparison χ).lam = S.lam := rfl

theorem rechoose_preserves_biShift_comp
    (χ : ∀ (p : ℤ × ℤ) (X Y : Syn),
      (SyntheticCategory.biShift p).obj (MonoidalCategory.tensorObj X Y) ≅
        MonoidalCategory.tensorObj ((SyntheticCategory.biShift p).obj X) Y) :
    (rechooseTensorComparison χ).biShift_comp = S.biShift_comp := rfl

theorem quotient_comparison_difference_factors
    [HasFunctorialCofiber (C := Syn)] {A B : Syn} (n : ℕ)
    (a b : XModLambdaN A n ⟶ B)
    (hab : XModLambdaN.incl A n ≫ a = XModLambdaN.incl A n ≫ b) :
    ∃ z : ((SyntheticCategory.biShift (0,-(n : ℤ))).obj A)⟦(1 : ℤ)⟧ ⟶ B,
      a-b = XModLambdaN.proj A n ≫ z := by
  apply CategoryTheory.Pretriangulated.Triangle.yoneda_exact₃
    (XModLambdaN.cofiberTriangle A n)
    (XModLambdaN.cofiberTriangle_distinguished A n) (a-b)
  change XModLambdaN.incl A n ≫ (a-b) = 0
  rw [Preadditive.comp_sub,hab,sub_self]

#print axioms rechoose_preserves_lam
#print axioms rechoose_preserves_biShift_comp
#print axioms quotient_comparison_difference_factors

end KIP126.InterfaceReview.MHLambdaTensor
