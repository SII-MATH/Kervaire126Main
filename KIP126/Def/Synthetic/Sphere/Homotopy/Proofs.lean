module

public import KIP126.Def.Synthetic.Sphere.Homotopy.Predicates
public import Mathlib.CategoryTheory.Triangulated.Yoneda

@[expose] public section

namespace KIP126.Synthetic.Context
open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The quotient predicate is equivalent to actual factorization through λʳ,
by exactness of its specified distinguished cofiber triangle. -/
theorem vanishesModLambda_iff_factors {m n : ℤ} {X : Syn} (r : ℕ)
    (x : BiHom m n X) :
    VanishesModLambda r x ↔
      ∃ y : Smn m n ⟶ (SyntheticCategory.biShift (0, -(r : ℤ))).obj X,
        y ≫ lambdaPow r X = x := by
  let T := XModLambdaN.cofiberTriangle X r
  have hT : T ∈ distTriang Syn := HasFunctorialCofiber.cofib_distinguished _
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := T.coyoneda_exact₂ hT x hx
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    change (y ≫ lambdaPow r X) ≫ XModLambdaN.incl X r = 0
    have hz : lambdaPow r X ≫ XModLambdaN.incl X r = 0 :=
      comp_distTriang_mor_zero₁₂ T hT
    rw [Category.assoc, hz, Limits.comp_zero]

end KIP126.Synthetic.Context
