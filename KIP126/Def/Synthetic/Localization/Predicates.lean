module

public import KIP126.Def.Synthetic.Localization.Data

@[expose] public section

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- Maps into every actual λ-invertible object see this morphism as an
equivalence: precomposition is bijective on the specified hom sets. -/
def IsLambdaLocalEquivalence {X Y : Syn} (f : X ⟶ Y) : Prop :=
  ∀ (Z : Syn), IsLambdaInvertible Z →
    Function.Bijective (fun g : Y ⟶ Z => f ≫ g)

end KIP126.Synthetic.Context
