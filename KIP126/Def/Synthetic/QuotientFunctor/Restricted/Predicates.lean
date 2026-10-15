module

public import KIP126.Def.Synthetic.QuotientMap.Data

@[expose] public section

/-! Only the λ-power cofibers need a functorial choice. This does not require
a strictly functorial cone on *all* commuting squares of a triangulated
homotopy category. Its maps are the existing XModLambdaN.map. -/
namespace KIP126.Synthetic.Context
open CategoryTheory KIP126.StableHomotopy
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
structure LambdaQuotientFunctoriality : Prop where
  map_id : ∀ (X : Syn) (n : ℕ), XModLambdaN.map (𝟙 X) n = 𝟙 _
  map_comp : ∀ {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ),
    XModLambdaN.map (f ≫ g) n = XModLambdaN.map f n ≫ XModLambdaN.map g n

end KIP126.Synthetic.Context
