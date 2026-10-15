module

public import KIP126.Def.Synthetic.QuotientFunctor.Restricted.Predicates

@[expose] public section

/-! Only the λ-power cofibers need a functorial choice. This does not require
a strictly functorial cone on *all* commuting squares of a triangulated
homotopy category. Its maps are the existing XModLambdaN.map. -/
namespace KIP126.Synthetic.Context
open CategoryTheory KIP126.StableHomotopy
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
noncomputable def LambdaQuotientFunctoriality.functor (Q : LambdaQuotientFunctoriality (Syn := Syn))
    (n : ℕ) : Syn ⥤ Syn where
  obj X := XModLambdaN X n
  map f := XModLambdaN.map f n
  map_id X := Q.map_id X n
  map_comp f g := Q.map_comp f g n
end KIP126.Synthetic.Context
