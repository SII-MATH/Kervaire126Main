module

public import KIP126.Def.Synthetic.QuotientRestrictions.Data
public import KIP126.Def.Synthetic.Context.Coherence.Restrictions.Proofs
public import KIP126.Def.StableHomotopy.Context.CofiberCoherence.Proofs

@[expose] public section

/-! Identity, composition, and object naturality for the already defined
quotient restrictions. The hypotheses constrain the original suspension and
cofiber choices; no alternative restriction maps are selected. -/

namespace KIP126.Synthetic.Context

open CategoryTheory KIP126.StableHomotopy

set_option backward.isDefEq.respectTransparency false

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

@[simp] theorem XModLambdaN.restriction_self
    (coh : BiShiftCoherence Syn) (cofib : FunctorialCofiberCoherence Syn)
    (X : Syn) (i : ℕ) : XModLambdaN.restriction coh X i i le_rfl =
      𝟙 (XModLambdaN X i) := by
  dsimp only [XModLambdaN.restriction]
  simp only [lambdaRestrictionSourceMap_self coh]
  exact cofib.map_id (lambdaPow i X) _

theorem XModLambdaN.restriction_comp
    (coh : BiShiftCoherence Syn) (cofib : FunctorialCofiberCoherence Syn)
    (X : Syn) (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    XModLambdaN.restriction coh X j k hjk ≫ XModLambdaN.restriction coh X i j hij =
      XModLambdaN.restriction coh X i k (hij.trans hjk) := by
  dsimp only [XModLambdaN.restriction]
  rw [cofib.cofibMap_comp]
  simp only [lambdaRestrictionSourceMap_comp coh, Category.comp_id]

theorem XModLambdaN.restriction_naturality
    (coh : BiShiftCoherence Syn) (cofib : FunctorialCofiberCoherence Syn)
    {X Y : Syn} (f : X ⟶ Y) (i j : ℕ) (hij : i ≤ j) :
    XModLambdaN.map f j ≫ XModLambdaN.restriction coh Y i j hij =
      XModLambdaN.restriction coh X i j hij ≫ XModLambdaN.map f i := by
  dsimp only [XModLambdaN.map, XModLambdaN.restriction]
  rw [cofib.cofibMap_comp, cofib.cofibMap_comp]
  simp only [Category.comp_id, Category.id_comp]
  exact HasFunctorialCofiber.cofibMap_congr _ _
    (lambdaRestrictionSourceMap_naturality i j hij f) rfl _ _

end KIP126.Synthetic.Context
