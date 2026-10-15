module

public import KIP126.Def.Kervaire.Theta5.Data

@[expose] public section

/-! Predicates for the abstract θ₅ choice-comparison argument.
These definitions state conditions on `Theta5ChoiceContext`. Their
interpretation on the actual synthetic sphere requires the corresponding
homotopy classes, operations and Adams comparisons; defining the predicates
does not assume or prove them. -/

namespace KIP126.Kervaire

section SourceTheorems

variable {Carrier : Type} [AddCommGroup Carrier]
variable (C : Theta5ChoiceContext (Carrier := Carrier))

/-- Order and choice-filtration conditions. On the synthetic sphere these require
deductions from classical Xu/IWX results and the comparison/torsion hypotheses;
they must not be catalogued wholesale as a prior literature theorem. -/
def Theta5OrderData : Prop :=
  (∀ θ, C.isChoice θ → IsOrderTwo θ) ∧
    (∀ θ ψ, C.isChoice θ → C.isChoice ψ →
      C.highDifference (C.difference θ ψ))

/-- Paper-normalized source criterion (historical name retained). Its finite
clause uses λη and exponent r+1. Burklund--Xu Proposition 7.19 instead uses η
and exponent r; LWX Remark 7.4 needs a no-λ-torsion argument to pass between them.
This predicate is distinct from the original literature statement. Choice independence
requires its explicit order and filtration hypotheses; its interpretation
on the actual synthetic sphere is a separate comparison. -/
def BJM_BXCriterion : Prop :=
  IsOrderTwo C.sourceChoice ∧
    (∀ r : ℕ, 1 ≤ r →
      (C.h6Survives (r + 3) ↔
        C.finiteZero (r + 1) C.sourceExpression)) ∧
    (C.is_permanent C.sourceExpression ↔ C.untruncatedZero C.sourceExpression)

/-- The located total-differential identity for the distinguished source choice. -/
def DistinguishedThetaTotalDifferentialIdentity : Prop :=
  C.deltaH6 = C.lambdaEta (C.square C.sourceChoice)

/-- The total-differential identity for every permitted order-two representative.
Choice independence is a conclusion of the argument, stated here as a predicate. -/
def TotalDifferentialIdentity : Prop :=
  ∀ θ, C.isChoice θ → IsOrderTwo θ →
    C.deltaH6 = C.lambdaEta (C.square θ)

/-- Order and choice-filtration conditions together with two λ-torsion
conditions. Each conjunct retains its own mathematical hypothesis; the
conjunction is not asserted as a single external computation result. -/
def Theta5OrderAndLambdaTorsionConditions : Prop :=
  Theta5OrderData C ∧ C.noLambdaTorsion62 ∧ C.noLambdaTorsion125

/-- Browder's geometric criterion, parameterized by one fixed framed context.
The existential side is the dimension-indexed statement used by the endpoint
theorems; the Adams permanence predicate is supplied by the same fixed sphere
sequence. -/
def BrowderCriterionStatement
    {Manifold : Type}
    (dimension : Manifold → ℕ)
    (kervaireOne : Manifold → Prop)
    (permanent : ℕ → Prop) : Prop :=
  ∀ n : ℕ,
    ((∃ M, dimension M = n ∧ kervaireOne M) ↔
      ∃ j : ℕ, 1 ≤ j ∧ n = 2 ^ (j + 1) - 2 ∧ permanent j)

/-- The HHR nonexistence result, with the project's framed-manifold predicate
and dimension convention as explicit parameters. -/
def HHRNonexistenceStatement
    {Manifold : Type}
    (dimension : Manifold → ℕ)
    (kervaireOne : Manifold → Prop) : Prop :=
  ∀ j : ℕ, 7 ≤ j →
    ¬ ∃ M, dimension M = 2 ^ (j + 1) - 2 ∧ kervaireOne M

/-- The Barratt--Jones--Mahowald inductive input. -/
def BJMInductionStatement
    {Class : Type}
    (detected : ℕ → Class → Prop)
    (isOrderTwo : Class → Prop)
    (squareZero : Class → Prop) : Prop :=
  ∀ j : ℕ, ∀ θ : Class,
    detected j θ → isOrderTwo θ → squareZero θ →
      ∃ next : Class, detected (j + 1) next ∧ isOrderTwo next

end SourceTheorems

end KIP126.Kervaire
