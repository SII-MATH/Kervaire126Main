module

public import KIP126.Computation.LinCoordinates.Model.Classes.Data
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

namespace KIP126.LinE2.SquareDetection

open KIP126.Algebra

/-- A small target which can detect the square without certifying the full CSV basis. -/
abbrev Target := Polynomial F2 ⧸ Ideal.span {((Polynomial.X : Polynomial F2) ^ 3)}

noncomputable def u : Target := Ideal.Quotient.mk _ Polynomial.X

/-- Keep only the h₆ variable, with its cube set to zero. -/
noncomputable def evaluate : Poly →+* Target :=
  MvPolynomial.eval₂Hom ((Ideal.Quotient.mk _).comp Polynomial.C)
    (fun i => if i = h6Generator then u else 0)

/-- Exponent after killing the other variables, capped at three. Malformed
encodings follow `polynomialOfPowers` and evaluate to zero. -/
def orderOfPowers : List ℕ → ℕ
  | [] => 0
  | [_] => 3
  | i :: a :: rest =>
      if i < RawData.generatorCount then
        if i = h6Generator.val then min 3 (a + orderOfPowers rest)
        else if a = 0 then orderOfPowers rest else 3
      else 3

def monomialOrder (code : String) : ℕ :=
  if code = "" then 0
  else orderOfPowers ((code.splitOn ",").map (fun n => n.toNat?.getD 0))

/-- Sufficient, intentionally stronger-than-necessary test: each individual
monomial of the relation dies in the target. -/
def relationCheck (code : String) : Bool :=
  (code.splitOn ";").all (fun m => decide (3 ≤ monomialOrder m))

/-- This finite test is executable; its value is not itself a proof certificate. -/
def allRelationsCheck : Bool := RawData.relations.all relationCheck

end KIP126.LinE2.SquareDetection
