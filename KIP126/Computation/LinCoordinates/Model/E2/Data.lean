module

public import KIP126.Computation.LinCoordinates.Generated.E2
public import KIP126.Def.Algebra.Coefficients.Data
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Span.Defs

@[expose] public section

/-!
The concrete truncated algebra from PR #110, pinned at
ff39e95147712fc00cd3f700e0dd1f490d16b863. All CSV data are retained. This is a
data algebra, not an assertion that the CSV computes the actual Adams page.
No reduction-algorithm soundness assumption is imported.
-/
namespace KIP126.LinE2

open KIP126.Algebra

abbrev Generator := Fin RawData.generatorCount
abbrev Poly := MvPolynomial Generator F2

def generatorDegree (i : Generator) : ℕ × ℕ :=
  let row := RawData.generators[i.val]!
  (row.2.1, row.2.2)

def generatorName (i : Generator) : String :=
  (RawData.generators[i.val]!).1

noncomputable def polynomialOfPowers : List ℕ → Poly
  | [] => 1
  | i :: a :: rest =>
      if h : i < RawData.generatorCount then
        MvPolynomial.X ⟨i, h⟩ ^ a * polynomialOfPowers rest
      else 0
  | [_] => 0

noncomputable def monomialOfString (s : String) : Poly :=
  if s = "" then 1
  else polynomialOfPowers ((s.splitOn ",").map (fun n => n.toNat?.getD 0))

noncomputable def relationPolynomial (s : String) : Poly :=
  ((s.splitOn ";").map monomialOfString).sum

def monomialDegree (m : Generator →₀ ℕ) : ℕ × ℕ :=
  m.sum fun i a => (a * (generatorDegree i).1, a * (generatorDegree i).2)

noncomputable def definingRelations : Set Poly :=
  {p | (∃ code ∈ RawData.relations, p = relationPolynomial code) ∨
    (∃ m : Generator →₀ ℕ,
      261 < (monomialDegree m).2 ∧ p = MvPolynomial.monomial m 1)}

noncomputable def definingIdeal : Ideal Poly := Ideal.span definingRelations

/-- The fixed CSV quotient, with all internal degrees above 261 truncated. -/
abbrev E2 := Poly ⧸ definingIdeal

noncomputable def projection : Poly →+* E2 := Ideal.Quotient.mk definingIdeal

noncomputable def generator (i : Generator) : E2 := projection (MvPolynomial.X i)

noncomputable def multiply (a b : E2) : E2 := a * b

noncomputable def homogeneousPart (s t : ℕ) : Submodule F2 E2 :=
  Submodule.span F2 {x | ∃ m : Generator →₀ ℕ,
    monomialDegree m = (s, t) ∧ x = projection (MvPolynomial.monomial m 1)}

abbrev E2At (s t : ℕ) := ↥(homogeneousPart s t)

/-- Zero-based CSV generator 69: h₆. -/
def h6Generator : Generator := ⟨69, by decide⟩

end KIP126.LinE2
