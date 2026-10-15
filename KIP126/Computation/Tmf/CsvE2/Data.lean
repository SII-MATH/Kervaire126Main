module

public import KIP126.Def.Algebra.Coefficients.Data
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Span.Defs

@[expose] public section

/-!
# Fixed tmf E₂ coordinate algebra

Exact source: Zenodo record 14875701, v126.3.cw49, kervaire_csv.rar.
Archive MD5: 631257d058529916d62d858e0da27417.
The UTF-16 files have SHA-256:
* tmf_AdamsE2_generators.csv: 11300b5957f2b4ecbf510fff591b90950d3ef3aaef216a602f13c2348cd7b830
* tmf_AdamsE2_relations.csv: 434a05d4edd9979825812c1e194be4f84b855be0e9a3019fa75d57968a1c4df2
All 13 generators and 72 relation rows are retained below, using (s,t),
not the CSV's (stem,s). Each relation is homogeneous in these degrees.
The archive's tmf_AdamsE2_basis.csv is empty: no basis certification is claimed.
This defines a coordinate algebra; identifying it with an actual Adams E₂
page is separate model-comparison data, not a consequence of the file hashes.
-/

namespace KIP126.Classical.Adams.Tmf.CsvE2

open KIP126.Algebra
noncomputable section

abbrev Generator := Fin 13
abbrev Poly := MvPolynomial Generator F2

/-- Generator IDs are exactly the fixed CSV order. -/
def generatorDegree (i : Generator) : ℕ × ℕ :=
  ![(1, 1), (1, 2), (1, 4), (3, 11), (4, 12), (3, 15), (4, 18), (3, 18), (4, 21), (4, 24), (5, 30), (7, 39), (8, 56)] i

/-- Each inner list is a monomial of (generator ID, exponent) pairs. -/
def relationPowers : List (List (List (Generator × ℕ))) := [
  [[(0, 1), (1, 1)]],
  [[(1, 1), (2, 1)]],
  [[(1, 3)], [(0, 2), (2, 1)]],
  [[(0, 3), (2, 1)]],
  [[(0, 1), (2, 2)]],
  [[(2, 3)]],
  [[(0, 1), (3, 1)]],
  [[(2, 1), (3, 1)]],
  [[(1, 2), (3, 1)]],
  [[(1, 1), (5, 1)]],
  [[(2, 1), (5, 1)], [(0, 1), (7, 1)]],
  [[(1, 1), (7, 1)]],
  [[(1, 1), (6, 1)], [(0, 2), (7, 1)]],
  [[(2, 2), (4, 1)], [(0, 2), (6, 1)]],
  [[(0, 3), (7, 1)]],
  [[(0, 3), (6, 1)]],
  [[(2, 1), (6, 1)], [(0, 1), (8, 1)]],
  [[(3, 2)]],
  [[(1, 1), (8, 1)], [(0, 1), (2, 1), (7, 1)]],
  [[(0, 2), (2, 1), (7, 1)]],
  [[(0, 3), (8, 1)]],
  [[(2, 1), (8, 1)], [(0, 1), (9, 1)]],
  [[(2, 2), (7, 1)], [(1, 1), (9, 1)]],
  [[(3, 1), (5, 1)], [(0, 2), (9, 1)]],
  [[(0, 3), (9, 1)]],
  [[(2, 1), (9, 1)]],
  [[(1, 2), (9, 1)]],
  [[(3, 1), (7, 1)]],
  [[(3, 1), (6, 1)]],
  [[(0, 1), (10, 1)]],
  [[(3, 1), (8, 1)]],
  [[(2, 1), (10, 1)]],
  [[(1, 2), (10, 1)], [(0, 1), (5, 1), (7, 1)]],
  [[(2, 1), (4, 1), (7, 1)], [(0, 1), (5, 1), (6, 1)]],
  [[(3, 1), (9, 1)]],
  [[(0, 2), (5, 1), (7, 1)]],
  [[(6, 1), (7, 1)], [(5, 1), (8, 1)]],
  [[(6, 2)], [(4, 1), (9, 1)]],
  [[(0, 1), (7, 2)]],
  [[(1, 1), (4, 1), (9, 1)], [(0, 2), (5, 1), (8, 1)]],
  [[(7, 1), (8, 1)], [(5, 1), (9, 1)]],
  [[(2, 1), (7, 2)]],
  [[(0, 1), (11, 1)]],
  [[(0, 1), (6, 1), (8, 1)]],
  [[(3, 1), (10, 1)], [(1, 1), (11, 1)]],
  [[(8, 2)], [(6, 1), (9, 1)]],
  [[(2, 1), (11, 1)]],
  [[(0, 1), (7, 1), (9, 1)]],
  [[(1, 2), (11, 1)], [(0, 1), (6, 1), (9, 1)]],
  [[(0, 2), (6, 1), (9, 1)]],
  [[(8, 1), (9, 1)], [(5, 1), (10, 1)]],
  [[(9, 2)], [(7, 1), (10, 1)]],
  [[(6, 1), (10, 1)], [(5, 2), (7, 1)]],
  [[(5, 2), (6, 1)], [(4, 1), (7, 2)]],
  [[(0, 1), (5, 2), (7, 1)]],
  [[(3, 1), (11, 1)]],
  [[(8, 1), (10, 1)], [(5, 1), (7, 2)]],
  [[(0, 1), (5, 2), (8, 1)]],
  [[(9, 1), (10, 1)], [(7, 3)]],
  [[(5, 1), (11, 1)], [(5, 2), (9, 1)]],
  [[(5, 1), (6, 1), (8, 1)], [(4, 1), (7, 1), (9, 1)]],
  [[(0, 1), (5, 2), (9, 1)]],
  [[(7, 1), (11, 1)], [(5, 1), (7, 1), (9, 1)]],
  [[(6, 1), (11, 1)], [(5, 1), (6, 1), (9, 1)]],
  [[(0, 1), (5, 1), (6, 1), (9, 1)]],
  [[(10, 2)], [(7, 2), (9, 1)], [(1, 2), (12, 1)]],
  [[(8, 1), (11, 1)], [(5, 2), (10, 1)]],
  [[(5, 4)], [(4, 1), (7, 1), (10, 1)], [(0, 4), (12, 1)]],
  [[(9, 1), (11, 1)], [(5, 1), (7, 1), (10, 1)]],
  [[(5, 3), (8, 1)], [(4, 1), (7, 3)]],
  [[(10, 1), (11, 1)], [(5, 1), (7, 3)], [(1, 1), (3, 1), (12, 1)]],
  [[(11, 2)], [(5, 2), (7, 1), (10, 1)]]
]

/-- Direct evaluation of the typed monomial encoding; no parser fallback. -/
def polynomialOfPowers (powers : List (Generator × ℕ)) : Poly :=
  (powers.map fun p => MvPolynomial.X p.1 ^ p.2).prod

def relationPolynomial (terms : List (List (Generator × ℕ))) : Poly :=
  (terms.map polynomialOfPowers).sum

def definingIdeal : Ideal Poly :=
  Ideal.span {p | ∃ terms ∈ relationPowers, p = relationPolynomial terms}

abbrev E2 := Poly ⧸ definingIdeal

def projection : Poly →+* E2 := Ideal.Quotient.mk definingIdeal

def generator (i : Generator) : E2 := projection (MvPolynomial.X i)

def monomialDegree (m : Generator →₀ ℕ) : ℕ × ℕ :=
  m.sum fun i a => (a * (generatorDegree i).1, a * (generatorDegree i).2)

def homogeneousPart (s t : ℕ) : Submodule F2 E2 :=
  Submodule.span F2 {x | ∃ m : Generator →₀ ℕ,
    monomialDegree m = (s, t) ∧ x = projection (MvPolynomial.monomial m 1)}

abbrev E2At (s t : ℕ) := ↥(homogeneousPart s t)

/-- CSV generator 12 is w₂ in degree (8,56); v₂¹⁶ denotes its square.
There is no assumption that an E₂ element named v₂ exists. -/
def v2SixteenValue : E2 := generator 12 ^ 2

/-- BR21 Table 5.4 writes the differential target as βg⁴.
The exact equality with the selected β⁵g expression is proved from two
relations of this quotient in CsvE2/Proofs.lean. -/
def betaGFourValue : E2 := generator 7 * generator 9 ^ 4

/-- CSV generator 7 is β in degree (3,18), and generator 9 is g in (4,24). -/
def betaFiveGValue : E2 := generator 7 ^ 5 * generator 9

end
end KIP126.Classical.Adams.Tmf.CsvE2
