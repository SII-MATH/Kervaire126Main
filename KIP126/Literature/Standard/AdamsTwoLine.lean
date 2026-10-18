module

public import KIP126.Literature.Standard

/-! Classical inputs for AimPaper Corollary 1.5, on the fixed sphere Adams
sequence. Original sources and adaptation limits are recorded in Blueprint.
Each source-to-model statement is a separate registered upstream obligation;
the exhaustive classification itself is proved in Main. -/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)

/-- The actual product of the two specified standard one-line classes. -/
public noncomputable def hiProduct (i j : ℕ) :
    ActualE2At model.classical (hiDegree i + hiDegree j) :=
  model.sphereAlgebra.product (hiDegree i) (hiDegree j)
    (model.standardClasses.standardHi i) (model.standardClasses.standardHi j)

/-- May's three exceptional low-dimensional mixed products. -/
public theorem may_two_line_products_permanent (i j : ℕ)
    (h : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 4)) :
    NonzeroSurvival model.classical.sphere (hiDegree i + hiDegree j) (hiProduct i j) := by
  sorry

/-- The low Kervaire squares, including the degree-zero class h₀². -/
public theorem may_low_squares_permanent (j : ℕ) (hj : j ≤ 3) :
    NonzeroSurvival model.classical.sphere (2,((2^(j+1) : ℕ) : ℤ))
      (model.standardClasses.standardHiSquare j) := by
  sorry

/-- Mahowald--Tangora's 30-stem Kervaire class. -/
public theorem mahowald_tangora_h4_square_permanent :
    NonzeroSurvival model.classical.sphere (2,32)
      (model.standardClasses.standardHiSquare 4) := by
  sorry

/-- Mahowald, Theorem 1', restricted to the family needed by Corollary 1.5. -/
public theorem mahowald_eta_family_permanent (j : ℕ) (hj : 3 ≤ j) :
    NonzeroSurvival model.classical.sphere (hiDegree 1 + hiDegree j) (hiProduct 1 j) := by
  sorry

/-- Only the nonzero differential and its actual target degree are chosen;
no arbitrary E₂ symbol is substituted for the target. -/
public theorem mahowald_tangora_h2_h5_d3 :
    ∃ y : model.classical.sphere.Page 2 (5,38),
      HasNonzeroDifferential model.classical.sphere 3 (2,36) (5,38) (hiProduct 2 5) y := by
  sorry

public theorem mahowald_tangora_h3_h5_d4 :
    ∃ y : model.classical.sphere.Page 2 (6,43),
      HasNonzeroDifferential model.classical.sphere 4 (2,40) (6,43) (hiProduct 3 5) y := by
  sorry

public theorem iwx_h3_h6_d3 :
    ∃ y : model.classical.sphere.Page 2 (5,74),
      HasNonzeroDifferential model.classical.sphere 3 (2,72) (5,74) (hiProduct 3 6) y := by
  sorry

/-- IWX's nonzero classical d₃ on h₀h₄. This class reaches E₃ and must
therefore be retained by d₂-stage screening before this later exclusion. -/
public theorem iwx_h0_h4_d3 :
    ∃ y : model.classical.sphere.Page 2 (5,19),
      HasNonzeroDifferential model.classical.sphere 3 (2,17) (5,19) (hiProduct 0 4) y := by
  sorry

/-- HHR's nonexistence theorem transported to the specified standard squares.
It neither selects a differential length nor asserts a known target. -/
public theorem hhr_high_squares_not_permanent (j : ℕ) (hj : 7 ≤ j) :
    ¬ NonzeroSurvival model.classical.sphere (2,((2^(j+1) : ℕ) : ℤ))
      (model.standardClasses.standardHiSquare j) := by
  sorry

end KIP126.Literature.Standard
