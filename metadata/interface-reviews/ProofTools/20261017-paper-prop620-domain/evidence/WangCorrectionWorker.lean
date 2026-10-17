module

import KIP126.ProofTools.Language

/-!
Arithmetic checks for the proposed correction to AimPaper Proposition 6.20.
These are checks of the actual grading formulas printed in AimPaper, not a
counterexample in the category of spectra and not a proof of the full iff.
No production declaration or public API is changed by this evidence file.
-/

namespace WangCorrectionWorker

/-- ESS differentials add their length to both Adams coordinates, and
preserve synthetic weight. The source is λ^a x', shifted by e(f). -/
private def essTargetDegree (s t n a b e : ℤ) : ℤ × ℤ × ℤ :=
  ((s+a)+(n-a-b), (t+a)+(n-a-b), t+e)

/-- Multiplication by λ^k fixes the two Adams coordinates and lowers
synthetic weight by k; the classical label starts in weight ty. -/
private def lambdaLabelDegree (sy ty k : ℤ) : ℤ × ℤ × ℤ :=
  (sy, ty, ty-k)

/-- Literal substitution of the original y for y' is homogeneous exactly
when b=0. This checks both Adams coordinates and the synthetic weight. -/
private theorem fixed_y_degree_iff (s t n a b e : ℤ) :
    essTargetDegree s t n a b e =
      lambdaLabelDegree (s+n) (t+n) (n-b-e) ↔ b=0 := by
  constructor
  · intro h
    have hfirst := congrArg Prod.fst h
    dsimp [essTargetDegree, lambdaLabelDegree] at hfirst
    omega
  · intro hb
    subst b
    simp only [essTargetDegree, lambdaLabelDegree, Prod.mk.injEq]
    omega

/-- The y' degree in Definition 5.9 is homogeneous for all b. -/
private theorem crossing_yprime_degree (s t n a b e : ℤ) :
    essTargetDegree s t n a b e =
      lambdaLabelDegree (s+n-b) (t+n-b) (n-b-e) := by
  simp only [essTargetDegree, lambdaLabelDegree, Prod.mk.injEq]
  omega

/-- Both the residual λ exponent after removing λ^a and the ESS length
must remain within the normalization's lower bound. -/
private theorem crossing_length_range (n a b e : ℤ) :
    (0 ≤ b ∧ e ≤ n-a-b) ↔ (0 ≤ b ∧ b ≤ n-a-e) := by
  omega

/-- With b=0 the correctly graded exact-target short equation has
length n-a and the original λ exponent n-e. -/
private theorem fixed_y_bzero_degree (s t n a e : ℤ) :
    essTargetDegree s t n a 0 e =
      lambdaLabelDegree (s+n) (t+n) (n-e) := by
  have h := (fixed_y_degree_iff s t n a 0 e).mpr rfl
  simpa only [sub_zero] using h

#print axioms fixed_y_degree_iff
#print axioms crossing_yprime_degree
#print axioms crossing_length_range
#print axioms fixed_y_bzero_degree

end WangCorrectionWorker
