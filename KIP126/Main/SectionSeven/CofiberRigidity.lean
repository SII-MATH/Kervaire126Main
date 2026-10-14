module

public import KIP126.Main.SectionSeven.NormalizedNu

/-! The final Cν rigidity step in LWX Proposition 7.9.
Adapted from Kervaire126 bbac1fc05843,
Main/Solution/Route/Section7/CnuRigidity.lean (MIT; see the retained source LICENSE).
Only the old representative/comparison subproof remains proof-port-pending;
the actual λν zero composite and the contradiction are retained as proofs. -/

@[expose] section
namespace KIP126.Main.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Core.SpectralSequence
open KIP126.Computation.Standard (T nuCofiberSequence bottom)
noncomputable section

/-- Paper-local specialization of BHS: the actual bottom-cell image
survives to E₆, so λ⁴ times the image of this detected representative is
nonzero. The old proof compares actual quotient representatives with B₅.
Proof-port-pending, not an added literature or computation input. -/
public theorem detected_target_bottom_lambda_four_nonzero
    (t : BiHom 125 139 (S_0_0 : SyntheticSpectrum))
    (ht : SphereDetected 14 139 0 T t) :
    lambdaMultiply 4 t ≫ nuBottom ≠ 0 := by
  have hp := KIP126.Computation.Standard.t_permanent_cycle
  have hs := KIP126.Computation.Standard.cofiber_target_to_e6
  sorry

/-- The exact λν equation contradicts that nonzero bottom-cell image. -/
public theorem target_divisibility_contradiction : ¬ TargetNuDivisible T hopfNu := by
  rintro ⟨t, a, ht, heq⟩
  apply detected_target_bottom_lambda_four_nonzero t ht
  rw [← heq]
  exact lambda_nu_multiple_bottom_zero a

/-- The original last-step formulation exposes the finite incoming window
2..5 on the same actual Cν class. It makes no permanence assertion about Cν. -/
public theorem target_divisibility_forces_cnu_incoming
    (hdiv : TargetNuDivisible T hopfNu) :
    ∃ r : ℤ, 2 ≤ r ∧ r ≤ 5 ∧
      HitOnPage nuCofiberSequence r (14,139) (bottom 14 139 T) := by
  exact False.elim (target_divisibility_contradiction hdiv)

end
end KIP126.Main.SectionSeven
