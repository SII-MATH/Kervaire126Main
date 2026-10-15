module

public import KIP126.Main.ExternalHypotheses.Data
public import KIP126.Main.Literature.AdamsSynthetic.Theorems

@[expose] public section

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- The compatibility premise is applicable: its exponent equation is
proved from the three source-bound exponents, not left as a vacuous ∀. -/
theorem NuCofiberNormalization.exponent_sum (P : NuCofiberNormalization D) :
    (normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.f : ℤ) +
      normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.g +
      normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.h = 1 := by
  change (normalizedExponent H D.hopfAndDetector.nuMap : ℤ) + _ + _ = 1
  rw [P.nu_exponent, P.bottom_exponent, P.top_exponent]
  norm_num

end
end KIP126.Literature.AdamsSynthetic
