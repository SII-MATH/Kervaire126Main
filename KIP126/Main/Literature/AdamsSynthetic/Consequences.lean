module

public import KIP126.Main.Literature.AdamsSynthetic.Applicability
public import KIP126.Main.ExternalHypotheses.Data
public import KIP126.Main.Literature.AdamsSynthetic.Theorems

@[expose] public section

namespace KIP126.Literature.AdamsSynthetic
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn) (η : BiHom 1 2 (S_0_0 : Syn)) (L : TmfDetectionClasses H)

/-- Supply the already frozen forward differential language from the
external BHS rigidity input. This is only projection, not a proof of BHS. -/
theorem AdamsSyntheticTheorems.differentialLift (I : AdamsSyntheticTheorems D η L) :
    KIP126.Literature.AdamsSynthetic.ClassicalSyntheticDifferentialComparison D := by
  intro X a s t r k hr x y h
  exact (I.synthetic.differentials X a s t r k hr x y).mp h

/-- The actual Cν triangle required by the Mahowald tool is available
without assuming the tool's conclusion or a computed ν-extension. -/
theorem AdamsSyntheticTheorems.nuTriangle (I : AdamsSyntheticTheorems D η L) :
    NormalizedTriangleCompatible D.toAdamsComparisonData D.hopfAndDetector.nuCofiberTriangle
      (I.applicability.nuCofiber.exponent_sum D) :=
  I.applicability.nuCofiber.triangle _
end KIP126.Literature.AdamsSynthetic
