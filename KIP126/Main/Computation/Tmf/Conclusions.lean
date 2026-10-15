module

public import KIP126.Def.AdamsSynthetic.ComparisonStatements

@[expose] public section

/-! The tmf detection and vanishing conclusions used in Section 7.
These predicates concern the fixed classical/synthetic Adams comparison.
Their proofs from the external hypotheses are given in Main. -/

namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

variable (D : AdamsComparison H M Syn) (L : TmfDetectionClasses H)

/-- The classical θ₅ Hurewicz vanishing used in LWX Prop. 7.8.
The map is the unit of D's selected detector, interpreted as 2-completed
connective tmf. Source: BMQ Figure 1.1 and Theorem 1.2 in degree 62.
This does NOT assert synthetic θ₅ vanishing: that still needs the
synthetic/classical comparison and the relevant λ-torsion analysis. -/
def TmfTheta5Vanishing : Prop :=
  ∀ θ : HomotopyGroup (C := C) 62 SphereSpectrum,
    ClassicalTheta D θ → θ ≫ D.hopfAndDetector.detectorUnit = 0

/-- A classical Adams consequence of the BMQ results, their product
comparison, and the computations with vanishing/separation: the leading grade g⁴Δh₁g
survives nontrivially, and ONE class it detects has nonzero tmf image.
Independence of the detected representative is a Main deduction, requiring
higher-filtration vanishing; it is not a further external input.
Identification of the selected detector/unit and these two labels with
the source alone does not prove nonzero leading grade. -/
def TmfHigh125Detection : Prop :=
  NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
    (25,150) (L.high125 M) ∧
  ∃ α : HomotopyGroup (C := C) 125 SphereSpectrum,
    TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (L.high125 M) α ∧ α ≫ D.hopfAndDetector.detectorUnit ≠ 0

/-- The small part of the classical tmf E₂ calculation needed to transport
the 62-stem vanishing through λ-localization. Source: BMQ §2,
H_*tmf = (A//A(2))_* and its change-of-rings E₂. There is no nonpositive-AF
class in positive stem 63. This is prior tmf input, not a Lin sphere CSV row. -/
def TmfLowFiltration63 : Prop :=
  ∀ s : ℤ, s ≤ 0 → Subsingleton (E2 H D.hopfAndDetector.detector s (63+s))

end
end KIP126.Literature.AdamsSynthetic


namespace KIP126.Literature.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

variable (D : AdamsComparison H M Syn) (L : TmfDetectionClasses H)

/-- Applied tmf facts used by Main, including the INTERNAL leading-grade
survival deduction. These conclusions are not fields of `ExternalHypotheses`.
Main derives them from the literature results, comparisons and finite computations, with
the explicit vanishing/separation premises. -/
structure TmfDetectionTheorems : Prop where
  theta5_vanishes : TmfTheta5Vanishing D
  high125_detected : TmfHigh125Detection D L
  low_filtration_63 : TmfLowFiltration63 D


end
end KIP126.Literature.AdamsSynthetic
