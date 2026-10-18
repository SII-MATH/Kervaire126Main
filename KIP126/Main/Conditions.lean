module

public import KIP126.AdamsCalculations

/-! The paper's Section 7 conditions on the fixed upstream system.
Adapted from Kervaire126 bbac1fc05843, Def/Kervaire/Route/Conditions/Predicates
(MIT; see the retained source LICENSE). These are definitions of paper goals, not additional inputs.
-/

@[expose] section
noncomputable section
namespace KIP126.Main
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Core.SpectralSequence KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)

public def H6SquareSupportsD12 : Prop :=
  HasNonzeroDifferential model.classical.sphere 12 (2,128) (14,139)
    model.standardClasses.standardH6Square KIP126.Computation.Standard.T

/-- A zero sixth differential includes an actual sixth-page representative. -/
public def Stem126D6Vanishes : Prop :=
  HasDifferential model.classical.sphere 6 (8,134) (14,139)
    KIP126.Computation.Standard.W 0

public def ThetaChoice (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) : Prop :=
  KIP126.Literature.Standard.Theta5Detected theta

/-- Nonzero detection of the square, retaining higher-filtration ambiguity. -/
public def Theta5SquareNonzeroDetectionAt (theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum)) : Prop :=
  DetectsNonzero (model.convergence .sphere) (10,134,128)
    (model.comparison.sphereE2 10 134 6 KIP126.Computation.Standard.U)
    (sphereProduct theta theta)

public def Theta5SquareNonzeroDetection : Prop := ∃ theta, ThetaChoice theta ∧ Theta5SquareNonzeroDetectionAt theta

public def UChoice (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) : Prop :=
  DetectsNonzero (model.convergence .sphere) (10,134,134)
    (model.comparison.sphereE2 10 134 0 KIP126.Computation.Standard.U) u

/-- This is associated-graded detection, not an exact representative equation.
No nonzero target requirement is added to the paper's condition. -/
public def EtaExtensionDetectionAt (u : BiHom 124 134 (S_0_0 : SyntheticSpectrum)) : Prop :=
  Detects (model.convergence .sphere) (14,139,133)
    (model.comparison.sphereE2 14 139 6 KIP126.Computation.Standard.T)
    (lambdaMultiply 3 (sphereProduct KIP126.Literature.Standard.eta u))

public def EtaExtensionDetection : Prop := ∃ u, UChoice u ∧ EtaExtensionDetectionAt u

/-- The endpoint keeps a common Z∞ representative and a nonzero E∞ image. -/
public abbrev H6SquarePermanent : Prop :=
  KIP126.AdamsSynthetic.Standard.H6SquarePermanent

end KIP126.Main
end
