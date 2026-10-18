module

import KIP126.Literature

/-! Fixed literature theorems are used by ordinary import, with no delivery,
model variable or result package supplied by the consumer. -/

open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (Spectrum SyntheticSpectrum model)
open KIP126.Literature.Standard

example : theta5 + theta5 = 0 := theta5_order_two

example : ClassicalTheta5Detected theta5 := theta5_detection

example : NonzeroSurvival model.classical.sphere (1,2)
    (model.standardClasses.standardHi 1) := eta_permanent

example (j : ℕ) (hj : 4 ≤ j) :
    HasNonzeroDifferential model.classical.sphere 2
      (1,((2^j : ℕ) : ℤ)) (3,1+((2^(j-1+1) : ℕ) : ℤ))
      (model.standardClasses.standardHi j) (oneLineTarget j) :=
  adamsOneLine_d2 j hj

example : g ≠ 0 := g_nonzero

example : HasDifferential (model.classical.obj model.auxiliary.detector)
    3 (16,112) (19,114)
    ((model.classical.map tmfIso.hom).pageMap 2 (16,112) tmfV2Sixteen)
    ((model.classical.map tmfIso.hom).pageMap 2 (19,114) tmfBetaGFour) := detector_d3

example : sphereFirstQuotient 1 2 (quotientClass 1 eta) =
    model.standardClasses.standardHi 1 := eta_label

example : sphereFirstQuotient 1 64 h6FirstQuotient =
    model.standardClasses.standardH6 := h6FirstQuotient_label

example : ∃ y : model.classical.sphere.Page 2 (5,19),
    HasNonzeroDifferential model.classical.sphere 3 (2,17) (5,19)
      (hiProduct 0 4) y := iwx_h0_h4_d3

#check_failure KIP126.Literature.LiteratureInterface
#check_failure KIP126.Literature.LiteratureResults
#check_failure KIP126.Literature.ClassicalResults
#check_failure KIP126.Literature.Standard.literature
#check_failure KIP126.Literature.Standard.mainTheorem
#check_failure KIP126.Literature.Standard.theta5_indeterminacy_AF_ge_6
