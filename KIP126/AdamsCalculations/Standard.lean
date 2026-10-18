module

public import KIP126.E2Computation.Standard

/-! Later Adams-page differentials, survival and boundary calculations.
The fixed classes and E₂ algebra are imported from E2Computation. -/

set_option backward.isDefEq.respectTransparency false

@[expose] section
namespace KIP126.Computation.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard

public theorem w_to_e6 : SurvivesTo model.classical.sphere 6 (8,134) W := by sorry
public theorem t_permanent_cycle : IsPermanentCycle model.classical.sphere (14,139) T := by sorry
/-- Complete incoming-page classification; it identifies actual differentials,
not an arbitrary choice of an E₂ lift. -/
public theorem t_only_incoming (r : ℤ) (h : HitOnPage model.classical.sphere r (14,139) T) :
    (r = 6 ∧ HasNonzeroDifferential model.classical.sphere 6 (8,134) (14,139) W T) ∨
    (r = 12 ∧ HasNonzeroDifferential model.classical.sphere 12 (2,128) (14,139) h6Square T) := by sorry
public theorem u_permanent : NonzeroSurvival model.classical.sphere (10,134) U := by sorry
/-- Exhaustion of the actual E₅ component, with its nonzero continuation. -/
public theorem high_e5 : ∃ y : model.classical.sphere.Page 5 (25,150),
    RepresentsOnPage model.classical.sphere 5 (25,150) highClass y ∧ y ≠ 0 ∧
    ∀ z : model.classical.sphere.Page 5 (25,150), z = 0 ∨ z = y := by sorry

public theorem v_to_e12 : SurvivesTo model.classical.sphere 12 (9,132) V := by sorry

public theorem v_not_hit : NeverHit model.classical.sphere (9,132) V := by sorry

public theorem d2_x125_8 : HasNonzeroDifferential model.classical.sphere 2 (8,133) (10,134)
    (atom .x_125_8) d2Target := by sorry

public theorem y_to_e5 : SurvivesTo model.classical.sphere 5 (11,136) Y := by sorry

public theorem y_not_hit : NeverHit model.classical.sphere (11,136) Y := by sorry

public theorem x_to_e6 : SurvivesTo model.classical.sphere 6 (8,130) X := by sorry

public theorem x_not_hit : NeverHit model.classical.sphere (8,130) X := by sorry

public theorem d2_h0Six_h6 : HasNonzeroDifferential model.classical.sphere 2 (7,70) (9,71)
    (product h0Six h6) (product h0 (atom .b)) := by sorry

public theorem d3_h4_x109_12 : HasNonzeroDifferential model.classical.sphere 3 (13,137) (16,139)
    (product h4 (atom .x_109_12) (h := T._proof_1))
    (product h1 (atom .x_122_15_2)) := by sorry

public theorem d3_h0Square_x123_13_2 : HasNonzeroDifferential model.classical.sphere 3 (15,138) (18,140)
    (product h0Square (atom .x_123_13_2))
    (product h0Square (atom .x_122_16)) := by sorry

public theorem d3_x126_4 : HasNonzeroDifferential model.classical.sphere 3 (4,130) (7,132)
    (atom .x_126_4) (product h0Square (atom .x_125_5)) := by sorry

public theorem d7_source : HasNonzeroDifferential model.classical.sphere 7 (11,134) (18,140)
    d7Source (product h1 (atom .x_121_17)) := by sorry

public theorem d3_x126_6_candidates :
    HasNonzeroDifferential model.classical.sphere 3 (6,132) (9,134)
      (atom .x_126_6) d3Candidate ∨
    HasNonzeroDifferential model.classical.sphere 3 (6,132) (9,134)
      (atom .x_126_6) d3OtherCandidate := by sorry

public theorem w_d6_targets : DifferentialTargets model.classical.sphere 6 (8,134) W
    (by simpa only [ClassicalAdamsFamily.sphere, ClassicalAdamsFamily.obj, model.classical.differentialDegree,
      Prod.mk_add_mk, Int.reduceSub, Int.reduceAdd] using T) := by sorry

public theorem correction_permanent : NonzeroSurvival model.classical.sphere (13,137) correction := by sorry

public theorem p_permanent : NonzeroSurvival model.classical.sphere (11,133) P := by sorry

public theorem q_permanent : NonzeroSurvival model.classical.sphere (12,134) Q := by sorry

public theorem p_h2_boundary : IsBoundaryBy model.classical.sphere 2 (12,137)
    (product P h2) := by sorry

public theorem q_h2_boundary : IsBoundaryBy model.classical.sphere 2 (13,138)
    (product Q h2) := by sorry

public theorem e5_stem124_af11 : Subsingleton (model.classical.sphere.Page 5 (11,135)) := by sorry

public theorem e4_stem124_af12 : Subsingleton (model.classical.sphere.Page 4 (12,136)) := by sorry

public theorem e4_stem125_af12 : Subsingleton (model.classical.sphere.Page 4 (12,137)) := by sorry

public theorem e5_stem125_af13 : Subsingleton (model.classical.sphere.Page 5 (13,138)) := by sorry

public theorem p_permanent_cycle : IsPermanentCycle model.classical.sphere (11,133) P := by
  obtain ⟨z, hz, _⟩ := p_permanent
  exact ⟨z, hz⟩
public theorem q_permanent_cycle : IsPermanentCycle model.classical.sphere (12,134) Q := by
  obtain ⟨z, hz, _⟩ := q_permanent
  exact ⟨z, hz⟩

public theorem table9 (r : ℤ) (_hr : 2 ≤ r) :
    ¬ HasNonzeroDifferential model.classical.sphere r (6,132) (14,139) (atom .x_126_6) T := by
  intro hd
  have hp := congrArg Prod.fst hd.toHasDifferential.target_degree
  have hdeg : (6 : ℤ) + r = 14 := by
    simpa only [ClassicalAdamsFamily.sphere, ClassicalAdamsFamily.obj,
      model.classical.differentialDegree, Prod.mk_add_mk, Prod.fst] using hp
  rcases t_only_incoming r hd.hit_target with hh | hh
  · omega
  · omega
public theorem no_other_incoming {r s t : ℤ} (_hr : 2 ≤ r) (h6 : r ≠ 6) (h12 : r ≠ 12)
    (x : model.classical.sphere.Page 2 (s,t)) :
    ¬ HasNonzeroDifferential model.classical.sphere r (s,t) (14,139) x T := by
  intro hx
  rcases t_only_incoming r hx.hit_target with hx | hx
  · exact h6 hx.1
  · exact h12 hx.1

public theorem cofiber_d3 : HasNonzeroDifferential nuCofiberSequence 3 (8,134) (11,136)
    cofiberSource (bottom 11 136 Y) := by sorry
public theorem cofiber_target_to_e6 :
    SurvivesTo nuCofiberSequence 6 (14,139) (bottom 14 139 T) := by sorry
public theorem cofiber_target_not_hit_through5 :
    NeverHitOnWindow nuCofiberSequence 2 5 (14,139) (bottom 14 139 T) := by sorry

/-- Derived from the fixed literature result, rather than a duplicate assumption. -/
public theorem d2_h6 : HasNonzeroDifferential model.classical.sphere 2 (1,64) (3,65)
    h6 (product h0 h5Square) := by
  have h := KIP126.Literature.Standard.adamsOneLine_d2 6 (by decide)
  change HasNonzeroDifferential model.classical.sphere 2 (1,64) (3,65)
    h6 (product h0 h5Square) at h
  exact h

/-- The actual detector differential uses the same source isomorphism and labels. -/
public theorem detector_d3 :
    HasDifferential (model.classical.obj model.auxiliary.detector) 3 (16,112) (19,114)
      (detectorComparison 16 112 detector_v2_agrees._proof_1 detectorV2Sixteen)
      (detectorComparison 19 114 detector_beta_agrees._proof_1 detectorBetaGFour) := by
  rw [detector_v2_agrees, detector_beta_agrees]
  exact KIP126.Literature.Standard.detector_d3

end KIP126.Computation.Standard
