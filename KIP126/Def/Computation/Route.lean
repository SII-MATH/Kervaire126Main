module

public import KIP126.Def.Computation.Near126

/-! Additional theorem-facing consequences in the original reviewed route.
These are results to be certified from finite computations and the separately
supplied literature range hypotheses, not claims obtained from data metadata.
Source: KIP126/Main/Solution/Computation/Route/Consequences.lean, fixed bbac1fc.
No high-filtration homotopy conclusion, Main criterion or final permanence
result is assumed by this contract. -/

set_option backward.isDefEq.respectTransparency false

@[expose] section
namespace KIP126.Computation
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Kervaire.Route KIP126.Classical.Adams KIP126.Core.SpectralSequence
open Bindings
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {D : Model C Syn}

/-- Remaining sphere facts consumed by the reviewed main proof. Scalar actions,
products, classes and pages all come from the same model and comparison. -/
public structure RouteResults (B : Bindings D) : Prop extends FactSevenSix B where
  v_to_e12 : SurvivesTo D.classical.sphere 12 (9,132) B.V
  v_not_hit : NeverHit D.classical.sphere (9,132) B.V
  d2_x125_8 : HasNonzeroDifferential D.classical.sphere 2 (8,133) (10,134)
    (B.atom .x_125_8) B.d2Target
  y_to_e5 : SurvivesTo D.classical.sphere 5 (11,136) B.Y
  y_not_hit : NeverHit D.classical.sphere (11,136) B.Y
  x_to_e6 : SurvivesTo D.classical.sphere 6 (8,130) B.X
  x_not_hit : NeverHit D.classical.sphere (8,130) B.X
  d2_h0Six_h6 : HasNonzeroDifferential D.classical.sphere 2 (7,70) (9,71)
    (product (D := D) (h0Six (D := D)) (h6 (D := D))) (product (D := D) (h0 (D := D)) (B.atom .b))
  d3_h4_x109_12 : HasNonzeroDifferential D.classical.sphere 3 (13,137) (16,139)
    (product (D := D) (h4 (D := D)) (B.atom .x_109_12))
    (product (D := D) (h1 (D := D)) (B.atom .x_122_15_2))
  d3_h0Square_x123_13_2 : HasNonzeroDifferential D.classical.sphere 3 (15,138) (18,140)
    (product (D := D) (h0Square (D := D)) (B.atom .x_123_13_2))
    (product (D := D) (h0Square (D := D)) (B.atom .x_122_16))
  d3_x126_4 : HasNonzeroDifferential D.classical.sphere 3 (4,130) (7,132)
    (B.atom .x_126_4) (product (D := D) (h0Square (D := D)) (B.atom .x_125_5))
  d7_source : HasNonzeroDifferential D.classical.sphere 7 (11,134) (18,140)
    B.d7Source (product (D := D) (h1 (D := D)) (B.atom .x_121_17))
  d3_x126_6_candidates :
    HasNonzeroDifferential D.classical.sphere 3 (6,132) (9,134)
      (B.atom .x_126_6) B.d3Candidate ∨
    HasNonzeroDifferential D.classical.sphere 3 (6,132) (9,134)
      (B.atom .x_126_6) B.d3OtherCandidate
  w_d6_targets : DifferentialTargets D.classical.sphere 6 (8,134) B.W
    (by simpa only [ClassicalAdamsFamily.sphere, ClassicalAdamsFamily.obj, D.classical.differentialDegree,
      Prod.mk_add_mk, Int.reduceSub, Int.reduceAdd] using B.T)
  correction_permanent : NonzeroSurvival D.classical.sphere (13,137) B.correction
  p_permanent : NonzeroSurvival D.classical.sphere (11,133) B.P
  q_permanent : NonzeroSurvival D.classical.sphere (12,134) B.Q
  h5Square_b_zero : product (D := D) (r := (10,134)) (h5Square (D := D)) (B.atom .b) = 0
  t_not_h0_multiple : ¬ ∃ a : D.classical.sphere.Page 2 (13,138),
    product (D := D) (r := (14,139)) (h0 (D := D)) a = B.T
  t_not_h2_multiple : ¬ ∃ a : D.classical.sphere.Page 2 (13,135),
    product (D := D) (r := (14,139)) (h2 (D := D)) a = B.T
  x_h2_zero : product (D := D) (r := (9,134)) B.X (h2 (D := D)) = 0
  y_not_h2_multiple : ¬ ∃ a : D.classical.sphere.Page 2 (10,132),
    product (D := D) (r := (11,136)) (h2 (D := D)) a = B.Y
  h1_correction_zero : product (D := D) (r := (14,139)) (h1 (D := D)) B.correction = 0
  p_h2_boundary : IsBoundaryBy D.classical.sphere 2 (12,137)
    (product (D := D) B.P (h2 (D := D)))
  q_h2_boundary : IsBoundaryBy D.classical.sphere 2 (13,138)
    (product (D := D) B.Q (h2 (D := D)))
  e2_stem125_low : ∀ s : ℕ, s ≤ 4 →
    Subsingleton (D.classical.sphere.Page 2 (s,(s : ℤ)+125))
  e5_stem124_af11 : Subsingleton (D.classical.sphere.Page 5 (11,135))
  e4_stem124_af12 : Subsingleton (D.classical.sphere.Page 4 (12,136))
  e4_stem125_af12 : Subsingleton (D.classical.sphere.Page 4 (12,137))
  e5_stem125_af13 : Subsingleton (D.classical.sphere.Page 5 (13,138))

namespace RouteResults
variable {B : Bindings D}

/-- The legacy weaker cycle conclusions are derived from the reviewed route's
stronger explicit nonzero E∞ certificates, rather than requested twice. -/
public theorem toNear126Results (h : RouteResults B) : Near126Results B where
  toFactSevenSix := h.toFactSevenSix
  v_to_e12 := h.v_to_e12
  v_not_hit := h.v_not_hit
  d2_x125_8 := h.d2_x125_8
  y_to_e5 := h.y_to_e5
  y_not_hit := h.y_not_hit
  x_to_e6 := h.x_to_e6
  x_not_hit := h.x_not_hit
  p_permanent_cycle := by
    obtain ⟨z, hz, _⟩ := h.p_permanent
    exact ⟨z, hz⟩
  q_permanent_cycle := by
    obtain ⟨z, hz, _⟩ := h.q_permanent
    exact ⟨z, hz⟩
end RouteResults
end KIP126.Computation
