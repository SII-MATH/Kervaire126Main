module

public import KIP126.Main.Literature.Near126.Sphere.Predicates
public import KIP126.Main.Literature.Near126.Sphere.Boundaries.Data

@[expose] public section


/-! First semantic slice of the Section 7 computation package.
Every field is an explicit mathematical premise. There is deliberately
no global inhabitant, new axiom, or final h₆²-survival field.
Sources below refer to labels/lines in MainPaper/main.tex; archive/query
provenance is audited separately in docs/external-inputs.json. -/
namespace KIP126.Computation.Near126
open KIP126.LinE2 KIP126.Classical.Adams

/-- Seven sphere identities and the unresolved, nonzero two-target d₃.
The eighth identity concerns the Adams sequence of Cν and is stated separately. -/
structure SphereDifferentialFacts where
  /-- fact:x_123_9, lines 2377–2385. -/
  d2_x_125_8 :
    (Sphere.Differential 2 (atom .x_125_8) (mulAt dataH1 V + U))
  /-- lem:toda2ext proof, lines 2538–2544. -/
  d2_h6 :
    (Sphere.Differential 2 dataH6 (mulAt dataH0 h5Sq))
  d2_h0Six_h6 :
    (Sphere.Differential 2 (mulAt h0Six dataH6) (mulAt dataH0 B))
  /-- lem:x_123_9 proof, lines 2400–2454. -/
  d3_h4_x_109_12 :
    (Sphere.Differential 3 (mulAt (atom .h4) (atom .x_109_12))
      (mulAt dataH1 (atom .x_122_15_2)))
  d3_h0Sq_x_123_13_2 :
    (Sphere.Differential 3 (mulAt h0Sq (atom .x_123_13_2))
      (mulAt h0Sq (atom .x_122_16)))
  /-- lem:toda2ext proof, line 2529. -/
  d3_x_126_4 :
    (Sphere.Differential 3 (atom .x_126_4) (mulAt h0Sq (atom .x_125_5)))
  /-- lem:x_123_9 proof, line 2439. -/
  d7_source :
    (Sphere.Differential 7 d7Source (mulAt dataH1 (atom .x_121_17)))
  /-- Remark following fact:theta5sqAF, lines 2169–2177. Neither alternative
  is selected; each branch includes nonvanishing on E₃, not just on E₂. -/
  d3_x_126_6_candidates :
    (Sphere.Differential 3 (atom .x_126_6) d3Candidate ∨
      Sphere.Differential 3 (atom .x_126_6) d3OtherCandidate)

/-- Survival, nonvanishing and global incoming exclusions explicitly used
by the main argument. Survival to Eᵣ does not assert vanishing of dᵣ. -/
structure SphereSurvivalFacts where
  /-- fact:theta5sqAF, lines 2156–2167. -/
  w_to_e6 : (Sphere.Survival 6 W)
  t_no_outgoing : (Sphere.NoOutgoing T)
  t_only_incoming : Sphere.OnlyIncomingT
  u_permanent : (Sphere.Permanent U)
  high_e5_exhaustion : Sphere.HighComponentExhaustion
  /-- prop:possible_h_6_sq proof, line 2358; a target-exhaustion input. -/
  w_d6_targets : Sphere.D6WTargets
  /-- prop:possible_h_6_sq proof, lines 2337–2342. -/
  correction_permanent : (Sphere.Permanent correction)
  /-- fact:x_123_9, lines 2377–2385. -/
  v_to_e12 : (Sphere.Survival 12 V)
  v_not_hit : (Sphere.NotHit V)
  /-- fact:h_0_sq_mul_x_125_9_2, lines 2466–2468; d₅(Y) is NOT specified. -/
  y_to_e5 : (Sphere.Survival 5 Y)
  y_not_hit : (Sphere.NotHit Y)
  /-- fact:h_1_mul_x_121_7, lines 2613–2615. -/
  x_to_e6 : (Sphere.Survival 6 X)
  x_not_hit : (Sphere.NotHit X)
  /-- fact:stem122, lines 2689–2696. -/
  p_permanent : (Sphere.Permanent P)
  q_permanent : (Sphere.Permanent Q)

/-- Selected E₂ products/nondivisibility used in the Toda and final
contradiction arguments. These can eventually be discharged by algebra
certificates in the existing quotient, independently of later differentials. -/
structure SphereProductFacts where
  /-- lem:toda2ext, line 2562. -/
  h5Sq_B_zero : ((mulAt h5Sq B).val = 0)
  /-- lem:toda2ext, lines 2500–2505. -/
  t_not_h0_multiple :
    (¬ ∃ a : E2At 13 138, mulAt dataH0 a = T)
  /-- prop:state5false, lines 2700–2707. -/
  t_not_h2_multiple :
    (¬ ∃ a : E2At 13 135, mulAt (atom .h2) a = T)
  /-- lem:nuext125, lines 2630–2644. -/
  x_h2_zero : ((mulAt X (atom .h2)).val = 0)
  y_not_h2_multiple :
    (¬ ∃ a : E2At 10 132, mulAt (atom .h2) a = Y)
  /-- lem:x_123_9 and prop:possible_h_6_sq. -/
  h1_correction_zero : ((mulAt dataH1 correction).val = 0)

/-- Selected whole-component vanishing queries. Bounds and page numbers are
part of the types; no inference is made from an unlisted table row. -/
structure SphereVanishingFacts where
  /-- Table:S125.19, line 3074; prop:possible_h_6_sq proof, line 2328. -/
  e2_stem125_low :
    (∀ (s : ℕ), s ≤ 4 → ∀ z : sphereAdamsData.Page 2 (s, (s : ℤ) + 125), z = 0)
  /-- Table:S124.12: AF=11 has an outgoing d₄, so E₄ is NOT asserted zero. -/
  e5_stem124_af11 :
    (∀ z : sphereAdamsData.Page 5 (11, 135), z = 0)
  /-- Table:S124.12, AF=12. -/
  e4_stem124_af12 :
    (∀ z : sphereAdamsData.Page 4 (12, 136), z = 0)
  /-- Table:S125.19, AF=12. -/
  e4_stem125_af12 :
    (∀ z : sphereAdamsData.Page 4 (12, 137), z = 0)
  /-- Table:S125.19, AF=13; prop:state5false proof. -/
  e5_stem125_af13 :
    (∀ z : sphereAdamsData.Page 5 (13, 138), z = 0)

/-- Usable sphere-only slice, not yet the complete near-126 proof input. -/
structure SphereFacts where
  differentials : SphereDifferentialFacts
  survival : SphereSurvivalFacts
  products : SphereProductFacts
  boundaries : SphereBoundaryFacts
  vanishing : SphereVanishingFacts

end KIP126.Computation.Near126
