module

public import KIP126.Main.ExternalHypotheses.Data
public import KIP126.Def.ClassicalAdams.Detection.Predicates
public import KIP126.Def.ClassicalAdams.SphereVanishing.Predicates

@[expose] public section

/-!
# Derived Adams statements for one E₂ interpretation

These propositions follow from the finite records, complete local bases,
product comparison, and independent range lemmas. They impose no additional
assumptions on `AdamsComputationTheorems` or `AdamsComparison`.
A level-9000 row means only `ReachesPage 1000` in `AdamsStatement`.
-/
namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.LinE2 KIP126.Computation.Near126
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  {D : AdamsComparison H M Syn}

-- Keep type unification from expanding the 6,000-line CSV relation ideal.
attribute [local irreducible] KIP126.LinE2.homogeneousPart
namespace Derived
variable (R : E2Interpretation D)

def Differential {s t s' t' : ℕ} (r : ℤ)
    (x : E2At s t) (y : E2At s' t') : Prop :=
  HasNonzeroDifferential (sequence D .sphere) r (s,t) (s',t')
    (R.sphere s t x) (R.sphere s' t' y)

def Survival {s t : ℕ} (r : ℤ) (x : E2At s t) : Prop :=
  SurvivesTo (sequence D .sphere) r (s,t) (R.sphere s t x)

def Permanent {s t : ℕ} (x : E2At s t) : Prop :=
  NonzeroSurvival (sequence D .sphere) (s,t) (R.sphere s t x)

def NotHit {s t : ℕ} (x : E2At s t) : Prop :=
  NeverHit (sequence D .sphere) (s,t) (R.sphere s t x)

/-- Whole-page exhaustion, including existence and nonzero value of the
specified class on E5. The record's E2 nonzero value alone is insufficient. -/
def High125Component : Prop :=
  ∃ y : (sequence D .sphere).Page 5 (25,150),
    RepresentsOnPage (sequence D .sphere) 5 (25,150)
      (R.sphere 25 150 highClass) y ∧ y ≠ 0 ∧
    ∀ z : (sequence D .sphere).Page 5 (25,150), z = 0 ∨ z = y

/-- The ONLY incoming possibilities in Fact 7.6; neither possibility is
asserted to occur. Arbitrarily late incoming pages require the general
negative-filtration lemma, not a finite database scan. -/
def OnlyIncomingT : Prop :=
  ∀ r : ℤ, HitOnPage (sequence D .sphere) r (14,139)
      (R.sphere 14 139 T) →
    (r = 6 ∧ Differential R 6 W T) ∨
      (r = 12 ∧ Differential R 12 dataH6Sq T)

/-- Sphere consequences to be proved on the specified interpretation `R`
from its computation hypotheses. Each class and differential refers to
this same interpretation. -/
structure SphereFacts : Prop where
  d2_x_125_8 : Differential R 2 (atom .x_125_8) (mulAt dataH1 V + U)
  d2_h6 : Differential R 2 dataH6 (mulAt dataH0 h5Sq)
  d2_h0Six_h6 : Differential R 2 (mulAt h0Six dataH6) (mulAt dataH0 B)
  d3_h4_x_109_12 : Differential R 3 (mulAt (atom .h4) (atom .x_109_12))
    (mulAt dataH1 (atom .x_122_15_2))
  d3_h0Sq_x_123_13_2 : Differential R 3 (mulAt h0Sq (atom .x_123_13_2))
    (mulAt h0Sq (atom .x_122_16))
  d3_x_126_4 : Differential R 3 (atom .x_126_4) (mulAt h0Sq (atom .x_125_5))
  d7_source : Differential R 7 d7Source (mulAt dataH1 (atom .x_121_17))
  /-- Uses E3 candidate coverage and both root refutations 2047477/2047478.
  The two refutations alone do not constitute candidate coverage. -/
  d3_x_126_6_candidates : Differential R 3 (atom .x_126_6) d3Candidate ∨
    Differential R 3 (atom .x_126_6) d3OtherCandidate
  w_to_e6 : Survival R 6 W
  t_permanent_cycle : IsPermanentCycle (sequence D .sphere) (14,139) (R.sphere 14 139 T)
  t_only_incoming : OnlyIncomingT R
  w_d6_targets : DifferentialTargets (sequence D .sphere) 6 (8,134)
    (R.sphere 8 134 W) (R.sphere 14 139 T)
  u_permanent : Permanent R U
  correction_permanent : Permanent R correction
  p_permanent : Permanent R P
  q_permanent : Permanent R Q
  v_to_e12 : Survival R 12 V
  v_not_hit : NotHit R V
  y_to_e5 : Survival R 5 Y
  /-- The finite incoming range needed for Y's nonzero detection modulo λ⁹.
  This does not assert the all-page incoming exclusion in Fact 7.15. -/
  y_not_hit_through_six : NeverHitOnWindow (sequence D .sphere) 2 6 (11,136)
    (R.sphere 11 136 Y)
  x_to_e6 : Survival R 6 X
  x_not_hit : NotHit R X
  high_e5 : High125Component R
  h5Sq_B_zero : R.sphere 10 134 (mulAt h5Sq B) = 0
  t_not_h0_multiple : ¬ ∃ a : E2 H SphereSpectrum 13 138,
    Sphere.Internal.product H M (s := 1) (t := 1) (s' := 13) (t' := 138)
      (Sphere.Internal.hi H M 0) a = R.sphere 14 139 T
  t_not_h2_multiple : ¬ ∃ a : E2 H SphereSpectrum 13 135,
    Sphere.Internal.product H M (s := 1) (t := 4) (s' := 13) (t' := 135)
      (Sphere.Internal.hi H M 2) a = R.sphere 14 139 T
  x_h2_zero : R.sphere 9 134 (mulAt X (atom .h2)) = 0
  y_not_h2_multiple : ¬ ∃ a : E2 H SphereSpectrum 10 132,
    Sphere.Internal.product H M (s := 1) (t := 4) (s' := 10) (t' := 132)
      (Sphere.Internal.hi H M 2) a = R.sphere 11 136 Y
  h1_correction_zero : R.sphere 14 139 (mulAt dataH1 correction) = 0
  p_h2_boundary : IsBoundaryBy (sequence D .sphere) 2 (12,137)
    (R.sphere 12 137 (mulAt P (atom .h2)))
  q_h2_boundary : IsBoundaryBy (sequence D .sphere) 2 (13,138)
    (R.sphere 13 138 (mulAt Q (atom .h2)))
  e2_stem125_low : ∀ s : ℕ, s ≤ 4 →
    Subsingleton ((sequence D .sphere).Page 2 (s,(s : ℤ)+125))
  /-- AF11 contains an outgoing d4; its vanishing page is E5, not E4. -/
  e5_stem124_af11 : Subsingleton ((sequence D .sphere).Page 5 (11,135))
  e4_stem124_af12 : Subsingleton ((sequence D .sphere).Page 4 (12,136))
  e4_stem125_af12 : Subsingleton ((sequence D .sphere).Page 4 (12,137))
  e5_stem125_af13 : Subsingleton ((sequence D .sphere).Page 5 (13,138))

-- The weight130 high-filtration exhaustion belongs to the synthetic
-- homotopy deductions in Computation/High125.lean. Classical E5 has
-- nonzero components at AF15 and AF18, so no all-AF>=15 vanishing field
-- belongs in this classical bundle.

/-- Lemma 7.20's actual Cnu equation. The source is the sum of all three
cells specified by the table, not just the top-cell summand in log 212838. -/
def CnuDifferential : Prop :=
  ∃ (x : Page D .nuCofiber 8 134) (y : Page D .nuCofiber 11 136),
    R.coordinateSum .nuCofiber 8 134 [0,3,4] = some x ∧
    R.coordinateSum .nuCofiber 11 136 [3] = some y ∧
    HasNonzeroDifferential (sequence D .nuCofiber) 3 (8,134) (11,136) x y
/-- Final contradiction, Table Cnu126: the same bottom-cell target is
nonzero on E6 and is not an incoming differential target on pages 2--5.
This is finite information; it does not claim permanent survival in Cnu. -/
def CnuTargetThrough5 : Prop :=
  ∃ y : Page D .nuCofiber 14 139,
    R.coordinateSum .nuCofiber 14 139 [2] = some y ∧
    SurvivesTo (sequence D .nuCofiber) 6 (14,139) y ∧
    NeverHitOnWindow (sequence D .nuCofiber) 2 5 (14,139) y
end Derived
end
end KIP126.Computation.SphereAndCofiber
