module

public import KIP126.Def.Computation.Classes

/-! The theorem-facing calculation contract on one actual sphere sequence.
Adapted from the fixed review baseline's Computation/Route/Consequences and
KIPBase's BjmBxCriterion at 5aa845241533b763c37a1d5fc70cce9708c4e68e.
The original finite-record proofs and independent range arguments must construct
this delivery. A finite staircase cutoff does not prove any permanent field. -/

@[expose] section
namespace KIP126.Computation
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Kervaire.Route KIP126.Classical.Adams KIP126.Core.SpectralSequence
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {D : Model C Syn}

/-- Exhaustion of the entire actual E₅ component, including its specified
nonzero representative; E₂ nonvanishing alone would be insufficient. -/
public def HighComponent (B : Bindings D) : Prop :=
  ∃ y : D.classical.sphere.Page 5 (25,150),
    RepresentsOnPage D.classical.sphere 5 (25,150) B.highClass y ∧ y ≠ 0 ∧
    ∀ z : D.classical.sphere.Page 5 (25,150), z = 0 ∨ z = y

/-- Complete incoming-page classification from the reviewed baseline. The
source is identified by a differential on its actual page. Equality of arbitrary
E₂ lifts would incorrectly exclude adding an earlier boundary to a source.
All legal pages are quantified; neither candidate is asserted to occur. -/
public def OnlyIncomingT (B : Bindings D) : Prop :=
  ∀ r : ℤ, HitOnPage D.classical.sphere r (14,139) B.T →
    (r = 6 ∧ HasNonzeroDifferential D.classical.sphere 6 (8,134) (14,139) B.W B.T) ∨
    (r = 12 ∧ HasNonzeroDifferential D.classical.sphere 12 (2,128) (14,139)
      D.standardClasses.standardH6Square B.T)

/-- The exact Fact 7.6 package. Permanent cycle and nonzero E∞ survival remain
separate; the latter keeps one common Z∞ representative and a nonzero image. -/
public structure FactSevenSix (B : Bindings D) : Prop where
  w_to_e6 : SurvivesTo D.classical.sphere 6 (8,134) B.W
  t_permanent_cycle : IsPermanentCycle D.classical.sphere (14,139) B.T
  t_only_incoming : OnlyIncomingT B
  u_permanent : NonzeroSurvival D.classical.sphere (10,134) B.U
  high_e5 : HighComponent B

/-- Additional table facts needed by the main argument. `NeverHit` quantifies
over every actual page class and every legal length. This is stronger than
absence of a named row, and does not assert absence of outgoing differentials. -/
public structure Near126Results (B : Bindings D) : Prop extends FactSevenSix B where
  v_to_e12 : SurvivesTo D.classical.sphere 12 (9,132) B.V
  v_not_hit : NeverHit D.classical.sphere (9,132) B.V
  d2_x125_8 : HasNonzeroDifferential D.classical.sphere 2 (8,133) (10,134)
    (B.atom .x_125_8) B.d2Target
  y_to_e5 : SurvivesTo D.classical.sphere 5 (11,136) B.Y
  y_not_hit : NeverHit D.classical.sphere (11,136) B.Y
  x_to_e6 : SurvivesTo D.classical.sphere 6 (8,130) B.X
  x_not_hit : NeverHit D.classical.sphere (8,130) B.X
  p_permanent_cycle : IsPermanentCycle D.classical.sphere (11,133) B.P
  q_permanent_cycle : IsPermanentCycle D.classical.sphere (12,134) B.Q

namespace Near126Results
variable {B : Bindings D} (h : Near126Results B)
include h

/-- Mathematical Table 3, with its actual sum and product target. -/
public theorem table3 :
    SurvivesTo D.classical.sphere 12 (9,132) B.V ∧
    NeverHit D.classical.sphere (9,132) B.V ∧
    HasNonzeroDifferential D.classical.sphere 2 (8,133) (10,134)
      (B.atom .x_125_8) B.d2Target :=
  ⟨h.v_to_e12, h.v_not_hit, h.d2_x125_8⟩

public theorem table7 :
    SurvivesTo D.classical.sphere 5 (11,136) B.Y ∧
      NeverHit D.classical.sphere (11,136) B.Y := ⟨h.y_to_e5, h.y_not_hit⟩

public theorem table2 :
    (SurvivesTo D.classical.sphere 6 (8,130) B.X ∧
      NeverHit D.classical.sphere (8,130) B.X) ∧
    (IsPermanentCycle D.classical.sphere (11,133) B.P ∧
      IsPermanentCycle D.classical.sphere (12,134) B.Q) :=
  ⟨⟨h.x_to_e6, h.x_not_hit⟩, ⟨h.p_permanent_cycle, h.q_permanent_cycle⟩⟩

public theorem table9 (r : ℤ) (_hr : 2 ≤ r) :
    ¬ HasNonzeroDifferential D.classical.sphere r (6,132) (14,139)
      (B.atom .x_126_6) B.T := by
  intro hd
  have hp := congrArg Prod.fst hd.toHasDifferential.target_degree
  have hdeg : (6 : ℤ) + r = 14 := by
    simpa only [ClassicalAdamsFamily.sphere, ClassicalAdamsFamily.obj,
      D.classical.differentialDegree, Prod.mk_add_mk, Prod.fst] using hp
  rcases h.t_only_incoming r hd.hit_target with hh | hh
  · omega
  · omega

/-- An actual late incoming target is rejected using the complete classifier. -/
public theorem no_other_incoming {r s t : ℤ}
    (_hr : 2 ≤ r) (h6 : r ≠ 6) (h12 : r ≠ 12)
    (x : D.classical.sphere.Page 2 (s,t)) :
    ¬ HasNonzeroDifferential D.classical.sphere r (s,t) (14,139) x B.T := by
  intro hx
  obtain ⟨hd, xr, yr, _, hyr, heq, hn⟩ := hx
  have hit : HitOnPage D.classical.sphere r (14,139) B.T :=
    ⟨(s,t), hd, xr, yr, hyr, hn, heq⟩
  rcases h.t_only_incoming r hit with hx | hx
  · exact h6 hx.1
  · exact h12 hx.1
end Near126Results
end KIP126.Computation
