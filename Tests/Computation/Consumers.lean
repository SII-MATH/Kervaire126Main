module

import KIP126.Def.Computation

set_option linter.unusedVariables false

/-! Ordinary public imports suffice for every mathematical consumer. -/
namespace Tests.Computation
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Kervaire.Route KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Computation
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {D : Model C Syn} {B : Bindings D}

/-- The original Fact 7.6 can be consumed before constructing its producer. -/
theorem factSevenSix (h : Near126Results B) :
    SurvivesTo D.classical.sphere 6 (8,134) B.W ∧
      IsPermanentCycle D.classical.sphere (14,139) B.T ∧
      NonzeroSurvival D.classical.sphere (10,134) B.U ∧ HighComponent B :=
  ⟨h.w_to_e6, h.t_permanent_cycle, h.u_permanent, h.high_e5⟩

theorem allIncomingPages (h : Near126Results B) {r s t : ℤ}
    (hr : 2 ≤ r) (h6 : r ≠ 6) (h12 : r ≠ 12)
    (x : D.classical.sphere.Page 2 (s,t)) :
    ¬ HasNonzeroDifferential D.classical.sphere r (s,t) (14,139) x B.T :=
  h.no_other_incoming hr h6 h12 x

theorem tableNine (h : Near126Results B) (r : ℤ) (hr : 2 ≤ r) :
    ¬ HasNonzeroDifferential D.classical.sphere r (6,132) (14,139)
      (B.atom .x_126_6) B.T := h.table9 r hr

theorem tableThree (h : Near126Results B) :
    SurvivesTo D.classical.sphere 12 (9,132) B.V ∧
    NeverHit D.classical.sphere (9,132) B.V ∧
    HasNonzeroDifferential D.classical.sphere 2 (8,133) (10,134)
      (B.atom .x_125_8) B.d2Target := h.table3

theorem tableSeven (h : Near126Results B) :
    SurvivesTo D.classical.sphere 5 (11,136) B.Y ∧
      NeverHit D.classical.sphere (11,136) B.Y := h.table7

theorem tableTwo (h : Near126Results B) :
    (SurvivesTo D.classical.sphere 6 (8,130) B.X ∧
      NeverHit D.classical.sphere (8,130) B.X) ∧
    (IsPermanentCycle D.classical.sphere (11,133) B.P ∧
      IsPermanentCycle D.classical.sphere (12,134) B.Q) := h.table2

/-- The bounded comparison also exposes the existing F₂ scalar structure. -/
noncomputable def sourceCoordinates (s t : ℕ) (ht : t ≤ 261) :
    letI := D.sphereAlgebra.scalar (s,t)
    B.data.component s t ≃ₗ[ZMod 2] D.classical.sphere.Page 2 (s,t) :=
  B.presentation.comparisonF2 s t ht

/-- Whole actual-page basis coordinates are fixed by the archived monomials. -/
theorem archivedBasis (s t : ℕ) (ht : t ≤ 261) (i : Fin (B.archive.basisCount s t)) :
    (B.presentation.comparison s t ht).symm
      ((B.presentation.coordinates B.sourceBasis s t ht).symm (Finsupp.single i 1)) =
      (B.archive.basisMonomial s t i).value B.data B.sourceBasis.generator :=
  B.presentation.comparison_symm_coordinates_basis B.sourceBasis s t ht i

/-- A supplied comparison transports the actual data product, with the bound
on total internal degree retained. -/
theorem productComparison (s t s' t' : ℕ) (ht : t+t' ≤ 261)
    (x : B.data.component s t) (y : B.data.component s' t') :
    B.presentation.comparison (s+s') (t+t') ht (B.data.product s t s' t' x y) =
      D.sphereAlgebra.product (s,t) (s',t')
        (B.presentation.comparison s t (by omega) x)
        (B.presentation.comparison s' t' (by omega) y) :=
  B.presentation.comparison_mul s t s' t' ht x y

/-- The intended final target uses the actual designated h₆ square. This only
identifies the E₂ label, and does not prove its permanence. -/
theorem squareIdentification :
    B.presentation.comparison 2 128 (by decide)
      (B.data.product 1 64 1 64 (B.data.atom .h6) (B.data.atom .h6)) =
      D.standardClasses.standardH6Square := B.presentation.h6_square

theorem cofiberFiniteSurvival {Q : CofiberBindings B} (h : CofiberResults B Q) :
    SurvivesTo (cofiberSequence D) 6 (14,139) (bottom D 14 139 B.T) ∧
      NeverHitOnWindow (cofiberSequence D) 2 5 (14,139) (bottom D 14 139 B.T) :=
  ⟨h.target_to_e6, h.target_not_hit_through5⟩

/-- A different model requires an explicit comparison/transport. -/
example (D' : Model C Syn) (B' : Bindings D') (h : Near126Results B) : True := by
  fail_if_success have _ : Near126Results B' := h
  fail_if_success have _ : NonzeroSurvival D'.classical.sphere (10,134) B'.U := h.u_permanent
  trivial

/-- Finite and permanent-cycle fields do not silently become nonzero E∞ data. -/
example (h : Near126Results B) : True := by
  fail_if_success have _ : NonzeroSurvival D.classical.sphere (8,134) B.W := h.w_to_e6
  fail_if_success have _ : NonzeroSurvival D.classical.sphere (14,139) B.T := h.t_permanent_cycle
  trivial

/-- A standard one-line differential is reused from the very same literature
input, instead of being demanded again as a computation certificate. -/
theorem literatureOneLine (L : KIP126.Literature.LiteratureInterface D) :
    HasNonzeroDifferential D.classical.sphere 2 (1,64) (3,65)
      (Bindings.h6 (D := D))
      (Bindings.product (D := D) (Bindings.h0 (D := D)) (Bindings.h5Square (D := D))) :=
  ComputationInterface.d2_h6 (L := L)

/-- Full downstream use starts from one literature delivery and its dependent
computation package; all data, classes and result projections are available. -/
theorem correlatedDelivery (L : KIP126.Literature.LiteratureInterface D)
    (I : ComputationInterface L) :
    NonzeroSurvival D.classical.sphere (10,134) I.bindings.toBindings.U :=
  I.near126.u_permanent

theorem detectorSourceComparison (L : KIP126.Literature.LiteratureInterface D)
    (I : ComputationInterface L) :
    HasDifferential (D.classical.obj D.auxiliary.detector) 3 (16,112) (19,114)
      (I.bindings.detectorPresentation.comparison 16 112 (by decide)
        I.bindings.detectorData.v2Sixteen)
      (I.bindings.detectorPresentation.comparison 19 114 (by decide)
        I.bindings.detectorData.betaGFour) := I.detector_d3

example (L L' : KIP126.Literature.LiteratureInterface D)
    (I : ComputationInterface L) : True := by
  fail_if_success have _ : ComputationInterface L' := I
  trivial
end Tests.Computation
