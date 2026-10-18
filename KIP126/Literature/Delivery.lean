module

public import KIP126.Literature.Classical
import all KIP126.Literature.Classical
public import KIP126.Literature.Rigidity
import all KIP126.Literature.Rigidity
public import KIP126.Literature.Triangles
import all KIP126.Literature.Triangles
public import KIP126.Literature.Lift
import all KIP126.Literature.Lift
public import KIP126.Literature.EInfinity
import all KIP126.Literature.EInfinity
public import KIP126.Literature.BHS
import all KIP126.Literature.BHS
public import KIP126.Literature.RealizationTransport
import all KIP126.Literature.RealizationTransport
public import KIP126.Literature.ClassicalRange
import all KIP126.Literature.ClassicalRange
public import KIP126.Literature.BX
import all KIP126.Literature.BX
public import KIP126.Literature.Secondary
import all KIP126.Literature.Secondary

/-! Correlated literature delivery, retaining the bindings/results/interface
architecture of Interface/Challenge/Literature/Delivery at bbac1fc05843.
The concrete producer is deliberately absent: its former `sorry` obligations
are not imported or converted into globally available axioms. -/

@[expose] section
set_option autoImplicit false
namespace KIP126.Literature
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

/-- Sources, their fixed coordinates, and comparison witnesses. -/
private structure LiteratureBindings extends ClassicalBindings D where
  rigidity : RigidityBindings D
  eInfinity : EInfinityPresentation D
  infinityShift : InfinityShiftCoordinates D
  weights_lambda : ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ)
    (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    rigidity.weights.map X s t w₁ w₂ hw ht = infinityShift.weightMap D X s t w₁ w₂ hw
  tmfSource : TmfSourceData D tmf
  secondary : SecondaryBindings D
  nuCofiber : NuCofiberApplicability D
  realizationTransport : BHSSelectedRealizationComparisons D realization

/-- Mathematical results use exactly the selected sources and background.
Internal arbitrary-choice θ₅ transport remains a separate theorem parameter. -/
private structure LiteratureResults (B : LiteratureBindings D) where
  foundation : ClassicalFoundationResults D
  classical : ClassicalResults D B.toClassicalBindings
  classicalRange : ClassicalRangeResults D
  rigidity : RigidityResults D B.rigidity
  triangles : NormalizedTriangleResults D
  lifts : LiftSourceResults D
  eInfinity : EInfinityCompatibility D B.eInfinity B.infinityShift
  bhs : BHSResults D
  selectedComparisons : BHSSelectedComparisons D
  realization : BHSRealizationResults D B.realization
  tmf : TmfSourceResults D B.tmfSource
  bx : BXDistinguishedInput D B.eta
  secondary : SecondaryResults D B.toClassicalBindings B.secondary

/-- A consumer supplies one correlated delivery on its given model. -/
private structure LiteratureInterface where
  bindings : LiteratureBindings D
  results : LiteratureResults D bindings

/-- The corrected weight map is epi by the same actual λ/quotient formula. -/
private theorem LiteratureInterface.weight_epi (L : LiteratureInterface D)
    (X : ClassicalObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t) :
    CategoryTheory.Epi (L.bindings.rigidity.weights.map X s t w₁ w₂ hw ht) := by
  rw [L.bindings.weights_lambda]
  exact L.results.eInfinity.weight_epi D X s t w₁ w₂ hw ht

end KIP126.Literature
