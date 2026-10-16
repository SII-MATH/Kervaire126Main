module

public import KIP126.AdamsSynthetic.Context

@[expose] section

/-! Object closure for the selected proof route. Auxiliary objects are
parameters with explicit maps, not asserted to have tmf's properties by
their names. A(M) supplies the literature identifications/properties.
The cofiber and its cell maps are derived from the supplied ν map. -/
namespace KIP126.Kervaire.Route
open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

public structure AuxiliaryData (C : Type u) [StableHomotopyCategory.{u, v} C] where
  /-- The classical η map used by the generalized Leibniz rule.
  Its identification with h₁ and with the synthetic η is an A(M) input. -/
  etaMap : Sphere (C := C) 1 ⟶ SphereSpectrum
  /-- The selected classical Hopf map; its h₂ detection is an A(M) input. -/
  nuMap : Sphere (C := C) 3 ⟶ SphereSpectrum
  /-- In the paper this pointed detecting spectrum is tmf. -/
  detector : C
  detectorUnit : SphereSpectrum ⟶ detector

/-- No other spectra are needed in the selected Section 7 route when C(M)
results are accepted; spectra used to prove C(M) are a separate dependency. -/
public inductive ClassicalObject
  | sphere
  | nuCofiber
  | detector
  | shift (n : ℤ) (X : ClassicalObject)

public noncomputable def ClassicalObject.obj [HasFunctorialCofiber (C := C)]
    (A : AuxiliaryData C) : ClassicalObject → C
  | .sphere => SphereSpectrum
  | .nuCofiber => HasFunctorialCofiber.cofib A.nuMap
  | .detector => A.detector
  | .shift n X => (shiftFunctor C n).obj (X.obj A)

/-- Synthetic objects used by normalized maps, finite λ/ρ/δ triangles,
and the untruncated argument. Closure includes all shifts and quotients,
but does not demand convergence on every object of the ambient category. -/
public inductive SyntheticObject
  | sphere
  | nu (X : ClassicalObject)
  | shift (p : ℤ × ℤ) (X : SyntheticObject)
  | quotient (n : ℕ) (X : SyntheticObject)

public noncomputable def SyntheticObject.obj [HasFunctorialCofiber (C := C)]
    {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
    (N : NuFunctorData C Syn) (A : AuxiliaryData C) : SyntheticObject → Syn
  | .sphere => S_0_0
  | .nu X => N.functor.obj (X.obj A)
  | .shift p X => (SyntheticCategory.biShift p).obj (X.obj N A)
  | .quotient n X => XModLambdaN (X.obj N A) n

/-- A distinguished triangle within the selected classical object closure.
The connecting map lands in the actual suspension of X. -/
public structure TriangleData [HasFunctorialCofiber (C := C)] (A : AuxiliaryData C) where
  X : ClassicalObject
  Y : ClassicalObject
  Z : ClassicalObject
  f : X.obj A ⟶ Y.obj A
  g : Y.obj A ⟶ Z.obj A
  h : Z.obj A ⟶ (ClassicalObject.shift 1 X).obj A
  distinguished : CategoryTheory.Pretriangulated.Triangle.mk f g h ∈
    distTriang C

/-- The specific triangle used in the ν-extension argument. Neither its
cofiber nor its bottom/top cell maps are independent choices. -/
public noncomputable def AuxiliaryData.nuRouteTriangle [HasFunctorialCofiber (C := C)]
    (A : AuxiliaryData C) : TriangleData A where
  X := .shift 3 .sphere
  Y := .sphere
  Z := .nuCofiber
  f := A.nuMap
  g := HasFunctorialCofiber.cofibι A.nuMap
  h := HasFunctorialCofiber.cofibδ A.nuMap
  distinguished := HasFunctorialCofiber.cofib_distinguished A.nuMap
end KIP126.Kervaire.Route
