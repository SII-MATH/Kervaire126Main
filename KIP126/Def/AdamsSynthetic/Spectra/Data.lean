module

public import KIP126.Def.Synthetic.Sphere.Data
public import KIP126.Def.StableHomotopy.Context.Proofs

@[expose] public section

/-! The classical and synthetic objects used in Section 7.
The classical Hopf maps and detecting spectrum are specified with their maps;
their detection and identification with tmf are separate literature hypotheses.
The ν-cofiber and its cell maps come from the chosen cofiber construction. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

structure HopfAndDetectorData (C : Type u) [StableHomotopyCategory.{u, v} C] where
  /-- The classical η map used by the generalized Leibniz rule.
  Its detection by h₁ and its comparison with synthetic η are literature hypotheses. -/
  etaMap : Sphere (C := C) 1 ⟶ SphereSpectrum
  /-- The selected classical Hopf map; its h₂ detection is a literature hypothesis. -/
  nuMap : Sphere (C := C) 3 ⟶ SphereSpectrum
  /-- In the paper this pointed detecting spectrum is tmf. -/
  detector : C
  detectorUnit : SphereSpectrum ⟶ detector

/-- The classical objects used in Section 7 after assuming the stated
external computations. The spectra used to establish those computations
are outside this object closure. -/
inductive ClassicalObject
  | sphere
  | nuCofiber
  | detector
  | shift (n : ℤ) (X : ClassicalObject)

noncomputable def ClassicalObject.obj [HasFunctorialCofiber (C := C)]
    (A : HopfAndDetectorData C) : ClassicalObject → C
  | .sphere => SphereSpectrum
  | .nuCofiber => HasFunctorialCofiber.cofib A.nuMap
  | .detector => A.detector
  | .shift n X => (shiftFunctor C n).obj (X.obj A)

/-- Synthetic objects used by normalized maps, finite λ/ρ/δ triangles,
and the untruncated argument. Closure includes all shifts and quotients,
but does not demand convergence on every object of the ambient category. -/
inductive SyntheticObject
  | sphere
  | nu (X : ClassicalObject)
  | shift (p : ℤ × ℤ) (X : SyntheticObject)
  | quotient (n : ℕ) (X : SyntheticObject)

noncomputable def SyntheticObject.obj [HasFunctorialCofiber (C := C)]
    {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
    (N : NuFunctorData C Syn) (A : HopfAndDetectorData C) : SyntheticObject → Syn
  | .sphere => S_0_0
  | .nu X => N.functor.obj (X.obj A)
  | .shift p X => (SyntheticCategory.biShift p).obj (X.obj N A)
  | .quotient n X => XModLambdaN (X.obj N A) n

/-- The actual ν cofiber triangle, with actual bottom/top cell maps. -/
noncomputable def HopfAndDetectorData.nuTriangle [HasFunctorialCofiber (C := C)]
    (A : HopfAndDetectorData C) : HoCofiberSequence (C := C) :=
  HoCofiberSequence.ofMorphism A.nuMap

/-- A distinguished triangle within the selected classical object closure.
The connecting map lands in the actual suspension of X. -/
structure ClassicalCofiberTriangle [HasFunctorialCofiber (C := C)] (A : HopfAndDetectorData C) where
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
noncomputable def HopfAndDetectorData.nuCofiberTriangle [HasFunctorialCofiber (C := C)]
    (A : HopfAndDetectorData C) : ClassicalCofiberTriangle A where
  X := .shift 3 .sphere
  Y := .sphere
  Z := .nuCofiber
  f := A.nuMap
  g := HasFunctorialCofiber.cofibι A.nuMap
  h := HasFunctorialCofiber.cofibδ A.nuMap
  distinguished := HasFunctorialCofiber.cofib_distinguished A.nuMap
end KIP126.AdamsSynthetic
