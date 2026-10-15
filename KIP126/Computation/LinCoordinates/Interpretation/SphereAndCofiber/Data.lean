module

public import KIP126.Computation.LinCoordinates.SphereAndCofiber.Tables
public import KIP126.Computation.LinCoordinates.Interpretation.Near126.Classes.Data
public import KIP126.Def.AdamsSynthetic.Comparison.Coherent.Data

@[expose] public section

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.LinE2
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

/-- The sphere and the cofiber of ν, whose Adams sequences occur in the
finite computation statements below. -/
def object (D : AdamsComparison H M Syn) : Raw.Spectrum → C
  | .sphere => SphereSpectrum
  | .nuCofiber => HasFunctorialCofiber.cofib D.hopfAndDetector.nuMap

abbrev sequence (D : AdamsComparison H M Syn) (o : Raw.Spectrum) :=
  adamsTowerInternalSpectralSequence H.unit (object D o)
abbrev Page (D : AdamsComparison H M Syn) (o : Raw.Spectrum) (s t : Nat) :=
  (sequence D o).Page 2 ((s : ℤ), (t : ℤ))

/-- A comparison choice, with no truth claims. Outside the finite catalogue
its basis function has no computational meaning. No unrelated SS is a field. -/
structure E2Interpretation (D : AdamsComparison H M Syn) where
  sphere : ∀ s t, E2At s t →ₗ[ℤ] E2 H SphereSpectrum s t
  basis : ∀ o s t, Nat → Page D o s t

/-- Fail closed: a missing degree or out-of-range local index has no meaning,
including a zero coordinate list at a missing degree. Unknown is never zero. -/
def E2Interpretation.coordinateSum {D : AdamsComparison H M Syn} (R : E2Interpretation D)
    (o : Raw.Spectrum) (s t : Nat) (indices : List Nat) : Option (Page D o s t) :=
  if Raw.coordinatesValid Raw.degrees o s t indices then
    some ((indices.map (R.basis o s t)).sum)
  else none

end
end KIP126.Computation.SphereAndCofiber
