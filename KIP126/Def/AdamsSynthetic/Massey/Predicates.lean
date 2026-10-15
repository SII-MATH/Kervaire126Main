module

public import KIP126.Def.AdamsSynthetic.SphereClasses.Data
public import KIP126.Def.ClassicalAdams.Detection.Predicates
public import KIP126.Def.StableHomotopy.Toda.Predicates

@[expose] public section

/-! The sphere E₃ Massey product actually used in LWX Lemma 7.16.
The defining differential is d₂ on the current tower, and the multiplication
is the standard Milnor cup product. No Massey value, zero indeterminacy,
no-crossing assertion, or Moss theorem is assumed here. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} (M : MilnorCooperations H)

/-- A full E₂ defining system for <h₅²,h₀,B>, |B|=(8,70).
The result has degree (9,134), hence stem 125. At p=2 all signs coincide.
Both nullhomotopies are quantified, retaining the full indeterminacy. -/
def ThetaBMasseyDefiningSystem (B : E2 H SphereSpectrum 8 70)
    (z : E2 H SphereSpectrum 9 134) : Prop :=
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  IsPageCycle E 2 (2, 64) (Sphere.Internal.hiSquare H M 5) ∧
  IsPageCycle E 2 (1, 1) (Sphere.Internal.hi H M 0) ∧
  IsPageCycle E 2 (8, 70) B ∧
  ∃ (a : E2 H SphereSpectrum 1 64) (b : E2 H SphereSpectrum 7 70),
    E.d 2 (1, 64) a =
      Sphere.Internal.product H M (s := 2) (t := 64) (s' := 1) (t' := 1)
        (Sphere.Internal.hiSquare H M 5) (Sphere.Internal.hi H M 0) ∧
    E.d 2 (7, 70) b =
      Sphere.Internal.product H M (s := 1) (t := 1) (s' := 8) (t' := 70)
        (Sphere.Internal.hi H M 0) B ∧
    z = Sphere.Internal.product H M (s := 1) (t := 64) (s' := 8) (t' := 70) a B +
      Sphere.Internal.product H M (s := 2) (t := 64) (s' := 7) (t' := 70)
        (Sphere.Internal.hiSquare H M 5) b

/-- The entire subset of E₃, using actual common-cycle representatives. -/
def ThetaBMassey (B : E2 H SphereSpectrum 8 70) :
    Set ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 3 (9, 134)) :=
  {x | ∃ z, ThetaBMasseyDefiningSystem M B z ∧
    RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) 3 (9, 134) z x}

/-- Zero indeterminacy is a property of that subset, not a selected output. -/
def ThetaBMasseyZeroIndeterminacy (B : E2 H SphereSpectrum 8 70) : Prop :=
  (ThetaBMassey M B).Nonempty ∧ (ThetaBMassey M B).Subsingleton

/-- Moss-direction crossings for a product degree, on the actual sphere
sequence. The paper's extension-crossing predicate has the other direction. -/
def SphereMossCrossing (r : ℤ) (p : ℤ × ℤ) : Prop :=
  ∃ m q : ℤ, r < m ∧ 0 ≤ q ∧ q < p.1 - (r - 1) ∧ p.1 < q + m ∧
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).d m
      (q, q + (p.2 - p.1) + 1) ≠ 0
end KIP126.AdamsSynthetic
