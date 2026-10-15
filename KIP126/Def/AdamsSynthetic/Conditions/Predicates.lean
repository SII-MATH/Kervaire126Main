module

public import KIP126.Def.AdamsSynthetic.Comparison.Data
public import KIP126.Def.Kervaire.Theta5.Synthetic.Predicates

@[expose] public section

/-! The differential-vanishing, square-detection and η-extension conditions
of LWX Proposition 7.8(3)--(5), on one classical/synthetic Adams comparison.
A definition is not an assertion of any of these conditions. -/
namespace KIP126.AdamsSynthetic
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} (M : MilnorCooperations H)
  (D : AdamsComparisonData H Syn) (L : SphereAdamsClasses H)

/-- No free permanence predicate: this is the existing internal T(M). -/
def PermanentH6Square : Prop :=
  NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
    (2, 128) (Sphere.Internal.hiSquare H M 6)

/-- LWX Proposition 7.8(2): the specified nonzero d₁₂ on h₆².
The target must be nonzero on E₁₂, not merely on E₂. -/
def H6SquareSupportsD12 : Prop :=
  HasNonzeroDifferential (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
    12 (2, 128) (14, 139) (Sphere.Internal.hiSquare H M 6) (L.target M)

/-- LWX Proposition 7.8(3): d₆ vanishes on x₁₂₆,₈,₄ + x₁₂₆,₈.
The zero differential requires an E₆ representative. This cannot be
satisfied merely because the source has no continuation to E₆. -/
def Stem126D6Vanishes : Prop :=
  HasDifferential (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
    6 (8, 134) (14, 139) L.W 0

/-- Admissible θ₅ choices use the standard h₅² and the same sphere comparison. -/
def ThetaChoice (θ : BiHom 62 64 (S_0_0 : Syn)) : Prop :=
  KIP126.Kervaire.SyntheticTheta5.DetectsTheta H M D.sphereFirstQuotient θ

/-- Fixed η is identified by the standard h₁, not an arbitrary operation. -/
def EtaChoice (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  KIP126.Kervaire.SyntheticTheta5.DetectsEta H M D.sphereFirstQuotient η

/-- Proposition 7.8(4) at a specified choice. Detection retains higher-AF
indeterminacy; its leading E∞ class is required to be nonzero. -/
def Theta5SquareNonzeroDetectionAt (θ : BiHom 62 64 (S_0_0 : Syn)) : Prop :=
  DetectsNonzero D.sphereConvergence (10, 134, 128)
    (D.sphereE2 10 134 6 (L.U M)) (sphereProduct θ θ)

/-- LWX Proposition 7.8(4), with an existential admissible θ₅ choice. -/
def Theta5SquareNonzeroDetection : Prop :=
  ∃ θ, ThetaChoice M D θ ∧ Theta5SquareNonzeroDetectionAt M D L θ

/-- `[U]` means an actual homotopy lift detected by U. -/
def UChoice (u : BiHom 124 134 (S_0_0 : Syn)) : Prop :=
  DetectsNonzero D.sphereConvergence (10, 134, 134)
    (D.sphereE2 10 134 0 (L.U M)) u

/-- Proposition 7.8(5). No nonzero condition is added to the target here:
Remark 7.12 makes that depend on the d₆-vanishing condition. The relation is equality in the
associated graded, NOT a selected exact homotopy equality. -/
def EtaExtensionDetectionAt (η : BiHom 1 2 (S_0_0 : Syn)) (u : BiHom 124 134 (S_0_0 : Syn)) : Prop :=
  Detects D.sphereConvergence (14, 139, 133)
    (D.sphereE2 14 139 6 (L.target M))
    (lambdaMultiply 3 (sphereProduct η u))

/-- LWX Proposition 7.8(5), with an existential detected U representative. -/
def EtaExtensionDetection (η : BiHom 1 2 (S_0_0 : Syn)) : Prop :=
  ∃ u, UChoice M D L u ∧ EtaExtensionDetectionAt M D L η u
end KIP126.AdamsSynthetic
