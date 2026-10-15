module

public import KIP126.Def.AdamsSynthetic.Conditions.Predicates
public import KIP126.Def.AdamsSynthetic.Comparison.Coherent.Data

@[expose] public section

open KIP126.Classical.Adams
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} (M : MilnorCooperations H)
  (D : AdamsComparison H M Syn) (L : SphereAdamsClasses H)

namespace KIP126.Main.Stem126.CandidateReduction
open KIP126.Classical.Adams KIP126.SpectralSequence
/-- The proposition reducing possible differentials on h₆² to the specified
d₁₂. This definition does not itself prove the reduction. Targets range over
E₂ labels in the required bidegrees; `HasNonzeroDifferential` requires a
nonzero differential on the actual Eᵣ-page. -/
def only_d12_differential_reduction : Prop :=
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  (∀ (r : ℤ), 2 ≤ r → r ≠ 12 →
    ∀ y : E.Page 2 (2 + r, 127 + r),
      ¬ HasNonzeroDifferential E r (2, 128) (2 + r, 127 + r)
        (Sphere.Internal.hiSquare H M 6) y) ∧
    ((∃ y : E.Page 2 (14, 139),
      HasNonzeroDifferential E 12 (2, 128) (14, 139)
        (Sphere.Internal.hiSquare H M 6) y) ↔ H6SquareSupportsD12 M L) ∧
    (¬ H6SquareSupportsD12 M L ↔ PermanentH6Square M)
end KIP126.Main.Stem126.CandidateReduction
