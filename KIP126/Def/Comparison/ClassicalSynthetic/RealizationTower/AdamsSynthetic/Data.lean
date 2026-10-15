module

public import KIP126.Def.Comparison.ClassicalSynthetic.RealizationTower.Pages.Data
public import KIP126.Def.AdamsSynthetic.Comparison.Coherent.Data

@[expose] public section

/-! Comparison of the ν E₂ classes with the specified realization tower.
The weight-base isomorphisms are explicit parameters from the λ-inversion
weight comparison and recovery isomorphism, rather than isomorphisms chosen
independently for individual classes. -/
namespace KIP126.Comparison.ClassicalSynthetic.RealizationTower
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn)

def nuWeightObject (X : ClassicalObject) (a w : ℤ) : Syn :=
  (SyntheticCategory.biShift (0,-w)).obj
    ((SyntheticCategory.biShift (0,a)).obj (D.nu.functor.obj (X.obj D.hopfAndDetector)))

/-- These maps identify the actual weight-desuspended objects, not merely
their isomorphism classes. The standard source constructs the collection
using its zero-weight recovery map and the actual realized lambda maps. -/
abbrev WeightBases := ∀ (X : ClassicalObject) (a w : ℤ),
  D.recovery.realization.obj (nuWeightObject D X a w) ≅ X.obj D.hopfAndDetector

variable [D.recovery.realization.Monoidal] [D.recovery.realization.Additive]
local instance realizationShift : D.recovery.realization.CommShift ℤ := D.realizationShift

/-- The coefficient iso is the SAME recovery component at HF2. -/
def coefficientIso :
    D.recovery.realization.obj (D.nu.functor.obj H.HF2) ≅ H.HF2 :=
  D.recovery.nuRealizationIso.app H.HF2

/-- Structural comparison obligation tying the named labels to the
canonical direction of tau inversion. The chosen tower presentation of D
is used literally. The E2 map is constructed from F.map on representatives
and the exact monoidal layer formula in `RealizationTower.Data`.

This record does NOT contain BHS differential rigidity, an E-infinity
formula, a permanence conclusion, or any selected local computation. -/
structure NuE2RealizationCompatibility (bases : WeightBases D) where
  tower : ∀ (X : ClassicalObject) (a w : ℤ),
    Comparison D.recovery.realization (nuCoefficientUnit H.unit D.nu) H.unit
      (coefficientIso D) (nuWeightObject D X a w) (X.obj D.hopfAndDetector) (bases X a w)
  label : ∀ (X : ClassicalObject) (a s t : ℤ) (k : ℕ)
      (x : E2 H (X.obj D.hopfAndDetector) s t),
    internalE2Map (tower X a (t+a-k)) (s,t)
      ((D.towerPresentation.forward
        ((SyntheticCategory.biShift (0,a)).obj (D.nu.functor.obj (X.obj D.hopfAndDetector)))
        (t+a-k)).pageMap (s,t) 0 (D.nuE2 X a s t k x)) = x

end
end KIP126.Comparison.ClassicalSynthetic.RealizationTower
