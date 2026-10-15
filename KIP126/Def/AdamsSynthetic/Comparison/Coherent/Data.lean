module

public import KIP126.Def.Synthetic.AdamsFiltration.Convergence.Canonical.Predicates
public import KIP126.Def.AdamsSynthetic.Comparison.Predicates

@[expose] public section

namespace KIP126.AdamsSynthetic
open KIP126.Classical.Adams
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H) (Syn : Type w)
  [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]

/-- Compatible classical/synthetic Adams data, including canonical tower
convergence, separation and multiplicative detection. This structure is
parameterized by its data; its existence and external theorems are separate
hypotheses. -/
structure AdamsComparison extends AdamsComparisonData H Syn where
  towerPresentation : TowerPresentation (nuCoefficientUnit H.unit nu) family
  /-- Detection uses the actual tower lift/cofiber comparison for this
  ONE presentation. An arbitrary E-infinity/associated-graded isomorphism
  does not identify the detected homotopy class. -/
  convergence_canonical : ∀ X,
    TowerConvergence.Canonical (nuCoefficientUnit H.unit nu) (convergence X) towerPresentation
  comparisonCompatible : ComparisonCompatible toAdamsComparisonData
  homotopySeparated : HomotopySeparated toAdamsComparisonData
  sphereProductCommutative : SphereProductCommutative (Syn := Syn)
  multiplicationCompatible : MultiplicationCompatible toAdamsComparisonData M
end KIP126.AdamsSynthetic
