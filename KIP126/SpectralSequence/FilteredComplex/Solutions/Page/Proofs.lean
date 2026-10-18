module

import all KIP126.SpectralSequence.FilteredComplex.Solutions.Proofs
import all KIP126.SpectralSequence.FilteredComplex.SpectralSequenceConstruction.Data
import all KIP126.SpectralSequence.Crossing.Predicates

@[expose] section

namespace KIP126.Core.SpectralSequence.FilteredComplex.Solutions

set_option backward.isDefEq.respectTransparency false
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An actual solution gives the canonical internal page differential. -/
theorem differentialRelation_of_fiber (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (n : ℕ) (s k : ℤ) {T : C}
    {x : T ⟶ FC.assocGraded s k}
    {y : T ⟶ FC.assocGraded (s + (n : ℤ)) (k - 1)}
    (a : Fiber FC n s k x y) :
    DifferentialRelation (FC.toSpectralSequence bnd) n (s, k) x y := by
  obtain ⟨xl, yl, hx, hy, hd⟩ :=
    (nonempty_fiber_iff (by omega : (0 : ℤ) ≤ n)).mp ⟨a⟩
  obtain ⟨zx, zy, hzx, hzy, hdiff⟩ :=
    FC.pageDifferential_of_strict_lifts s k n xl yl hd
  refine ⟨zx, hzx.trans hx, zy, hzy.trans hy, ?_⟩
  change zx ≫ _ ≫ (FC.toPreSS bnd).d (n : ℤ) (s, k) = _
  rw [FC.toPreSS_d_nat bnd]
  exact hdiff

end KIP126.Core.SpectralSequence.FilteredComplex.Solutions
