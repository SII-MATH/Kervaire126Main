module

import all KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Restriction.Data
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] section

namespace KIP126.Core.SpectralSequence.FilteredComplex.Solutions

open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {FC GD : FilteredComplex C}

/-- Simultaneously impose the later equation and its specified earlier lift. -/
noncomputable def liftingMap (f : Morphism FC GD) (T : C) (r s k : ℤ) :
    Representatives FC T r s k →+
      Equations FC T r s k × Representatives GD T r s k :=
  (equation FC T r s k).prod (representativesMap f T r s k)

/-- A concrete cokernel obstruction; no solution is chosen in either fiber. -/
noncomputable def LiftingObstruction (f : Morphism FC GD) (T : C) (r s k : ℤ) :=
  (Equations FC T r s k × Representatives GD T r s k) ⧸
    (liftingMap f T r s k).range

noncomputable instance (f : Morphism FC GD) (T : C) (r s k : ℤ) :
    AddCommGroup (LiftingObstruction f T r s k) :=
  inferInstanceAs (AddCommGroup (_ ⧸ (liftingMap f T r s k).range))

/-- The obstruction of the actual earlier representative equation. -/
noncomputable def obstruction (f : Morphism FC GD) {T : C} {r s k : ℤ}
    (x : T ⟶ FC.assocGraded s k) (y : T ⟶ FC.assocGraded (s + r) (k - 1))
    (a : Fiber GD r s k (x ≫ f.associatedGradedMap s k)
      (y ≫ f.associatedGradedMap (s + r) (k - 1))) :
    LiftingObstruction f T r s k :=
  QuotientAddGroup.mk ((x, y, 0), a.val)

end KIP126.Core.SpectralSequence.FilteredComplex.Solutions
