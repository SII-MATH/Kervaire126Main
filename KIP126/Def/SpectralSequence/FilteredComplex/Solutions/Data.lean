module

public import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Predicates
public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section

/-! Actual fibers of the filtered representative equation. Neither the
solution set nor its group of differences is an independently chosen input. -/

namespace KIP126.SpectralSequence.FilteredComplex

open CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Solutions

/-- The two actual filtered representatives, before imposing their equation. -/
abbrev Representatives (FC : FilteredComplex C) (T : C) (r s k : ℤ) :=
  (T ⟶ Subobject.underlying.obj (FC.fil s k)) ×
    (T ⟶ Subobject.underlying.obj (FC.fil (s + r) (k - 1)))

/-- Source label, target label, and the differential discrepancy. -/
abbrev Equations (FC : FilteredComplex C) (T : C) (r s k : ℤ) :=
  (T ⟶ FC.assocGraded s k) × (T ⟶ FC.assocGraded (s + r) (k - 1)) ×
    (T ⟶ FC.A (k - 1))

/-- All three equations use the original filtered complex and quotient maps.
The ambient differential equation avoids a choice of a shorter-image group:
changing the source lift already allows every higher-filtration correction. -/
noncomputable def equation (FC : FilteredComplex C) (T : C) (r s k : ℤ) :
    Representatives FC T r s k →+ Equations FC T r s k where
  toFun z := (z.1 ≫ FC.filToAssocGraded s k,
    z.2 ≫ FC.filToAssocGraded (s + r) (k - 1),
    z.1 ≫ (FC.fil s k).arrow ≫ FC.d k -
      z.2 ≫ (FC.fil (s + r) (k - 1)).arrow)
  map_zero' := by simp
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, Preadditive.add_comp, Prod.mk_add_mk]
    congr 2
    abel

/-- The actual representative-solution fiber over the prescribed labels. -/
def Fiber (FC : FilteredComplex C) {T : C} (r s k : ℤ)
    (x : T ⟶ FC.assocGraded s k)
    (y : T ⟶ FC.assocGraded (s + r) (k - 1)) :=
  { z : Representatives FC T r s k // equation FC T r s k z = (x, y, 0) }

end Solutions
end KIP126.SpectralSequence.FilteredComplex
