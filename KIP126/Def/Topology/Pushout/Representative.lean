module

public import KIP126.Def.Topology.Pushout.Cells.Proofs

@[expose] public section

section

namespace KIP126.Topology
open CategoryTheory CategoryTheory.Limits _root_.Topology Set
universe u
set_option backward.isDefEq.respectTransparency false

/-- Choose the actual cell representative of a point outside the old space. -/
noncomputable def pushoutCellRepresentative
    {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (x : P) (hx : x ∉ Set.range b) : A :=
  ((Types.eq_or_eq_of_isPushout (h.map (forget TopCat)) x).resolve_right hx).choose


end KIP126.Topology

end

section

namespace KIP126.Topology
open CategoryTheory CategoryTheory.Limits _root_.Topology Set
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem pushoutCellRepresentative_projection
    {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (x : P) (hx : x ∉ Set.range b) :
    a (pushoutCellRepresentative h x hx) = x :=
  ((Types.eq_or_eq_of_isPushout (h.map (forget TopCat)) x).resolve_right hx).choose_spec

theorem pushoutCellRepresentative_not_boundary
    {S A B P : TopCat.{u}} {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (x : P) (hx : x ∉ Set.range b) :
    pushoutCellRepresentative h x hx ∉ Set.range i := by
  rintro ⟨s,hs⟩
  apply hx
  refine ⟨f s,?_⟩
  have hw := ConcreteCategory.congr_hom h.w s
  exact hw.symm.trans ((congrArg a hs).trans (pushoutCellRepresentative_projection h x hx))

/-- Outside the old space, the selected representative is the unique actual
cell representative. -/
theorem pushoutCellRepresentative_eq
    {S A B P : TopCat.{u}} [NormalSpace A] [T1Space A]
    {i : S ⟶ A} {f : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsPushout i f a b) (hi : IsClosedEmbedding i)
    (x : P) (hx : x ∉ Set.range b) (y : A) (hy : a y = x) :
    pushoutCellRepresentative h x hx = y :=
  pushout_cell_eq_of_outside_boundary h hi (pushoutCellRepresentative_not_boundary h x hx)
    ((pushoutCellRepresentative_projection h x hx).trans hy.symm)


end KIP126.Topology

end
