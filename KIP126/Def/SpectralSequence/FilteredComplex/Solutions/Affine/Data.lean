module

public import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Proofs

@[expose] public section

namespace KIP126.Core.SpectralSequence.FilteredComplex.Solutions

open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {FC : FilteredComplex C} {T : C} {r s k : ℤ}
  {x : T ⟶ FC.assocGraded s k} {y : T ⟶ FC.assocGraded (s + r) (k - 1)}

/-- Translation by a homogeneous solution uses addition of the actual lifts. -/
noncomputable def translate (g : differences FC T r s k) (a : Fiber FC r s k x y) :
    Fiber FC r s k x y :=
  ⟨g.val + a.val, add_mem_fiber g a⟩

/-- The unique homogeneous displacement between two actual solutions. -/
noncomputable def displacement (b a : Fiber FC r s k x y) :
    differences FC T r s k :=
  ⟨b.val - a.val, sub_mem_differences b a⟩

/-- A chosen actual solution identifies its fiber with the actual kernel.
This does not assert that an empty fiber has a point. -/
noncomputable def coordinateEquiv (a : Fiber FC r s k x y) :
    differences FC T r s k ≃ Fiber FC r s k x y where
  toFun g := translate g a
  invFun b := displacement b a
  left_inv g := by apply Subtype.ext; simp [displacement, translate]
  right_inv b := by apply Subtype.ext; simp [displacement, translate]

end KIP126.Core.SpectralSequence.FilteredComplex.Solutions
