module

public import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Restriction.Proofs
public import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Obstruction.Proofs

@[expose] public section

namespace KIP126.Core.SpectralSequence.FilteredComplex.Solutions

open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {FC GD : FilteredComplex C} {T : C} {r s k : ℤ}
  {x : T ⟶ FC.assocGraded s k} {y : T ⟶ FC.assocGraded (s + r) (k - 1)}

/-- Restriction carries the displacement of two actual solutions to the
displacement of their restrictions. -/
theorem restrict_displacement (f : Morphism FC GD) (b a : Fiber FC r s k x y) :
    restrictDifferences f T r s k (displacement b a) =
      displacement (restrict f b) (restrict f a) := by
  apply Subtype.ext
  exact map_sub (representativesMap f T r s k) b.val a.val

/-- Once a later solution is specified, lifting every earlier strict solution
is equivalent to lifting every homogeneous displacement. Existence of the
basepoint alone does not imply either surjectivity assertion. -/
theorem restrict_surjective_iff_differences_surjective (f : Morphism FC GD)
    (a : Fiber FC r s k x y) :
    Function.Surjective (restrict f : Fiber FC r s k x y → _) ↔
      Function.Surjective (restrictDifferences f T r s k) := by
  constructor
  · intro h g
    obtain ⟨b, hb⟩ := h (translate g (restrict f a))
    refine ⟨displacement b a, ?_⟩
    rw [restrict_displacement, hb]
    exact (coordinateEquiv (restrict f a)).left_inv g
  · intro h b
    obtain ⟨g, hg⟩ := h (displacement b (restrict f a))
    refine ⟨translate g a, ?_⟩
    rw [restrict_translate, hg]
    exact (coordinateEquiv (restrict f a)).apply_symm_apply b

/-- Vanishing of the specified strict lifting obstruction for every earlier
solution is exactly surjectivity on the actual solution fibers. -/
theorem forall_obstruction_eq_zero_iff_surjective (f : Morphism FC GD) :
    (∀ a : Fiber GD r s k (x ≫ f.associatedGradedMap s k)
      (y ≫ f.associatedGradedMap (s + r) (k - 1)), obstruction f x y a = 0) ↔
      Function.Surjective (restrict f : Fiber FC r s k x y → _) := by
  simp only [obstruction_eq_zero_iff, Function.Surjective]

/-- With a later basepoint, all strict lifting obstructions vanish precisely
when the actual homomorphism of homogeneous solution groups is surjective. -/
theorem forall_obstruction_eq_zero_iff_differences_surjective (f : Morphism FC GD)
    (a : Fiber FC r s k x y) :
    (∀ b : Fiber GD r s k (x ≫ f.associatedGradedMap s k)
      (y ≫ f.associatedGradedMap (s + r) (k - 1)), obstruction f x y b = 0) ↔
      Function.Surjective (restrictDifferences f T r s k) :=
  (forall_obstruction_eq_zero_iff_surjective f).trans
    (restrict_surjective_iff_differences_surjective f a)

end KIP126.Core.SpectralSequence.FilteredComplex.Solutions
