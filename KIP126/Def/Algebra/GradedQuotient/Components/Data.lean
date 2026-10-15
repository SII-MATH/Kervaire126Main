module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section


/-! Homogeneous components and representative-independent quotient decomposition maps. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace KIP126.Algebra.GradedQuotient
noncomputable section
open DirectSum
variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommMonoid ι] [DecidableEq ι]
  (G : ι → Submodule R A) [GradedAlgebra G] (I : Ideal A)

/-- The image of an original homogeneous component in the quotient. -/
def part (i : ι) : Submodule R (A ⧸ I) :=
  (G i).map (Ideal.Quotient.mkₐ R I).toLinearMap

def partMap (i : ι) : G i →ₗ[R] part G I i :=
  ((Ideal.Quotient.mkₐ R I).toLinearMap.comp (G i).subtype).codRestrict _
    (fun x => ⟨x, x.property, rfl⟩)

def split : A →ₗ[R] ⨁ i, part G I i :=
  (DirectSum.lmap (partMap G I)).comp (DirectSum.decomposeLinearEquiv G).toLinearMap

/-- Decompose a quotient class; homogeneity makes this independent of the representative. -/
def quotientSplit (hI : I.IsHomogeneous G) : (A ⧸ I) →+ ⨁ i, part G I i :=
  QuotientAddGroup.lift I.toAddSubgroup (split G I).toAddMonoidHom (by
    intro a ha
    ext i
    change Ideal.Quotient.mk I (DirectSum.decompose G a i : A) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI i ha))

end
end KIP126.Algebra.GradedQuotient
