module

public import KIP126.Def.Algebra.GradedQuotient.Components.Data

@[expose] public section


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace KIP126.Algebra.GradedQuotient
noncomputable section
open DirectSum
variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommMonoid ι] [DecidableEq ι]
  (G : ι → Submodule R A) [GradedAlgebra G] (I : Ideal A)

@[simp] theorem split_apply (a : A) (i : ι) :
    (split G I a i : A ⧸ I) =
      Ideal.Quotient.mk I (DirectSum.decompose G a i : A) := rfl

theorem split_of_mem {i : ι} {a : A} (ha : a ∈ G i) :
    split G I a = DirectSum.lof R ι (fun j => part G I j) i
      ⟨Ideal.Quotient.mk I a, ⟨a, ha, rfl⟩⟩ := by
  change DirectSum.lmap (partMap G I) (DirectSum.decompose G a) = _
  rw [DirectSum.decompose_of_mem G ha]
  rw [DirectSum.lmap_of]
  rfl

theorem split_zero_of_mem (hI : I.IsHomogeneous G) {a : A} (ha : a ∈ I) :
    split G I a = 0 := by
  ext i
  change Ideal.Quotient.mk I (DirectSum.decompose G a i : A) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI i ha)

@[simp] theorem quotientSplit_mk (hI : I.IsHomogeneous G) (a : A) :
    quotientSplit G I hI (Ideal.Quotient.mk I a) = split G I a := rfl

theorem quotientSplit_of_mem (hI : I.IsHomogeneous G) {i : ι} {a : A ⧸ I}
    (ha : a ∈ part G I i) :
    quotientSplit G I hI a = DirectSum.lof R ι (fun j => part G I j) i ⟨a, ha⟩ := by
  obtain ⟨b, hb, rfl⟩ := ha
  change quotientSplit G I hI (Ideal.Quotient.mk I b) = _
  rw [quotientSplit_mk]
  exact split_of_mem G I hb

end
end KIP126.Algebra.GradedQuotient
