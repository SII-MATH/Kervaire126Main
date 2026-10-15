module

public import KIP126.Def.Algebra.GradedQuotient.Components.Proofs

@[expose] public section


/-! The genuine grading on a quotient by a homogeneous ideal. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace KIP126.Algebra.GradedQuotient
noncomputable section
open DirectSum
variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommMonoid ι] [DecidableEq ι]
  (G : ι → Submodule R A) [GradedAlgebra G] (I : Ideal A)

/-- The quotient components form a direct sum, rather than only a family of spans. -/
@[implicit_reducible] def decomposition (hI : I.IsHomogeneous G) : DirectSum.Decomposition (part G I) :=
  DirectSum.Decomposition.ofAddHom (part G I) (quotientSplit G I hI) (by
    ext a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction a using DirectSum.Decomposition.inductionOn G with
    | zero => simp
    | homogeneous a =>
      rw [AddMonoidHom.comp_apply, quotientSplit_mk, split_of_mem G I a.property]
      simp only [DirectSum.lof_eq_of, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb) (by
    apply DirectSum.addHom_ext
    intro i a
    simpa only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
      AddMonoidHom.id_apply, DirectSum.lof_eq_of] using quotientSplit_of_mem G I hI a.property)

/-- Multiplication on the quotient respects the quotient grading. -/
@[implicit_reducible] def gradedAlgebra (hI : I.IsHomogeneous G) : GradedAlgebra (part G I) where
  toDecomposition := decomposition G I hI
  one_mem := ⟨1, SetLike.one_mem_graded G, map_one (Ideal.Quotient.mkₐ R I)⟩
  mul_mem := by
    intro i j a b ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x * y, SetLike.mul_mem_graded hx hy, map_mul (Ideal.Quotient.mkₐ R I) x y⟩

end
end KIP126.Algebra.GradedQuotient
