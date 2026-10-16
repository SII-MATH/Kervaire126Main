module
public import KIP126.Literature.EInfinity
/-! Definitional quotient operations used in the migrated finite-coordinate proofs.
These expose no new mathematical input. -/
@[expose] section
namespace KIP126.Main.Internal
open KIP126.Literature
universe u v
variable {R : Type u} [Ring R] {A : Type v} [AddCommGroup A] [Module R A]
theorem subquotientClass_eq_zero_iff (Z B : Submodule R A) (z : Z) :
    subquotientClass Z B z = 0 ↔ z.val ∈ B := by
  exact Submodule.Quotient.mk_eq_zero (B.comap Z.subtype)
end KIP126.Main.Internal
