module

public import KIP126.Def.Algebra.Coefficients.Data
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section

/-!
# Exhaustion by zero and one specified vector

The F₂ singleton-span lemma is pure module theory. The transport and
identification lemmas hold over every semiring and preserve all variables;
no data catalogue, actual-model comparison or nonvanishing is supplied here.
-/
namespace KIP126.Algebra
universe u v
/-- Every vector in a singleton span over F₂ is zero or its spanning vector. -/
theorem eq_zero_or_of_span_singleton {V : Type u} [AddCommGroup V] [Module F2 V]
    (a x : V) (hx : x ∈ Submodule.span F2 ({a} : Set V)) : x = 0 ∨ x = a := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
  have h : ∀ r : F2, r = 0 ∨ r = 1 := by decide
  rcases h r with rfl | rfl
  · exact Or.inl (by simpa using hr.symm)
  · exact Or.inr (by simpa using hr.symm)
/-- A linear equivalence transports exhaustion by zero and one specified vector. -/
theorem LinearEquiv.zero_or_of_exhaustion {R : Type*} [Semiring R]
    {V : Type u} {W : Type v} [AddCommMonoid V] [AddCommMonoid W]
    [Module R V] [Module R W] (e : V ≃ₗ[R] W) (a : V)
    (ha : ∀ x : V, x = 0 ∨ x = a) (y : W) : y = 0 ∨ y = e a := by
  obtain ⟨x, rfl⟩ := e.surjective y
  rcases ha x with rfl | rfl
  · exact Or.inl (map_zero e)
  · exact Or.inr rfl
/-- Any independently specified nonzero vector equals the transported vector. -/
theorem LinearEquiv.image_eq_of_exhaustion {R : Type*} [Semiring R]
    {V : Type u} {W : Type v} [AddCommMonoid V] [AddCommMonoid W]
    [Module R V] [Module R W] (e : V ≃ₗ[R] W) (a : V)
    (ha : ∀ x : V, x = 0 ∨ x = a) (b : W) (hb : b ≠ 0) : e a = b := by
  exact ((zero_or_of_exhaustion e a ha b).resolve_left hb).symm
end KIP126.Algebra
