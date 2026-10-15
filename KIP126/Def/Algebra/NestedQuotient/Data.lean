module

public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

namespace KIP126.Algebra.NestedQuotient

universe u v
variable {R : Type u} [Ring R] {A : Type v} [AddCommGroup A] [Module R A]

/-- The quotient of a submodule by its intersection with another submodule.
In cycle/boundary applications the latter is already contained in the former. -/
abbrev Space (Z B : Submodule R A) := Z ⧸ B.comap Z.subtype

/-- The same ambient representative, viewed in the subquotient. -/
def projection (Z B : Submodule R A) : Z →ₗ[R] Space Z B :=
  (B.comap Z.subtype).mkQ

/-- Inclusion of cycle submodules and enlargement of boundary submodules
induce a specified linear map, with no choice of representatives. -/
def map {Z Z' B B' : Submodule R A} (hZ : Z ≤ Z') (hB : B ≤ B') :
    Space Z B →ₗ[R] Space Z' B' :=
  (B.comap Z.subtype).mapQ (B'.comap Z'.subtype)
    (Submodule.inclusion hZ) (fun _ hx => hB hx)

end KIP126.Algebra.NestedQuotient
