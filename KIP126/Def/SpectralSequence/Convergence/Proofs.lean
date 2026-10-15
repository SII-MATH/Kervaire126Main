module

public import KIP126.Def.SpectralSequence.Convergence.Data
public import KIP126.Def.Algebra.Filtration.Data

@[expose] public section

/-!
# Proofs for convergence of nested-subobject spectral sequences
-/

namespace KIP126.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

@[simp]
theorem Filtration.transportGraded_self
    {ω' : Type w} {A : ω' → C} (F : Filtration A)
    {r : ℤ × ω'} (h : r = r) :
    F.transportGraded h = 𝟙 (F.associatedGraded r.1 r.2) :=
  rfl

end KIP126.SpectralSequence
