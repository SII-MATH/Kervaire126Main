module

public import KIP126.Def.ClassicalAdams.Convergence.Tower.Data
public import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data
public import KIP126.Def.Algebra.Completion.Data

@[expose] public section

/-! Strong convergence for the actual tower and actual homotopy groups,
following BHS `SynRevBigraded.tex`, Definition `dfn:strong-conv`.
It requires completeness, Hausdorffness and associated-graded identification;
it does not require finite-page stabilization or eventual vanishing. -/

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Source-faithful strong convergence of this constructed Adams sequence.
The filtration, abutment and E∞ are fixed; witnesses assert properties of
them and do not select replacements. Completeness uses the canonical cone
to the filtration quotients. -/
structure IsAdamsTowerStronglyConvergent : Prop where
  complete : ∀ n : ℤ,
    Nonempty (Algebra.Filtration.CompletionWitness (adamsHomotopyFiltration unit X) n)
  separated : ∀ (n : ℤ) (S : Subobject (towerAbutment X n)),
    (∀ s : ℤ, S ≤ (adamsHomotopyFiltration unit X).F s n) → S = ⊥
  associatedGraded : ∀ (s t : ℤ),
    Nonempty (((adamsTowerInternalSpectralSequence unit X).ssData (s, t)).eInfty ≅
      (adamsHomotopyFiltration unit X).associatedGraded s (t - s))

end KIP126.Classical.Adams
