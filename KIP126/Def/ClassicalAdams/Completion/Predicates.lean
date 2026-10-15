module

public import KIP126.Def.ClassicalAdams.Completion.Data
public import KIP126.Def.StableHomotopy.InverseSequence.Predicates

@[expose] public section

namespace KIP126.Classical.Adams

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]

/-- `E`-nilpotent completeness means vanishing of the actual residual
Adams tower's homotopy limit. For the mod-two statement, `unit` is the
specified unit of the same `H𝔽₂` datum. It is neither an arbitrary
completeness proposition nor an assumption of strong SS convergence.

Source: BHS `SynRevBigraded.tex`, definition `dfn:E-complete`, and
`SynRevAdams.tex`, proof of `lemm:easy-e-compton`.
-/
def IsENilpotentComplete {H : C} (unit : 𝟙_ C ⟶ H) (X : C) : Prop :=
  (adamsResidualSequence unit X).IsAcyclic

end KIP126.Classical.Adams
