module

public import KIP126.Def.ClassicalAdams.Completion.Predicates
public import KIP126.Def.ClassicalAdams.Convergence.Tower.Predicates

@[expose] public section

/-! Applicability of the untruncated BHS theorem, on the actual classical
Adams tower. These are explicit completeness and convergence hypotheses,
separate from the structural data of an Adams comparison. An associated-graded
identification alone does not establish them.

BHS, SynRevBigraded.tex, Theorem A.1 and definitions preceding it;
SynRevAdams.tex, cor:tau-surj and proof of A.1(2)--(4).
The finite Cτ^q assertions have a more general proof (lemm:comp1), and are
intentionally not made conditional on this record. -/
namespace KIP126.Classical.Adams
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C}

/-- The choice of products is an explicit parameter of the nilpotent-completeness
hypothesis, fixing the products used to form the inverse limit. -/
structure BHSObjectApplicability (products : HasProductsOfShape ℕ C)
    (unit : 𝟙_ C ⟶ H) (X : C) : Prop where
  nilpotent_complete : letI := products; IsENilpotentComplete unit X
  strongly_convergent : IsAdamsTowerStronglyConvergent unit X

end KIP126.Classical.Adams
