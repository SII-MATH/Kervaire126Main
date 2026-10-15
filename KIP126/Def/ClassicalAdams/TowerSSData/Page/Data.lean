module

public import KIP126.Def.ClassicalAdams.TowerSSData.Data
public import KIP126.Def.ClassicalAdams.TowerRepresentatives.Proofs
public import KIP126.Def.SpectralSequence.ModuleQuotient.Data

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Internal stage `n` is isomorphic to the actual tower quotient at page `n+2`.
The isomorphism comes from the identity on first-page representatives. -/
def adamsTowerSSDataPageIso (s t : ℤ) (n : ℕ) :
    (adamsTowerSSData unit X s t).page (n : WithTop ℕ) ≅
      ModuleCat.of ℤ (adamsPage unit X (n + 2) (by omega) s t) :=
  submoduleCokernelIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
    (adamsFiniteBoundarySubmodule unit X s t n)
    (adamsFiniteCycleSubmodule unit X s t n)
    (adamsFiniteBoundarySubmodule_le_cycle unit X s t n n) ≪≫
  (Submodule.Quotient.equiv _ _ (adamsFiniteCycleEquiv unit X s t n)
    (adamsFiniteCycleEquiv_boundaries unit X s t n)).toModuleIso

end
end KIP126.Classical.Adams
