module

public import KIP126.Def.ClassicalAdams.Detection.Convergence.Data
public import KIP126.Def.SpectralSequence.Computation.Predicates

@[expose] public section

namespace KIP126.Classical.Adams.TowerDetection
open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : 𝟙_ C ⟶ H} {X : C}

def Detects (c : Convergence unit X) (p : ℤ × ℤ)
    (x : (adamsTowerInternalSpectralSequence unit X).Page 2 p)
    (α : HomotopyGroup (p.2 - p.1) X) : Prop :=
  let D := (adamsTowerInternalSpectralSequence unit X).ssData p
  ∃ z : (Subobject.underlying.obj (D.Z ⊤) : ModuleCat ℤ),
    (Subobject.ofLE _ _ (D.Z_anti le_top) ≫ D.pageπ 0) z = x ∧
    ∃ a : (Subobject.underlying.obj ((filtration unit X).F p.1 (p.2 - p.1)) : ModuleCat ℤ),
      ((filtration unit X).F p.1 (p.2 - p.1)).arrow a = α ∧
      (c.identification p).hom (D.pageπ ⊤ z) =
        (filtration unit X).toAssociatedGraded p.1 (p.2 - p.1) a

/-- The residual tower condition needed in a Moss input. No tower stages
or restriction maps are supplied separately. This is a predicate, not an
assumption silently added to the mathematical model. -/
def ResidualInjectivity (unit : 𝟙_ C ⟶ H) (X : C) : Prop :=
  ∀ (s : ℕ) (n : ℤ) (f : HomotopyGroup n (adamsTower unit X (s + 1))),
    (∀ (t : ℕ) (hst : s + 1 ≤ t),
      ∃ g : HomotopyGroup n (adamsTower unit X t),
        g ≫ adamsTowerMap unit X (s + 1) t hst = f) →
    f ≫ adamsTowerMap unit X s (s + 1) (Nat.le_succ s) = 0 → f = 0
end KIP126.Classical.Adams.TowerDetection
