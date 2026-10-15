module

public import KIP126.Def.ClassicalAdams.Tower.Data

@[expose] public section

/-! Finite chains of actual morphisms, including their composite. -/

namespace KIP126.StableHomotopy

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- A chain of exactly `k` composable morphisms with specified endpoints.
The empty chain exists only when its endpoints agree. -/
inductive FiniteMorphismChain : C → C → ℕ → Type (max u v)
  | nil (X : C) : FiniteMorphismChain X X 0
  | cons {X Y Z : C} {k : ℕ} (f : X ⟶ Y)
      (tail : FiniteMorphismChain Y Z k) : FiniteMorphismChain X Z (k + 1)

/-- Compose a finite chain in its specified order. -/
def FiniteMorphismChain.composite {X Y : C} {k : ℕ}
    (chain : FiniteMorphismChain X Y k) : X ⟶ Y :=
  match chain with
  | .nil X => 𝟙 X
  | .cons f tail => f ≫ tail.composite

end KIP126.StableHomotopy

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The actual successor maps from stage `k` down to stage zero. -/
def adamsTowerChain {H : C} (unit : 𝟙_ C ⟶ H) (Y : C) :
    (k : ℕ) → FiniteMorphismChain (adamsTower unit Y k) Y k
  | 0 => .nil Y
  | k + 1 => .cons (adamsTowerStep unit Y k) (adamsTowerChain unit Y k)

end KIP126.Classical.Adams
