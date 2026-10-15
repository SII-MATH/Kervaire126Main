module

public import KIP126.Def.ClassicalAdams.MapFiltration.Data
public import KIP126.Def.StableHomotopy.Cohomology.Data

@[expose] public section

/-!
# Adams filtration of a map

The lower bound is a factorization through the target's constructed Adams
tower. It does not select an arbitrary filtration integer and does not use
spectral-sequence pages or survival predicates.
-/

namespace KIP126.StableHomotopy

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- Every morphism in the finite chain satisfies the specified condition. -/
def FiniteMorphismChain.All (P : ∀ {X Y : C}, (X ⟶ Y) → Prop)
    {X Y : C} {k : ℕ} (chain : FiniteMorphismChain X Y k) : Prop :=
  match chain with
  | .nil _ => True
  | .cons f tail => P f ∧ tail.All P

end KIP126.StableHomotopy

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- The actual homology homomorphism vanishes in every degree. -/
def IsZeroOnMod2Homology (H : Mod2EilenbergMacLane (C := C))
    {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ n : ℤ, Mod2Homology.pushforward H f n = 0

/-- A factorization into exactly `k` actual mod-two-homology-zero maps.
For `k = 0` this requires an empty chain, hence an identity; the Adams
filtration decomposition theorem is consequently stated for positive `k`. -/
def HasMod2ZeroFactorization (H : Mod2EilenbergMacLane (C := C))
    {X Y : C} (f : X ⟶ Y) (k : ℕ) : Prop :=
  ∃ chain : FiniteMorphismChain X Y k,
    chain.composite = f ∧ chain.All (IsZeroOnMod2Homology H)

end KIP126.StableHomotopy.Cohomology

namespace KIP126.Classical.Adams

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- A map has Adams filtration at least `k` when it factors through stage
`k` of the actual target Adams tower for the specified mod-2 unit. -/
def AdamsFiltrationAtLeast (H : Mod2EilenbergMacLane (C := C))
    {X Y : C} (f : X ⟶ Y) (k : ℕ) : Prop :=
  ∃ lift : X ⟶ adamsTower H.unit Y k,
    lift ≫ adamsTowerMap H.unit Y 0 k (Nat.zero_le k) = f

end KIP126.Classical.Adams
