module

public import KIP126.SpectralSequence.Internal.Algebra.Filtration.Data
import all KIP126.SpectralSequence.Internal.Algebra.Filtration.Data

@[expose] section

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A filtration is bounded on both sides degreewise. -/
public structure Filtration.IsBounded
    {ω : Type w} {A : ω → C} (F : Filtration A) where
  /-- Lower bound. -/
  lo : ω → ℤ
  /-- Upper bound. -/
  hi : ω → ℤ
  /-- Bounds occur in the expected order. -/
  lo_le_hi : ∀ k, lo k ≤ hi k
  /-- The filtration is top below the lower bound. -/
  boundedBelow : ∀ (k : ω) (s : ℤ), s ≤ lo k → F.F s k = ⊤
  /-- The filtration is bottom above the upper bound. -/
  boundedAbove : ∀ (k : ω) (s : ℤ), hi k ≤ s → F.F s k = ⊥

/-- A filtration is bounded below degreewise. -/
public structure Filtration.IsBoundedBelow
    {ω : Type w} {A : ω → C} (F : Filtration A) where
  /-- Lower bound. -/
  lo : ω → ℤ
  /-- The filtration is top below the bound. -/
  boundedBelow : ∀ (k : ω) (s : ℤ), s ≤ lo k → F.F s k = ⊤

/-- A filtration is bounded above degreewise. -/
public structure Filtration.IsBoundedAbove
    {ω : Type w} {A : ω → C} (F : Filtration A) where
  /-- Upper bound. -/
  hi : ω → ℤ
  /-- The filtration is bottom above the bound. -/
  boundedAbove : ∀ (k : ω) (s : ℤ), hi k ≤ s → F.F s k = ⊥

/-- Every graded component is the whole object at some filtration level.
This is degreewise eventual top, stronger than exhaustiveness expressed only
by a union or colimit of the filtration levels. -/
public def Filtration.IsExhaustive
    {ω : Type w} {A : ω → C} (F : Filtration A) : Prop :=
  ∀ (k : ω), ∃ (s : ℤ), F.F s k = ⊤

/-- Degreewise Hausdorffness: the intersection of the filtration levels is
zero, expressed by its subobject universal property. No finite level is
required to vanish. -/
public def Filtration.IsHausdorff
    {ω : Type w} {A : ω → C} (F : Filtration A) : Prop :=
  ∀ (k : ω) (S : Subobject (A k)), (∀ s : ℤ, S ≤ F.F s k) → S = ⊥

namespace Filtration

variable {ι : Type w} {A : CategoryTheory.GradedObject ι C}

/-- A filtration is degreewise eventually bottom: every component vanishes at
some filtration level.  Because the filtration is decreasing, it then vanishes
at every higher level.  This is stronger than separatedness, which asks only
for zero intersection. -/
def IsEventuallyZero (F : Filtration A) : Prop :=
  ∀ i : ι, ∃ s : ℤ, F.F s i = ⊥

/-! A Mittag-Leffler condition for the decreasing filtration.  The images of
deeper levels inside any fixed level must eventually stabilize. -/

/-- The filtration images `F^(s+n) ↪ F^s` stabilize degreewise. -/
def IsMittagLeffler (F : Filtration A) : Prop :=
  ∀ (i : ι) (s : ℤ), ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    imageSubobject (F.inclusion (t := s) (s := s + (n : ℤ)) (by omega) i) =
      imageSubobject (F.inclusion (t := s) (s := s + (N : ℤ)) (by omega) i)

end Filtration

end KIP126.Core.SpectralSequence
