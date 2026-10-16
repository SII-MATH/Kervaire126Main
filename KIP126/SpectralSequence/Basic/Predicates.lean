module

public import KIP126.SpectralSequence.Basic.Data
import all KIP126.SpectralSequence.Basic.Data

@[expose] section

/-!
# Predicates for nested-subobject spectral sequences
-/

namespace KIP126.Core.SpectralSequence

universe u v w

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A spectral sequence degenerates at `N` when all differentials from page `N` vanish. -/
public def DegeneratesAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (N : ℤ) : Prop :=
  ∀ (r : ℤ), N ≤ r → ∀ (k : ι), E.d r k = 0

end KIP126.Core.SpectralSequence
