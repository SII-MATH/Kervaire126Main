module

public import KIP126.Def.SpectralSequence.Basic.Data
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section

namespace KIP126.Classical.Adams

/-- An Adams spectral sequence starting on page 2 with differential degree
`(r, r - 1)`. Its identification with a specified spectrum's Adams tower and
with computational coordinates requires separate comparisons; permanence is
not asserted by this structure. -/
structure AdamsSSData where
  sequence : KIP126.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ)
  firstPage : sequence.r₀ = 2
  differentialDegree : ∀ r, sequence.diffDeg r = (r, r - 1)

end KIP126.Classical.Adams
