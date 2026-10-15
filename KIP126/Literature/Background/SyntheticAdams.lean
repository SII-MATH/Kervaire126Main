module

public import KIP126.Literature.Standard.SyntheticContext

@[expose] public section

/-! The assumed standard synthetic Adams context over the fixed classical
HF₂-local stable category.

The intended source is the hypercomplete category of spherical sheaves of
spectra on the finite HF₂-projective ∞-site. Its synthetic analogue ν, λ,
Adams tower, λ-inversion recovery, detector and comparisons must all come
from that construction over the same fixed HF₂-local classical category.
This declaration assumes the synthetic category and its structural
comparisons. External literature and computation conclusions are stated
separately about these same objects.
-/
namespace KIP126.AdamsSynthetic

/-- The standard Pstrągowski synthetic context over the fixed HF₂ Adams
context, including the structural properties of `SyntheticAdamsContext.adamsComparison`.
Its existence is assumed here. -/
axiom standardSyntheticContext : KIP126.Classical.Adams.StandardSyntheticContext

end KIP126.AdamsSynthetic
