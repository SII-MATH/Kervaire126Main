module

public import KIP126.Def.AdamsSynthetic.AlgebraRealization.Data
public import KIP126.Literature.Standard.SyntheticComparison

@[expose] public section

/-! Assumed algebra and realization comparisons for the standard synthetic
Adams context. These identify the designated quotient algebras and their
units, specify the realization and weight comparisons, and fix the tensor
boundary conventions used in May's theorem. All comparisons concern the
already selected objects, algebras and functors.

The following axiom records these structural properties; external theorems
and computed Adams differentials remain separate hypotheses. -/

namespace KIP126.AdamsSynthetic

/-- The algebra, realization, weight and tensor boundary comparisons on
the standard Adams/synthetic context, assumed together on the same objects. -/
axiom standardAdamsSyntheticComparisons :
    KIP126.AdamsSynthetic.AlgebraRealizationComparison KIP126.Classical.Adams.standardAdamsComparison

end KIP126.AdamsSynthetic
