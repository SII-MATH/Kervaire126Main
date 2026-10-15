module

public import KIP126.Main.AdamsSynthetic.Context
import KIP126.Main.AdamsSynthetic.Toda.Product
import KIP126.Main.AdamsSynthetic.Toda.Low
import KIP126.Main.AdamsSynthetic.Toda.Symmetric

@[expose] public section

namespace KIP126.Main.AdamsSynthetic

open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Literature.AdamsSynthetic in
@[no_expose]
noncomputable def todaSecondaryComparison :
    KIP126.Literature.AdamsSynthetic.TodaSecondaryComparison etaClass
      literature.sources.sourceComparisons.todaSource := by
  let twoStar : BiHom 1 0 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn) :=
    lambdaMultiply 2 etaClass
  have hstar : ∀ θ : BiHom 62 64 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn),
      sphereProduct twoStar θ = lambdaMultiply 2 (sphereProduct etaClass θ) := by
    intro θ
    exact Toda.secondary_star_product adamsComparison etaClass θ
  exact {
    low_bracket := Toda.low_bracket
    twoStar := twoStar
    symmetric := by
      intro θ hθ
      rw [hstar θ]
      exact Toda.symmetric_bracket θ hθ
    star_product := hstar }

end KIP126.Main.AdamsSynthetic
