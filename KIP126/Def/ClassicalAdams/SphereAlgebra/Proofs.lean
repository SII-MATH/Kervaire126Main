module

public import KIP126.Def.ClassicalAdams.SphereAlgebra.Data
public import KIP126.Def.ClassicalAdams.SphereAlgebra.Components.Data

@[expose] public section

/-! Canonical inclusions and the distributive product on the specified E₂ direct sum. -/

namespace KIP126.Classical.Adams.Sphere.Algebra

open KIP126.Algebra
noncomputable section

variable {Q : KIP126.StableHomotopy.Spectra.CompletionModel} (c : KIP126.HF2AdamsContext Q)

attribute [local irreducible] ActualE2At actualE2AtModule actualE2Product

/-- Distinct actual classes of a fixed bidegree remain distinct in the direct sum. -/
theorem embed_injective (p : ℕ × ℕ) : Function.Injective ((embed c) p) :=
  DirectSum.of_injective (β := (ActualE2At c)) p

end
end KIP126.Classical.Adams.Sphere.Algebra
