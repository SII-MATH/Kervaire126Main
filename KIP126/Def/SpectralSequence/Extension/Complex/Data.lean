module

public import KIP126.Def.SpectralSequence.Extension.Proofs

@[expose] public section

/-!
# The canonical two-term complex
-/

namespace KIP126.SpectralSequence.BoundedExtension

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [CategoryTheory.Category.{v} C] [Abelian C]

/-- The canonical chain complex carried by a two-term differential. -/
noncomputable def twoTermComplex (X₁ X₂ : C) (f : X₁ ⟶ X₂) : ChainComplex C ℤ :=
  ChainComplex.of
    (twoTermObj X₁ X₂)
    (fun k => twoTermDiff X₁ X₂ f (k + 1) ≫
      eqToHom (congrArg (twoTermObj X₁ X₂) (by omega : (k + 1) - 1 = k)))
    (fun k => by
      exact twoTermDiff_sq_transport X₁ X₂ f (k + 1 + 1) (k + 1) k
        (by omega) (by omega))

end KIP126.SpectralSequence.BoundedExtension
