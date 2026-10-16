module

import all KIP126.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs

@[expose] section

namespace KIP126.Core.SpectralSequence.BoundedExtension
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The degreewise map of two-term complexes determined by a square. -/
noncomputable def twoTermMap {X₁ X₂ Y₁ Y₂ : C}
    (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂) (k : ℤ) :
    twoTermObj X₁ X₂ k ⟶ twoTermObj Y₁ Y₂ k :=
  if h : k = 1 then
    eqToHom (by simp [twoTermObj, h]) ≫ a ≫ eqToHom (by simp [twoTermObj, h])
  else if h : k = 0 then
    eqToHom (by simp [twoTermObj, h]) ≫ b ≫ eqToHom (by simp [twoTermObj, h])
  else 0

end KIP126.Core.SpectralSequence.BoundedExtension
