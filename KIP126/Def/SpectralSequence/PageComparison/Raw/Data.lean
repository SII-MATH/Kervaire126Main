module

public import KIP126.Def.SpectralSequence.Basic.Data
import all KIP126.Def.SpectralSequence.Basic.Data

@[expose] section

/-!
# Page isomorphisms compatible with the actual differentials

Two nested-subobject models can have different ambient objects and still
describe isomorphic admissible pages.  This comparison therefore asks only
for page isomorphisms, a common displayed page convention, and commuting
differential squares.  It does not assert an ambient or cycle-subobject
isomorphism.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

/-- An isomorphism on each admissible page that commutes with the specified
differentials.  Successor-page compatibility is stated separately using the
homology map induced by these same isomorphisms. -/
structure PagewiseIso (E F : KIP126.Core.SpectralSequence C ι) where
  firstPage_eq : E.r₀ = F.r₀
  diffDeg_eq : E.diffDeg = F.diffDeg
  pageIso : ∀ (r : ℤ), E.r₀ ≤ r → ∀ k : ι, E.Page r k ≅ F.Page r k
  comm_d : ∀ (r : ℤ) (hr : E.r₀ ≤ r) (k : ι),
    (pageIso r hr k).hom ≫ F.d r k =
      E.d r k ≫ (pageIso r hr (k + E.diffDeg r)).hom ≫
        eqToHom (by rw [diffDeg_eq])

namespace PagewiseIso

variable {E F : KIP126.Core.SpectralSequence C ι} (Q : PagewiseIso E F)

/-- The actual comparison at the left vertex of the short complex centered
at `k`, including the change of displayed differential degree. -/
noncomputable def leftIso (r : ℤ) (hr : E.r₀ ≤ r) (k : ι) :
    (E.pageShortComplex r (k - E.diffDeg r)).X₁ ≅
      (F.pageShortComplex r (k - F.diffDeg r)).X₁ :=
  Q.pageIso r hr (k - E.diffDeg r) ≪≫ eqToIso (by
    change F.Page r (k - E.diffDeg r) = F.Page r (k - F.diffDeg r)
    rw [Q.diffDeg_eq])

/-- The actual comparison at the middle vertex of the centered short complex.
The displayed indices retain the same explicit transports as `pageShortComplex`. -/
noncomputable def middleIso (r : ℤ) (hr : E.r₀ ≤ r) (k : ι) :
    (E.pageShortComplex r (k - E.diffDeg r)).X₂ ≅
      (F.pageShortComplex r (k - F.diffDeg r)).X₂ :=
  Q.pageIso r hr (k - E.diffDeg r + E.diffDeg r) ≪≫
    eqToIso (by
      change F.Page r (k - E.diffDeg r + E.diffDeg r) =
        F.Page r (k - F.diffDeg r + F.diffDeg r)
      rw [Q.diffDeg_eq])

/-- The actual comparison at the right vertex of the centered short complex. -/
noncomputable def rightIso (r : ℤ) (hr : E.r₀ ≤ r) (k : ι) :
    (E.pageShortComplex r (k - E.diffDeg r)).X₃ ≅
      (F.pageShortComplex r (k - F.diffDeg r)).X₃ :=
  Q.pageIso r hr (k - E.diffDeg r + E.diffDeg r + E.diffDeg r) ≪≫
    eqToIso (by
      change F.Page r (k - E.diffDeg r + E.diffDeg r + E.diffDeg r) =
        F.Page r (k - F.diffDeg r + F.diffDeg r + F.diffDeg r)
      rw [Q.diffDeg_eq])

end PagewiseIso
end KIP126.Core.SpectralSequence
