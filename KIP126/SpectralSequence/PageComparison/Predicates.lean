module

import all KIP126.SpectralSequence.PageComparison.Data
public import KIP126.SpectralSequence.Basic.PageHomology.Data
import all KIP126.SpectralSequence.Basic.PageHomology.Data

@[expose] section

/-!
# Successor compatibility of pagewise spectral-sequence comparisons

The successor square uses the canonical page-to-homology isomorphisms of
the nested-subobject model and the homology map already induced by the same
page comparison.  This is stronger than independent isomorphisms on each
page, while leaving the two ambient objects unconstrained.
-/

namespace KIP126.Core.SpectralSequence.PagewiseIso

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
  {E F : KIP126.Core.SpectralSequence C ι}

/-- The next-page isomorphism agrees with the isomorphism induced on the
homology of the preceding page's actual differential. -/
def RespectsSuccessor (Q : PagewiseIso E F) : Prop :=
  ∀ (r : ℤ) (hr : E.r₀ ≤ r) (k : ι),
    (pageHomologyIso E r k hr).hom ≫ (Q.homologyIso r hr k).hom =
      (Q.pageIso (r + 1) (by omega) k).hom ≫
        (pageHomologyIso F r k (by rw [← Q.firstPage_eq]; exact hr)).hom

end KIP126.Core.SpectralSequence.PagewiseIso
