module

import all KIP126.Def.SpectralSequence.PageComparison.Raw.Proofs
public import Mathlib.Algebra.Homology.ShortComplex.Homology

@[expose] section

/-!
# The induced centered-complex and homology isomorphisms

Both maps are constructed from the supplied page isomorphisms and their
differential compatibility.  A comparison supplies no additional homology
map and no ambient-object map.
-/

namespace KIP126.Core.SpectralSequence.PagewiseIso

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
  {E F : KIP126.Core.SpectralSequence C ι} (Q : PagewiseIso E F)

/-- The centered short-complex isomorphism assembled from the very same
page maps and the two differential squares. -/
noncomputable def shortComplexIso (r : ℤ) (hr : E.r₀ ≤ r) (k : ι) :
    E.pageShortComplex r (k - E.diffDeg r) ≅
      F.pageShortComplex r (k - F.diffDeg r) :=
  ShortComplex.isoMk (Q.leftIso r hr k) (Q.middleIso r hr k)
    (Q.rightIso r hr k) (Q.left_middle_comm r hr k) (Q.middle_right_comm r hr k)

/-- The actual map induced on homology by the centered-complex comparison. -/
noncomputable def homologyIso (r : ℤ) (hr : E.r₀ ≤ r) (k : ι) :
    (E.pageShortComplex r (k - E.diffDeg r)).homology ≅
      (F.pageShortComplex r (k - F.diffDeg r)).homology :=
  ShortComplex.homologyMapIso (Q.shortComplexIso r hr k)

end KIP126.Core.SpectralSequence.PagewiseIso
