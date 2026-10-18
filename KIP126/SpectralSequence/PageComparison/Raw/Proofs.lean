module

import all KIP126.SpectralSequence.PageComparison.Raw.Data

@[expose] section

/-! Commuting squares for the actual centered page comparisons. -/

namespace KIP126.Core.SpectralSequence.PagewiseIso

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
  {E F : KIP126.Core.SpectralSequence C ι} (Q : PagewiseIso E F)

/-- The left square is the specified differential square after transporting
the left and middle indices by the common differential degree. -/
theorem left_middle_comm (r : ℤ) (hr : E.r₀ ≤ r) (k : ι) :
    (Q.leftIso r hr k).hom ≫ (F.pageShortComplex r (k - F.diffDeg r)).f =
      (E.pageShortComplex r (k - E.diffDeg r)).f ≫ (Q.middleIso r hr k).hom := by
  simp only [leftIso, middleIso, KIP126.Core.SpectralSequence.pageShortComplex,
    Iso.trans_hom, eqToIso.hom]
  have hleft : k - E.diffDeg r = k - F.diffDeg r := by
    rw [Q.diffDeg_eq]
  rw [Category.assoc,
    ← eqToHom_naturality (fun j => F.d r j) hleft,
    ← Category.assoc, Q.comm_d r hr (k - E.diffDeg r)]
  simp [Category.assoc, Q.diffDeg_eq]

/-- The right square is the same differential compatibility at the middle
index, with the specified degree transports. -/
theorem middle_right_comm (r : ℤ) (hr : E.r₀ ≤ r) (k : ι) :
    (Q.middleIso r hr k).hom ≫ (F.pageShortComplex r (k - F.diffDeg r)).g =
      (E.pageShortComplex r (k - E.diffDeg r)).g ≫ (Q.rightIso r hr k).hom := by
  simp only [middleIso, rightIso, KIP126.Core.SpectralSequence.pageShortComplex,
    Iso.trans_hom, eqToIso.hom]
  have hmiddle : k - E.diffDeg r + E.diffDeg r =
      k - F.diffDeg r + F.diffDeg r := by simp
  rw [Category.assoc,
    ← eqToHom_naturality (fun j => F.d r j) hmiddle,
    ← Category.assoc, Q.comm_d r hr (k - E.diffDeg r + E.diffDeg r)]
  simp [Category.assoc, Q.diffDeg_eq]

end KIP126.Core.SpectralSequence.PagewiseIso
