module

public import KIP126.Def.Synthetic.AdamsSequence.Data

@[expose] public section

/-!
# Internal classical--synthetic regrading

Both endpoints use the internal nested-subobject model. The maps on every
page, including E∞, are induced by the displayed ambient maps. This is the
precise comparison datum; no comparison to Mathlib spectral sequences is
introduced. Identification of its sequences with a selected classical Adams
tower and the ν/quotient objects of one `SyntheticAdamsFamily` requires a
separate comparison.
-/

namespace KIP126.Comparison.ClassicalSynthetic

open CategoryTheory
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.SpectralSequence

universe v
noncomputable section

abbrev InternalClassicalSequence :=
  KIP126.SpectralSequence (ModuleCat.{v} ℤ) Bidegree

def classicalPage (E : InternalClassicalSequence.{v}) (r : ℤ) (b : Bidegree) :
    ModuleCat.{v} ℤ := (E.ssData b).page (↑(r - 2).toNat : WithTop ℕ)

/-- The actual source differential, normalized only by its Adams convention. -/
def classicalDifferential (E : InternalClassicalSequence.{v})
    (firstPage : E.r₀ = 2) (degree : ∀ r : ℤ, E.diffDeg r = (r, r - 1))
    (r : ℤ) (b : Bidegree) :
    classicalPage E r b ⟶ classicalPage E r (b + (r, r - 1)) :=
  eqToHom (by simp only [classicalPage, firstPage]) ≫
    E.d r b ≫ eqToHom (by
      simp only [classicalPage, firstPage, degree])

end
end KIP126.Comparison.ClassicalSynthetic
