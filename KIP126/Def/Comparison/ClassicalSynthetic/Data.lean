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

structure ReindexedSpectralSequenceMap
    (classical : InternalClassicalSequence.{v}) (synthetic : SyntheticAdamsSS.{v}) where
  firstPage : classical.r₀ = 2
  differentialDegree : ∀ r : ℤ, classical.diffDeg r = (r, r - 1)
  ambient : ∀ w : ℤ, SSDataMorphism Bidegree classical.ssData
    (fun b => synthetic.sequence.ssData (b.1, b.2, w))
  comm_d : ∀ (w r : ℤ) (b : Bidegree),
    (ambient w).pageMap b (↑(r - 2).toNat : WithTop ℕ) ≫
        fixedWeightDifferential synthetic w r b =
      classicalDifferential classical firstPage differentialDegree r b ≫
        (ambient w).pageMap (b + (r, r - 1)) (↑(r - 2).toNat : WithTop ℕ)

def sourcePageMap
    {classical : InternalClassicalSequence.{v}} {synthetic : SyntheticAdamsSS.{v}}
    (comparison : ReindexedSpectralSequenceMap classical synthetic)
    (w r : ℤ) (b : Bidegree) :
    classicalPage classical r b ⟶ fixedWeightPage synthetic w r b :=
  (comparison.ambient w).pageMap b (↑(r - 2).toNat : WithTop ℕ)

/-- The E∞ map is induced by exactly the same ambient map as the finite pages. -/
def sourceEInftyMap
    {classical : InternalClassicalSequence.{v}} {synthetic : SyntheticAdamsSS.{v}}
    (comparison : ReindexedSpectralSequenceMap classical synthetic)
    (w : ℤ) (b : Bidegree) :
    (classical.ssData b).eInfty ⟶
      (synthetic.sequence.ssData (b.1, b.2, w)).eInfty :=
  (comparison.ambient w).pageMap b ⊤

abbrev classicalH₄Degree : Bidegree := (1, 16)
abbrev classicalH₀H₃SquaredDegree : Bidegree := (3, 17)
abbrev syntheticH₄Degree : Tridegree := nuDegree classicalH₄Degree
abbrev syntheticH₀H₃SquaredDegree : Tridegree :=
  nuDegree classicalH₀H₃SquaredDegree
abbrev syntheticH₄TargetDegree : Tridegree :=
  lambdaTarget syntheticH₀H₃SquaredDegree

end
end KIP126.Comparison.ClassicalSynthetic
