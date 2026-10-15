module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Replacement.Cubical.Order.Model.Comparison
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Replacement.Cubical.WellBased.Proofs
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Replacement.Cubical.CompactlyGenerated.Proofs
public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.HomotopyEquivalence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory
open KIP126.Topology.SimplicialRealization

universe u

/-- The specified original replacement comparison has a based inverse, with
both actual homotopies fixed at the specified original basepoints. -/
theorem cubicalReplacementRealizedComparison_based_inverse (X : Prespectrum.{u}) (n : ℕ) :
    ∃ g : (cubicalReplacementFunctor.obj X).level n ⟶ cubicalReplacementRealizedModel X n,
      (g.map.comp (cubicalReplacementBasedRealizedComparison X n).map).HomotopicRel
        (ContinuousMap.id _) {(cubicalReplacementRealizedModel X n).point} ∧
      ((cubicalReplacementBasedRealizedComparison X n).map.comp g.map).HomotopicRel
        (ContinuousMap.id _) {((cubicalReplacementFunctor.obj X).level n).point} := by
  obtain ⟨e, he⟩ := cubicalReplacementRealizedComparison_homotopyEquiv X n
  exact BasedSpace.exists_based_inverse_of_homotopyEquiv
    (cubicalReplacementRealizedModel_isGood X n).2.1
    (cubicalReplacementFunctor_level_wellBased X n)
    (cubicalReplacementBasedRealizedComparison X n) e he

/-- Every original cubical replacement level has actual based CW type.
The model is its specified simplicial realization and the comparison is the
original stage-induced map, with both homotopies relative to the basepoint. -/
theorem cubicalReplacementFunctor_level_hasCWType (X : Prespectrum.{u}) (n : ℕ) :
    ((cubicalReplacementFunctor.obj X).level n).HasCWType := by
  obtain ⟨g, hL, hR⟩ := cubicalReplacementRealizedComparison_based_inverse X n
  exact ⟨cubicalReplacementRealizedModel X n,
    realization_t2Space (cubicalReplacementSimplicialModel X n),
    realization_nonempty_classicalCWComplex (cubicalReplacementSimplicialModel X n),
    (cubicalReplacementRealizedModel_isGood X n).2.1,
    g, cubicalReplacementBasedRealizedComparison X n, hR, hL⟩

/-- The actual cubical replacement has compactly generated, well-based
levels of based CW homotopy type, with no hypothesis on its input. -/
theorem cubicalReplacementFunctor_level_isGood (X : Prespectrum.{u}) (n : ℕ) :
    ((cubicalReplacementFunctor.obj X).level n).IsGood :=
  ⟨inferInstance, cubicalReplacementFunctor_level_wellBased X n,
    cubicalReplacementFunctor_level_hasCWType X n⟩

end KIP126.StableHomotopy.Spectra.Prespectrum
