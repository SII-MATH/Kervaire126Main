module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Simplicial.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Classical.Charts.Proofs
public import KIP126.Def.StableHomotopy.Spectra.HF2.Topology.Proofs
public import KIP126.Def.StableHomotopy.Spectra.Generators

@[expose] public section

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open KIP126.Topology.SimplicialRealization

/-- The actual Dold--Kan coefficient-space realization is Hausdorff. -/
theorem hf2Realization_t2Space (n : ℕ) : T2Space (hf2RealizationLevel n) :=
  realization_t2Space (hf2SimplicialSet n)

/-- The fixed coefficient level has the classical characteristic-cell CW
structure required by the actual source-space predicates. -/
theorem hf2Realization_nonempty_classicalCWComplex (n : ℕ) :
    Nonempty (_root_.Topology.CWComplex (Set.univ : Set (hf2RealizationLevel n))) :=
  realization_nonempty_classicalCWComplex (hf2SimplicialSet n)

/-- The actual coefficient level has based CW homotopy type, using its
own proved CW structure and the identity based homotopy equivalence. -/
theorem hf2RealizationLevel_hasCWType (n : ℕ) :
    (hf2RealizationLevel n).HasCWType := by
  refine ⟨hf2RealizationLevel n,hf2Realization_t2Space n,
    hf2Realization_nonempty_classicalCWComplex n,hf2RealizationLevel_isWellBased n,
    𝟙 _,𝟙 _,?_,?_⟩
  all_goals exact ContinuousMap.HomotopicRel.refl _

/-- All three actual good-space obligations for the Dold--Kan coefficient
levels now follow from their concrete realization topology and cells. -/
theorem hf2RealizationLevel_isGood (n : ℕ) :
    (hf2RealizationLevel n).IsGood :=
  ⟨hf2RealizationLevel_uCompactlyGeneratedSpace n,hf2RealizationLevel_isWellBased n,
    hf2RealizationLevel_hasCWType n⟩

end KIP126.StableHomotopy.Spectra
