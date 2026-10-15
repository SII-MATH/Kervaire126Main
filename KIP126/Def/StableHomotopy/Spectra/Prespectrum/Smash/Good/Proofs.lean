module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Smash.Good.Predicates
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Replacement.Cubical.Good.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra
open CategoryTheory _root_.Topology
open scoped unitInterval
namespace Prespectrum

theorem IsGood.wellBased {X : Prespectrum.{0}} (hX : X.IsGood) : X.IsWellBased :=
  fun n => (hX n).2.1

/-- These objects cover the entire ordinary stable localization. -/
theorem goodReplacement (X : Prespectrum.{0}) :
    ∃ (Y : Prespectrum.{0}) (_ : Y.IsGood) (q : Y ⟶ X), stableEquivalences q := by
  exact ⟨cubicalReplacementFunctor.obj X, cubicalReplacementFunctor_level_isGood X,
    cubicalReplacementComparison.app X, cubicalReplacementComparison_stableEquivalence X⟩

end Prespectrum
end KIP126.StableHomotopy.Spectra
