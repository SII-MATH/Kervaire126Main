module

public import KIP126.Def.StableHomotopy.Spectra.Completion

@[expose] public section

/-! The existence of the HF₂-local reflection on the specified prespectrum
category, taken as a literature hypothesis. The chosen functor retains its
actual unit and universal property; its construction is not proved here. -/
namespace KIP126.StableHomotopy.Spectra

open CategoryTheory

/-- Existence of an HF₂-local reflection with the specified point-set unit
and universal property. Source: the standard HF₂ localization background
recorded under Ravenel in the source inventory. -/
axiom completionModel_exists : Nonempty CompletionModel

/-- The one reflection selected from the external existence hypothesis. -/
noncomputable def completionModel : CompletionModel := Classical.choice completionModel_exists

end KIP126.StableHomotopy.Spectra
