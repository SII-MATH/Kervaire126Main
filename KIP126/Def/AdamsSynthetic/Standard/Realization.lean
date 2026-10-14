module

public import KIP126.Def.AdamsSynthetic.Standard.Background
public import KIP126.Def.AdamsSynthetic.Realization

/-! Fixed point-set realizations. These are mathematical model constructions,
not a package of downstream conclusions. Their construction remains deferred;
the localization comparisons below are derived from the specified models. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory KIP126.StableHomotopy HomotopicalAlgebra
noncomputable section

/-- The chosen cofibrantly generated monoidal model of classical spectra. -/
public def spectrumRealization : SpectrumModelRealization.{1,0,1,0} Spectrum := by sorry

/-- A stable point-set realization of the same fixed synthetic category. -/
public def syntheticRealization : SyntheticModelRealization.{1,0,1,0} SyntheticSpectrum := by sorry

public def spectrumHomotopyEquivalence :
    letI := spectrumRealization.pointSetCategory
    letI := spectrumRealization.pointSetModel
    (weakEquivalences spectrumRealization.PointSet).Localization ≌ Spectrum :=
  spectrumRealization.toStableModelRealization.homotopyEquivalence

public def spectrumLocalizationComparison :
    letI := spectrumRealization.pointSetCategory
    letI := spectrumRealization.pointSetModel
    (weakEquivalences spectrumRealization.PointSet).Q ⋙
      spectrumHomotopyEquivalence.functor ≅ spectrumRealization.localization :=
  spectrumRealization.toStableModelRealization.localizationComparison

public def syntheticHomotopyEquivalence :
    letI := syntheticRealization.pointSetCategory
    letI := syntheticRealization.pointSetModel
    (weakEquivalences syntheticRealization.PointSet).Localization ≌ SyntheticSpectrum :=
  syntheticRealization.homotopyEquivalence

public def syntheticLocalizationComparison :
    letI := syntheticRealization.pointSetCategory
    letI := syntheticRealization.pointSetModel
    (weakEquivalences syntheticRealization.PointSet).Q ⋙
      syntheticHomotopyEquivalence.functor ≅ syntheticRealization.localization :=
  syntheticRealization.localizationComparison

end
end KIP126.AdamsSynthetic.Standard
