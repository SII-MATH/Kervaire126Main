module
import all KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.SectionSeven.Predicates
public import KIP126.Main.Conditions
import all KIP126.Main.SectionSeven.AnyYTarget
import all KIP126.Main.SectionSeven.WeakYDetection

/- Research only: each definition below records an unproved mathematical
proposition. Defining a Prop supplies no proof of it. No new assumption is
added to the project and this file is not a production dependency. -/
namespace MainPaperSectionSevenRemaining
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Main KIP126.Main.SectionSeven
open KIP126.Literature.Standard (eta syntheticH0)

def OneFilteredTodaMember : Prop :=
  ∀ (_hc3 : Stem126D6Vanishes) (_hc5 : EtaExtensionDetection)
    (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11)),
    AlphaOneProperties a11 →
    ∃ z : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      ModuleTripleToda (lambdaMultiply 3
        (a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide))) syntheticH0 eta z ∧
      FiltrationAtLeast model.syntheticTower 11 z

def AllTodaDifferencesInFiltrationEleven : Prop :=
  ∀ (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11)),
    AlphaOneProperties a11 →
    ∀ z z0 : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      ModuleTripleToda (lambdaMultiply 3
        (a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide))) syntheticH0 eta z →
      ModuleTripleToda (lambdaMultiply 3
        (a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide))) syntheticH0 eta z0 →
      FiltrationAtLeast model.syntheticTower 11 (z-z0)

def EveryTodaMemberDetectedByY : Prop :=
  ∀ (_hc3 : Stem126D6Vanishes) (_hc5 : EtaExtensionDetection)
    (a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11)),
    AlphaOneProperties a11 →
    ∀ z : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      ModuleTripleToda (lambdaMultiply 3
        (a11 ≫ (model.quotients.tower S_0_0).rho 9 11 (by decide))) syntheticH0 eta z →
      FiniteDetected 9 (by decide) 11 136 4 KIP126.Computation.Standard.Y z

def H0KillsDifferencesOfYRepresentatives : Prop :=
  ∀ (_hc3 : Stem126D6Vanishes) (_hc5 : EtaExtensionDetection)
    (y y0 : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)),
    FiniteDetected 9 (by decide) 11 136 4 KIP126.Computation.Standard.Y y →
    FiniteDetected 9 (by decide) 11 136 4 KIP126.Computation.Standard.Y y0 →
    sphereAction syntheticH0 (y-y0)=0

def FullAnyYH0Extension : Prop :=
  Stem126D6Vanishes → EtaExtensionDetection →
    AnyYH0Extension KIP126.Computation.Standard.Y KIP126.Computation.Standard.T syntheticH0

end MainPaperSectionSevenRemaining
