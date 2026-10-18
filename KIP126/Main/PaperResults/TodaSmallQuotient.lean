module

import all KIP126.Main.Internal.FiniteReflection
import all KIP126.Main.SectionSeven.WeakStrip

/-! Reflection of the two low candidate layers through the actual map
from the ninth to the third lambda quotient. This does not assert the
vanishing of the eta image in the third quotient. -/

@[expose] section
namespace KIP126.Main.Paper.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Main.Internal.FiniteReflection
open KIP126.Main.SectionSeven.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem ninth_to_third_stem125_weight132_injective
    (s : ℤ) (hs : 7 ≤ s ∧ s ≤ 9) :
    Function.Injective (((model.family.functor.map
      ((model.quotients.tower (S_0_0 : SyntheticSpectrum)).rho 3 9 (by decide))).eInftyMap
        (s,125+s,132)).hom) := by
  exact finite_sphere_rho_injective 3 9 (by decide) (by decide)
    s (125+s) 132 (by constructor <;> omega)

/-- A high-filtration image in Q3 rules out both of the low Q9 candidate
layers. The filtration-ten gap in Q9 then gives the desired F11 bound. -/
private theorem ninth_stem125_weight132_filtration_eleven_of_third
    (a : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ha : FiltrationAtLeast model.syntheticTower 10
      (a ≫ (model.quotients.tower (S_0_0 : SyntheticSpectrum)).rho 3 9 (by decide))) :
    FiltrationAtLeast model.syntheticTower 11 a := by
  let rho := (model.quotients.tower (S_0_0 : SyntheticSpectrum)).rho 3 9 (by decide)
  have hstep (s : ℤ) (hs : 7 ≤ s ∧ s ≤ 9)
      (hsf : FiltrationAtLeast model.syntheticTower s a) :
      FiltrationAtLeast model.syntheticTower (s+1) a := by
    apply next_filtration_of_infinity_injective
      (model.convergentMap (.quotient 9 .sphere) (.quotient 3 .sphere) rho)
      (125,132) s (ninth_to_third_stem125_weight132_injective s hs) a hsf
    exact model.syntheticTower.filtrationSubmodule_antitone _ (125,132)
      (show s+1 ≤ 10 by omega) ha
  have h7 := finite_sphere_bottom_filtration 9 (by decide) 7 132 a
  have h8 : FiltrationAtLeast model.syntheticTower 8 a := hstep 7 (by omega) h7
  have h9 : FiltrationAtLeast model.syntheticTower 9 a := hstep 8 (by omega) h8
  have h10 : FiltrationAtLeast model.syntheticTower 10 a := hstep 9 (by omega) h9
  exact (strip_low_even_gap 10 (Or.inr rfl) a).mp h10

end
end KIP126.Main.Paper.Internal
