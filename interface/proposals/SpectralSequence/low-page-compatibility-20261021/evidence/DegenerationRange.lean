module
import KIP126.Literature.Standard

namespace KIP126.Literature.Standard.BridgeContinuation
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (Spectrum SyntheticSpectrum model)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem degenerationFreeRange
    (X : ClassicalObject) (N : ℤ)
    (hD : DegeneratesAt (model.classical.obj (X.obj model.auxiliary)) N)
    (r : ℤ) (hr : 2 ≤ r) (hNr : N ≤ r)
    (s t w : ℤ) (hf : r-2 ≤ t-w) :
    (model.family.nu model.nu (X.obj model.auxiliary)).sequence.d r (s,t,w) = 0 := by
  have hd : KIP126.Literature.classicalDifferential model X r s t = 0 := by
    dsimp only [KIP126.Literature.classicalDifferential]
    rw [hD r hNr (s,t), zero_comp]
  have hs : KIP126.Literature.syntheticDifferential model X r s t w = 0 := by
    apply (cancel_mono (free_component X r hr (s+r) (t+r-1) w (by omega)).hom).mp
    rw [free_differential X r hr s t w hf, hd, comp_zero, zero_comp]
  dsimp only [KIP126.Literature.syntheticDifferential, SyntheticAdamsSS.d] at hs
  simpa only [Preadditive.IsIso.comp_right_eq_zero] using hs

private theorem degenerationAboveDiagonal
    (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (hw : t < w) :
    (model.family.nu model.nu (X.obj model.auxiliary)).sequence.d r (s,t,w) = 0 := by
  have hz := above_diagonal X r hr s t w hw
  exact hz.eq_of_src _ _

#print axioms degenerationFreeRange
#print axioms degenerationAboveDiagonal

private theorem degenerationDisplayedPages
    (X : ClassicalObject) (N : ℤ)
    (hD : DegeneratesAt (model.classical.obj (X.obj model.auxiliary)) N)
    (r : ℤ) (hr : 2 ≤ r) (hNr : N ≤ r) (s t w : ℤ) :
    (model.family.nu model.nu (X.obj model.auxiliary)).sequence.d r (s,t,w) = 0 := by
  by_cases hw : w ≤ t
  · have hd : KIP126.Literature.classicalDifferential model X r s t = 0 := by
      dsimp only [KIP126.Literature.classicalDifferential]
      rw [hD r hNr (s,t), zero_comp]
    have hs : KIP126.Literature.syntheticDifferential model X r s t w = 0 := by
      apply (cancel_mono (free_component X r hr (s+r) (t+r-1) w (by omega)).hom).mp
      rw [free_inversion X r hr (s+r) (t+r-1) w (by omega)]
      rw [inversion_differential X r hr s t w, hd, comp_zero, zero_comp]
    dsimp only [KIP126.Literature.syntheticDifferential, SyntheticAdamsSS.d] at hs
    simpa only [Preadditive.IsIso.comp_right_eq_zero] using hs
  · exact degenerationAboveDiagonal X r hr s t w (by omega)

private theorem degenerationFromPageTwo
    (X : ClassicalObject) (N : ℤ) (hN : 2 ≤ N)
    (hD : DegeneratesAt (model.classical.obj (X.obj model.auxiliary)) N) :
    DegeneratesAt (model.family.nu model.nu (X.obj model.auxiliary)).sequence N := by
  intro r hr p
  rcases p with ⟨s,t,w⟩
  exact degenerationDisplayedPages X N hD r (by omega) hr s t w

private theorem degenerationIffLowPages
    (X : ClassicalObject) (N : ℤ)
    (hD : DegeneratesAt (model.classical.obj (X.obj model.auxiliary)) N) :
    DegeneratesAt (model.family.nu model.nu (X.obj model.auxiliary)).sequence N ↔
      ∀ (r : ℤ), N ≤ r → r < 2 → ∀ (p : Tridegree),
        (model.family.nu model.nu (X.obj model.auxiliary)).sequence.d r p = 0 := by
  constructor
  · intro h r hr _ p
    exact h r hr p
  · intro h r hr p
    by_cases h2 : 2 ≤ r
    · rcases p with ⟨s,t,w⟩
      exact degenerationDisplayedPages X N hD r h2 hr s t w
    · exact h r hr (by omega) p

#print axioms degenerationDisplayedPages
#print axioms degenerationFromPageTwo
#print axioms degenerationIffLowPages

end
end KIP126.Literature.Standard.BridgeContinuation
