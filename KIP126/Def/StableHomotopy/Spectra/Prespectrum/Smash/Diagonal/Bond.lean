module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Smash.Diagonal.Tail.Data
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Smash.Diagonal.Bond.Existence.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Spectra
open CategoryTheory _root_.Topology
open scoped unitInterval
namespace Prespectrum

noncomputable def pairedBond (X Y : Prespectrum.{0}) :
    C(((X.level 0).smash (Y.level 0)).suspension × I,
      (X.level 1).smash (Y.level 1)) := (pairedBond_exists X Y).exists.choose

def diagonalLevel (X Y : Prespectrum.{0}) : ℕ → BasedSpace.{0}
  | 0 => (X.level 0).smash (Y.level 0)
  | 1 => ((X.level 0).smash (Y.level 0)).suspension
  | n+2 => diagonalLevel X.tail Y.tail n

noncomputable def diagonalBond (X Y : Prespectrum.{0}) :
    ∀ n, C(diagonalLevel X Y n × I, diagonalLevel X Y (n+1))
  | 0 => BasedSpace.suspensionProjection _
  | 1 => pairedBond X Y
  | n+2 => diagonalBond X.tail Y.tail n

end Prespectrum
end KIP126.StableHomotopy.Spectra

end

section

namespace KIP126.StableHomotopy.Spectra
open CategoryTheory _root_.Topology
open scoped unitInterval
namespace Prespectrum

theorem diagonalBond_laws (X Y : Prespectrum.{0}) (n : ℕ) :
    (∀ t, diagonalBond X Y n ((diagonalLevel X Y n).point,t) =
      (diagonalLevel X Y (n+1)).point) ∧
    (∀ a, diagonalBond X Y n (a,0) = (diagonalLevel X Y (n+1)).point) ∧
    (∀ a, diagonalBond X Y n (a,1) = (diagonalLevel X Y (n+1)).point) := by
  induction n using Nat.twoStepInduction generalizing X Y with
  | zero =>
    exact ⟨fun _ => BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl),
      fun _ => BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl)),
      fun _ => BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))⟩
  | one => exact (pairedBond_exists X Y).exists.choose_spec.2
  | more n ih _ => exact ih X.tail Y.tail

end Prespectrum
end KIP126.StableHomotopy.Spectra

end
