module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Smash.Diagonal.Data

@[expose] public section

namespace KIP126.StableHomotopy.Spectra
open CategoryTheory _root_.Topology
open scoped unitInterval
namespace Prespectrum

theorem diagonalMapLevel_bond {X Y X' Y' : Prespectrum.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) (a : diagonalLevel X Y n) (t : I) :
    (diagonalMapLevel f g (n+1)).map (diagonalBond X Y n (a,t)) =
      diagonalBond X' Y' n ((diagonalMapLevel f g n).map a,t) := by
  induction n using Nat.twoStepInduction generalizing X Y X' Y' with
  | zero => rfl
  | one =>
    refine Quot.inductionOn a ?_
    rintro ⟨b,s⟩
    refine Quot.inductionOn b ?_
    rintro ⟨x,y⟩
    have hsm {A B A' B' : BasedSpace.{0}} (p : A ⟶ A') (q : B ⟶ B') (x : A) (y : B) :
        (BasedSpace.smashMap p q).map (BasedSpace.smashPoint A B x y) =
          BasedSpace.smashPoint A' B' (p.map x) (q.map y) :=
      (BasedSpace.smashMap_exists p q).exists.choose_spec x y
    have hp (U V : Prespectrum.{0}) (x : U.level 0) (y : V.level 0) (s t : I) :
        pairedBond U V (BasedSpace.suspensionProjection _
          (BasedSpace.smashPoint _ _ x y,s),t) =
        BasedSpace.smashPoint _ _ (U.bond 0 (x,s)) (V.bond 0 (y,t)) :=
      (pairedBond_exists U V).exists.choose_spec.1 x y s t
    change (BasedSpace.smashMap ⟨f.level 1, f.point 1⟩ ⟨g.level 1, g.point 1⟩).map
        (pairedBond X Y (BasedSpace.suspensionProjection _
          (BasedSpace.smashPoint _ _ x y,s),t)) =
      pairedBond X' Y' (BasedSpace.suspensionProjection _
        ((BasedSpace.smashMap ⟨f.level 0, f.point 0⟩ ⟨g.level 0, g.point 0⟩).map
          (BasedSpace.smashPoint _ _ x y),s),t)
    rw [hp, hsm, hsm, hp]
    change BasedSpace.smashPoint _ _ (f.level 1 (X.bond 0 (x,s)))
        (g.level 1 (Y.bond 0 (y,t))) = _
    rw [f.bond, g.bond]
  | more n ih _ => exact ih (tailMap f) (tailMap g) a

end Prespectrum
end KIP126.StableHomotopy.Spectra
