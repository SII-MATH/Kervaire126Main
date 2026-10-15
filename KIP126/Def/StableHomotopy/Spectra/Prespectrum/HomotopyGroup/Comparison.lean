module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.HomotopyGroup.Colimit.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

universe u

/-- Send the original stable quotient to the cofinal direct limit using
only the actual stabilization of its representatives. -/
noncomputable def stableGroupCode (X : Prespectrum.{u}) (d : ℤ) :
    StableHomotopy X d → stableGroupColimit X d :=
  Quot.lift Representative.groupColimit (fun a _ h => by
    cases h with
    | homotopy p h => exact a.groupColimit_homotopy p h
    | stabilization => exact a.groupColimit_next)

/-- Realize a direct-limit element as its original stable cubical class. -/
noncomputable def stableGroupRealize (X : Prespectrum.{u}) (d : ℤ) :
    stableGroupColimit X d → StableHomotopy X d :=
  DirectLimit.lift (stableLevelTransition X d) (stableLevelClass X d)
    (stableLevelClass_transition X d)

end KIP126.StableHomotopy.Spectra.Prespectrum

end

section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

set_option backward.isDefEq.respectTransparency false

universe u

theorem stableGroupRealize_code (X : Prespectrum.{u}) (d : ℤ)
    (x : StableHomotopy X d) : stableGroupRealize X d (stableGroupCode X d x) = x := by
  induction x using Quot.inductionOn with
  | h a =>
    change stableLevelClass X d a.stage
      (((Representative.next^[stableGroupStage d 0]) a).atStableLevel a.stage
        (by rw [Representative.iterate_next_stage]; unfold stableGroupStage; omega)) = _
    rw [stableLevelClass_atStableLevel]
    exact (a.class_eq_iterate_next _).symm

theorem stableGroupCode_levelClass (X : Prespectrum.{u}) (d : ℤ) (k : ℕ)
    (x : stableLevelGroup X d k) :
    stableGroupCode X d (stableLevelClass X d k x) = (⟦⟨k,x⟩⟧ : stableGroupColimit X d) := by
  induction x using Quotient.inductionOn with
  | h p =>
    exact Representative.groupColimit_atStableLevel
      ⟨stableGroupStage d k,stableGroupDimension d k,stableGroup_degree d k,p⟩ k rfl

theorem stableGroupCode_realize (X : Prespectrum.{u}) (d : ℤ)
    (x : stableGroupColimit X d) : stableGroupCode X d (stableGroupRealize X d x) = x := by
  induction x using DirectLimit.induction with
  | ih k x => exact stableGroupCode_levelClass X d k x

end KIP126.StableHomotopy.Spectra.Prespectrum

end
