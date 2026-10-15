module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.HomotopyGroup.System

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open Topology
open scoped Topology.Homotopy

universe u

/-- The direct limit of the actual level groups in a cofinal range. -/
abbrev stableGroupColimit (X : Prespectrum.{u}) (d : ℤ) :=
  DirectLimit (stableLevelGroup X d) (stableLevelTransition X d)

/-- Read a displayed representative at a specified cofinal stage. -/
def Representative.atStableLevel {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) (k : ℕ) (h : a.stage = stableGroupStage d k) :
    stableLevelGroup X d k := by
  rcases a with ⟨n,r,hr,p⟩
  dsimp only at h
  subst n
  have hd : r = stableGroupDimension d k := by have := stableGroup_degree d k; omega
  subst r
  exact ⟦p⟧

/-- Every representative reaches a chosen cofinal stage after a fixed number
of its actual bonds. -/
noncomputable def Representative.groupColimit {X : Prespectrum.{u}} {d : ℤ}
    (a : Representative X d) : stableGroupColimit X d :=
  ⟦⟨a.stage, ((Representative.next^[stableGroupStage d 0]) a).atStableLevel a.stage
    (by rw [Representative.iterate_next_stage]; unfold stableGroupStage; omega)⟩⟧

/-- The canonical map from a cofinal level homotopy group to the original
stable quotient. -/
def stableLevelClass (X : Prespectrum.{u}) (d : ℤ) (k : ℕ) :
    stableLevelGroup X d k → StableHomotopy X d :=
  Quotient.lift (loopClass X d (stableGroupStage d k)
    (stableGroupDimension d k) (stableGroup_degree d k))
    (fun p q h => loopClass_eq_of_homotopic _ _ _ p q h)

end KIP126.StableHomotopy.Spectra.Prespectrum
