module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Replacement.Cubical.HomotopyExtension.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory CategoryTheory.Limits KIP126.Topology.SmallObject
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Each actual replacement level has a closed basepoint with genuine
homotopy extension for every specified basepoint path. -/
theorem cubicalReplacementFunctor_level_wellBased (X : Prespectrum.{u}) (n : ℕ) :
    ((cubicalReplacementFunctor.obj X).level n).IsWellBased := by
  refine ⟨isClosed_singleton, ?_⟩
  intro Y f p hp
  let i := colimit.ι
    (cellularSequence cubicalCellBoundary (Over.mk (zeroMap zeroPrespectrum X))) 0
  have hi : i.level n (zeroPrespectrum.level n).point =
      ((cubicalReplacementFunctor.obj X).level n).point := i.point n
  obtain ⟨H, hH0, hHi⟩ := cubicalReplacementInitialInclusion_level_hasHomotopyExtension X n
    Y f (p.comp ⟨Prod.snd, continuous_snd⟩) (by
      intro x
      have hx : x = (zeroPrespectrum.level n).point :=
        @Subsingleton.elim PUnit inferInstance _ _
      change p 0 = f (i.level n x)
      rw [hx, hi]
      exact hp)
  refine ⟨H, hH0, ?_⟩
  intro t
  have h := hHi (zeroPrespectrum.level n).point t
  change H (i.level n (zeroPrespectrum.level n).point, t) = p t at h
  rwa [hi] at h

/-- The actual functorial cubical replacement is a well-based
prespectrum in its original levels and topology. -/
theorem cubicalReplacementFunctor_wellBased (X : Prespectrum.{u}) :
    (cubicalReplacementFunctor.obj X).IsWellBased :=
  cubicalReplacementFunctor_level_wellBased X

end KIP126.StableHomotopy.Spectra.Prespectrum
