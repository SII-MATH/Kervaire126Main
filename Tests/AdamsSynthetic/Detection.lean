module

import KIP126.Def.AdamsSynthetic

/-! Ordinary-import consumers of the fixed project background.
Only actual objects, maps, classes and mathematical hypotheses are parameters. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence
open KIP126.Core.SpectralSequence KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable (U V : SyntheticObject) (i : Tridegree)

example : SyntheticCanonicalIdentification syntheticTower (U.obj nu auxiliary) (convergence U).identification := (convergence U).canonical

example (s m w : ℤ) (a : BiHom m w (U.obj nu auxiliary)) :
    FiltrationAtLeast syntheticTower s a ↔
      ∃ b : BiHom m w ((syntheticTower.tower (U.obj nu auxiliary)).stageAt s),
        b ≫ (syntheticTower.tower (U.obj nu auxiliary)).projection s = a := Iff.rfl

example (f : (U.obj nu auxiliary) ⟶ (V.obj nu auxiliary)) (p : ℤ × ℤ) (a : BiHom p.1 p.2 (U.obj nu auxiliary)) :
    syntheticHomotopyMap f p a = a ≫ f := rfl

example (x : (family.obj (U.obj nu auxiliary)).E₂ i) (a : BiHom (i.2.1-i.1) i.2.2 (U.obj nu auxiliary))
    (h : DetectsNonzero (convergence U) i x a) : Detects (convergence U) i x a := h.1

example (a : BiHom (i.2.1-i.1) i.2.2 (U.obj nu auxiliary)) (h : Detects (convergence U) i 0 a) :
    FiltrationAtLeast syntheticTower (i.1+1) a := detects_zero_filtration (convergence U) i h

example (x : (family.obj (U.obj nu auxiliary)).E₂ i) (a b : BiHom (i.2.1-i.1) i.2.2 (U.obj nu auxiliary))
    (ha : Detects (convergence U) i x a) (hb : Detects (convergence U) i x b) :
    FiltrationAtLeast syntheticTower (i.1+1) (a-b) := detects_sub_filtration (convergence U) i ha hb

example (x : (family.obj (U.obj nu auxiliary)).E₂ i) (e e' : ((family.obj (U.obj nu auxiliary)).sequence.ssData i).eInfty)
    (h : HasInfinityRepresentative (family.obj (U.obj nu auxiliary)) 2 i x e)
    (h' : HasInfinityRepresentative (family.obj (U.obj nu auxiliary)) 2 i x e') : e=e' := h.unique h'


-- A zero leading term still supplies no nonzero detection.
example (a : BiHom (i.2.1-i.1) i.2.2 (U.obj nu auxiliary))
    (_h : Detects (convergence U) i 0 a) : True := by
  fail_if_success have : DetectsNonzero (convergence U) i 0 a := _h
  trivial

end
