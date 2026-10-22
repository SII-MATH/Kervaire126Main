module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/BasedSpace/Loop/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Loop.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Generators

@[expose] section

namespace KIP126.AdamsSynthetic.Source.BasedSpace

open CategoryTheory Topology
open scoped unitInterval

universe u

/-- Postcompose actual based loops with a based continuous map. -/
def basedLoopMap {A B : BasedSpace.{u}} (f : A ⟶ B) :
    Prespectrum.loopLevel A ⟶ Prespectrum.loopLevel B where
  map :=
    { toFun p :=
        { toFun t := f.map (p t)
          continuous_toFun := f.map.continuous.comp p.continuous
          source' := by rw [Path.source, f.point]
          target' := by rw [Path.target, f.point] }
      continuous_toFun := Path.continuous_uncurry_iff.mp
        (f.map.continuous.comp continuous_eval) }
  point := by apply Path.ext; funext t; exact f.point

/-- Curry an actual based interval family with collapsed endpoints. -/
def basedLoopCurry {A B : BasedSpace.{u}} (f : C(A × I, B))
    (hp : ∀ t, f (A.point,t) = B.point)
    (h0 : ∀ x, f (x,0) = B.point) (h1 : ∀ x, f (x,1) = B.point) :
    A ⟶ Prespectrum.loopLevel B where
  map :=
    { toFun x :=
        { toFun t := f (x,t)
          continuous_toFun := f.continuous.comp (continuous_const.prodMk continuous_id)
          source' := h0 x
          target' := h1 x }
      continuous_toFun := Path.continuous_uncurry_iff.mp f.continuous }
  point := by apply Path.ext; funext t; exact hp t

end KIP126.AdamsSynthetic.Source.BasedSpace
