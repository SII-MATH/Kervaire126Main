module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Colimit/Bond.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Colimit.Level.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Loop.Data

@[expose] section

section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Curry the actual bonds, retaining the based path endpoints, to a
cocone on the actual based level diagram. -/
noncomputable def pointwiseColimitBondCocone {J : Type u} [Category.{u} J]
    (F : J ⥤ Prespectrum.{u}) (n : ℕ) : Cocone (F ⋙ evaluationFunctor n) where
  pt := loopLevel (pointwiseColimitLevel F (n+1))
  ι :=
    { app := fun j =>
        BasedSpace.basedLoopCurry ((F.obj j).bond n)
          ((F.obj j).bond_point n) ((F.obj j).bond_zero n) ((F.obj j).bond_one n) ≫
        BasedSpace.basedLoopMap (pointwiseColimitLevelInclusion F (n+1) j)
      naturality := by
        intro j k h
        apply BasedSpace.Hom.ext
        apply ContinuousMap.ext
        intro x
        apply Path.ext
        funext t
        change (pointwiseColimitLevelInclusion F (n+1) k).map
          ((F.obj k).bond n ((F.map h).level n x,t)) =
            (pointwiseColimitLevelInclusion F (n+1) j).map ((F.obj j).bond n (x,t))
        rw [← (F.map h).bond n x t]
        exact congrArg (fun g => g.map ((F.obj j).bond n (x,t)))
          (colimit.w (F ⋙ evaluationFunctor (n+1)) h) }

noncomputable def pointwiseColimitBondAdjoint {J : Type u} [Category.{u} J]
    (F : J ⥤ Prespectrum.{u}) (n : ℕ) :
    pointwiseColimitLevel F n ⟶ loopLevel (pointwiseColimitLevel F (n+1)) :=
  colimit.desc (F ⋙ evaluationFunctor n) (pointwiseColimitBondCocone F n)

/-- The genuine continuous structure map obtained from based path evaluation. -/
noncomputable def pointwiseColimitBond {J : Type u} [Category.{u} J]
    (F : J ⥤ Prespectrum.{u}) (n : ℕ) :
    C(pointwiseColimitLevel F n × I, pointwiseColimitLevel F (n+1)) where
  toFun z := (pointwiseColimitBondAdjoint F n).map z.1 z.2
  continuous_toFun := continuous_eval.comp
    (((pointwiseColimitBondAdjoint F n).map.continuous.comp continuous_fst).prodMk
      continuous_snd)

end KIP126.AdamsSynthetic.Source.Prespectrum

end

section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u
variable {J : Type u} [Category.{u} J] (F : J ⥤ Prespectrum.{u})

theorem pointwiseColimitBond_point (n : ℕ) (t : I) :
    pointwiseColimitBond F n ((pointwiseColimitLevel F n).point,t) =
      (pointwiseColimitLevel F (n+1)).point :=
  congrArg (fun p => p t) (pointwiseColimitBondAdjoint F n).point

theorem pointwiseColimitBond_zero (n : ℕ) (x : pointwiseColimitLevel F n) :
    pointwiseColimitBond F n (x,0) = (pointwiseColimitLevel F (n+1)).point :=
  Path.source _

theorem pointwiseColimitBond_one (n : ℕ) (x : pointwiseColimitLevel F n) :
    pointwiseColimitBond F n (x,1) = (pointwiseColimitLevel F (n+1)).point :=
  Path.target _

/-- The actual colimit bond restricts to each specified input bond. -/
theorem pointwiseColimitBond_inclusion (n : ℕ) (j : J) (x : (F.obj j).level n) (t : I) :
    pointwiseColimitBond F n ((pointwiseColimitLevelInclusion F n j).map x,t) =
      (pointwiseColimitLevelInclusion F (n+1) j).map ((F.obj j).bond n (x,t)) :=
  congrArg (fun (f : (F.obj j).level n ⟶ loopLevel (pointwiseColimitLevel F (n+1))) =>
    f.map x t) (colimit.ι_desc (pointwiseColimitBondCocone F n) j)

end KIP126.AdamsSynthetic.Source.Prespectrum

end
