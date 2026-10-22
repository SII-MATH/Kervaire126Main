module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Colimit/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Colimit.Bond

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits Topology

universe u
variable {J : Type u} [Category.{u} J]

set_option backward.isDefEq.respectTransparency false

/-- The actual colimit prespectrum of any small strict diagram. -/
noncomputable def pointwiseColimit (F : J ⥤ Prespectrum.{u}) : Prespectrum.{u} where
  level := pointwiseColimitLevel F
  bond := pointwiseColimitBond F
  bond_point := pointwiseColimitBond_point F
  bond_zero := pointwiseColimitBond_zero F
  bond_one := pointwiseColimitBond_one F

noncomputable def pointwiseColimitInclusion (F : J ⥤ Prespectrum.{u}) (j : J) :
    F.obj j ⟶ pointwiseColimit F where
  level n := (pointwiseColimitLevelInclusion F n j).map
  point n := (pointwiseColimitLevelInclusion F n j).point
  bond n x t := (pointwiseColimitBond_inclusion F n j x t).symm

/-- The actual based-space cocone underlying a strict cocone at one level. -/
def pointwiseCoconeLevel {F : J ⥤ Prespectrum.{u}} (c : Cocone F) (n : ℕ) :
    Cocone (F ⋙ evaluationFunctor n) where
  pt := c.pt.level n
  ι :=
    { app := fun j => ⟨(c.ι.app j).level n, (c.ι.app j).point n⟩
      naturality := by
        intro j k h
        apply BasedSpace.Hom.ext
        exact congrArg (fun f => f.level n) (c.w h) }

noncomputable def pointwiseColimitDesc {F : J ⥤ Prespectrum.{u}} (c : Cocone F) :
    pointwiseColimit F ⟶ c.pt where
  level n := (colimit.desc (F ⋙ evaluationFunctor n) (pointwiseCoconeLevel c n)).map
  point n := (colimit.desc (F ⋙ evaluationFunctor n) (pointwiseCoconeLevel c n)).point
  bond n x t := by
    have he : pointwiseColimitBondAdjoint F n ≫
        BasedSpace.basedLoopMap (colimit.desc (F ⋙ evaluationFunctor (n+1))
          (pointwiseCoconeLevel c (n+1))) =
        colimit.desc (F ⋙ evaluationFunctor n) (pointwiseCoconeLevel c n) ≫
          BasedSpace.basedLoopCurry (c.pt.bond n) (c.pt.bond_point n)
            (c.pt.bond_zero n) (c.pt.bond_one n) := by
      apply colimit.hom_ext
      intro j
      rw [← Category.assoc, ← Category.assoc]
      change (colimit.ι (F ⋙ evaluationFunctor n) j ≫
          colimit.desc (F ⋙ evaluationFunctor n) (pointwiseColimitBondCocone F n)) ≫ _ = _
      rw [colimit.ι_desc, colimit.ι_desc]
      apply BasedSpace.Hom.ext
      apply ContinuousMap.ext
      intro y
      apply Path.ext
      funext s
      have hn := congrArg (fun f => f.map ((F.obj j).bond n (y,s)))
        (colimit.ι_desc (pointwiseCoconeLevel c (n+1)) j)
      exact hn.trans ((c.ι.app j).bond n y s)
    exact congrArg (fun f => f.map x t) he

/-- The canonical strict cocone with the actual pointwise based colimit levels. -/
noncomputable def pointwiseColimitCocone (F : J ⥤ Prespectrum.{u}) : Cocone F where
  pt := pointwiseColimit F
  ι :=
    { app := pointwiseColimitInclusion F
      naturality := by
        intro j k h
        apply Hom.ext
        funext n
        exact congrArg BasedSpace.Hom.map (colimit.w (F ⋙ evaluationFunctor n) h) }

end KIP126.AdamsSynthetic.Source.Prespectrum
