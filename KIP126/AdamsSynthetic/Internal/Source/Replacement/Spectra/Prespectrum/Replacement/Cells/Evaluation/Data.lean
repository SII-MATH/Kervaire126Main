module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Replacement/Cells/Evaluation/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Colimit.Evaluation.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Colimit.Cells.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u v

set_option backward.isDefEq.respectTransparency false

variable {I : Type v} {A B : I → Prespectrum.{u}} {g : ∀ i, A i ⟶ B i}
  {X Y : Prespectrum.{u}} {f : X ⟶ Y} (c : AttachCells.{u} g f)

/-- Evaluation of a genuine prespectrum cell attachment is the genuine
based cell attachment at that level, with the same cells. -/
noncomputable def attachCells_evaluation (n : ℕ) :
    AttachCells.{u} (fun i => (evaluationFunctor n).map (g i))
      ((evaluationFunctor n).map f) := by
  let E := evaluationFunctor.{u} n
  letI : PreservesColimitsOfSize.{0,0} E :=
    preservesSmallestColimits_of_preservesColimits _
  exact {
    ι := c.ι
    π := c.π
    cofan₁ := Cofan.mk (E.obj c.cofan₁.pt) (fun i => E.map (c.cofan₁.inj i))
    cofan₂ := Cofan.mk (E.obj c.cofan₂.pt) (fun i => E.map (c.cofan₂.inj i))
    isColimit₁ := Cofan.isColimitMapCoconeEquiv E _ c.cofan₁
      (isColimitOfPreserves E c.isColimit₁)
    isColimit₂ := Cofan.isColimitMapCoconeEquiv E _ c.cofan₂
      (isColimitOfPreserves E c.isColimit₂)
    m := E.map c.m
    hm i := by
      change E.map (c.cofan₁.inj i) ≫ E.map c.m =
        E.map (g (c.π i)) ≫ E.map (c.cofan₂.inj i)
      rw [← E.map_comp,← E.map_comp,c.hm i]
    g₁ := E.map c.g₁
    g₂ := E.map c.g₂
    isPushout := c.isPushout.map E }

/-- The same strict prespectrum attachment is an actual unbased
topological cell attachment at each level. -/
noncomputable def attachCells_evaluation_forgetToTop (n : ℕ) :
    AttachCells.{u} (fun i => ((evaluationFunctor n) ⋙ BasedSpace.forgetToTop).map (g i))
      (((evaluationFunctor n) ⋙ BasedSpace.forgetToTop).map f) :=
  BasedSpace.attachCells_forgetToTop (attachCells_evaluation c n)

end KIP126.AdamsSynthetic.Source.Prespectrum
