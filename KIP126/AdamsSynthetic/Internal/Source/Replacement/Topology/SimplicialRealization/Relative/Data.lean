module

import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.DiskPair.Proofs

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite HomotopicalAlgebra

universe u

local instance : PreservesWellOrderContinuousOfShape ℕ SSet.toTop.{u} where
  preservesColimitsOfShape _ _ := inferInstance

/-- Realization of the actual relative simplex filtration of any simplicial monomorphism. -/
noncomputable def relativeCellComplex {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    RelativeCellComplex.{u}
      (fun (n : ℕ) (_ : Unit) => SSet.toTop.map (∂Δ[n].ι))
      (SSet.toTop.map i) where
  toTransfiniteCompositionOfShape :=
    (SSet.relativeCellComplexOfMono i).toTransfiniteCompositionOfShape.map SSet.toTop
  attachCells n hn := by
    let c := (SSet.relativeCellComplexOfMono i).attachCells n hn
    exact {
      ι := c.ι
      π := c.π
      cofan₁ := Cofan.mk _ (fun i => SSet.toTop.map (c.cofan₁.inj i))
      cofan₂ := Cofan.mk _ (fun i => SSet.toTop.map (c.cofan₂.inj i))
      isColimit₁ := isColimitCofanMkObjOfIsColimit SSet.toTop _ _ c.isColimit₁
      isColimit₂ := isColimitCofanMkObjOfIsColimit SSet.toTop _ _ c.isColimit₂
      m := SSet.toTop.map c.m
      hm := fun i => by
        change SSet.toTop.map (c.cofan₁.inj i) ≫ SSet.toTop.map c.m =
          SSet.toTop.map _ ≫ SSet.toTop.map (c.cofan₂.inj i)
        rw [← Functor.map_comp, ← Functor.map_comp, c.hm i]
      g₁ := SSet.toTop.map c.g₁
      g₂ := SSet.toTop.map c.g₂
      isPushout := c.isPushout.map SSet.toTop }

/-- The same relative filtration with actual Euclidean disk-boundary attachments. -/
noncomputable def relativeCWComplex {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    TopCat.RelativeCWComplex (SSet.toTop.map i) where
  toTransfiniteCompositionOfShape := (relativeCellComplex i).toTransfiniteCompositionOfShape
  attachCells n hn :=
    ((relativeCellComplex i).attachCells n hn).reindexCellTypes
      (TopCat.RelativeCWComplex.basicCell n) (fun _ => Unit.unit)
      (fun _ => Classical.choice (nonempty_boundary_realization_disk_arrow_iso n))

end KIP126.Topology.SimplicialRealization
