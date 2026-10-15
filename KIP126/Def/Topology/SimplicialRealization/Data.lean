module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite HomotopicalAlgebra

universe u

local instance : PreservesWellOrderContinuousOfShape ℕ SSet.toTop.{u} where
  preservesColimitsOfShape _ _ := inferInstance

/-- Geometric realization sends the actual simplicial cell filtration to
a topological filtration attaching realized simplex boundaries. Identification
of these boundary pairs with disks is a separate geometric assertion. -/
noncomputable def cellComplex (X : SSet.{u}) :
    RelativeCellComplex.{u}
      (fun (n : ℕ) (_ : Unit) => SSet.toTop.map (∂Δ[n].ι))
      (SSet.toTop.map (SSet.Subcomplex.ι (⊥ : X.Subcomplex))) where
  toTransfiniteCompositionOfShape :=
    X.relativeCellComplex.toTransfiniteCompositionOfShape.map SSet.toTop
  attachCells n hn := by
    let c := X.relativeCellComplex.attachCells n hn
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

end KIP126.Topology.SimplicialRealization
