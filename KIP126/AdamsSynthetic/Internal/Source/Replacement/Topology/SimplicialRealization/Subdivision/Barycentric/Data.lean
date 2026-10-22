module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SimplicialRealization.Subdivision.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Simplex.Combination.Proofs
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

@[expose] section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- The continuous affine combination of simplex-valued vertices. -/
noncomputable def simplexCombination {A B : Type*} [Fintype A] [Fintype B]
    (v : A → stdSimplex ℝ B) : C(stdSimplex ℝ A,stdSimplex ℝ B) := {
  toFun := fun t => ⟨Simplex.combinationCoordinates v t,
    Simplex.combinationCoordinates_nonneg v t,Simplex.combinationCoordinates_sum v t⟩
  continuous_toFun := (Simplex.continuous_combinationCoordinates v).subtype_mk _ }

/-- The barycenter of the nonempty face represented by a finite chain. -/
noncomputable def finiteChainBarycenter (n : SimplexCategory)
    (c : PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n.len+1)))) :
    stdSimplex ℝ (Fin (n.len+1)) := by
  letI : Nonempty c.finset := c.nonempty.to_subtype
  exact stdSimplex.map (fun x : c.finset => x.val.down) stdSimplex.barycenter

/-- The actual singular-simplex map on the flag triangulation: extend
the face barycenters affinely over every flag. Naturality in the flag
simplex includes its degeneracies. -/
noncomputable def simplexSubdivisionBarycentricAdjoint (n : SimplexCategory) :
    SimplexCategory.sd.{u}.obj n ⟶ TopCat.toSSet.obj (SimplexCategory.toTop.obj n) where
  app d := TypeCat.ofHom fun s =>
    (TopCat.toSSetObjEquiv _ _).symm {
      toFun := fun t => ULift.up (simplexCombination (fun k => finiteChainBarycenter n (s.obj k)) t)
      continuous_toFun := continuous_uliftUp.comp (simplexCombination _).continuous }
  naturality {d e} f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply (TopCat.toSSetObjEquiv _ _).injective
    apply ContinuousMap.ext
    intro t
    apply ULift.down_injective
    apply stdSimplex.ext
    change Simplex.combinationCoordinates
      (fun k => finiteChainBarycenter n (s.obj (f.unop k))) t =
      Simplex.combinationCoordinates (fun k => finiteChainBarycenter n (s.obj k))
        (stdSimplex.map f.unop t)
    exact (Simplex.combinationCoordinates_map
      (A := Fin (e.unop.len+1)) (B := Fin (d.unop.len+1)) (C := Fin (n.len+1))
      f.unop (fun k => finiteChainBarycenter n (s.obj k)) t).symm

/-- The continuous barycentric projection of the actual subdivided
standard simplex. Homeomorphism and mesh estimates are separate results. -/
noncomputable def simplexSubdivisionBarycentric (n : SimplexCategory) :
    C(|SimplexCategory.sd.{u}.obj n|,stdSimplex ℝ (Fin (n.len+1))) :=
  (⟨ULift.down,continuous_uliftDown⟩ : C(SimplexCategory.toTop.obj n,_)).comp
    ((sSetTopAdj.homEquiv _ _).symm (simplexSubdivisionBarycentricAdjoint n)).hom

end KIP126.Topology.SimplicialRealization
