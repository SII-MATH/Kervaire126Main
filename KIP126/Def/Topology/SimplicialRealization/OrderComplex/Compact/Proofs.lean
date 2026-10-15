module

public import KIP126.Def.Topology.SimplicialRealization.FiniteSupport.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Suborder.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCone.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- A simplicial map with finitely many source vertices factors through
the nerve of an actual finite induced suborder of its target. The target
order itself need not be finite. -/
theorem simplicialMap_factor_finite_suborder {K : SSet.{u}}
    [Finite (K.obj (op ⦋0⦌))] (P : Type u) [PartialOrder P]
    (f : K ⟶ nerve P) :
    ∃ S : Set P, S.Finite ∧
      ∃ g : K ⟶ nerve S, g ≫ orderSuborderInclusion P S = f := by
  classical
  let S : Set P := Set.range (fun v : K.obj (op ⦋0⦌) => (f.app _ v).obj 0)
  have hS : S.Finite := Set.finite_range _
  let i := orderSuborderInclusion P S
  have hf : SSet.Subcomplex.range f ≤ SSet.Subcomplex.range i := by
    intro d s hs
    obtain ⟨x,rfl⟩ := hs
    change f.app d x ∈ Set.range ((nerveMap (OrderEmbedding.subtype (· ∈ S)).monotone.functor).app d)
    apply (nerveMap_orderEmbedding_range_iff (OrderEmbedding.subtype (· ∈ S)) d _).mpr
    intro k
    have hk : (f.app d x).obj k ∈ S := by
      refine ⟨K.map (SimplexCategory.const ⦋0⦌ d.unop k).op x,?_⟩
      exact congrArg (fun z : (nerve P).obj (op ⦋0⦌) => z.obj 0)
        (ConcreteCategory.congr_hom (f.naturality
          (SimplexCategory.const ⦋0⦌ d.unop k).op) x)
    exact ⟨⟨_,hk⟩,rfl⟩
  let g := (SSet.Subcomplex.range i).lift f hf ≫ inv (SSet.Subcomplex.toRange i)
  refine ⟨S,hS,g,?_⟩
  have hi : inv (SSet.Subcomplex.toRange i) ≫ i = (SSet.Subcomplex.range i).ι := by
    have h := IsIso.inv_hom_id_assoc (SSet.Subcomplex.toRange i)
      (SSet.Subcomplex.range i).ι
    rw [SSet.Subcomplex.toRange_ι] at h
    exact h
  dsimp only [g]
  change (SSet.Subcomplex.lift f hf ≫ inv (SSet.Subcomplex.toRange i)) ≫ i = f
  rw [Category.assoc,hi,SSet.Subcomplex.lift_ι]

/-- Every continuous map from a compact space to the realization of an
arbitrary order complex factors through a finite induced suborder. -/
theorem continuousMap_factor_finite_suborder (P : Type u) [PartialOrder P]
    {D : Type*} [TopologicalSpace D] [CompactSpace D]
    (f : C(D,|nerve P|)) :
    ∃ S : Set P, S.Finite ∧ ∃ g : C(D,|nerve S|),
      ∀ x, SSet.toTop.map (orderSuborderInclusion P S) (g x) = f x := by
  obtain ⟨A,hA,g,hg⟩ := continuousMap_factor_finite_simplicial_subcomplex (nerve P) f
  letI := hA
  obtain ⟨S,hS,a,ha⟩ := simplicialMap_factor_finite_suborder P A.ι
  refine ⟨S,hS,(SSet.toTop.map a).hom.comp g,?_⟩
  intro x
  change (SSet.toTop.map a ≫ SSet.toTop.map (orderSuborderInclusion P S)) (g x) = _
  rw [← Functor.map_comp,ha]
  exact hg x

end KIP126.Topology.SimplicialRealization
