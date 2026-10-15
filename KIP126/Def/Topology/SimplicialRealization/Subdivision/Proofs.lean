module

public import KIP126.Def.Topology.SimplicialRealization.Subdivision.Data
public import KIP126.Def.Topology.SimplicialRealization.Equalizer.Proofs
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite

set_option backward.isDefEq.respectTransparency false

universe u

/-- The extended last-vertex map restricts to exactly the displayed
maximum-of-flags map on every representable simplex. -/
theorem subdivisionLastVertex_stdSimplex (n : SimplexCategory) :
    SSet.stdSimplex.sdIso.inv.app n ≫
      subdivisionLastVertex.app (SSet.stdSimplex.{u}.obj n) =
        simplexSubdivisionLastVertex n :=
  Functor.descOfIsLeftKanExtension_fac_app _ _ _ _ n

/-- Last-vertex comparison commutes with every actual simplicial map. -/
theorem subdivisionLastVertex_natural {K L : SSet.{u}} (f : K ⟶ L) :
    SSet.sd.map f ≫ subdivisionLastVertex.app L =
      subdivisionLastVertex.app K ≫ f :=
  subdivisionLastVertex.naturality f

/-- A finite partial order has only finitely many nondegenerate nerve
simplices; a strict chain cannot have more vertices than the order. -/
theorem finite_nerve_of_finite_order (P : Type u) [PartialOrder P] [Finite P] :
    SSet.Finite (nerve P) := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  haveI : (nerve P).HasDimensionLT (Fintype.card P) := ⟨by
    intro n hn
    ext s
    simp only [SSet.mem_degenerate_iff_notMem_nonDegenerate,Set.top_eq_univ,
      Set.mem_univ,iff_true]
    intro hs
    have hi := (PartialOrder.mem_nerve_nonDegenerate_iff_injective s).mp hs
    have hc := Fintype.card_le_of_injective s.obj hi
    simp only [Fintype.card_fin] at hc
    omega⟩
  apply SSet.finite_of_hasDimensionLT _ (Fintype.card P)
  intro n _
  haveI : Finite ((nerve P).obj (op ⦋n⦌)) :=
    Finite.of_injective (fun s : (nerve P).obj (op ⦋n⦌) => s.obj) (by
      intro a b hab
      ext : 1
      exact hab)
  infer_instance

/-- The flag set of a finite partial order is itself finite. -/
theorem finite_nonemptyFiniteChains (P : Type u) [PartialOrder P] [Finite P] :
    Finite (PartialOrder.NonemptyFiniteChains P) := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  exact Finite.of_injective PartialOrder.NonemptyFiniteChains.finset (by
    intro a b h
    exact PartialOrder.NonemptyFiniteChains.ext h)

/-- A strict flag of nonempty subsets of a finite order has at most as
many entries as the order has elements. -/
theorem nonemptyFiniteChains_nerve_hasDimensionLT (P : Type u)
    [PartialOrder P] [Fintype P] :
    (nerve (PartialOrder.NonemptyFiniteChains P)).HasDimensionLT (Fintype.card P) := by
  classical
  constructor
  intro d hd
  ext s
  simp only [SSet.mem_degenerate_iff_notMem_nonDegenerate,Set.top_eq_univ,
    Set.mem_univ,iff_true]
  intro hs
  have hmono := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mp hs
  have hc (k : Fin (d+1)) : 0 < (s.obj k).finset.card :=
    Finset.card_pos.mpr (s.obj k).nonempty
  let r : Fin (d+1) → Fin (Fintype.card P) := fun k =>
    ⟨(s.obj k).finset.card - 1,by
      have := Finset.card_le_univ (s.obj k).finset
      have := hc k
      omega⟩
  have hr : Function.Injective r := by
    apply StrictMono.injective
    intro a b hab
    have hlt := Finset.card_lt_card (hmono hab)
    have := hc a
    have := hc b
    change (s.obj a).finset.card - 1 < (s.obj b).finset.card - 1
    omega
  have hcard := Fintype.card_le_of_injective r hr
  simp only [Fintype.card_fin] at hcard
  omega

/-- Barycentric subdivision preserves the dimension of a standard simplex. -/
theorem simplexSubdivision_hasDimensionLE (n : SimplexCategory) :
    (SimplexCategory.sd.{u}.obj n).HasDimensionLE n.len := by
  change (nerve (PartialOrder.NonemptyFiniteChains
    (ULift.{u} (Fin (n.len+1))))).HasDimensionLT (n.len+1)
  have h := nonemptyFiniteChains_nerve_hasDimensionLT
    (ULift.{u} (Fin (n.len+1)))
  simpa only [Fintype.card_ulift,Fintype.card_fin] using h

/-- The actual subdivision of a standard simplex is a finite simplicial set. -/
theorem finite_simplexSubdivision (n : SimplexCategory) :
    SSet.Finite (SimplexCategory.sd.{u}.obj n) := by
  letI := finite_nonemptyFiniteChains (ULift.{u} (Fin (n.len+1)))
  exact finite_nerve_of_finite_order
    (PartialOrder.NonemptyFiniteChains (ULift.{u} (Fin (n.len+1))))

/-- The actual subdivided standard simplex has compact realization. -/
theorem compactSpace_simplexSubdivision (n : SimplexCategory) :
    CompactSpace |SimplexCategory.sd.{u}.obj n| := by
  letI := finite_simplexSubdivision.{u} n
  exact compactSpace_of_finite _

/-- The characteristic map of a standard-simplex simplex is precisely
its barycentric vertex map. -/
theorem toTopHomeo_simplexPoint (n : SimplexCategory) {d : SimplexCategoryᵒᵖ}
    (s : (SSet.stdSimplex.{u}.obj n).obj d)
    (t : stdSimplex ℝ (Fin (d.unop.len+1))) :
    SimplexCategory.toTopHomeo n (simplexPoint _ s t) =
      stdSimplex.map (SSet.stdSimplex.objEquiv s) t := by
  rcases d with ⟨⟨d⟩⟩
  rw [simplexPoint_eq_yoneda]
  have h : SSet.yonedaEquiv.symm s = SSet.stdSimplex.map (SSet.stdSimplex.objEquiv s) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply,SSet.yonedaEquiv_map,Equiv.symm_apply_apply]
  rw [h,SimplexCategory.toTopHomeo_naturality_apply,Homeomorph.apply_symm_apply]

/-- On every actual flag simplex, last-vertex realization pushes its
weights to the maximal vertex of each face in the flag. -/
theorem simplexSubdivisionLastVertex_simplex (n : SimplexCategory)
    {d : SimplexCategoryᵒᵖ} (s : (SimplexCategory.sd.{u}.obj n).obj d)
    (t : stdSimplex ℝ (Fin (d.unop.len+1))) :
    SimplexCategory.toTopHomeo n
      (SSet.toTop.map (simplexSubdivisionLastVertex n) (simplexPoint _ s t)) =
        stdSimplex.map (fun k => (finiteChainLastVertex
          (ULift.{u} (Fin (n.len+1))) (s.obj k)).down) t := by
  rw [simplexPoint_map,toTopHomeo_simplexPoint]
  rfl

end KIP126.Topology.SimplicialRealization
