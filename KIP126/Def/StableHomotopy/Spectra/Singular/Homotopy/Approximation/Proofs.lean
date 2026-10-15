module

public import KIP126.Def.StableHomotopy.Spectra.Realization.Proofs
public import KIP126.Def.Topology.SimplicialRealization.FiniteSupport.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory Topology Simplicial Opposite
open scoped unitInterval Topology.Homotopy

universe u

set_option backward.isDefEq.respectTransparency false

/-- Realization carries a specified simplicial vertex to precisely its
specified image vertex. -/
theorem basedRealization_map_point {K L : SSet.{u}} (f : K ⟶ L)
    (v : K.obj (op ⦋0⦌)) :
    SSet.toTop.map f (basedRealization K v).point =
      (basedRealization L (f.app (op ⦋0⦌) v)).point := by
  rw [← basedRealization_point K v, ← TopCat.comp_app, ← Functor.map_comp, SSet.const_comp]
  exact basedRealization_point _ _

/-- A compact map into a based realization factors through an actual
finite simplicial subcomplex that contains the specified simplicial
vertex, including when that vertex is absent from the map's image. -/
theorem continuousMap_factor_finite_based_simplicial_subcomplex
    (K : SSet.{u}) (v : K.obj (op ⦋0⦌))
    {D : Type*} [TopologicalSpace D] [CompactSpace D] (f : C(D,|K|)) :
    ∃ (A : K.Subcomplex), A.toSSet.Finite ∧
      ∃ hv : v ∈ A.obj (op ⦋0⦌),
        ∃ g : C(D, basedRealization A.toSSet ⟨v,hv⟩),
          ∀ d, SSet.toTop.map A.ι (g d) = f d := by
  classical
  obtain ⟨C,hC,g,hg⟩ :=
    KIP126.Topology.SimplicialRealization.continuousMap_factor_finite_simplicial_subcomplex K f
  let family : Bool → K.Subcomplex := fun b => if b then C else SSet.Subcomplex.ofSimplex v
  let A : K.Subcomplex := ⨆ b, family b
  have hfinite : A.toSSet.Finite := by
    apply (SSet.finite_iSup_iff family).mpr
    intro b
    cases b
    · exact SSet.finite_of_epi (SSet.Subcomplex.toOfSimplex v)
    · exact hC
  have hCA : C ≤ A := le_iSup family true
  have hv : v ∈ A.obj (op ⦋0⦌) :=
    (SSet.Subcomplex.ofSimplex_le_iff v A).mp (le_iSup family false)
  let j := SSet.Subcomplex.homOfLE hCA
  refine ⟨A,hfinite,hv,(SSet.toTop.map j).hom.comp g,?_⟩
  intro d
  change SSet.toTop.map A.ι (SSet.toTop.map j (g d)) = _
  rw [← TopCat.comp_app, ← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
  exact hg d

/-- Every actual based cubical loop factors exactly through a finite
simplicial subcomplex with its inherited, specified vertex. -/
theorem genLoop_factor_finite_simplicial_subcomplex
    (K : SSet.{u}) (v : K.obj (op ⦋0⦌)) (r : ℕ)
    (p : GenLoop (Fin r) (basedRealization K v) (basedRealization K v).point) :
    ∃ (A : K.Subcomplex), A.toSSet.Finite ∧
      ∃ hv : v ∈ A.obj (op ⦋0⦌),
        ∃ q : GenLoop (Fin r) (basedRealization A.toSSet ⟨v,hv⟩)
          (basedRealization A.toSSet ⟨v,hv⟩).point,
          ∀ t, SSet.toTop.map A.ι (q t) = p t := by
  obtain ⟨A,hA,hv,g,hg⟩ :=
    continuousMap_factor_finite_based_simplicial_subcomplex K v p.val
  have hj := KIP126.Topology.SimplicialRealization.realization_mono_isClosedEmbedding A.ι
  refine ⟨A,hA,hv,⟨g,?_⟩,hg⟩
  intro t ht
  apply hj.injective
  rw [hg t, basedRealization_map_point]
  exact p.property t ht

/-- A based cubical homotopy and both of its endpoints lie in one actual
finite simplicial subcomplex. The lifted homotopy remains fixed at the
same specified vertex on every boundary point. -/
theorem genLoop_homotopy_factor_finite_simplicial_subcomplex
    (K : SSet.{u}) (v : K.obj (op ⦋0⦌)) (r : ℕ)
    (p q : GenLoop (Fin r) (basedRealization K v) (basedRealization K v).point)
    (H : p.val.HomotopyRel q.val (_root_.Cube.boundary (Fin r))) :
    ∃ (A : K.Subcomplex), A.toSSet.Finite ∧
      ∃ hv : v ∈ A.obj (op ⦋0⦌),
        ∃ (p' q' : GenLoop (Fin r) (basedRealization A.toSSet ⟨v,hv⟩)
            (basedRealization A.toSSet ⟨v,hv⟩).point)
          (H' : p'.val.HomotopyRel q'.val (_root_.Cube.boundary (Fin r))),
          (∀ t, SSet.toTop.map A.ι (p' t) = p t) ∧
          (∀ t, SSet.toTop.map A.ι (q' t) = q t) ∧
          (∀ z, SSet.toTop.map A.ι (H' z) = H z) := by
  obtain ⟨A,hA,hv,g,hg⟩ :=
    continuousMap_factor_finite_based_simplicial_subcomplex K v H.toContinuousMap
  have hj := KIP126.Topology.SimplicialRealization.realization_mono_isClosedEmbedding A.ι
  have hb (s : I) (t : Fin r → I) (ht : t ∈ _root_.Cube.boundary (Fin r)) :
      g (s,t) = (basedRealization A.toSSet ⟨v,hv⟩).point := by
    apply hj.injective
    rw [hg, basedRealization_map_point]
    exact (H.eq_fst s ht).trans (p.property t ht)
  let p' : GenLoop (Fin r) (basedRealization A.toSSet ⟨v,hv⟩)
      (basedRealization A.toSSet ⟨v,hv⟩).point :=
    ⟨g.comp ((ContinuousMap.const _ 0).prodMk (ContinuousMap.id _)),hb 0⟩
  let q' : GenLoop (Fin r) (basedRealization A.toSSet ⟨v,hv⟩)
      (basedRealization A.toSSet ⟨v,hv⟩).point :=
    ⟨g.comp ((ContinuousMap.const _ 1).prodMk (ContinuousMap.id _)),hb 1⟩
  let H' : p'.val.HomotopyRel q'.val (_root_.Cube.boundary (Fin r)) := {
    toContinuousMap := g
    map_zero_left := fun _ => rfl
    map_one_left := fun _ => rfl
    prop' := fun s t ht => (hb s t ht).trans (hb 0 t ht).symm }
  refine ⟨A,hA,hv,p',q',H',?_,?_,hg⟩
  · intro t
    exact (hg (0,t)).trans (H.apply_zero t)
  · intro t
    exact (hg (1,t)).trans (H.apply_one t)

end KIP126.StableHomotopy.Spectra
