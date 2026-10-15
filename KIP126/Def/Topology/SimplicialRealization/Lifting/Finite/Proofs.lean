module

public import KIP126.Def.Topology.SimplicialRealization.FiniteSupport.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Pullback.Finite.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Predicates

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual relative cubical lifting can be checked over the actual
finite simplicial subcomplexes of the target. -/
theorem hasCubicalLifting_of_finite_subcomplexes {X Y : SSet.{u}} (p : X ⟶ Y)
    (hfinite : ∀ (A : Y.Subcomplex), A.toSSet.Finite →
      HomotopyLifting.HasCubicalLifting
        (⟨SSet.toTop.map (pullback.snd p A.ι), (SSet.toTop.map (pullback.snd p A.ι)).hom.continuous⟩ :
          C(|pullback p A.ι|,|A.toSSet|))) :
    HomotopyLifting.HasCubicalLifting
      (⟨SSet.toTop.map p,(SSet.toTop.map p).hom.continuous⟩ : C(|X|,|Y|)) := by
  intro n g H hcomm
  obtain ⟨A,hA,H',hH'⟩ := continuousMap_factor_finite_simplicial_subcomplex Y H
  letI := hA
  let e := finitePullbackHomeomorph p A.ι
  let a : C(HomotopyLifting.CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n)),
      {xy : |X| × |A.toSSet| // SSet.toTop.map p xy.1 = SSet.toTop.map A.ι xy.2}) :=
    ⟨fun z => ⟨(g z,H' z.val),(hcomm z).trans (hH' z.val).symm⟩,
      (g.continuous.prodMk (H'.continuous.comp continuous_subtype_val)).subtype_mk _⟩
  let g' : C(HomotopyLifting.CylinderHorn (Fin n → I) (_root_.Cube.boundary (Fin n)),
      |pullback p A.ι|) := (⟨e.symm,e.symm.continuous⟩ : C(_, _)).comp a
  have hg' (z) : SSet.toTop.map (pullback.snd p A.ι) (g' z) = H' z.val := by
    have he := finitePullbackHomeomorph_snd p A.ι (e.symm (a z))
    change (e (e.symm (a z))).val.2 = _ at he
    rw [Homeomorph.apply_symm_apply] at he
    exact he.symm
  obtain ⟨L,hL,hLg⟩ := hfinite A hA n g' H' hg'
  let fst : C(|pullback p A.ι|,|X|) :=
    ⟨SSet.toTop.map (pullback.fst p A.ι),(SSet.toTop.map (pullback.fst p A.ι)).hom.continuous⟩
  refine ⟨fst.comp L,?_,?_⟩
  · intro z
    have he := (e (L z)).property
    rw [finitePullbackHomeomorph_fst,finitePullbackHomeomorph_snd] at he
    exact he.trans ((congrArg (SSet.toTop.map A.ι) (hL z)).trans (hH' z))
  · intro z
    change fst (L z.val) = g z
    rw [hLg z]
    have he := finitePullbackHomeomorph_fst p A.ι (e.symm (a z))
    change (e (e.symm (a z))).val.1 = _ at he
    rw [Homeomorph.apply_symm_apply] at he
    exact he.symm

end KIP126.Topology.SimplicialRealization
