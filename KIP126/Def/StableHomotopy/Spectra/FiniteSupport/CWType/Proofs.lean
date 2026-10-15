module

public import KIP126.Def.StableHomotopy.Spectra.FiniteSupport.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.BasedSpace
open CategoryTheory _root_.Topology
open scoped unitInterval
universe u

/-- A cubical loop in a space of based CW homotopy type is represented, up
to based homotopy, through an actual finite subcomplex of its CW model. -/
theorem genLoop_factor_finite_model_of_hasCWType (X : BasedSpace.{u})
    (hX : X.HasCWType) {r : ℕ} (p : GenLoop (Fin r) X X.point) :
    ∃ (Y : BasedSpace.{u}) (hY : T2Space Y) (cY : CWComplex (Set.univ : Set Y)),
      letI := hY
      letI := cY
      ∃ E : CWComplex.Subcomplex (Set.univ : Set Y),
        CWComplex.Finite (E : Set Y) ∧ ∃ hp : Y.point ∈ E,
          ∃ (q : GenLoop (Fin r) (Y.subspace E hp) (Y.subspace E hp).point)
            (b : Y.subspace E hp ⟶ X),
            GenLoop.Homotopic
              (⟨b.map.comp q.val, fun t ht =>
                (congrArg b.map (q.property t ht)).trans b.point⟩ : GenLoop (Fin r) X X.point) p := by
  obtain ⟨Y,hY,⟨cY⟩,_,f,g,⟨H⟩,_⟩ := hX
  letI := hY
  letI := cY
  let qY : GenLoop (Fin r) Y Y.point :=
    ⟨f.map.comp p.val, fun t ht => (congrArg f.map (p.property t ht)).trans f.point⟩
  obtain ⟨E,hE,hp,q,hq⟩ := genLoop_factor_finite_subcomplex Y qY
  let b : Y.subspace E hp ⟶ X := Y.subspaceInclusion E hp ≫ g
  refine ⟨Y,hY,cY,E,hE,hp,q,b,⟨?_⟩⟩
  exact {
    toFun := fun z => H (z.1,p z.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (p.val.continuous.comp continuous_snd))
    map_zero_left := fun t => (H.apply_zero (p t)).trans
      (congrArg g.map (hq t).symm)
    map_one_left := fun t => H.apply_one (p t)
    prop' := by
      intro s t ht
      change H (s,p t) = g.map (q t).val
      have ht' : p t = X.point := p.property t ht
      rw [ht']
      exact (H.eq_fst s (Set.mem_singleton _)).trans (by
        change g.map (f.map X.point) = g.map (q t).val
        rw [f.point]
        exact congrArg g.map ((congrArg Subtype.val (q.property t ht)).symm)) }

end KIP126.StableHomotopy.Spectra.BasedSpace
