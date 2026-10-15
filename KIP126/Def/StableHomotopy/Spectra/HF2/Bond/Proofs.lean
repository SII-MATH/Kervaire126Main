module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Data

@[expose] public section

namespace KIP126.StableHomotopy.Spectra
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

namespace HF2Bond

theorem coneEvaluation_one (A : SSet.{0}) (x : |decalage A|) :
    coneEvaluation A (x, 1) = SSet.toTop.map (decalageProjection A) x := by
  let f : |decalage A| ⟶ |A| := TopCat.ofHom
    ⟨fun x => coneEvaluation A (x, 1), (coneEvaluation A).continuous.comp
      (continuous_id.prodMk continuous_const)⟩
  have h : f = SSet.toTop.map (decalageProjection A) := by
    apply realization_hom_ext
    intro a z u
    change coneEvaluation A (realizeSimplex (decalage A) z u, 1) = _
    rw [coneEvaluation_realizeSimplex, conePoint_one, realizeSimplex_map]
    change _ = realizeSimplex A (A.map (SimplexCategory.δ 0).op z) u
    rw [realizeSimplex_naturality]
    rfl
  exact ConcreteCategory.congr_hom h x

theorem realizeSimplex_zero (A : SimplicialObject (ModuleCat.{0} (ZMod 2)))
    (a : SimplexCategoryᵒᵖ) (u : stdSimplex ℝ (Fin (a.unop.len + 1))) :
    realizeSimplex (A ⋙ forget (ModuleCat (ZMod 2))) (0 : A.obj a) u =
      moduleRealizationPoint A := by
  let f := SimplexCategory.const a.unop ⦋0⦌ 0
  have h := realizeSimplex_naturality (A ⋙ forget (ModuleCat (ZMod 2))) f 0 u
  have hz : (A ⋙ forget (ModuleCat (ZMod 2))).map f.op 0 = 0 := by
    exact (A.map f.op).hom.map_zero
  rw [hz] at h
  exact h.trans (by
    change (realizeSimplex (A ⋙ forget (ModuleCat (ZMod 2))) 0) _ =
      (realizeSimplex (A ⋙ forget (ModuleCat (ZMod 2))) 0) default
    congr 1
    exact Subsingleton.elim _ _)

theorem realizeSimplex_vertex_zero (A : SimplicialObject (ModuleCat.{0} (ZMod 2)))
    [Subsingleton (A.obj (op ⦋0⦌))] (a : SimplexCategory)
    (x : A.obj (op a)) :
    realizeSimplex (A ⋙ forget (ModuleCat (ZMod 2))) x (stdSimplex.vertex 0) =
      moduleRealizationPoint A := by
  have h := realizeSimplex_naturality (A ⋙ forget (ModuleCat (ZMod 2)))
    (SimplexCategory.const ⦋0⦌ a 0) x (stdSimplex.vertex 0)
  rw [stdSimplex.map_vertex] at h
  have hz : (A ⋙ forget (ModuleCat (ZMod 2))).map
      (SimplexCategory.const ⦋0⦌ a 0).op x = 0 := by
    change (A.map (SimplexCategory.const ⦋0⦌ a 0).op) x = 0
    exact Subsingleton.elim _ _
  rw [hz, realizeSimplex_zero] at h
  exact h.symm

theorem coneEvaluation_zero (A : SimplicialObject (ModuleCat.{0} (ZMod 2)))
    [Subsingleton (A.obj (op ⦋0⦌))]
    (x : |decalage (A ⋙ forget (ModuleCat (ZMod 2)))|) :
    coneEvaluation (A ⋙ forget (ModuleCat (ZMod 2))) (x, 0) =
      moduleRealizationPoint A := by
  let f : |decalage (A ⋙ forget (ModuleCat (ZMod 2)))| ⟶
      |A ⋙ forget (ModuleCat (ZMod 2))| := TopCat.ofHom
    ⟨fun x => coneEvaluation (A ⋙ forget (ModuleCat (ZMod 2))) (x, 0),
      (coneEvaluation _).continuous.comp (continuous_id.prodMk continuous_const)⟩
  have h : f = TopCat.const (moduleRealizationPoint A) := by
    apply realization_hom_ext
    intro a z u
    change coneEvaluation _ (realizeSimplex _ z u, 0) = _
    rw [coneEvaluation_realizeSimplex, conePoint_zero]
    exact realizeSimplex_vertex_zero A _ z
  exact ConcreteCategory.congr_hom h x

theorem loopBond_zero (n : ℕ) (x : loopRealizationLevel n) :
    loopBond n (x, 0) = (hf2RealizationLevel (n + 1)).point := by
  letI : Subsingleton ((hf2SimplicialModule (n + 1)).obj (op ⦋0⦌)) :=
    ModuleCat.subsingleton_of_isZero (hf2SimplicialModule_isZero_below
      (n + 1) 0 (Nat.zero_lt_succ n))
  exact coneEvaluation_zero (hf2SimplicialModule (n + 1)) _

theorem loopBond_one (n : ℕ) (x : loopRealizationLevel n) :
    loopBond n (x, 1) = (hf2RealizationLevel (n + 1)).point := by
  let f : |loopSet n| ⟶ |hf2SimplicialSet (n + 1)| := TopCat.ofHom
    ⟨fun x => loopBond n (x, 1), (loopBond n).continuous.comp
      (continuous_id.prodMk continuous_const)⟩
  have h : f = TopCat.const (hf2RealizationLevel (n + 1)).point := by
    apply realization_hom_ext
    intro a z u
    change coneEvaluation _ (SSet.toTop.map (loopSetInclusion n)
      (realizeSimplex (loopSet n) z u), 1) = _
    rw [realizeSimplex_map, coneEvaluation_realizeSimplex, conePoint_one]
    change realizeSimplex _ _ (stdSimplex.map
      (SimplexCategory.δ (0 : Fin (a.unop.len + 2))).toOrderHom u) = _
    have hn := realizeSimplex_naturality (hf2SimplicialSet (n + 1))
      (SimplexCategory.δ (0 : Fin (a.unop.len + 2)))
      ((loopSetInclusion n).app a z) u
    refine hn.symm.trans ?_
    have hz := congrArg (fun g : loopModule n ⟶ hf2SimplicialModule (n + 1) =>
      g.app a z) (kernel.condition (decalageProjection (hf2SimplicialModule (n + 1))))
    change ((hf2SimplicialSet (n + 1)).map (SimplexCategory.δ 0).op)
      ((loopSetInclusion n).app a z) =
        (0 : (hf2SimplicialModule (n + 1)).obj a) at hz
    rw [hz]
    exact realizeSimplex_zero _ _ _
  exact ConcreteCategory.congr_hom h x

theorem loopBond_point (n : ℕ) (t : I) :
    loopBond n ((loopRealizationLevel n).point, t) =
      (hf2RealizationLevel (n + 1)).point := by
  change coneEvaluation _ (SSet.toTop.map (loopSetInclusion n)
    (realizeSimplex (loopSet n) (0 : (loopModule n).obj (op ⦋0⦌)) default), t) = _
  rw [realizeSimplex_map, coneEvaluation_realizeSimplex]
  have hz : (loopSetInclusion n).app (op ⦋0⦌)
      (0 : (loopModule n).obj (op ⦋0⦌)) =
        (0 : (hf2SimplicialModule (n + 1)).obj (op ⦋1⦌)) :=
    ((loopInclusion n).app (op ⦋0⦌)).hom.map_zero
  rw [hz]
  exact realizeSimplex_zero _ _ _

end HF2Bond
end KIP126.StableHomotopy.Spectra
