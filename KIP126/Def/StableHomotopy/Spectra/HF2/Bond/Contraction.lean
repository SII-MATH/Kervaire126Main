module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Comparison
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Duplicating the new initial vertex is natural for décalage. -/
theorem coneOperator_σ_zero {a b : SimplexCategory} (f : a ⟶ b) :
    SimplexCategory.σ (0 : Fin (a.len + 2)) ≫ coneOperator f =
      coneOperator (coneOperator f) ≫ SimplexCategory.σ (0 : Fin (b.len + 2)) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  induction j using Fin.cases with
  | zero => rfl
  | succ j =>
    change (coneOperator f).toOrderHom (Fin.predAbove 0 j.succ) =
      Fin.predAbove 0 ((coneOperator (coneOperator f)).toOrderHom j.succ)
    rw [Fin.predAbove_zero_succ, coneOperator_succ, Fin.predAbove_zero_succ]

/-- An actual extra degeneracy lifting the identity into a second décalage. -/
def decalageContractionLift (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) :
    decalage A ⟶ decalage (decalage A) where
  app a := A.map (SimplexCategory.σ (0 : Fin (a.unop.len + 2))).op
  naturality a b f := by
    change A.map (coneOperator f.unop).op ≫ A.map (SimplexCategory.σ 0).op =
      A.map (SimplexCategory.σ 0).op ≫ A.map (coneOperator (coneOperator f.unop)).op
    rw [← A.map_comp, ← A.map_comp]
    congr 1
    exact congrArg Quiver.Hom.op (coneOperator_σ_zero f.unop)

@[reassoc] theorem decalageContractionLift_projection
    (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) :
    decalageContractionLift A ≫ decalageProjection (decalage A) = 𝟙 (decalage A) := by
  apply NatTrans.ext
  funext a
  change A.σ (0 : Fin (a.unop.len + 2)) ≫ (decalage A).δ 0 = 𝟙 _
  rw [decalage_δ]
  exact A.δ_comp_σ_succ (i := 0)

noncomputable def decalageContractionLiftSet (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) :
    decalage (A ⋙ forget (ModuleCat (ZMod 2))) ⟶ decalage (decalage (A ⋙ forget (ModuleCat (ZMod 2)))) :=
  Functor.whiskerRight (decalageContractionLift A)
    (forget (ModuleCat (ZMod 2)))

/-- The actual based realization of the simplicial décalage path object. -/
noncomputable def pathRealizationLevel (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) : BasedSpace.{0} where
  space := |decalage (A ⋙ forget (ModuleCat (ZMod 2)))|
  point := moduleRealizationPoint (decalage A)

/-- A geometric contraction of the décalage realization, constructed from the
actual extra degeneracy and the continuous cone formula. -/
noncomputable def pathContraction (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) :
    C(pathRealizationLevel A × I, pathRealizationLevel A) :=
  (coneEvaluation (decalage (A ⋙ forget (ModuleCat (ZMod 2))))).comp
    (((SSet.toTop.map (decalageContractionLiftSet A)).hom.comp ContinuousMap.fst).prodMk
      ContinuousMap.snd)

theorem pathContraction_one (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) (x : pathRealizationLevel A) :
    pathContraction A (x, 1) = x := by
  change coneEvaluation _ (SSet.toTop.map (decalageContractionLiftSet A) x, 1) = x
  rw [coneEvaluation_one, ← TopCat.comp_app, ← Functor.map_comp]
  have h : decalageContractionLiftSet A ≫
      decalageProjection (decalage (A ⋙ forget (ModuleCat (ZMod 2)))) = 𝟙 _ := by
    exact congrArg (fun f => Functor.whiskerRight f (forget (ModuleCat (ZMod 2))))
      (decalageContractionLift_projection A)
  rw [h]
  exact ConcreteCategory.congr_hom (CategoryTheory.Functor.map_id _ _) x

theorem decalageContractionLift_initial_vertex
    (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) [Subsingleton (A.obj (op ⦋0⦌))]
    (a : SimplexCategoryᵒᵖ) (x : (decalage A).obj a) :
    (decalage A).map (SimplexCategory.const ⦋0⦌ ⦋a.unop.len + 1⦌ 0).op
      ((decalageContractionLift A).app a x) = 0 := by
  have hm : coneOperator (SimplexCategory.const ⦋0⦌ ⦋a.unop.len + 1⦌ 0) ≫
      SimplexCategory.σ (0 : Fin (a.unop.len + 2)) =
      SimplexCategory.σ (0 : Fin 1) ≫
        SimplexCategory.const ⦋0⦌ ⦋a.unop.len + 1⦌ 0 := by
    ext j
    fin_cases j <;> rfl
  change (A.map (coneOperator (SimplexCategory.const ⦋0⦌ ⦋a.unop.len + 1⦌ 0)).op)
    (A.map (SimplexCategory.σ (0 : Fin (a.unop.len + 2))).op x) = 0
  rw [← ConcreteCategory.comp_apply, ← A.map_comp, ← op_comp, hm, op_comp, A.map_comp]
  change (A.σ (0 : Fin 1)) (A.map (SimplexCategory.const ⦋0⦌ ⦋a.unop.len + 1⦌ 0).op x) = 0
  rw [Subsingleton.elim (A.map (SimplexCategory.const ⦋0⦌ ⦋a.unop.len + 1⦌ 0).op x) 0]
  exact (A.σ (0 : Fin 1)).hom.map_zero

theorem pathContraction_zero (A : SimplicialObject (ModuleCat.{0} (ZMod 2)))
    [Subsingleton (A.obj (op ⦋0⦌))] (x : pathRealizationLevel A) :
    pathContraction A (x, 0) = (pathRealizationLevel A).point := by
  let f : |decalage (A ⋙ forget (ModuleCat (ZMod 2)))| ⟶ |decalage (A ⋙ forget (ModuleCat (ZMod 2)))| :=
    TopCat.ofHom ⟨fun x => pathContraction A (x, 0),
      (pathContraction A).continuous.comp (continuous_id.prodMk continuous_const)⟩
  have h : f = TopCat.const (pathRealizationLevel A).point := by
    apply realization_hom_ext
    intro a z u
    change coneEvaluation _ (SSet.toTop.map (decalageContractionLiftSet A)
      (realizeSimplex _ z u), 0) = _
    rw [realizeSimplex_map, coneEvaluation_realizeSimplex, conePoint_zero]
    have hn := realizeSimplex_naturality (decalage (A ⋙ forget (ModuleCat (ZMod 2))))
      (SimplexCategory.const ⦋0⦌ ⦋a.unop.len + 1⦌ 0)
      ((decalageContractionLiftSet A).app a z) (stdSimplex.vertex 0)
    rw [stdSimplex.map_vertex] at hn
    refine hn.symm.trans ?_
    have hz := decalageContractionLift_initial_vertex A a z
    change (decalage (A ⋙ forget (ModuleCat (ZMod 2)))).map
      (SimplexCategory.const ⦋0⦌ ⦋a.unop.len + 1⦌ 0).op
      ((decalageContractionLiftSet A).app a z) =
        (0 : A.obj (op ⦋1⦌)) at hz
    rw [hz]
    exact realizeSimplex_zero (decalage A) (op ⦋0⦌) (stdSimplex.vertex 0)
  exact ConcreteCategory.congr_hom h x

theorem pathContraction_point (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) (t : I) :
    pathContraction A ((pathRealizationLevel A).point, t) = (pathRealizationLevel A).point := by
  change coneEvaluation _ (SSet.toTop.map (decalageContractionLiftSet A)
    (realizeSimplex (decalage (A ⋙ forget (ModuleCat (ZMod 2)))) (a := op ⦋0⦌)
      (0 : A.obj (op ⦋1⦌)) default), t) = _
  rw [realizeSimplex_map, coneEvaluation_realizeSimplex]
  have hz : (decalageContractionLiftSet A).app (op ⦋0⦌)
      (0 : A.obj (op ⦋1⦌)) =
        (0 : A.obj (op ⦋2⦌)) :=
    ((decalageContractionLift A).app (op ⦋0⦌)).hom.map_zero
  rw [hz]
  exact realizeSimplex_zero (decalage A) (op ⦋1⦌) _

/-- The actual realized simplicial path object is contractible. -/
noncomputable def pathContractionHomotopy (A : SimplicialObject (ModuleCat.{0} (ZMod 2)))
    [Subsingleton (A.obj (op ⦋0⦌))] :
    ContinuousMap.Homotopy
      (ContinuousMap.const (pathRealizationLevel A) (pathRealizationLevel A).point)
      (ContinuousMap.id (pathRealizationLevel A)) where
  toFun p := pathContraction A (p.2, p.1)
  continuous_toFun := (pathContraction A).continuous.comp continuous_swap
  map_zero_left := pathContraction_zero A
  map_one_left := pathContraction_one A

end KIP126.StableHomotopy.Spectra.HF2Bond
