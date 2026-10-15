module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Contraction

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The geometric cone evaluation is natural in the simplicial set. -/
theorem coneEvaluation_naturality {A B : SSet.{0}} (f : A ⟶ B)
    (x : |decalage A|) (t : I) :
    SSet.toTop.map f (coneEvaluation A (x, t)) =
      coneEvaluation B (SSet.toTop.map (Functor.whiskerLeft coneFunctor.op f) x, t) := by
  let g : |decalage A| ⟶ TopCat.of C(I, |B|) := TopCat.ofHom
    (((SSet.toTop.map f).hom.comp (coneEvaluation A)).curry)
  let h : |decalage A| ⟶ TopCat.of C(I, |B|) := TopCat.ofHom
    ((coneEvaluation B).curry.comp (SSet.toTop.map (Functor.whiskerLeft coneFunctor.op f)).hom)
  have e : g = h := by
    apply realization_hom_ext
    intro a z u
    ext s
    change SSet.toTop.map f (coneEvaluation A (realizeSimplex (decalage A) z u, s)) =
      coneEvaluation B (SSet.toTop.map (Functor.whiskerLeft coneFunctor.op f)
        (realizeSimplex (decalage A) z u), s)
    calc
      _ = SSet.toTop.map f (realizeSimplex A z (conePoint u s)) :=
        congrArg (SSet.toTop.map f) (coneEvaluation_realizeSimplex A a z u s)
      _ = realizeSimplex B (f.app (coneFunctor.op.obj a) z) (conePoint u s) :=
        realizeSimplex_map f (coneFunctor.op.obj a) z (conePoint u s)
      _ = coneEvaluation B (realizeSimplex (decalage B)
          ((Functor.whiskerLeft coneFunctor.op f).app a z) u, s) :=
        (coneEvaluation_realizeSimplex B a _ u s).symm
      _ = _ := congrArg (fun y => coneEvaluation B (y, s))
        (realizeSimplex_map (show decalage A ⟶ decalage B from
          Functor.whiskerLeft coneFunctor.op f) a z u).symm
  exact congrArg (fun p : C(I, |B|) => p t) (ConcreteCategory.congr_hom e x)

/-- The extra degeneracy also splits the décalage of the endpoint projection. -/
@[reassoc] theorem decalageContractionLift_whisker_projection
    (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) :
    decalageContractionLift A ≫ Functor.whiskerLeft coneFunctor.op
      (decalageProjection A) = 𝟙 (decalage A) := by
  apply NatTrans.ext
  funext a
  change A.σ (0 : Fin (a.unop.len + 2)) ≫ A.δ 0 = 𝟙 _
  exact A.δ_comp_σ_self (i := 0)

/-- Projecting the actual path contraction gives the original cone path. -/
theorem pathContraction_projection
    (A : SimplicialObject (ModuleCat.{0} (ZMod 2)))
    (x : pathRealizationLevel A) (t : I) :
    SSet.toTop.map (decalageProjection (A ⋙ forget (ModuleCat (ZMod 2))))
      (pathContraction A (x, t)) =
        coneEvaluation (A ⋙ forget (ModuleCat (ZMod 2))) (x, t) := by
  change SSet.toTop.map _ (coneEvaluation _
    (SSet.toTop.map (decalageContractionLiftSet A) x, t)) = _
  rw [coneEvaluation_naturality]
  have h : decalageContractionLiftSet A ≫ Functor.whiskerLeft coneFunctor.op
      (decalageProjection (A ⋙ forget (ModuleCat (ZMod 2)))) = 𝟙 _ := by
    exact congrArg (fun f => Functor.whiskerRight f (forget (ModuleCat (ZMod 2))))
      (decalageContractionLift_whisker_projection A)
  have e : SSet.toTop.map (Functor.whiskerLeft coneFunctor.op
      (decalageProjection (A ⋙ forget (ModuleCat (ZMod 2)))))
      (SSet.toTop.map (decalageContractionLiftSet A) x) = x := by
    change (SSet.toTop.map (decalageContractionLiftSet A) ≫
      SSet.toTop.map (Functor.whiskerLeft coneFunctor.op
        (decalageProjection (A ⋙ forget (ModuleCat (ZMod 2)))))) x = x
    rw [← Functor.map_comp, h, CategoryTheory.Functor.map_id]
    rfl
  exact congrArg (fun z => coneEvaluation (A ⋙ forget (ModuleCat (ZMod 2))) (z, t)) e

/-- Continuous based paths, with the subspace compact-open topology. -/
def basedPathSpace (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) :=
  {p : C(I, |A ⋙ forget (ModuleCat (ZMod 2))|) // p 0 = moduleRealizationPoint A}

instance (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) :
    TopologicalSpace (basedPathSpace A) := inferInstanceAs (TopologicalSpace (Subtype _))

/-- The actual geometric path-object comparison. -/
noncomputable def pathComparison (A : SimplicialObject (ModuleCat.{0} (ZMod 2)))
    [Subsingleton (A.obj (op ⦋0⦌))] : C(pathRealizationLevel A, basedPathSpace A) where
  toFun x := ⟨(coneEvaluation (A ⋙ forget (ModuleCat (ZMod 2)))).curry x,
    coneEvaluation_zero A x⟩
  continuous_toFun := (coneEvaluation (A ⋙ forget (ModuleCat (ZMod 2)))).curry.continuous.subtype_mk _

/-- The endpoint of the path comparison is exactly the realized face projection. -/
theorem pathComparison_endpoint (A : SimplicialObject (ModuleCat.{0} (ZMod 2)))
    [Subsingleton (A.obj (op ⦋0⦌))] (x : pathRealizationLevel A) :
    (pathComparison A x).val 1 =
      SSet.toTop.map (decalageProjection (A ⋙ forget (ModuleCat (ZMod 2)))) x :=
  coneEvaluation_one _ x

/-- The actual continuous comparison from realized simplicial loops to the
compact-open space of based topological loops. -/
noncomputable def loopComparison (n : ℕ) :
    C(loopRealizationLevel n,
      Path (hf2RealizationLevel (n + 1)).point (hf2RealizationLevel (n + 1)).point) where
  toFun x :=
    { toContinuousMap := (loopBond n).curry x
      source' := loopBond_zero n x
      target' := loopBond_one n x }
  continuous_toFun := Path.continuous_uncurry_iff.mp (loopBond n).continuous

@[simp] theorem loopComparison_apply (n : ℕ) (x : loopRealizationLevel n) (t : I) :
    loopComparison n x t = loopBond n (x, t) := rfl

@[simp] theorem loopComparison_point (n : ℕ) :
    loopComparison n (loopRealizationLevel n).point =
      Path.refl (hf2RealizationLevel (n + 1)).point := by
  ext t
  exact loopBond_point n t

/-- The topological adjoint of the specified coefficient spectrum structure map. -/
noncomputable def bondAdjoint (n : ℕ) :
    C(hf2RealizationLevel n,
      Path (hf2RealizationLevel (n + 1)).point (hf2RealizationLevel (n + 1)).point) :=
  (loopComparison n).comp ⟨coefficientLoopRealizationHomeomorph n, (coefficientLoopRealizationHomeomorph n).continuous⟩

@[simp] theorem bondAdjoint_apply (n : ℕ) (x : hf2RealizationLevel n) (t : I) :
    bondAdjoint n x t = bond n (x, t) := rfl

@[simp] theorem bondAdjoint_point (n : ℕ) :
    bondAdjoint n (hf2RealizationLevel n).point =
      Path.refl (hf2RealizationLevel (n + 1)).point := by
  ext t
  exact bond_point n t


/-- The geometric cone on the zero simplex is the constant based path. -/
theorem coneEvaluation_point (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) (t : I) :
    coneEvaluation (A ⋙ forget (ModuleCat (ZMod 2)))
      ((pathRealizationLevel A).point, t) = moduleRealizationPoint A := by
  change coneEvaluation _
    (realizeSimplex (decalage (A ⋙ forget (ModuleCat (ZMod 2))))
      (a := op ⦋0⦌) (0 : A.obj (op ⦋1⦌)) default, t) = _
  rw [coneEvaluation_realizeSimplex]
  exact realizeSimplex_zero A (op ⦋1⦌) _

/-- The comparison takes the specified zero vertex to the constant path. -/
theorem pathComparison_point (A : SimplicialObject (ModuleCat.{0} (ZMod 2)))
    [Subsingleton (A.obj (op ⦋0⦌))] :
    pathComparison A (pathRealizationLevel A).point =
      ⟨ContinuousMap.const I (moduleRealizationPoint A), rfl⟩ := by
  apply Subtype.ext
  ext t
  exact coneEvaluation_point A t

/-- The realized inclusion of the actual simplicial loop kernel. -/
noncomputable def loopRealizationInclusion (n : ℕ) :
    C(loopRealizationLevel n, pathRealizationLevel (hf2SimplicialModule (n + 1))) :=
  (SSet.toTop.map (loopSetInclusion n)).hom

@[simp] theorem loopRealizationInclusion_point (n : ℕ) :
    loopRealizationInclusion n (loopRealizationLevel n).point =
      (pathRealizationLevel (hf2SimplicialModule (n + 1))).point := by
  change SSet.toTop.map (loopSetInclusion n)
    (realizeSimplex (loopSet n) (a := op ⦋0⦌) (0 : (loopModule n).obj (op ⦋0⦌)) default) = _
  rw [realizeSimplex_map]
  have hz : (loopSetInclusion n).app (op ⦋0⦌)
      (0 : (loopModule n).obj (op ⦋0⦌)) =
        (0 : (hf2SimplicialModule (n + 1)).obj (op ⦋1⦌)) :=
    ((loopInclusion n).app (op ⦋0⦌)).hom.map_zero
  rw [hz]
  exact realizeSimplex_zero (decalage (hf2SimplicialModule (n + 1))) (op ⦋0⦌) _

/-- The realized endpoint projection annihilates the realized loop inclusion. -/
theorem loopRealizationInclusion_projection (n : ℕ) (x : loopRealizationLevel n) :
    SSet.toTop.map (decalageProjection (hf2SimplicialSet (n + 1)))
      (loopRealizationInclusion n x) = (hf2RealizationLevel (n + 1)).point :=
  (coneEvaluation_one _ _).symm.trans (loopBond_one n x)

/-- On the simplicial kernel, the path comparison is exactly the actual loop
comparison, including its parametrization. -/
theorem pathComparison_loopRealizationInclusion (n : ℕ)
    [Subsingleton ((hf2SimplicialModule (n + 1)).obj (op ⦋0⦌))]
    (x : loopRealizationLevel n) :
    (pathComparison (hf2SimplicialModule (n + 1)) (loopRealizationInclusion n x)).val =
      (loopComparison n x).toContinuousMap := rfl

/-- Contracting a point of the realized simplicial kernel and projecting gives
exactly its specified topological based loop. -/
theorem pathContraction_loop_projection (n : ℕ) (x : loopRealizationLevel n) (t : I) :
    SSet.toTop.map (decalageProjection (hf2SimplicialSet (n + 1)))
      (pathContraction (hf2SimplicialModule (n + 1)) (loopRealizationInclusion n x, t)) =
        loopComparison n x t :=
  pathContraction_projection _ _ t

end KIP126.StableHomotopy.Spectra.HF2Bond
