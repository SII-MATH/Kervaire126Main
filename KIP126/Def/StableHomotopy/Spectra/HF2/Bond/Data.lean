module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Simplicial.Proofs
public import Mathlib.Topology.CompactOpen

@[expose] public section

namespace KIP126.StableHomotopy.Spectra
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

namespace HF2Bond

/-- Extend a simplex operator by fixing a new initial vertex. -/
def coneOperator {a b : SimplexCategory} (f : a ⟶ b) :
    ⦋a.len + 1⦌ ⟶ ⦋b.len + 1⦌ :=
  SimplexCategory.Hom.mk
    ⟨Fin.cases 0 (fun i => (f.toOrderHom i).succ), by
      intro i
      induction i using Fin.cases with
      | zero => intro j hij; exact Fin.zero_le _
      | succ i =>
        intro j
        induction j using Fin.cases with
        | zero => intro hij; exact False.elim (by simp at hij)
        | succ j =>
          intro hij
          exact Fin.succ_le_succ_iff.mpr
            (f.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hij))⟩

@[simp] theorem coneOperator_zero {a b : SimplexCategory} (f : a ⟶ b) :
    (coneOperator f).toOrderHom 0 = 0 := rfl

@[simp] theorem coneOperator_succ {a b : SimplexCategory} (f : a ⟶ b)
    (i : Fin (a.len + 1)) :
    (coneOperator f).toOrderHom i.succ = (f.toOrderHom i).succ := rfl

/-- Adjoining an initial vertex as a functor on the simplex category. -/
def coneFunctor : SimplexCategory ⥤ SimplexCategory where
  obj a := ⦋a.len + 1⦌
  map f := coneOperator f
  map_id a := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_comp f g := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- The upper décalage, used as a concrete simplicial path object. -/
def decalage {C : Type*} [Category C] (A : SimplicialObject C) : SimplicialObject C :=
  coneFunctor.op ⋙ A

/-- Delete the newly adjoined initial vertex. -/
def decalageProjection {C : Type*} [Category C] (A : SimplicialObject C) :
    decalage A ⟶ A where
  app a := A.map (SimplexCategory.δ (0 : Fin (a.unop.len + 2))).op
  naturality a b f := by
    dsimp [decalage, coneFunctor]
    rw [← A.map_comp, ← A.map_comp]
    congr 1

/-- The cone coordinate on a geometric simplex. -/
noncomputable def conePoint {n : ℕ} (u : stdSimplex ℝ (Fin (n + 1))) (t : I) :
    stdSimplex ℝ (Fin (n + 2)) :=
  ⟨(1 - (t : ℝ)) • (stdSimplex.vertex (0 : Fin (n + 2)) : Fin (n + 2) → ℝ) +
    (t : ℝ) • (stdSimplex.map Fin.succ u : Fin (n + 2) → ℝ),
    (convex_stdSimplex ℝ _) (stdSimplex.vertex 0).property
      (stdSimplex.map Fin.succ u).property (sub_nonneg.mpr t.property.2)
      t.property.1 (by ring)⟩

@[simp] theorem conePoint_zero {n : ℕ} (u : stdSimplex ℝ (Fin (n + 1))) :
    conePoint u 0 = stdSimplex.vertex 0 := by ext i; simp [conePoint]

@[simp] theorem conePoint_one {n : ℕ} (u : stdSimplex ℝ (Fin (n + 1))) :
    conePoint u 1 = stdSimplex.map Fin.succ u := by apply Subtype.ext; simp [conePoint]; rfl

@[fun_prop] theorem continuous_conePoint (n : ℕ) :
    Continuous (fun p : stdSimplex ℝ (Fin (n + 1)) × I => conePoint p.1 p.2) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub continuous_snd.subtype_val).smul continuous_const).add
    (continuous_snd.subtype_val.smul
      (continuous_subtype_val.comp ((stdSimplex.continuous_map Fin.succ).comp continuous_fst)))

theorem conePoint_naturality {a b : SimplexCategory} (f : a ⟶ b)
    (u : stdSimplex ℝ (Fin (a.len + 1))) (t : I) :
    stdSimplex.map (coneOperator f).toOrderHom (conePoint u t) =
      conePoint (stdSimplex.map f.toOrderHom u) t := by
  apply Subtype.ext
  change FunOnFinite.linearMap ℝ ℝ (coneOperator f).toOrderHom
    ((1 - (t : ℝ)) • _ + (t : ℝ) • _) = _
  rw [map_add, map_smul, map_smul]
  have hv : FunOnFinite.linearMap ℝ ℝ (coneOperator f).toOrderHom
      (stdSimplex.vertex (0 : Fin (a.len + 2)) : Fin (a.len + 2) → ℝ) =
      (stdSimplex.vertex 0 : Fin (b.len + 2) → ℝ) := by
    exact congrArg (fun s : stdSimplex ℝ (Fin (b.len + 2)) => (s : Fin (b.len + 2) → ℝ))
      (stdSimplex.map_vertex (coneOperator f).toOrderHom 0)
  have hs : FunOnFinite.linearMap ℝ ℝ (coneOperator f).toOrderHom
      (stdSimplex.map Fin.succ u : Fin (a.len + 2) → ℝ) =
      (stdSimplex.map Fin.succ (stdSimplex.map f.toOrderHom u) : Fin (b.len + 2) → ℝ) := by
    change (stdSimplex.map (coneOperator f).toOrderHom (stdSimplex.map Fin.succ u) :
      Fin (b.len + 2) → ℝ) = _
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
    rfl
  rw [hv, hs]
  rfl

/-- The characteristic map of a simplex in the geometric realization. -/
noncomputable def realizeSimplex (A : SSet.{0}) {a : SimplexCategoryᵒᵖ}
    (x : A.obj a) : C(stdSimplex ℝ (Fin (a.unop.len + 1)), |A|) :=
  (SSet.toTop.obj A).toSSetObjEquiv a ((sSetTopAdj.unit.app A).app a x)

theorem realizeSimplex_naturality (A : SSet.{0}) {a b : SimplexCategory}
    (f : a ⟶ b) (x : A.obj (op b)) (u : stdSimplex ℝ (Fin (a.len + 1))) :
    realizeSimplex A (A.map f.op x) u = realizeSimplex A x (stdSimplex.map f.toOrderHom u) := by
  have h := ConcreteCategory.congr_hom ((sSetTopAdj.unit.app A).naturality f.op) x
  exact congrArg (fun y => (SSet.toTop.obj A).toSSetObjEquiv (op a) y u) h

/-- The cone on each simplex, regarded as a continuous family of paths. -/
noncomputable def coneSimplex (A : SSet.{0}) (a : SimplexCategoryᵒᵖ)
    (x : (decalage A).obj a) :
    C(stdSimplex ℝ (Fin (a.unop.len + 1)), C(I, |A|)) :=
  (ContinuousMap.comp (realizeSimplex A x)
    ⟨fun p => conePoint p.1 p.2, continuous_conePoint a.unop.len⟩).curry

/-- Simplicial naturality glues the geometric cone maps into the singular
simplicial set of the actual compact-open path space. -/
noncomputable def coneSingularMap (A : SSet.{0}) :
    decalage A ⟶ TopCat.toSSet.obj (TopCat.of C(I, |A|)) where
  app a := ↾fun x => (TopCat.of C(I, |A|)).toSSetObjEquiv a |>.symm (coneSimplex A a x)
  naturality a b f := by
    ext x
    apply ((TopCat.of C(I, |A|)).toSSetObjEquiv b).injective
    ext u t
    change realizeSimplex A (A.map (coneOperator f.unop).op x) (conePoint u t) =
      realizeSimplex A x (conePoint (stdSimplex.map f.unop.toOrderHom u) t)
    rw [realizeSimplex_naturality, conePoint_naturality]
    rfl

/-- A continuous cone evaluation obtained from geometric realization's
adjunction, with no assumed homotopy or realization-product comparison. -/
noncomputable def coneEvaluation (A : SSet.{0}) : C(|decalage A| × I, |A|) :=
  ((sSetTopAdj.homEquiv _ _).symm (coneSingularMap A)).hom.uncurry

/-- Evaluation of the realization adjunction on an actual simplex. -/
theorem adjointMap_realizeSimplex {A : SSet.{0}} {Y : TopCat.{0}}
    (f : A ⟶ TopCat.toSSet.obj Y) (a : SimplexCategoryᵒᵖ)
    (x : A.obj a) (u : stdSimplex ℝ (Fin (a.unop.len + 1))) :
    ((sSetTopAdj.homEquiv _ _).symm f) (realizeSimplex A x u) =
      Y.toSSetObjEquiv a (f.app a x) u := by
  have h := (sSetTopAdj.homEquiv _ _).apply_symm_apply f
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun g : A ⟶ TopCat.toSSet.obj Y => Y.toSSetObjEquiv a (g.app a x) u) h

theorem coneEvaluation_realizeSimplex (A : SSet.{0})
    (a : SimplexCategoryᵒᵖ) (x : (decalage A).obj a)
    (u : stdSimplex ℝ (Fin (a.unop.len + 1))) (t : I) :
    coneEvaluation A (realizeSimplex (decalage A) x u, t) =
      realizeSimplex A x (conePoint u t) := by
  exact congrArg (fun p : C(I, |A|) => p t)
    (adjointMap_realizeSimplex (coneSingularMap A) a x u)

/-- Continuous maps out of realization are determined by their values on simplices. -/
theorem realization_hom_ext {A : SSet.{0}} {Y : TopCat.{0}} (f g : |A| ⟶ Y)
    (h : ∀ (a : SimplexCategoryᵒᵖ) (x : A.obj a)
      (u : stdSimplex ℝ (Fin (a.unop.len + 1))),
      f (realizeSimplex A x u) = g (realizeSimplex A x u)) : f = g := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext a x
  apply (Y.toSSetObjEquiv a).injective
  ext u
  exact h a x u

theorem realizeSimplex_map {A B : SSet.{0}} (f : A ⟶ B)
    (a : SimplexCategoryᵒᵖ) (x : A.obj a)
    (u : stdSimplex ℝ (Fin (a.unop.len + 1))) :
    SSet.toTop.map f (realizeSimplex A x u) = realizeSimplex B (f.app a x) u := by
  have h := congrArg (fun g : A ⟶ TopCat.toSSet.obj (SSet.toTop.obj B) =>
    (SSet.toTop.obj B).toSSetObjEquiv a (g.app a x) u)
    (sSetTopAdj.unit.naturality f)
  exact h.symm

/-- The actual simplicial module of loops is the kernel of the face projection. -/
noncomputable def loopModule (n : ℕ) : SimplicialObject (ModuleCat.{0} (ZMod 2)) :=
  kernel (decalageProjection (hf2SimplicialModule (n + 1)))

/-- The inclusion of those actual simplicial loops into the path object. -/
noncomputable def loopInclusion (n : ℕ) :
    loopModule n ⟶ decalage (hf2SimplicialModule (n + 1)) :=
  kernel.ι (decalageProjection (hf2SimplicialModule (n + 1)))

noncomputable def loopSet (n : ℕ) : SSet.{0} :=
  loopModule n ⋙ forget (ModuleCat (ZMod 2))

noncomputable def loopSetInclusion (n : ℕ) :
    loopSet n ⟶ decalage (hf2SimplicialSet (n + 1)) :=
  Functor.whiskerRight (loopInclusion n) (forget (ModuleCat (ZMod 2)))

/-- A concrete continuous loop of maps from the realization of the simplicial
loop module. Identifying its source with `hf2RealizationLevel n` is a separate
Dold--Kan shift comparison, not part of this definition. -/
noncomputable def loopBond (n : ℕ) : C(|loopSet n| × I, hf2RealizationLevel (n + 1)) :=
  (coneEvaluation (hf2SimplicialSet (n + 1))).comp
    (((SSet.toTop.map (loopSetInclusion n)).hom.comp ContinuousMap.fst).prodMk
      ContinuousMap.snd)

/-- The zero vertex in a realized simplicial module. -/
noncomputable def moduleRealizationPoint (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) :
    |A ⋙ forget (ModuleCat (ZMod 2))| :=
  TopCat.toSSetObj₀Equiv
    ((sSetTopAdj.unit.app (A ⋙ forget (ModuleCat (ZMod 2)))).app (op ⦋0⦌) (0 : A.obj (op ⦋0⦌)))

/-- The based source of the concrete loop bond. -/
noncomputable def loopRealizationLevel (n : ℕ) : BasedSpace.{0} where
  space := |loopSet n|
  point := moduleRealizationPoint (loopModule n)

end HF2Bond
end KIP126.StableHomotopy.Spectra
