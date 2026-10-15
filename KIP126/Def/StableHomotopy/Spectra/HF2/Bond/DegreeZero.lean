module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Comparison

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The actual constant simplicial coefficient module. -/
abbrev constantCoefficientModule : SimplicialObject (ModuleCat.{0} (ZMod 2)) :=
  (Functor.const SimplexCategoryᵒᵖ).obj (ModuleCat.of (ZMod 2) (ZMod 2))

/-- Positive normalized degrees of the constant module vanish because a
higher face is the identity. -/
theorem constantCoefficient_normalized_isZero (r : ℕ) :
    IsZero (((normalizedMooreComplex (ModuleCat (ZMod 2))).obj constantCoefficientModule).X
      (r + 1)) := by
  have h := normalized_arrow_δ_succ constantCoefficientModule r (0 : Fin (r + 1))
  change (NormalizedMooreComplex.objX constantCoefficientModule (r + 1)).arrow ≫ 𝟙 _ = 0 at h
  rw [Category.comp_id] at h
  exact (IsZero.iff_id_eq_zero _).mpr (by
    apply (cancel_mono (NormalizedMooreComplex.objX constantCoefficientModule (r + 1)).arrow).mp
    rw [Category.id_comp, zero_comp, h])

instance constantCoefficient_normalized_zero_arrow_isIso :
    IsIso (NormalizedMooreComplex.objX constantCoefficientModule 0).arrow := by
  change IsIso (⊤ : Subobject (ModuleCat.of (ZMod 2) (ZMod 2))).arrow
  infer_instance

/-- The fixed coefficient generator gives the normalized constant complex. -/
noncomputable def constantCoefficientChainMap : hf2ChainComplex 0 ⟶
    (normalizedMooreComplex (ModuleCat (ZMod 2))).obj constantCoefficientModule :=
  HomologicalComplex.mkHomFromSingle (inv (NormalizedMooreComplex.objX constantCoefficientModule 0).arrow)
    (by intro k hk; change k + 1 = 0 at hk; omega)

instance constantCoefficientChainMap_isIso : IsIso constantCoefficientChainMap := by
  haveI (r : ℕ) : IsIso (constantCoefficientChainMap.f r) := by
    cases r with
    | zero =>
      dsimp only [constantCoefficientChainMap]
      rw [HomologicalComplex.mkHomFromSingle_f]
      infer_instance
    | succ r =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
        (ModuleCat.of (ZMod 2) (ZMod 2)) (r + 1) (by omega)).isIso
          (constantCoefficient_normalized_isZero r) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The actual degree-zero Dold--Kan coefficient object is isomorphic to the
constant simplicial module, through its specified normalized generator. -/
noncomputable def coefficientZeroConstantIso : hf2SimplicialModule 0 ≅ constantCoefficientModule :=
  CategoryTheory.Abelian.DoldKan.Γ.mapIso (asIso constantCoefficientChainMap) ≪≫
    (CategoryTheory.Abelian.DoldKan.equivalence.unitIso.app constantCoefficientModule).symm

/-- The constant simplicial set on an actual type. -/
abbrev constantSet (T : Type) : SSet.{0} := (Functor.const SimplexCategoryᵒᵖ).obj T

/-- A constant simplex is the actual constant singular simplex of the
discrete topological space. -/
noncomputable def constantToSingularDiscrete (T : Type) :
    constantSet T ⟶ TopCat.toSSet.obj (TopCat.discrete.obj T) where
  app a := ↾fun x => ((TopCat.discrete.obj T).toSSetObjEquiv a).symm (ContinuousMap.const _ x)
  naturality a b f := by
    ext x
    apply ((TopCat.discrete.obj T).toSSetObjEquiv b).injective
    rfl

/-- The concrete map from the realization of a constant simplicial set to
the discrete space, obtained from its constant singular simplices. -/
noncomputable def constantRealizationMap (T : Type) :
    C(|constantSet T|, TopCat.discrete.obj T) :=
  ((sSetTopAdj.homEquiv _ _).symm (constantToSingularDiscrete T)).hom

/-- Evaluation on every realized simplex returns its constant label. -/
theorem constantRealizationMap_simplex (T : Type) (a : SimplexCategoryᵒᵖ)
    (x : (constantSet T).obj a) (u : stdSimplex ℝ (Fin (a.unop.len + 1))) :
    constantRealizationMap T (realizeSimplex (constantSet T) x u) = x := by
  exact adjointMap_realizeSimplex (constantToSingularDiscrete T) a x u

/-- A realized constant simplex is the vertex with the same label. -/
theorem constantRealizeSimplex_vertex (T : Type) (a : SimplexCategoryᵒᵖ)
    (x : (constantSet T).obj a) (u : stdSimplex ℝ (Fin (a.unop.len + 1))) :
    realizeSimplex (constantSet T) x u =
      realizeSimplex (constantSet T) (a := op ⦋0⦌) x default := by
  have h := realizeSimplex_naturality (constantSet T) (SimplexCategory.const a.unop ⦋0⦌ 0) x u
  exact h.trans (congrArg (realizeSimplex (constantSet T) (a := op ⦋0⦌) x)
    (Subsingleton.elim _ _))

/-- Geometric realization of the actual constant simplicial set is the
actual discrete topological space. -/
noncomputable def constantRealizationHomeomorph (T : Type) :
    |constantSet T| ≃ₜ TopCat.discrete.obj T where
  toFun := constantRealizationMap T
  invFun x := realizeSimplex (constantSet T) (a := op ⦋0⦌) x default
  left_inv x := by
    let v : C(TopCat.discrete.obj T, |constantSet T|) :=
      ⟨fun t => realizeSimplex (constantSet T) (a := op ⦋0⦌) t default,
        continuous_of_discreteTopology⟩
    have h : TopCat.ofHom (v.comp (constantRealizationMap T)) = 𝟙 |constantSet T| := by
      apply realization_hom_ext
      intro a z u
      change realizeSimplex (constantSet T) (a := op ⦋0⦌)
        (constantRealizationMap T (realizeSimplex (constantSet T) z u)) default = _
      rw [constantRealizationMap_simplex]
      exact (constantRealizeSimplex_vertex T a z u).symm
    exact ConcreteCategory.congr_hom h x
  right_inv x := constantRealizationMap_simplex T (op ⦋0⦌) x default
  continuous_toFun := (constantRealizationMap T).continuous
  continuous_invFun := continuous_of_discreteTopology

/-- Forgetting the proved degree-zero module isomorphism. -/
noncomputable def coefficientZeroConstantSetIso : hf2SimplicialSet 0 ≅ constantSet (ZMod 2) :=
  ((SimplicialObject.whiskering _ _).obj (forget (ModuleCat (ZMod 2)))).mapIso
    coefficientZeroConstantIso ≪≫ Functor.constComp _ _ _

/-- The actual fixed coefficient space in degree zero is the discrete field
with two elements, through an explicit realization homeomorphism. -/
noncomputable def coefficientZeroRealizationHomeomorph :
    hf2RealizationLevel 0 ≃ₜ TopCat.discrete.obj (ZMod 2) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso coefficientZeroConstantSetIso)).trans
    (constantRealizationHomeomorph (ZMod 2))

@[simp] theorem coefficientZeroRealizationHomeomorph_point :
    coefficientZeroRealizationHomeomorph (hf2RealizationLevel 0).point = (0 : ZMod 2) := by
  change constantRealizationMap (ZMod 2)
    (SSet.toTop.map coefficientZeroConstantSetIso.hom
      (realizeSimplex (hf2SimplicialSet 0) (a := op ⦋0⦌)
        (0 : (hf2SimplicialModule 0).obj (op ⦋0⦌)) default)) = (0 : ZMod 2)
  rw [realizeSimplex_map, constantRealizationMap_simplex]
  exact (coefficientZeroConstantIso.hom.app (op ⦋0⦌)).hom.map_zero

instance coefficientZeroRealization_discrete : DiscreteTopology (hf2RealizationLevel 0) :=
  coefficientZeroRealizationHomeomorph.isEmbedding.discreteTopology

/-- A totally disconnected space has its actual points as its path components. -/
noncomputable def zerothHomotopyEquivOfTotallyDisconnected (X : Type*) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] : ZerothHomotopy X ≃ X where
  toFun := Quotient.lift id (by
    intro x y h
    obtain ⟨p⟩ := h
    exact p.source.symm.trans
      ((TotallyDisconnectedSpace.eq_of_continuous p p.continuous 0 1).trans p.target))
  invFun := ZerothHomotopy.mk
  left_inv x := Quotient.inductionOn x (fun _ => rfl)
  right_inv _ := rfl

/-- The actual cubical π₀ of the fixed degree-zero coefficient space is F₂. -/
noncomputable def coefficientZeroPiZeroEquiv :
    HomotopyGroup.Pi 0 (hf2RealizationLevel 0) (hf2RealizationLevel 0).point ≃ ZMod 2 :=
  (HomotopyGroup.pi0EquivZerothHomotopy).trans
    ((zerothHomotopyEquivOfTotallyDisconnected (hf2RealizationLevel 0)).trans
      coefficientZeroRealizationHomeomorph.toEquiv)

/-- Every positive-dimensional cubical loop in a totally disconnected based
space is the constant loop, as an actual continuous map. -/
theorem cubicalLoop_eq_const_of_totallyDisconnected (X : BasedSpace.{0})
    [TotallyDisconnectedSpace X] (r : ℕ)
    (p : GenLoop (Fin (r + 1)) X X.point) : p = GenLoop.const := by
  apply GenLoop.ext
  intro u
  exact (TotallyDisconnectedSpace.eq_of_continuous p p.val.continuous u 0).trans
    (p.property 0 ⟨0, Or.inl rfl⟩)

/-- All positive cubical homotopy groups of the fixed degree-zero coefficient
space vanish; this follows from its proved discrete topology. -/
theorem coefficientZeroPiPositive_subsingleton (r : ℕ) :
    Subsingleton (HomotopyGroup.Pi (r + 1) (hf2RealizationLevel 0)
      (hf2RealizationLevel 0).point) := by
  refine ⟨fun x y => Quotient.inductionOn₂ x y (fun p q => ?_)⟩
  rw [cubicalLoop_eq_const_of_totallyDisconnected _ r p,
    cubicalLoop_eq_const_of_totallyDisconnected _ r q]

end KIP126.StableHomotopy.Spectra.HF2Bond
