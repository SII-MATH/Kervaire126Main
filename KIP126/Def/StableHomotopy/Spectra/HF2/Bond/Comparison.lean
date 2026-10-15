module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.ShiftProofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
open CategoryTheory.Preadditive
set_option backward.isDefEq.respectTransparency false

@[simp] theorem coneOperator_δ {r : ℕ} (i : Fin (r + 2)) :
    coneOperator (SimplexCategory.δ i) = SimplexCategory.δ i.succ := by
  ext j
  induction j using Fin.cases with
  | zero => simp [SimplexCategory.δ]
  | succ j => simp [SimplexCategory.δ, Fin.succ_succAbove_succ]

@[simp] theorem decalage_δ (A : SimplicialObject (ModuleCat.{0} (ZMod 2)))
    {r : ℕ} (i : Fin (r + 2)) : (decalage A).δ i = A.δ i.succ := by
  change A.map (coneOperator (SimplexCategory.δ i)).op = _
  rw [coneOperator_δ]
  rfl

theorem normalized_arrow_δ_succ (A : SimplicialObject (ModuleCat.{0} (ZMod 2)))
    (r : ℕ) (i : Fin (r + 1)) :
    (NormalizedMooreComplex.objX A (r + 1)).arrow ≫ A.δ i.succ = 0 :=
  AlgebraicTopology.DoldKan.HigherFacesVanish.inclusionOfMooreComplexMap
    (X := A) r i (by omega)

theorem normalized_d_arrow (A : SimplicialObject (ModuleCat.{0} (ZMod 2))) (r : ℕ) :
    ((normalizedMooreComplex (ModuleCat (ZMod 2))).obj A).d (r + 1) r ≫
      (NormalizedMooreComplex.objX A r).arrow =
        (NormalizedMooreComplex.objX A (r + 1)).arrow ≫ A.δ 0 := by
  rw [normalizedMooreComplex_objD]
  cases r with
  | zero => simp [NormalizedMooreComplex.objD, Category.assoc]
  | succ r => simp only [NormalizedMooreComplex.objD, Subobject.factorThru_arrow]

theorem hf2Normalized_d_eq_zero (n r s : ℕ) :
    ((normalizedMooreComplex (ModuleCat (ZMod 2))).obj (hf2SimplicialModule n)).d r s = 0 := by
  apply (cancel_mono ((hf2NormalizedComplexIso n).hom.f s)).mp
  rw [zero_comp, ← (hf2NormalizedComplexIso n).hom.comm]
  simp only [hf2ChainComplex, HomologicalComplex.single_obj_d, comp_zero]

theorem hf2Normalized_arrow_δ_zero (n r : ℕ) :
    (NormalizedMooreComplex.objX (hf2SimplicialModule n) (r + 1)).arrow ≫
      (hf2SimplicialModule n).δ (0 : Fin (r + 2)) = 0 := by
  rw [← normalized_d_arrow, hf2Normalized_d_eq_zero, zero_comp]

/-- The normalized simplicial loops as actual simplices one degree higher. -/
noncomputable def normalizedLoopArrow (n r : ℕ) :
    ((normalizedMooreComplex (ModuleCat (ZMod 2))).obj (loopModule n)).X r ⟶
      (hf2SimplicialModule (n + 1)).obj (op ⦋r + 1⦌) :=
  (NormalizedMooreComplex.objX (loopModule n) r).arrow ≫
    (loopInclusion n).app (op ⦋r⦌)

@[reassoc] theorem normalizedLoopArrow_δ_zero (n r : ℕ) :
    normalizedLoopArrow n r ≫ (hf2SimplicialModule (n + 1)).δ 0 = 0 := by
  unfold normalizedLoopArrow
  rw [Category.assoc]
  have h := NatTrans.congr_app
    (kernel.condition (decalageProjection (hf2SimplicialModule (n + 1)))) (op ⦋r⦌)
  change (loopInclusion n).app (op ⦋r⦌) ≫
    (hf2SimplicialModule (n + 1)).δ 0 = 0 at h
  rw [h, comp_zero]

@[reassoc] theorem normalizedLoopArrow_δ_succ_succ (n r : ℕ) (i : Fin (r + 1)) :
    normalizedLoopArrow n (r + 1) ≫ (hf2SimplicialModule (n + 1)).δ i.succ.succ = 0 := by
  unfold normalizedLoopArrow
  rw [Category.assoc, ← decalage_δ, ← SimplicialObject.δ_naturality, ← Category.assoc,
    normalized_arrow_δ_succ, zero_comp]

/-- Remove the first-face component by an actual degeneracy correction. -/
noncomputable def correctedNormalizedLoopArrow (n r : ℕ) :
    ((normalizedMooreComplex (ModuleCat (ZMod 2))).obj (loopModule n)).X r ⟶
      (hf2SimplicialModule (n + 1)).obj (op ⦋r + 1⦌) :=
  normalizedLoopArrow n r - normalizedLoopArrow n r ≫
    (hf2SimplicialModule (n + 1)).δ 1 ≫ (hf2SimplicialModule (n + 1)).σ 0

theorem correctedNormalizedLoopArrow_δ_one (n r : ℕ) :
    correctedNormalizedLoopArrow n r ≫ (hf2SimplicialModule (n + 1)).δ 1 = 0 := by
  have h : (hf2SimplicialModule (n + 1)).σ (0 : Fin (r + 1)) ≫
      (hf2SimplicialModule (n + 1)).δ 1 = 𝟙 _ :=
    (hf2SimplicialModule (n + 1)).δ_comp_σ_succ (i := 0)
  simp only [correctedNormalizedLoopArrow, sub_comp, Category.assoc, h,
    Category.comp_id, sub_self]

set_option maxHeartbeats 800000 in
theorem correctedNormalizedLoopArrow_δ_succ_succ (n r : ℕ) (i : Fin (r + 1)) :
    correctedNormalizedLoopArrow n (r + 1) ≫
      (hf2SimplicialModule (n + 1)).δ i.succ.succ = 0 := by
  have hσ : (hf2SimplicialModule (n + 1)).σ (0 : Fin (r + 2)) ≫
      (hf2SimplicialModule (n + 1)).δ i.succ.succ =
      (hf2SimplicialModule (n + 1)).δ i.succ ≫
        (hf2SimplicialModule (n + 1)).σ (0 : Fin (r + 1)) :=
    (hf2SimplicialModule (n + 1)).δ_comp_σ_of_gt (n := r) (i := i.succ) (j := 0)
      (show (0 : Fin (r + 1)).castSucc < i.succ by simp)
  have hδ : (hf2SimplicialModule (n + 1)).δ (1 : Fin (r + 3)) ≫
      (hf2SimplicialModule (n + 1)).δ i.succ =
      (hf2SimplicialModule (n + 1)).δ i.succ.succ ≫
        (hf2SimplicialModule (n + 1)).δ (1 : Fin (r + 2)) :=
    ((hf2SimplicialModule (n + 1)).δ_comp_δ
      (show (1 : Fin (r + 2)) ≤ i.succ from
        Fin.succ_le_succ_iff.mpr (Fin.zero_le i))).symm
  simp only [correctedNormalizedLoopArrow, sub_comp, Category.assoc,
    normalizedLoopArrow_δ_succ_succ, hσ]
  rw [← Category.assoc _ ((hf2SimplicialModule (n + 1)).δ i.succ), hδ]
  simp only [← Category.assoc, normalizedLoopArrow_δ_succ_succ, zero_comp, sub_zero]

theorem correctedNormalizedLoopArrow_normalized (n r : ℕ) :
    (NormalizedMooreComplex.objX (hf2SimplicialModule (n + 1)) (r + 1)).Factors
      (correctedNormalizedLoopArrow n r) := by
  apply (Subobject.finset_inf_factors _).mpr
  intro i hi
  apply kernelSubobject_factors
  cases r with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    exact correctedNormalizedLoopArrow_δ_one n 0
  | succ r =>
    induction i using Fin.cases with
    | zero => exact correctedNormalizedLoopArrow_δ_one n (r + 1)
    | succ i => exact correctedNormalizedLoopArrow_δ_succ_succ n r i

theorem normalizedLoopArrow_δ_one (n r : ℕ) :
    normalizedLoopArrow n r ≫ (hf2SimplicialModule (n + 1)).δ 1 = 0 := by
  have h : correctedNormalizedLoopArrow n r ≫ (hf2SimplicialModule (n + 1)).δ 0 = 0 := by
    rw [← Subobject.factorThru_arrow _ _ (correctedNormalizedLoopArrow_normalized n r),
      Category.assoc, hf2Normalized_arrow_δ_zero, comp_zero]
  have hσ : (hf2SimplicialModule (n + 1)).σ (0 : Fin (r + 1)) ≫
      (hf2SimplicialModule (n + 1)).δ 0 = 𝟙 _ :=
    (hf2SimplicialModule (n + 1)).δ_comp_σ_self (i := 0)
  simpa only [correctedNormalizedLoopArrow, sub_comp, Category.assoc,
    normalizedLoopArrow_δ_zero, hσ, Category.comp_id, zero_sub, neg_eq_zero] using h

theorem normalizedLoopArrow_normalized (n r : ℕ) :
    (NormalizedMooreComplex.objX (hf2SimplicialModule (n + 1)) (r + 1)).Factors
      (normalizedLoopArrow n r) := by
  apply (Subobject.finset_inf_factors _).mpr
  intro i hi
  apply kernelSubobject_factors
  cases r with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    exact normalizedLoopArrow_δ_one n 0
  | succ r =>
    induction i using Fin.cases with
    | zero => exact normalizedLoopArrow_δ_one n (r + 1)
    | succ i => exact normalizedLoopArrow_δ_succ_succ n r i

/-- The actual normalized-loop simplices included into the shifted normalized
coefficient complex. The first-face vanishing was proved using its zero differential. -/
noncomputable def normalizedLoopToShift (n r : ℕ) :
    ((normalizedMooreComplex (ModuleCat (ZMod 2))).obj (loopModule n)).X r ⟶
      ((normalizedMooreComplex (ModuleCat (ZMod 2))).obj (hf2SimplicialModule (n + 1))).X (r + 1) :=
  Subobject.factorThru _ (normalizedLoopArrow n r) (normalizedLoopArrow_normalized n r)

@[reassoc (attr := simp)] theorem normalizedLoopToShift_arrow (n r : ℕ) :
    normalizedLoopToShift n r ≫
      (NormalizedMooreComplex.objX (hf2SimplicialModule (n + 1)) (r + 1)).arrow =
        normalizedLoopArrow n r := Subobject.factorThru_arrow _ _ _

instance normalizedLoopArrow_mono (n r : ℕ) : Mono (normalizedLoopArrow n r) := by
  haveI : Mono (loopInclusion n) := inferInstanceAs
    (Mono (kernel.ι (decalageProjection (hf2SimplicialModule (n + 1)))))
  unfold normalizedLoopArrow
  infer_instance

instance normalizedLoopToShift_mono (n r : ℕ) : Mono (normalizedLoopToShift n r) :=
  mono_of_mono_fac (normalizedLoopToShift_arrow n r)

/-- Normalized loops vanish in all degrees except their coefficient degree. -/
theorem normalizedLoop_isZero_away (n r : ℕ) (hr : r ≠ n) :
    IsZero (((normalizedMooreComplex (ModuleCat (ZMod 2))).obj (loopModule n)).X r) := by
  apply IsZero.of_mono (normalizedLoopToShift n r)
  exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) (n + 1)
    (ModuleCat.of (ZMod 2) (ZMod 2)) (r + 1) (by omega)).of_iso
      ((HomologicalComplex.eval _ _ (r + 1)).mapIso (hf2NormalizedComplexIso (n + 1)))

/-- The normalization isomorphism identifying the actual coefficient generator. -/
noncomputable def normalizedCoefficientIso (n : ℕ) :
    ModuleCat.of (ZMod 2) (ZMod 2) ≅
      ((normalizedMooreComplex (ModuleCat (ZMod 2))).obj (hf2SimplicialModule (n + 1))).X (n + 1) :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) (n + 1)
    (ModuleCat.of (ZMod 2) (ZMod 2))).symm ≪≫
    (HomologicalComplex.eval _ _ (n + 1)).mapIso (hf2NormalizedComplexIso (n + 1)).symm

/-- The chain map used in the bonds sends the coefficient to the actual
specified normalization generator, exactly, before passing to homotopy. -/
@[reassoc] theorem coefficientNormalizedLoop_shift (n : ℕ) :
    coefficientNormalizedLoop n ≫ normalizedLoopToShift n n = (normalizedCoefficientIso n).hom := by
  apply (cancel_mono (NormalizedMooreComplex.objX (hf2SimplicialModule (n + 1)) (n + 1)).arrow).mp
  rw [Category.assoc, normalizedLoopToShift_arrow, normalizedLoopArrow,
    ← Category.assoc, coefficientNormalizedLoop_arrow, coefficientLoop_inclusion]
  rfl

instance coefficientNormalizedLoop_isIso (n : ℕ) : IsIso (coefficientNormalizedLoop n) := by
  refine ⟨⟨normalizedLoopToShift n n ≫ (normalizedCoefficientIso n).inv, ?_, ?_⟩⟩
  · rw [← Category.assoc, coefficientNormalizedLoop_shift, Iso.hom_inv_id]
  · apply (cancel_mono (normalizedLoopToShift n n)).mp
    rw [Category.id_comp, Category.assoc, Category.assoc, coefficientNormalizedLoop_shift,
      Iso.inv_hom_id, Category.comp_id]

instance coefficientLoopChainMap_isIso (n : ℕ) : IsIso (coefficientLoopChainMap n) := by
  haveI (r : ℕ) : IsIso ((coefficientLoopChainMap n).f r) := by
    by_cases hr : r = n
    · subst r
      dsimp only [coefficientLoopChainMap]
      rw [HomologicalComplex.mkHomFromSingle_f]
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) n
        (ModuleCat.of (ZMod 2) (ZMod 2)) r hr).isIso
          (normalizedLoop_isZero_away n r hr) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The simplicial map underlying the actual spectrum bond is the full
Dold--Kan loop comparison isomorphism. -/
instance coefficientToLoop_isIso (n : ℕ) : IsIso (coefficientToLoop n) := by
  unfold coefficientToLoop
  infer_instance

/-- The fixed denormalization is isomorphic to the actual simplicial loop kernel. -/
noncomputable def coefficientLoopIso (n : ℕ) : hf2SimplicialModule n ≅ loopModule n :=
  asIso (coefficientToLoop n)

/-- Geometric realization of the proved simplicial loop comparison. -/
noncomputable def coefficientLoopRealizationHomeomorph (n : ℕ) :
    hf2RealizationLevel n ≃ₜ loopRealizationLevel n :=
  TopCat.homeoOfIso (SSet.toTop.mapIso
    (((SimplicialObject.whiskering _ _).obj (forget (ModuleCat (ZMod 2)))).mapIso
      (coefficientLoopIso n)))

@[simp] theorem coefficientLoopRealizationHomeomorph_point (n : ℕ) :
    coefficientLoopRealizationHomeomorph n (hf2RealizationLevel n).point =
      (loopRealizationLevel n).point := coefficientToLoopSet_point n

end KIP126.StableHomotopy.Spectra.HF2Bond
