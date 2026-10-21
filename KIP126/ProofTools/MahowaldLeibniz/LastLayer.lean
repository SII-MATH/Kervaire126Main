module

import all KIP126.ProofTools.MahowaldLeibniz.Bockstein
import all KIP126.ProofTools.GeneralizedMahowald.FinalDivision
import all KIP126.ProofTools.GeneralizedMahowald.FTransportLambda
import KIP126.ProofTools.MahowaldLeibniz

/-! Actual highest-layer maps and the terminal normalized-map condition.
The lambda map, first-quotient labels and normalized map are those of the
selected model. Classical boundary membership is converted to vanishing of
an actual highest-layer representative. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

private def oneQuotientCast (A : SyntheticSpectrum) (n : ℕ) (hn : n=1)
    (m w : ℤ) (a : BiHom m w (XModLambdaN A 1)) :
    BiHom m w (XModLambdaN A n) := hn.symm ▸ a

private def oneInclusionCast (A B : SyntheticSpectrum) (d n : ℕ) (hn : n=1)
    (l : (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A n) ⟶ B) :
    (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A 1) ⟶ B := hn ▸ l

/-- The selected last-layer inclusion, with its source quotient literally Q₁. -/
private def finiteTopInclusion (A : SyntheticSpectrum) (d : ℕ) (hd : 0 < d) :
    (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A 1) ⟶
      XModLambdaN A (d+1) :=
  oneInclusionCast A _ d ((d+1)-d) (by omega)
    ((model.quotients.tower A).triangle hd (Nat.lt_succ_self d)).lambdaMap

/-- A specified first-quotient class inserted into the last finite layer. -/
private def finiteTopOfFirst (A : SyntheticSpectrum) (d : ℕ) (hd : 0 < d)
    (m w : ℤ) (a : BiHom m w (XModLambdaN A 1)) :
    BiHom m (w-d) (XModLambdaN A (d+1)) :=
  homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
    (shiftHomotopyClass (0,-(d:ℤ)) (m,w) a) ≫ finiteTopInclusion A d hd

private theorem finiteTopInclusion_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (d : ℕ) (hd : 0 < d) :
    finiteTopInclusion A d hd ≫ XModLambdaN.map f (d+1) =
      (SyntheticCategory.biShift (0,-(d:ℤ))).map (XModLambdaN.map f 1) ≫
        finiteTopInclusion B d hd := by
  have transport (n : ℕ) (hn : n=1)
      (lA : (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A n) ⟶ XModLambdaN A (d+1))
      (lB : (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN B n) ⟶ XModLambdaN B (d+1))
      (h : lA ≫ XModLambdaN.map f (d+1) =
        (SyntheticCategory.biShift (0,-(d:ℤ))).map (XModLambdaN.map f n) ≫ lB) :
      oneInclusionCast A _ d n hn lA ≫ XModLambdaN.map f (d+1) =
        (SyntheticCategory.biShift (0,-(d:ℤ))).map (XModLambdaN.map f 1) ≫
          oneInclusionCast B _ d n hn lB := by
    subst n
    exact h
  exact transport _ (by omega) _ _
    ((model.quotients.natural f).lambda_naturality hd (Nat.lt_succ_self d)).symm

private theorem finiteTopOfFirst_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (d : ℕ) (hd : 0 < d) (m w : ℤ)
    (a : BiHom m w (XModLambdaN A 1)) :
    finiteTopOfFirst A d hd m w a ≫ XModLambdaN.map f (d+1) =
      finiteTopOfFirst B d hd m w (a ≫ XModLambdaN.map f 1) := by
  unfold finiteTopOfFirst
  rw [Category.assoc,finiteTopInclusion_natural,shift_hom_comp,regrade_comp]
  simp only [Category.assoc]

/-- The top class attached to one specified classical E₂ label. -/
private def finiteTopLabel (X : ClassicalObject) (d : ℕ) (hd : 0 < d)
    (s t : ℤ) (x : Ambient model X (s,t)) :
    BiHom (t-s) (t-d)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (d+1)) :=
  finiteTopOfFirst _ d hd (t-s) t (nativeFirstLabel X s t x)

private theorem finiteTopLabel_detects (X : ClassicalObject) (d : ℕ) (hd : 0 < d)
    (s t : ℤ) (x : Ambient model X (s,t)) :
    Detects (model.convergence (.quotient (d+1) (.nu X))) (s,t,t-d)
      (finiteTargetLabel model X (d+1) s t d x) (finiteTopLabel X d hd s t x) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let a := oneQuotientCast A ((d+1)-d) (by omega) (t-s) t (nativeFirstLabel X s t x)
  have first (n : ℕ) (hn : n=1) (h1 : 1≤n) (z : BiHom (t-s) t (XModLambdaN A 1)) :
      oneQuotientCast A n hn (t-s) t z ≫ (model.quotients.tower A).rho 1 n h1=z := by
    subst n
    simp only [oneQuotientCast,(model.quotients.tower A).rho_id,Category.comp_id]
  have ha := first ((d+1)-d) (by omega) (by omega) (nativeFirstLabel X s t x)
  have h := finite_quotient_lambda_detects X (d+1) d hd (Nat.lt_succ_self d) s t x a ha
  have transport (n : ℕ) (hn : n=1)
      (l : (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A n) ⟶ XModLambdaN A (d+1))
      (z : BiHom (t-s) t (XModLambdaN A 1)) :
      homotopyRegrade (m':=t-s) (w':=t-d) (by simp) (by simp [sub_eq_add_neg])
          (shiftHomotopyClass (0,-(d:ℤ)) (t-s,t) z) ≫ oneInclusionCast A _ d n hn l =
        homotopyRegrade (m':=t-s) (w':=t-d) (by simp) (by simp [sub_eq_add_neg])
          (shiftHomotopyClass (0,-(d:ℤ)) (t-s,t) (oneQuotientCast A n hn (t-s) t z)) ≫ l := by
    subst n
    rfl
  have heq : finiteTopLabel X d hd s t x = finiteLambdaClass X (d+1) d hd (Nat.lt_succ_self d) s t a :=
    transport _ (by omega) _ _
  rw [heq]
  exact h

private theorem finiteTopLabel_zero_iff_boundary (X : ClassicalObject)
    (d : ℕ) (hd : 0 < d) (s t : ℤ) (x : Ambient model X (s,t)) :
    finiteTopLabel X d hd s t x = 0 ↔ x ∈ boundaries model X (d+1) (s,t) := by
  have h := finite_top_detected_zero_iff_boundary X (d+1) (by omega) s t x
  simpa only [Nat.cast_add,Nat.cast_one] using
    h (finiteTopLabel X d hd s t x) (finiteTopLabel_detects X d hd s t x)

/-- Every actual class in the last nonzero filtration has a specified top label. -/
private theorem finiteTopLabel_exists (X : ClassicalObject) (d : ℕ) (hd : 0<d)
    (s t : ℤ)
    (a : BiHom (t-s) (t-d) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (d+1)))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    ∃ x : Ambient model X (s,t), a=finiteTopLabel X d hd s t x := by
  obtain ⟨x,_,hx⟩ := finite_filtered_target_label X (d+1) (by omega) s t (t-d) (by omega) a ha
  have hlabel : nuWeightLabel model X s t (t-d) (by omega) x = targetNuLabel model X s t d x := by
    have hd' : (t-(t-d)).toNat=d := by omega
    have transport (a b : ℕ) (hab : a=b) (h : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 h (targetNuLabel model X s t a x) = targetNuLabel model X s t b x := by
      subst b
      rfl
    exact transport _ d hd' _
  rw [hlabel] at hx
  exact ⟨x,finite_top_detection_unique X (d+1) (by omega) s t (t-d) (by omega)
    _ a _ hx (finiteTopLabel_detects X d hd s t x)⟩

private theorem nativeFirstLabel_of_firstQuotient (X : ClassicalObject) (s t : ℤ)
    (a : BiHom (t-s) (t+0) (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) 1)) :
    nativeFirstLabel X s t ((model.firstQuotient X 0 s t) a) =
      homotopyRegrade rfl (by omega) a ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  unfold nativeFirstLabel firstLabel
  rw [LinearEquiv.symm_apply_apply]
  congr 1
  have cast (m w w' : ℤ) (h : w=w') (A : SyntheticSpectrum) (a : BiHom m w A) :
      (congrArg (fun v => BiHom m v A) h).mp a=homotopyRegrade rfl h a := by
    subst w'; rfl
  exact cast _ _ _ _ _ _

private def lastLayerNormalizedMap (T : TriangleData model.auxiliary)
    (hef : normalizedExponent model.classicalTower T.f = 1) :
    (SyntheticCategory.biShift (0,1)).obj (model.nu.functor.obj (T.X.obj model.auxiliary)) ⟶
      model.nu.functor.obj (T.Y.obj model.auxiliary) := by
  simpa only [hef,Nat.cast_one] using (model.normalizedMap T.X T.Y T.f).map

/-- The fixed normalized Q₁-map has exactly the advertised classical boundary label. -/
private theorem normalizedFirstMap_boundary (T : TriangleData model.auxiliary)
    (hef : normalizedExponent model.classicalTower T.f = 1) (s t : ℤ)
    (x : Ambient model T.X (s,t)) :
    homotopyRegrade (m':=(t+1)-(s+1)) (w':=t+1) (by omega) rfl
      ((model.firstQuotient T.X 1 s t).symm x ≫ XModLambdaN.map (lastLayerNormalizedMap T hef) 1) =
    nativeFirstLabel T.Y (s+1) (t+1) (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hef s t x) := by
  unfold KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary
  rw [nativeFirstLabel_of_firstQuotient]
  simp only [regrade_comp,Category.assoc]
  rw [←model.quotients.functoriality.map_comp,Iso.inv_hom_id_app,
    model.quotients.functoriality.map_id]
  dsimp only [Functor.id_obj]
  rw [Category.comp_id]
  have trans {m₁ m₂ m₃ w₁ w₂ w₃ : ℤ} {A : SyntheticSpectrum}
      (hm₁ : m₁=m₂) (hm₂ : m₂=m₃) (hw₁ : w₁=w₂) (hw₂ : w₂=w₃) (a : BiHom m₁ w₁ A) :
      homotopyRegrade hm₂ hw₂ (homotopyRegrade hm₁ hw₁ a)=
        homotopyRegrade (hm₁.trans hm₂) (hw₁.trans hw₂) a := by
    subst m₂; subst m₃; subst w₂; subst w₃; rfl
  rw [trans]
  rfl

private theorem finiteTopOfFirst_regrade (A : SyntheticSpectrum) (d : ℕ) (hd : 0<d)
    (m m' w w' : ℤ) (hm : m=m') (hw : w=w')
    (a : BiHom m w (XModLambdaN A 1)) :
    homotopyRegrade hm (show w-d=w'-d by omega) (finiteTopOfFirst A d hd m w a) =
      finiteTopOfFirst A d hd m' w' (homotopyRegrade hm hw a) := by
  subst m'; subst w'; rfl

/-- The entire first-quotient NC2 hypothesis kills every actual normalized
map image of a last-layer class; the classical operation is fixed by T.f. -/
private theorem normalizedFirstMap_top_zero (T : TriangleData model.auxiliary)
    (hef : normalizedExponent model.classicalTower T.f = 1)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (hNC2 : ∀ x : Ambient model T.X (s,t),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hef s t x ∈
        boundaries model T.Y (d+1) (s+1,t+1))
    (a : BiHom (t-s) (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) 1)) :
    finiteTopOfFirst _ d hd (t-s) (t+1) a ≫
      XModLambdaN.map (lastLayerNormalizedMap T hef) (d+1) = 0 := by
  let x := (model.firstQuotient T.X 1 s t) a
  have hfirst := normalizedFirstMap_boundary T hef s t x
  dsimp only [x] at hfirst
  rw [LinearEquiv.symm_apply_apply] at hfirst
  rw [finiteTopOfFirst_natural]
  have hh := congrArg (finiteTopOfFirst _ d hd ((t+1)-(s+1)) (t+1)) hfirst
  rw [←finiteTopOfFirst_regrade] at hh
  have hzero := (finiteTopLabel_zero_iff_boundary T.Y d hd (s+1) (t+1) _).mpr (hNC2 x)
  change _ = finiteTopLabel T.Y d hd (s+1) (t+1) _ at hh
  rw [hzero] at hh
  have hh' := congrArg (homotopyRegrade (show (t+1)-(s+1)=t-s by omega) (rfl : t+1-d=t+1-d)) hh
  have regrade_zero {m m' w w' : ℤ} {A : SyntheticSpectrum} (hm : m=m') (hw : w=w') :
      homotopyRegrade hm hw (0 : BiHom m w A)=0 := by
    subst m'; subst w'; rfl
  simpa only [homotopy_regrade_inverse,regrade_zero] using hh'

private def oneQuotientUncast (A : SyntheticSpectrum) (n : ℕ) (hn : n=1)
    (m w : ℤ) (a : BiHom m w (XModLambdaN A n)) :
    BiHom m w (XModLambdaN A 1) := hn ▸ a

private theorem finiteTopOfFirst_eq_raw (A : SyntheticSpectrum) (d : ℕ) (hd : 0<d)
    (m w : ℤ) (a : BiHom m w (XModLambdaN A 1)) :
    finiteTopOfFirst A d hd m w a =
      homotopyRegrade (m':=m) (w':=w-d) (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(d:ℤ)) (m,w)
          (oneQuotientCast A ((d+1)-d) (by omega) m w a)) ≫
        ((model.quotients.tower A).triangle hd (Nat.lt_succ_self d)).lambdaMap := by
  have transport (n : ℕ) (hn : n=1)
      (l : (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A n) ⟶ XModLambdaN A (d+1)) :
      homotopyRegrade (m':=m) (w':=w-d) (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(d:ℤ)) (m,w) a) ≫ oneInclusionCast A _ d n hn l =
      homotopyRegrade (m':=m) (w':=w-d) (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(d:ℤ)) (m,w) (oneQuotientCast A n hn m w a)) ≫ l := by
    subst n
    rfl
  exact transport _ (by omega) _

private theorem raw_eq_finiteTopOfFirst (A : SyntheticSpectrum) (d : ℕ) (hd : 0<d)
    (m w : ℤ) (a : BiHom m w (XModLambdaN A ((d+1)-d))) :
    homotopyRegrade (m':=m) (w':=w-d) (by simp) (by simp [sub_eq_add_neg])
        (shiftHomotopyClass (0,-(d:ℤ)) (m,w) a) ≫
        ((model.quotients.tower A).triangle hd (Nat.lt_succ_self d)).lambdaMap =
      finiteTopOfFirst A d hd m w (oneQuotientUncast A ((d+1)-d) (by omega) m w a) := by
  rw [finiteTopOfFirst_eq_raw]
  have inv (n : ℕ) (hn : n=1) (z : BiHom m w (XModLambdaN A n)) :
      oneQuotientCast A n hn m w (oneQuotientUncast A n hn m w z)=z := by
    subst n; rfl
  rw [inv]

/-- PDF NC2 kills the actual finite normalized map on the whole last
filtration. The only comparison parameter is an actual quotient/shift
isomorphism preserving the quotient inclusion, supplied by the model's
coherence theorem. No graded-action or target-survival premise is added. -/
private theorem normalizedFirstMap_last_layer_zero
    (T : TriangleData model.auxiliary)
    (hef : normalizedExponent model.classicalTower T.f = 1)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (T.X.obj model.auxiliary))) (d+1) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (d+1)))
    (hεq : XModLambdaN.incl _ (d+1) ≫ εq.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (d+1)))
    (hNC2 : ∀ x : Ambient model T.X (s,t),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hef s t x ∈
        boundaries model T.Y (d+1) (s+1,t+1))
    (a : BiHom (t-s) (t-d)
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (d+1)))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    (homotopyRegrade (m':=t-s+0) (w':=t+1-d) (by simp) (by dsimp; omega)
        (shiftHomotopyClass (0,1) (t-s,t-d) a) ≫ εq.inv) ≫
      XModLambdaN.map (lastLayerNormalizedMap T hef) (d+1) = 0 := by
  obtain ⟨x,rfl⟩ := finiteTopLabel_exists T.X d hd s t a ha
  let A := model.nu.functor.obj (T.X.obj model.auxiliary)
  letI := model.exactness.shiftCommShift (0,1)
  letI := model.exactness.shiftExact (0,1)
  obtain ⟨εn,hεn,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) ((d+1)-d) A
  let b := oneQuotientCast A ((d+1)-d) (by omega) (t-s) t (nativeFirstLabel T.X s t x)
  have htop : finiteTopLabel T.X d hd s t x =
      finiteLambdaClass T.X (d+1) d hd (Nat.lt_succ_self d) s t b :=
    finiteTopOfFirst_eq_raw A d hd (t-s) t _
  have hshift := shifted_finite_lambda_class_general T.X (0,1) (d+1) d hd
    (Nat.lt_succ_self d) s t εn εq hεn hεq b
  rw [←htop] at hshift
  have hshift' :
      homotopyRegrade (m':=t-s+0) (w':=t+1-d) (by simp) (by dsimp; omega)
          (shiftHomotopyClass (0,1) (t-s,t-d) (finiteTopLabel T.X d hd s t x)) ≫ εq.inv =
        finiteTopOfFirst _ d hd (t-s+0) (t+1)
          (oneQuotientUncast _ ((d+1)-d) (by omega) (t-s+0) (t+1)
            (shiftHomotopyClass (0,1) (t-s,t) b ≫ εn.inv)) := by
    have hr := raw_eq_finiteTopOfFirst ((SyntheticCategory.biShift (0,1)).obj A) d hd
      (t-s+0) (t+1) (shiftHomotopyClass (0,1) (t-s,t) b ≫ εn.inv)
    exact hshift.trans hr
  rw [hshift']
  have hz := normalizedFirstMap_top_zero T hef d hd s t hNC2
  have transport (m m' : ℤ) (hm : m=m')
      (h : ∀ (b : BiHom m (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj A) 1)),
        finiteTopOfFirst _ d hd m (t+1) b ≫ XModLambdaN.map (lastLayerNormalizedMap T hef) (d+1)=0) :
      ∀ (b : BiHom m' (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj A) 1)),
        finiteTopOfFirst _ d hd m' (t+1) b ≫ XModLambdaN.map (lastLayerNormalizedMap T hef) (d+1)=0 := by
    subst m'
    exact h
  exact transport (t-s) (t-s+0) (by omega) hz _

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
