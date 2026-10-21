module

import all KIP126.ProofTools.GeneralizedMahowald.FiniteMayAtTriangle
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelSourceLabel
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDelta
import all KIP126.ProofTools.GeneralizedMahowald.RotatedNuTriangle
import all KIP126.ProofTools.MahowaldLeibniz.Filtration
import all KIP126.ProofTools.MahowaldLeibniz.Bockstein

/-!
# A fixed-model finite-quotient comparison for Mahowald--Leibniz

The finite May representative is constructed from the actual normalized
triangle. A second, prescribed representative with the same detected source
has the same image when the actual higher-filtration ambiguity is killed.
This is an internal finite-quotient theorem, not the classical composition
statement: producing its detected inputs and deriving its annihilation
hypothesis from classical page conditions are separate obligations.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- Exponent zero removes the actual negative-target normalization by its
specified unit comparison.  This is a map identity, not an E₂ hypothesis. -/
private theorem negative_lift_zero_comparison {A B : SyntheticSpectrum} {k : ℕ}
    (hk : k=0) (M : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B)
    (g : A ⟶ B) (hM : lambdaToPositivePow k A ≫ M = g) :
    negativeLift k M ≫
      eqToHom (congrArg (fun j : ℕ =>
        (SyntheticCategory.biShift (0,-(j:ℤ))).obj B) hk) ≫
      SyntheticCategory.biShift_zero.hom.app B = g := by
  subst k
  simp only [eqToHom_refl,Category.id_comp]
  have hf := negative_lift_factorization 0 M
  simpa only [lambdaPow] using hf.trans hM

/-- The comparison from the normalized third vertex to the native νZ when
the actual exponent of g is zero. -/
private def normalizedThirdZeroIso
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0) :
    (normalizedTriangle model T he).obj₃ ≅
      model.nu.functor.obj (T.Z.obj model.auxiliary) :=
  eqToIso (congrArg (fun j : ℕ =>
    (SyntheticCategory.biShift (0,-(j:ℤ))).obj
      (model.nu.functor.obj (T.Z.obj model.auxiliary))) hg) ≪≫
    SyntheticCategory.biShift_zero.app _

/-- The literal second normalized arrow is νg after this comparison.
Consequently the ordinary E₂ map is appropriate exactly in this branch. -/
private theorem normalized_second_arrow_zero
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0) :
    (normalizedTriangle model T he).mor₂ ≫
      (normalizedThirdZeroIso T he hg).hom = model.nu.functor.map T.g := by
  exact negative_lift_zero_comparison hg (model.normalizedMap T.Y T.Z T.g).map
    (model.nu.functor.map T.g) (model.normalizedMap T.Y T.Z T.g).factorization

private theorem raw_connecting_one_zero_zero {A C D : SyntheticSpectrum}
    (ef eg eh : ℕ) (he : (ef:ℤ)+eg+eh=1)
    (hf : ef=1) (hg : eg=0) (hh : eh=0)
    (h : (SyntheticCategory.biShift (0,(eh:ℤ))).obj C ⟶ D)
    (σ : D ≅ (SyntheticCategory.biShift (1,1)).obj A)
    (g : C ⟶ D) (hfg : lambdaToPositivePow eh C ≫ h=g) :
    raw_normalized_connecting ef eg eh he h σ ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _ ≫
      (SyntheticCategory.biShift_comp (0,(ef:ℤ)) (1,0)).hom.app A ≫
      eqToHom (congrArg (fun p : ℤ×ℤ => (SyntheticCategory.biShift p).obj A)
        (show (0,(ef:ℤ))+(1,0)=(1,1) by ext <;> dsimp <;> omega)) =
      (zero_negative_iso C eg hg).hom ≫ g ≫ σ.hom := by
  subst ef
  subst eg
  subst eh
  have hh := negative_lift_zero_map_form 0 rfl h g hfg
  dsimp only [raw_normalized_connecting,zero_negative_iso] at hh ⊢
  simp only [eqToHom_refl,eqToIso_refl,Iso.trans_hom,Iso.refl_hom,
    Category.id_comp,Category.comp_id] at hh ⊢
  simp only [Category.assoc,Iso.hom_inv_id_app_assoc]
  have hr := model.quotients.coherence.right_unit (1,1) A
  dsimp only [biShiftAddIso] at hr
  simp only [eqToIso_refl,Iso.trans_refl] at hr
  erw [hr]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  erw [SyntheticCategory.biShift_zero.hom.naturality_assoc]
  simp only [Functor.id_map,Iso.inv_hom_id_app]
  erw [Category.comp_id]
  erw [SyntheticCategory.biShift_zero.hom.naturality]
  simp only [Functor.id_map,←Category.assoc]
  rw [Category.assoc _ (negativeLift 0 h)]
  erw [hh]
  rfl

/-- The actual suspension comparison used when e_f=1.  Both the ordinary
suspension and the positive weight shift are retained in the definition. -/
private def normalizedSuspensionNativeIso
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1) :
    ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) ≅
      model.nu.functor.obj ((ClassicalObject.shift 1 T.X).obj model.auxiliary) :=
  (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
    (SyntheticCategory.biShift_comp
      (0,(normalizedExponent model.classicalTower T.f:ℤ)) (1,0)).app _ ≪≫
    eqToIso (congrArg (fun p : ℤ×ℤ => (SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary)))
      (show (0,(normalizedExponent model.classicalTower T.f:ℤ))+(1,0)=(1,1)
        by ext <;> dsimp <;> omega)) ≪≫
    (model.nu.suspensionIso (T.X.obj model.auxiliary)).symm

/-- Calibrate the selected normalized connecting arrow against the very
same ordinary νh.  The e_f=1,e_g=e_h=0 branch uses the displayed suspension
comparison, rather than identifying those objects definitionally. -/
private theorem normalized_third_arrow_zero
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0) :
    (normalizedTriangle model T he).mor₃ ≫
      (normalizedSuspensionNativeIso T he hf).hom =
      (normalizedThirdZeroIso T he hg).hom ≫ model.nu.functor.map T.h := by
  have h := raw_connecting_one_zero_zero _ _ _ he hf hg hh
    (model.normalizedMap T.Z (.shift 1 T.X) T.h).map
    (model.nu.suspensionIso (T.X.obj model.auxiliary))
    (model.nu.functor.map T.h)
    (model.normalizedMap T.Z (.shift 1 T.X) T.h).factorization
  have h' := congrArg (fun z => z ≫ (model.nu.suspensionIso
    (T.X.obj model.auxiliary)).inv) h
  simpa only [normalizedTriangle,Triangle.mk,normalizedConnecting,
    raw_normalized_connecting,normalizedSuspensionNativeIso,
    normalizedThirdZeroIso,zero_negative_iso,Iso.trans_hom,Iso.symm_hom,
    Iso.app_hom,Iso.app_inv,eqToIso.hom,Category.assoc,Iso.hom_inv_id,
    Category.comp_id] using h'

/-- The actual first quotient coordinates commute strictly with ν of a
classical map.  Detection naturality gives equality modulo the next
filtration, and the one-layer window makes that ambiguity zero. -/
private theorem native_first_label_natural
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (s t : ℤ) (x : Ambient model X (s,t)) :
    nativeFirstLabel X s t x ≫ XModLambdaN.map (model.nu.functor.map f) 1 =
      nativeFirstLabel Y s t ((model.classical.map f).pageMap 2 (s,t) x) := by
  have ha := first_label_detects_unshifted X 1 (by omega) s t x
    (nativeFirstLabel X s t x) (by
      rw [(model.quotients.tower _).rho_id,Category.comp_id]
      rfl)
  have hb := first_label_detects_unshifted Y 1 (by omega) s t
    ((model.classical.map f).pageMap 2 (s,t) x)
    (nativeFirstLabel Y s t ((model.classical.map f).pageMap 2 (s,t) x)) (by
      rw [(model.quotients.tower _).rho_id,Category.comp_id]
      rfl)
  have hm := detects_map (.quotient 1 (.nu X)) (.quotient 1 (.nu Y))
    (XModLambdaN.map (model.nu.functor.map f) 1) (s,t,t) _ _ ha
  rw [←zero_weight_label X 1 s t x] at hm
  erw [finite_weight_label_natural X Y f 1 s t t (by omega) x] at hm
  rw [zero_weight_label Y 1 s t] at hm
  exact finite_top_detection_unique Y 1 (by omega) s t t (by omega) _ _ _ hm hb

private def adjacentDelta (A : SyntheticSpectrum) (q : ℕ) (hq : 0<q) :
    XModLambdaN A q ⟶
      ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
  simpa only [show q.succ-q=1 by omega] using
    ((model.quotients.tower A).triangle hq (Nat.lt_succ_self q)).delta

private theorem adjacent_delta_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (q : ℕ) (hq : 0<q) :
    XModLambdaN.map f q ≫ adjacentDelta B q hq =
      adjacentDelta A q hq ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.map f 1)) := by
  have h := (model.quotients.natural f).delta_naturality hq (Nat.lt_succ_self q)
  have transport (n : ℕ) (hn : n=1)
      (da : XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧)
      (db : XModLambdaN B q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN B n))⟦(1:ℤ)⟧)
      (h : XModLambdaN.map f q ≫ db = da ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.map f n))) :
      XModLambdaN.map f q ≫
        (Eq.mp (congrArg (fun j => XModLambdaN B q ⟶
          ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN B j))⟦(1:ℤ)⟧) hn) db) =
      (Eq.mp (congrArg (fun j => XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A j))⟦(1:ℤ)⟧) hn) da) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.map f 1)) := by
    subst n
    exact h
  exact transport (q.succ-q) (by omega) _ _ h

private theorem homotopy_regrade_injective {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') :
    Function.Injective (homotopyRegrade hm hw (X:=A)) := by
  subst m'
  subst w'
  exact fun _ _ h => h

/-- A prescribed second classical differential produces the exact finite
delta--g square.  In particular its target is the supplied v, including
when its first-quotient image is an earlier classical boundary. -/
private theorem classical_differential_finite_square
    (Y Z : ClassicalObject) (g : Y.obj model.auxiliary ⟶ Z.obj model.auxiliary)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient model Z (s,t)) (v : Ambient model Y (s+q+1,t+q))
    (hd : HasDifferential (model.classical.obj (Z.obj model.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z
      ((model.classical.map g).pageMap 2 (s+q+1,t+q) v)) :
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel Y (s+q+1) (t+q) v))
    ∃ a : BiHom (t-s) t
        (XModLambdaN (model.nu.functor.obj (Z.obj model.auxiliary)) q),
      a ≫ (model.quotients.tower _).rho 1 q hq = nativeFirstLabel Z s t z ∧
      a ≫ adjacentDelta _ q hq =
        b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map
            (XModLambdaN.map (model.nu.functor.map g) 1)) := by
  dsimp only
  obtain ⟨a,ha,hd⟩ := (differential_iff_specified_finite_lift Z q hq s t z
    ((model.classical.map g).pageMap 2 (s+q+1,t+q) v)).mp hd
  refine ⟨a,ha,?_⟩
  apply (biSuspensionHomEquiv (t-s) t (q:ℤ)
    (XModLambdaN (model.nu.functor.obj (Z.obj model.auxiliary)) 1)).injective
  rw [bi_susp_natural model.quotients.coherence,AddEquiv.apply_symm_apply]
  apply homotopy_regrade_injective
    (show (t-s)-1=(t+q)-(s+q+1) by omega) rfl
  rw [regrade_comp,homotopy_regrade_inverse,
    native_first_label_natural Y Z g (s+q+1) (t+q) v]
  simpa only [adjacentFiniteBoundary,adjacentDelta] using hd

/-- The same prescribed classical second differential supplies an actual
finite May representative.  Neither a finite source class nor a signed
target image is assumed: the Bockstein lift and TR3/TR4 construct them. -/
private theorem classical_second_differential_may
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient model T.Z (s,t)) (v : Ambient model T.Y (s+q+1,t+q))
    (hd : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z
      ((model.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (ey : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (q+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1))) :
    let V := normalizedTriangle model T he
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN V.obj₂ 1) ⟶
        XModLambdaN V.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((model.quotients.tower V.obj₂).triangle hq (Nat.lt_succ_self q)).lambdaMap
    ∃ (a : BiHom (t-s) t (XModLambdaN V.obj₃ q))
      (c : BiHom (t-s) t (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (q+1))),
      a ≫ (model.quotients.tower _).rho 1 q hq =
        nativeFirstLabel T.Z s t z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1 ∧
      a ≫ adjacentDelta V.obj₃ q hq =
        b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(q:ℤ))).map (XModLambdaN.map V.mor₂ 1)) ∧
      c ≫ (model.quotients.tower _).rho q (q+1) (by omega) =
        a ≫ XModLambdaN.map V.mor₃ q ∧
      c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (q+1) ≫
        ey.hom = -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly) := by
  dsimp only
  let V := normalizedTriangle model T he
  let E := normalizedThirdZeroIso T he hg
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
    (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1)).symm
      (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
        (nativeFirstLabel T.Y (s+q+1) (t+q) v))
  obtain ⟨a₀,ha₀,hab₀⟩ := classical_differential_finite_square T.Y T.Z T.g q hq s t z v hd
  let a := a₀ ≫ XModLambdaN.map E.inv q
  have hag : model.nu.functor.map T.g ≫ E.inv = V.mor₂ := by
    apply (cancel_mono E.hom).mp
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      (normalized_second_arrow_zero T he hg).symm
  have hab : a ≫ adjacentDelta V.obj₃ q hq =
      b ≫ S.map (F.map (XModLambdaN.map V.mor₂ 1)) := by
    dsimp only [a]
    rw [Category.assoc,adjacent_delta_natural E.inv q hq,←Category.assoc,hab₀]
    simp only [Category.assoc]
    rw [←Functor.map_comp,←Functor.map_comp,
      ←model.quotients.functoriality.map_comp,hag]
  obtain ⟨c,hcr,hcf⟩ := finite_may_at_normalized_triangle_explicit_lengths T he hT q 1 hq
    (by omega) (t-s) t ey hey a b hab
  refine ⟨a,c,?_,hab,hcr,hcf⟩
  dsimp only [a]
  rw [Category.assoc,←(model.quotients.natural E.inv).rho_naturality hq,
    ←Category.assoc,ha₀]

/-- At level zero the May representative has exactly the prescribed
ordinary h₂z first label after the fixed suspension comparison. -/
private theorem finite_may_source_first_label
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (q N : ℕ) (hq : 0<q) (hqN : q≤N) (s t : ℤ)
    (z : Ambient model T.Z (s,t))
    (a : BiHom (t-s) t (XModLambdaN (normalizedTriangle model T he).obj₃ q))
    (c : BiHom (t-s) t
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N))
    (ha : a ≫ (model.quotients.tower _).rho 1 q hq =
      nativeFirstLabel T.Z s t z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hc : c ≫ (model.quotients.tower _).rho q N hqN =
      a ≫ XModLambdaN.map (normalizedTriangle model T he).mor₃ q) :
    (c ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N) ≫
      (model.quotients.tower _).rho 1 N (by omega) =
        nativeFirstLabel (.shift 1 T.X) s t
          ((model.classical.map T.h).pageMap 2 (s,t) z) := by
  let E := normalizedSuspensionNativeIso T he hf
  let EZ := normalizedThirdZeroIso T he hg
  let V := normalizedTriangle model T he
  have hfirst : c ≫ (model.quotients.tower _).rho 1 N (by omega) =
      (nativeFirstLabel T.Z s t z ≫ XModLambdaN.map EZ.inv 1) ≫
        XModLambdaN.map V.mor₃ 1 := by
    rw [←(model.quotients.tower _).rho_comp (show 1≤q by omega) hqN,
      ←Category.assoc,hc,Category.assoc,
      ←(model.quotients.natural V.mor₃).rho_naturality hq,
      ←Category.assoc,ha]
  rw [Category.assoc,←(model.quotients.natural E.hom).rho_naturality (show 1≤N by omega),
    ←Category.assoc,hfirst]
  simp only [Category.assoc]
  rw [←model.quotients.functoriality.map_comp,normalized_third_arrow_zero T he hf hg hh,
    ←model.quotients.functoriality.map_comp]
  simp only [EZ,Category.assoc,Iso.inv_hom_id_assoc]
  exact native_first_label_natural T.Z (.shift 1 T.X) T.h s t z

/-- The actual May source therefore detects h₂z at the bottom finite
layer, and its cycle qualification follows from that same actual lift. -/
private theorem finite_may_source_detects
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (q N : ℕ) (hq : 0<q) (hqN : q≤N) (s t : ℤ)
    (z : Ambient model T.Z (s,t))
    (a : BiHom (t-s) t (XModLambdaN (normalizedTriangle model T he).obj₃ q))
    (c : BiHom (t-s) t
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) N))
    (ha : a ≫ (model.quotients.tower _).rho 1 q hq =
      nativeFirstLabel T.Z s t z ≫ XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1)
    (hc : c ≫ (model.quotients.tower _).rho q N hqN =
      a ≫ XModLambdaN.map (normalizedTriangle model T he).mor₃ q) :
    Detects (model.convergence (.quotient N (.nu (.shift 1 T.X)))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model (.shift 1 T.X) N s t 0
        ((model.classical.map T.h).pageMap 2 (s,t) z)))
      (c ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N) ∧
      IsCycle model (.shift 1 T.X) N (s,t)
        ((model.classical.map T.h).pageMap 2 (s,t) z) := by
  have hfirst := finite_may_source_first_label T he hf hg hh q N hq hqN s t z a c ha hc
  exact ⟨first_label_detects_unshifted (.shift 1 T.X) N (by omega) s t _ _ hfirst,
    specified_adjacent_lift_cycles (.shift 1 T.X) N (by omega) s t _ _ hfirst⟩

/-- Actual finite May comparison with an arbitrary visible source level K.
The same fixed triangle and the same quotient lengths occur throughout.
The May representative is produced by TR3/TR4, not supplied as a premise.
No first-quotient operation or classical differential conclusion is assumed.
-/
private theorem finite_may_image_of_same_source_and_annihilation
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (A B K : ℕ) (hA : 0 < A) (hB : 0 < B) (hKA : K < A)
    (s t : ℤ) (p : ℤ × ℤ)
    (hp : p.1 = t-s+1)
    (hw : p.2 = t+(normalizedExponent model.classicalTower T.f : ℤ)-K)
    (x : Ambient model T.X (s,t))
    (exA : XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) A ≅
      (XModLambdaN (normalizedTriangle model T he).obj₁ A)⟦(1:ℤ)⟧)
    (exN : XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) (A+B) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₁ (A+B))⟦(1:ℤ)⟧)
    (eyN : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (A+B) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (A+B))⟦(1:ℤ)⟧)
    (hexA : XModLambdaN.incl _ A ≫ exA.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ A))
    (hexN : XModLambdaN.incl _ (A+B) ≫ exN.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (A+B)))
    (heyN : XModLambdaN.incl _ (A+B) ≫ eyN.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (A+B)))
    (a : BiHom p.1 p.2 (XModLambdaN (normalizedTriangle model T he).obj₃ A))
    (b : BiHom p.1 p.2
      (((SyntheticCategory.biShift (0,-(A:ℤ))).obj
        (XModLambdaN (normalizedTriangle model T he).obj₂ ((A+B)-A)))⟦(1:ℤ)⟧))
    (d : BiHom p.1 p.2
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) (A+B)))
    (hab : a ≫ ((model.quotients.tower (normalizedTriangle model T he).obj₃).triangle
        hA (show A < A+B by omega)).delta =
      b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(A:ℤ))).map
          (XModLambdaN.map (normalizedTriangle model T he).mor₂ ((A+B)-A))))
    (ha : Detects (model.convergence (.shift (1,0) (.quotient A
        (.shift (0,(normalizedExponent model.classicalTower T.f : ℤ)) (.nu T.X)))))
      (s,p.1+s,p.2)
      (finiteConclusionSourceLabel T.X A K (normalizedExponent model.classicalTower T.f)
        s t p hp hw x)
      (homotopyRegrade (by dsimp; omega) rfl
        (a ≫ XModLambdaN.map (normalizedTriangle model T he).mor₃ A ≫ exA.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)))
    (hd : Detects (model.convergence (.shift (1,0) (.quotient (A+B)
        (.shift (0,(normalizedExponent model.classicalTower T.f : ℤ)) (.nu T.X)))))
      (s,p.1+s,p.2)
      (finiteConclusionSourceLabel T.X (A+B) K (normalizedExponent model.classicalTower T.f)
        s t p hp hw x)
      (homotopyRegrade (by dsimp; omega) rfl
        (d ≫ exN.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)))
    (hkill : ∀ e : BiHom p.1 p.2
        (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) (A+B)),
      FiltrationAtLeast model.syntheticTower (s+1)
        (e ≫ exN.hom ≫ (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _) →
      e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle model T he).mor₁) (A+B) ≫ eyN.hom = 0) :
    x ∈ cycles model T.X ((A+B:ℕ)-K) (s,t) ∧
      d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (normalizedTriangle model T he).mor₁) (A+B) ≫ eyN.hom =
        -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((model.quotients.tower (normalizedTriangle model T he).obj₂).triangle
            hA (show A < A+B by omega)).lambdaMap) := by
  obtain ⟨c,hcr,hcf⟩ := finite_may_at_normalized_triangle T he hT A B hA hB
    p.1 p.2 eyN heyN a b hab
  obtain ⟨hc,hx⟩ := finite_suspended_source_label_reflection T.X
    (normalizedExponent model.classicalTower T.f) A (A+B) K (by omega) hKA
    s t p hp hw x exA exN hexA hexN
    (a ≫ XModLambdaN.map (normalizedTriangle model T he).mor₃ A) c hcr (by
      simpa only [Category.assoc,normalizedTriangle,Triangle.mk,SyntheticObject.obj] using ha)
  refine ⟨?_,?_⟩
  · simpa only [Nat.cast_sub (show K ≤ A+B by omega),Nat.cast_add] using hx
  · have hdiff := detects_sub_filtration
      (model.convergence (.shift (1,0) (.quotient (A+B)
        (.shift (0,(normalizedExponent model.classicalTower T.f : ℤ)) (.nu T.X)))))
      (s,p.1+s,p.2) hd hc
    have hdiff' : FiltrationAtLeast model.syntheticTower (s+1)
        ((d-c) ≫ exN.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _) := by
      apply (regrade_filtration_iff (show p.1 = (p.1+s)-s by omega) rfl (s+1) _).mp
      simpa only [Preadditive.sub_comp,regrade_precomp,Preadditive.comp_sub,
        normalizedTriangle,Triangle.mk,SyntheticObject.obj,Category.assoc] using hdiff
    have hz := hkill (d-c) hdiff'
    simp only [Preadditive.sub_comp] at hz
    exact (sub_eq_zero.mp hz).trans hcf

/-- The existing classical finite-layer condition annihilates the actual
higher-filtration ambiguity of the normalized triangle.  The finite quotient
comparison is used as a map between the selected convergent objects. -/
private theorem finite_layer_surj_normalized_annihilation
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (hT : NormalizedTriangleCompatible model T he)
    (c K : ℕ) (hK : 2≤K) (S V : ℤ)
    (hsurj : KIP126.ProofTools.Standard.MahowaldLeibnizFiniteLayerSurjectivity
      T (c+2) K (S-(c+2:ℕ)) (V-(c+2:ℕ)+1))
    (exQ : XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) (c+K) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₁ (c+K))⟦(1:ℤ)⟧)
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) (c+K)))
    (ha : FiltrationAtLeast model.syntheticTower (S+1)
      (a ≫ exQ.hom ≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) (c+K) = 0 := by
  let N := normalizedTriangle model T he
  let E := normalizedSuspensionNativeIso T he hf
  let EZ := normalizedThirdZeroIso T he hg
  let Source : SyntheticObject := .shift (1,0)
    (.quotient (c+K) (extensionSourceObject model T.X T.Y T.f))
  let Target : SyntheticObject := .quotient (c+K) (.nu (.shift 1 T.X))
  let j : Source.obj model.nu model.auxiliary ⟶ Target.obj model.nu model.auxiliary :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app _ ≫
      exQ.inv ≫ XModLambdaN.map E.hom (c+K)
  have hat : FiltrationAtLeast model.syntheticTower (S+1)
      (a ≫ XModLambdaN.map E.hom (c+K)) := by
    have h := map_preserves_filtration (model.convergentMap Source Target j)
      (V-S+1,V-c+1) (S+1)
      (a ≫ exQ.hom ≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _) ha
    change FiltrationAtLeast model.syntheticTower (S+1)
      ((a ≫ exQ.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app
            (XModLambdaN N.obj₁ (c+K))) ≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app
          (XModLambdaN N.obj₁ (c+K)) ≫ exQ.inv ≫
          XModLambdaN.map E.hom (c+K)) at h
    simpa only [Category.assoc,Iso.inv_hom_id_app_assoc,Iso.hom_inv_id_assoc] using h
  obtain ⟨b,_,hb⟩ := finite_layer_surj_ordinary_h_filtered T c K hK S V hsurj
    (a ≫ XModLambdaN.map E.hom (c+K)) hat
  have hcomm : XModLambdaN.map N.mor₃ (c+K) ≫ XModLambdaN.map E.hom (c+K) =
      XModLambdaN.map EZ.hom (c+K) ≫
        XModLambdaN.map (model.nu.functor.map T.h) (c+K) := by
    rw [←model.quotients.functoriality.map_comp,←model.quotients.functoriality.map_comp]
    exact congrArg (fun f => XModLambdaN.map f (c+K))
      (normalized_third_arrow_zero T he hf hg hh)
  have haq : (b ≫ XModLambdaN.map EZ.inv (c+K)) ≫
      XModLambdaN.map N.mor₃ (c+K) = a := by
    let eQ := (model.quotients.functoriality.functor (c+K)).mapIso E
    apply (cancel_mono eQ.hom).mp
    change _ ≫ XModLambdaN.map E.hom (c+K) = _
    rw [Category.assoc,Category.assoc,hcomm]
    rw [←Category.assoc (XModLambdaN.map EZ.inv (c+K)),
      ←model.quotients.functoriality.map_comp,Iso.inv_hom_id,
      model.quotients.functoriality.map_id,Category.id_comp]
    exact hb
  obtain ⟨ey,_,hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he hT (c+K) (by omega)
  have hzero := comp_distTriang_mor_zero₂₃ _ hrow
  change XModLambdaN.map N.mor₃ (c+K) ≫
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (c+K) ≫
      ey.hom))=0 at hzero
  rw [Preadditive.comp_neg,neg_eq_zero] at hzero
  have hzero' : XModLambdaN.map N.mor₃ (c+K) ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (c+K)=0 := by
    apply (cancel_mono ey.hom).mp
    simpa only [Category.assoc,zero_comp] using hzero
  rw [←haq,Category.assoc,hzero',comp_zero]

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
