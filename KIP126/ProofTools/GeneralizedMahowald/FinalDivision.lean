module
import all KIP126.ProofTools.GeneralizedMahowald.TargetSurvival
import all KIP126.ProofTools.GeneralizedMahowald.CumulativeBoundary
import all KIP126.ProofTools.GeneralizedLeibniz.DivisionLabels
import all KIP126.ProofTools.GeneralizedLeibniz.RightEdge

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

private theorem finite_filtered_target_label (X : ClassicalObject)
    (q : ℕ) (hq : 0<q) (s t w : ℤ) (hw : 0≤t-w ∧ t-w<q)
    (b : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hb : FiltrationAtLeast model.syntheticTower s b) :
    ∃ y : Ambient model X (s,t),
      y ∈ cycles model X (q-t+w) (s,t) ∧
      Detects (model.convergence (.quotient q (.nu X))) (s,t,w)
        ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w)
          (nuWeightLabel model X s t w (by omega) y)) b := by
  obtain ⟨br,hbr⟩ := filtration_representative_exists model.syntheticTower _ (t-s,w) s b hb
  let e := ((model.convergence (.quotient q (.nu X))).identification (s,t,w)).inv
    ((model.syntheticTower.filtration _).toAssociatedGraded s (t-s,w) br)
  obtain ⟨y,hy⟩ := CrossingLabels.subquotient_rep
    (cycles model X (q-t+w) (s,t)) (boundaries model X (1+t-w) (s,t))
    (KIP126.Literature.Standard.infinityFiniteWindow X q hq (s,t) w hw e)
  refine ⟨y.val,y.property,e,?_,br,hbr,?_⟩
  · exact (KIP126.Literature.Standard.eInfinity_finite_labels X q hq s t w hw y.val e).mpr
      ⟨y.property,hy.symm⟩
  · exact ((model.convergence (.quotient q (.nu X))).identification (s,t,w)).toLinearEquiv.apply_symm_apply _

private def finiteWeightedLambdaClass (X : ClassicalObject)
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t w : ℤ)
    (b : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-k))) :
    BiHom (t-s) (w-k) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) :=
  homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
    (shiftHomotopyClass (0,-(k:ℤ)) (t-s,w) b) ≫
    ((model.quotients.tower _).triangle hk hkq).lambdaMap

private theorem finite_weighted_lambda_detects (X : ClassicalObject)
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t w : ℤ)
    (hw : 0≤t-w ∧ t-w<(q-k:ℕ))
    (y : Ambient model X (s,t))
    (b : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)))
    (hb : Detects (model.convergence (.quotient (q-k) (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) y)) b) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,w-k)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w-k)
        (nuWeightLabel model X s t (w-k) (by omega) y))
      (finiteWeightedLambdaClass X q k hk hkq s t w b) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let L : ((SyntheticObject.shift (0,-(k:ℤ)) (.quotient (q-k) (.nu X))).obj model.nu model.auxiliary) ⟶
      ((SyntheticObject.quotient q (.nu X)).obj model.nu model.auxiliary) :=
    ((model.quotients.tower A).triangle hk hkq).lambdaMap
  have hs : (s,t,w)=(s,(t-s)+s,w) := by simp
  have hbStem := detects_transport hs _ _ hb
  have hm := shifted_map_detects (.quotient (q-k) (.nu X)) (.quotient q (.nu X))
    (0,-(k:ℤ)) (t-s,w) s L _ b hbStem
  have hp : (s,((t-s,w)+(0,-(k:ℤ))).1+s,((t-s,w)+(0,-(k:ℤ))).2) =
      (s,t,w-k) := by ext <;> simp [sub_eq_add_neg]
  have hm := detects_transport hp _ _ hm
  obtain ⟨e,he,br,hbr,hge⟩ := hm
  obtain ⟨e0,he0,_⟩ := hb
  have heMap := shifted_representative_map (.quotient (q-k) (.nu X)) (.quotient q (.nu X))
    (0,-(k:ℤ)) (t-s,w) s L _ _ (representative_transport hs _ _ he0)
  have heMap := representative_transport hp _ _ heMap
  have heq := he.unique heMap
  have heq' : e = KIP126.Literature.Standard.infinityFiniteLambda X q k hkq (s,t) w e0 := by
    convert heq using 1
    simp only [KIP126.Literature.Standard.infinityFiniteLambda,
      InfinityShiftCoordinates.finiteLambdaMap, show k ≠ 0 by omega, ↓reduceDIte,
      InfinityShiftCoordinates.shift, infinityShift, Iso.trans_hom, ModuleCat.comp_apply,
      eqToIso.hom, KIP126.Literature.Standard.infinityShiftData,
      KIP126.Literature.Standard.infinityShift_comparison]
    rw [infinity_map_regrade L hp]
    rfl
  have hlabel : HasInfinityRepresentative _ 2 (s,t,w-k)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w-k)
        (nuWeightLabel model X s t (w-k) (by omega) y))
      (KIP126.Literature.Standard.infinityFiniteLambda X q k hkq (s,t) w e0) := by
    obtain ⟨hy,hye⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels X (q-k) (by omega)
      s t w hw y e0).mp he0
    apply (KIP126.Literature.Standard.eInfinity_finite_labels X q (by omega)
      s t (w-k) (by omega) y _).mpr
    have hy' : y ∈ cycles model X (q-t+(w-k)) (s,t) := by
      convert hy using 1
      congr 1
      omega
    refine ⟨hy',?_⟩
    rw [KIP126.Literature.Standard.eInfinity_lambda_finite X q k hkq (s,t) w hw,hye]
    rfl
  refine ⟨e,?_,br,?_,hge⟩
  · rw [heq']
    exact hlabel
  · convert hbr using 1
    simp only [finiteWeightedLambdaClass,regrade_precomp,Category.assoc]
    simp only [←Category.assoc,eqToHom_trans]
    rfl

private theorem finite_lambda_target_label_congruent (X : ClassicalObject)
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t w : ℤ)
    (hw : 0≤t-w ∧ t-w<(q-k:ℕ))
    (y : Ambient model X (s,t))
    (b : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)))
    (hb : FiltrationAtLeast model.syntheticTower s b)
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,w-k)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w-k)
        (nuWeightLabel model X s t (w-k) (by omega) y))
      (finiteWeightedLambdaClass X q k hk hkq s t w b)) :
    ∃ y' : Ambient model X (s,t),
      Detects (model.convergence (.quotient (q-k) (.nu X))) (s,t,w)
        ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)).pageMap 2 (s,t,w)
          (nuWeightLabel model X s t w (by omega) y')) b ∧
      y'-y ∈ boundaries model X (1+t-w+k) (s,t) := by
  obtain ⟨y',_,hy'⟩ := finite_filtered_target_label X (q-k) (by omega) s t w hw b hb
  have hl := finite_weighted_lambda_detects X q k hk hkq s t w hw y' b hy'
  refine ⟨y',hy',?_⟩
  have hc := finite_detected_labels_congruent X q (by omega) s t (w-k) (by omega)
    y' y _ hl ha
  convert hc using 1
  congr 1
  omega

private def finiteWeightedLambdaDivisionClass (X : ClassicalObject)
    (q k : ℕ) (hkq : k<q) (s t w : ℤ)
    (b : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-k))) :
    BiHom (t-s) (w-k) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) := by
  by_cases hk : k=0
  · subst k
    exact homotopyRegrade rfl (by simp) b
  · exact finiteWeightedLambdaClass X q k (by omega) hkq s t w b

private theorem finite_lambda_target_label_congruent_uniform (X : ClassicalObject)
    (q k : ℕ) (hkq : k<q) (s t w : ℤ)
    (hw : 0≤t-w ∧ t-w<(q-k:ℕ))
    (y : Ambient model X (s,t))
    (b : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)))
    (hb : FiltrationAtLeast model.syntheticTower s b)
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,w-k)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w-k)
        (nuWeightLabel model X s t (w-k) (by omega) y))
      (finiteWeightedLambdaDivisionClass X q k hkq s t w b)) :
    ∃ y' : Ambient model X (s,t),
      Detects (model.convergence (.quotient (q-k) (.nu X))) (s,t,w)
        ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)).pageMap 2 (s,t,w)
          (nuWeightLabel model X s t w (by omega) y')) b ∧
      y'-y ∈ boundaries model X (1+t-w+k) (s,t) := by
  by_cases hk : k=0
  · subst k
    obtain ⟨y',_,hy'⟩ := finite_filtered_target_label X q hkq s t w hw b hb
    have hy : Detects (model.convergence (.quotient q (.nu X))) (s,t,w)
        ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w)
          (nuWeightLabel model X s t w (by omega) y)) b := by
      have hp : (s,t,w-(0:ℕ))=(s,t,w) := by simp
      have ht := detects_transport hp _ _ ha
      convert ht using 1
      · have transport (v v' : ℤ) (hv : v=v') (hv₁ : v≤t) (hv₂ : v'≤t)
            (h : (s,t,v)=(s,t,v')) :
            regradeE2 h
              ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,v)
                (nuWeightLabel model X s t v hv₁ y)) =
              ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,v')
                (nuWeightLabel model X s t v' hv₂ y)) := by subst v'; rfl
        exact (transport _ w (by simp) _ _ hp).symm
      · simp only [finiteWeightedLambdaDivisionClass,↓reduceDIte]
        have cancel (A : SyntheticSpectrum) (m v v' : ℤ) (hv : v=v') (hv' : v'=v)
            (c : BiHom m v A) :
            homotopyRegrade rfl hv' (homotopyRegrade rfl hv c)=c := by subst v'; rfl
        exact (cancel _ _ _ _ _ _ b).symm
    refine ⟨y',hy',?_⟩
    simpa only [Nat.cast_zero,add_zero] using
      finite_detected_labels_congruent X q hkq s t w hw y' y b hy' hy
  · exact finite_lambda_target_label_congruent X q k (by omega) hkq s t w hw y b hb
      (by simpa only [finiteWeightedLambdaDivisionClass,dif_neg hk] using ha)

/-- The final target and its precise boundary ambiguity, once an actual divided
source with the required target filtration has been constructed. The two
substantive inputs are kept separate: a strict finite f-image and detection of
its actual long-quotient lambda image. No arbitrary May preimage is selected. -/
private theorem final_f_division_target (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q k : ℕ) (hkq : k<q) (n s t : ℤ)
    (hn : (normalizedExponent model.classicalTower f : ℤ)≤n)
    (hw : n-normalizedExponent model.classicalTower f<(q-k:ℕ))
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (af : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      ((SyntheticObject.quotient (q-k) (extensionSourceObject model X Y f)).obj model.nu model.auxiliary))
    (haf : Detects (model.convergence (.quotient (q-k) (extensionSourceObject model X Y f)))
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
      (finiteSourceForExtension model X Y f (q-k) s t x)
      (homotopyRegrade (by dsimp; omega) rfl af))
    (hfil : FiltrationAtLeast model.syntheticTower (s+n)
      (af≫finiteExtensionMap model X Y f (q-k)))
    (hMay : Detects (model.convergence (.quotient q (.nu Y)))
      (s+n,t+n,t+normalizedExponent model.classicalTower f-k)
      ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) q).pageMap 2
        (s+n,t+n,t+normalizedExponent model.classicalTower f-k)
        (nuWeightLabel model Y (s+n) (t+n)
          (t+normalizedExponent model.classicalTower f-k) (by omega) y))
      (finiteWeightedLambdaDivisionClass Y q k hkq (s+n) (t+n)
        (t+normalizedExponent model.classicalTower f)
        (homotopyRegrade (by omega) rfl (af≫finiteExtensionMap model X Y f (q-k))))) :
    ∃ y' : Ambient model Y (s+n,t+n),
      y'-y∈boundaries model Y (1+n-normalizedExponent model.classicalTower f+k) (s+n,t+n) ∧
      ∃ (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
          ((SyntheticObject.quotient (q-k) (extensionSourceObject model X Y f)).obj model.nu model.auxiliary))
        (b : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
          (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) (q-k))),
        Detects (model.convergence (.quotient (q-k) (extensionSourceObject model X Y f)))
          (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
          (finiteSourceForExtension model X Y f (q-k) s t x)
          (homotopyRegrade (by dsimp; omega) rfl a) ∧
        Detects (model.convergence (.quotient (q-k) (.nu Y)))
          (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f)
          (finiteTargetForExtension model X Y f (q-k) n s t hn y')
          (homotopyRegrade (by dsimp; omega) rfl b) ∧
        a≫finiteExtensionMap model X Y f (q-k)=b := by
  let b := af≫finiteExtensionMap model X Y f (q-k)
  let b' := homotopyRegrade (by omega : t-s=(t+n)-(s+n)) rfl b
  have hfil' : FiltrationAtLeast model.syntheticTower (s+n) b' := by
    exact (regrade_filtration_iff _ _ _ _).mpr hfil
  obtain ⟨y',hy',hcong⟩ := finite_lambda_target_label_congruent_uniform Y q k hkq
    (s+n) (t+n) (t+normalizedExponent model.classicalTower f) (by omega)
    y b' hfil' hMay
  refine ⟨y',?_,af,b,haf,?_,rfl⟩
  · convert hcong using 1
    congr 1
    omega
  · have hp : (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f)=
        (s+n,t+n,t+normalizedExponent model.classicalTower f) := by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · dsimp
          omega
        · rfl
    have ht := detects_transport hp.symm _ _ hy'
    have hl := finite_extension_target_weight_label X Y f (q-k) n s t hn y'
    have hregrade {E : SyntheticAdamsSS} {p p' : Tridegree} (h : p=p') (z : E.E₂ p) :
        regradeE2 h.symm (regradeE2 h z)=z := by subst p'; rfl
    rw [←hl,hregrade] at ht
    convert ht using 1
    dsimp only [b']
    simp only [regrade_precomp,←Category.assoc,eqToHom_trans]

private theorem finite_lambda_inclusion (X : ClassicalObject)
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t : ℤ)
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary))) :
    finiteLambdaClass X q k hk hkq s t (a≫XModLambdaN.incl _ (q-k)) =
      lambdaMultiply k a≫XModLambdaN.incl _ q := by
  simp only [finiteLambdaClass,regrade_precomp,shiftHomotopyClass,Functor.map_comp,
    lambdaMultiply,Category.assoc]
  rw [((model.quotients.tower _).triangle hk hkq).lambda_quotient,
    ←Category.assoc ((SyntheticCategory.biShift (0,-(k:ℤ))).map a),lambdaPow_naturality]
  simp only [←Category.assoc]

private theorem finite_lambda_add (X : ClassicalObject)
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t : ℤ)
    (a b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-k))) :
    finiteLambdaClass X q k hk hkq s t (a+b)=
      finiteLambdaClass X q k hk hkq s t a+finiteLambdaClass X q k hk hkq s t b := by
  simp only [finiteLambdaClass,shiftHomotopyClass,Functor.map_add,Preadditive.comp_add,
    Preadditive.add_comp,regrade_precomp]

/-- A boundary torsion lift corrects the divided source's *exact* first label
while preserving its strict lambda image. This does not claim that its f image
retains a prescribed filtration. -/
private theorem finite_divided_source_exact_label (X : ClassicalObject)
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t : ℤ)
    (x x0 : Ambient model X (s,t))
    (b0 : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)))
    (hb0 : b0≫(model.quotients.tower _).rho 1 (q-k) (by omega)=
      firstLabel model X s t x0≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : a≫XModLambdaN.incl _ 1=
      firstLabel model X s t (x-x0)≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (haz : lambdaMultiply k a=0) :
    ∃ b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)),
      b≫(model.quotients.tower _).rho 1 (q-k) (by omega)=
        firstLabel model X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      Detects (model.convergence (.quotient (q-k) (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel model X (q-k) s t 0 x)) b ∧
      finiteLambdaClass X q k hk hkq s t b=finiteLambdaClass X q k hk hkq s t b0 := by
  let b := b0+a≫XModLambdaN.incl _ (q-k)
  have hfirst : b≫(model.quotients.tower _).rho 1 (q-k) (by omega)=
      firstLabel model X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
    dsimp only [b]
    rw [Preadditive.add_comp,hb0,Category.assoc,(model.quotients.tower _).rho_quotient,ha,
      firstLabel_sub,Preadditive.sub_comp]
    abel
  refine ⟨b,hfirst,first_label_detects_unshifted X (q-k) (by omega) s t x b hfirst,?_⟩
  dsimp only [b]
  rw [finite_lambda_add,finite_lambda_inclusion,haz,zero_comp,add_zero]

/-- Positive finite lambda division with the prescribed exact source label.
The boundary ambiguity of an arbitrary preimage is corrected by a torsion
representative, leaving its strict long-quotient lambda image unchanged. -/
private theorem finite_detected_source_division_exact (X : ClassicalObject)
    (q k : ℕ) (hk : 0<k) (hkq : k<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,t-k)
        (nuWeightLabel model X s t (t-k) (by omega) x)) a) :
    ∃ b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)),
      b≫(model.quotients.tower _).rho 1 (q-k) (by omega)=
        firstLabel model X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      Detects (model.convergence (.quotient (q-k) (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel model X (q-k) s t 0 x)) b ∧
      finiteLambdaClass X q k hk hkq s t b=a := by
  obtain ⟨b0,hb0⟩ := finite_detected_source_division X q k hk hkq s t x a ha
  obtain ⟨x0,hx0⟩ := quotient_first_label_exists X (q-k) (by omega) s t b0
  have hb0' : finiteLambdaClass X q k hk hkq s t b0=a :=
    (finiteLambdaClass_vertical X q k hk hkq s t b0).trans hb0
  have hcong := finite_lambda_first_label_congruent X q k hk hkq s t x x0 b0 hx0 a ha hb0'
  obtain ⟨c,hc,hcz⟩ := cumulative_boundary_torsion_lift_unshifted X k s t (x-x0) hcong
  obtain ⟨b,hb,hbd,hbl⟩ := finite_divided_source_exact_label X q k hk hkq s t x x0 b0 hx0 c hc hcz
  exact ⟨b,hb,hbd,hbl.trans hb0'⟩

private theorem finite_detected_bottom_first (X : ClassicalObject)
    (q : ℕ) (hq : 0<q) (s t : ℤ) (x : Ambient model X (s,t))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,t)
        (nuWeightLabel model X s t t (by omega) x)) a) :
    a≫(model.quotients.tower _).rho 1 q hq=
      firstLabel model X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  obtain ⟨x0,hx0⟩ := quotient_first_label_exists X q hq s t a
  have hdet := first_label_detects_unshifted X q hq s t x0 a hx0
  rw [←zero_weight_label X q s t x0] at hdet
  have hc := finite_detected_labels_congruent X q hq s t t (by omega) x x0 a ha hdet
  have he : x=x0 := by simpa only [add_sub_cancel_right,boundaries_one,Submodule.mem_bot,sub_eq_zero] using hc
  simpa only [he] using hx0

private theorem finite_detected_source_division_exact_uniform (X : ClassicalObject)
    (q k : ℕ) (hkq : k<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,t-k)
        (nuWeightLabel model X s t (t-k) (by omega) x)) a) :
    ∃ b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)),
      b≫(model.quotients.tower _).rho 1 (q-k) (by omega)=
        firstLabel model X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      Detects (model.convergence (.quotient (q-k) (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel model X (q-k) s t 0 x)) b ∧
      finiteLambdaDivisionClass X q k hkq s t b=a := by
  by_cases hk : k=0
  · subst k
    let b := homotopyRegrade rfl (by simp : t-(0:ℕ)=t) a
    have hp : (s,t,t-(0:ℕ))=(s,t,t) := by simp
    have ht := detects_transport hp _ _ ha
    have hbdet : Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
        ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,t)
          (nuWeightLabel model X s t t (by omega) x)) b := by
      convert ht using 1
      · have transport (v v' : ℤ) (hv : v=v') (hv₁ : v≤t) (hv₂ : v'≤t)
            (h : (s,t,v)=(s,t,v')) :
            regradeE2 h
              ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,v)
                (nuWeightLabel model X s t v hv₁ x)) =
              ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,v')
                (nuWeightLabel model X s t v' hv₂ x)) := by subst v'; rfl
        exact (transport _ t (by simp) _ _ hp).symm
    have hbfirst := finite_detected_bottom_first X q hkq s t x b hbdet
    refine ⟨b,hbfirst,first_label_detects_unshifted X q hkq s t x b hbfirst,?_⟩
    simp only [finiteLambdaDivisionClass,↓reduceDIte,b]
    have cancel (A : SyntheticSpectrum) (m v v' : ℤ) (hv : v=v') (hv' : v'=v)
        (c : BiHom m v A) :
        homotopyRegrade rfl hv' (homotopyRegrade rfl hv c)=c := by subst v'; rfl
    exact cancel _ _ _ _ _ _ a
  · obtain ⟨b,hb,hbd,hbl⟩ := finite_detected_source_division_exact X q k (by omega) hkq s t x a ha
    refine ⟨b,hb,hbd,?_⟩
    simpa only [finiteLambdaDivisionClass,dif_neg hk] using hbl

private theorem finite_target_source_division_exact (X : ClassicalObject)
    (q k : ℕ) (hkq : k<q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X q s t k x) a) :
    ∃ b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)),
      b≫(model.quotients.tower _).rho 1 (q-k) (by omega)=
        firstLabel model X s t x≫XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      Detects (model.convergence (.quotient (q-k) (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel model X (q-k) s t 0 x)) b ∧
      finiteLambdaDivisionClass X q k hkq s t b=a := by
  have hlabel : nuWeightLabel model X s t (t-k) (by omega) x =
      targetNuLabel model X s t k x := by
    have hk' : (t-(t-k)).toNat=k := by omega
    have transport (a b : ℕ) (hab : a=b)
        (h : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 h (targetNuLabel model X s t a x) = targetNuLabel model X s t b x := by
      subst b
      rfl
    exact transport _ k hk' _
  apply finite_detected_source_division_exact_uniform X q k hkq s t x a
  rw [hlabel]
  exact ha

end
end KIP126.ProofTools.Internal.Mahowald
