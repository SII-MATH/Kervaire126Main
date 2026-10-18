module
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingDelta
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingRange

/-! Finite-quotient bounds used in the crossing comparison of AimPaper
Proposition `prop:cross-f-Er`. Actual λ division of a higher-filtration source
forces its normalized image into filtration at least `u + e(f)`. Thus crossing
is impossible at lengths at most `e(f)`; at length at most `e(f) + 1` its
position is forced. The general finite no-crossing conversion is not asserted. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem normalized_finite_source_division (X : ClassicalObject)
    (e : ℤ) (i q : ℕ) (hi : 0 < i) (hiq : i < q) (m w u : ℤ)
    (hs : (i:ℤ) ≤ m+u-(w-e))
    (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : FiltrationAtLeast model.syntheticTower u a) :
    ∃ b : BiHom m w ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
        (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) (q-i))),
      b ≫ ((model.quotients.tower _).triangle hi hiq).lambdaMap = a := by
  let A : SyntheticObject := .shift (0,e) (.nu X)
  let T := (model.quotients.tower (A.obj model.nu model.auxiliary)).triangle hi hiq
  letI := model.exactness.shiftCommShift (0,e)
  letI := model.exactness.shiftExact (0,e)
  obtain ⟨Q,_,_⟩ := quotient_shift_exists model.quotients.coherence (0,e) i
    (model.nu.functor.obj (X.obj model.auxiliary))
  have harho : FiltrationAtLeast model.syntheticTower u (a≫T.rho) :=
    map_preserves_filtration (model.convergentMap (.quotient q A) (.quotient i A) T.rho)
      (m,w) u a ha
  have hQ : FiltrationAtLeast model.syntheticTower u (a≫T.rho≫Q.hom) := by
    change (a≫T.rho≫Q.hom) ∈ model.syntheticTower.filtrationSubmodule
      ((SyntheticObject.shift (0,e) (.quotient i (.nu X))).obj model.nu model.auxiliary) u (m,w)
    simpa only [Category.assoc] using map_preserves_filtration (model.convergentMap (.quotient i A)
      (.shift (0,e) (.quotient i (.nu X))) Q.hom) (m,w) u (a≫T.rho) harho
  have hz := shifted_finite_high_filtration_zero X i hi e m w u hs _ hQ
  have hrho : a≫T.rho=0 := by
    have he := congrArg (fun z => z≫Q.inv) hz
    simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id,zero_comp] using he
  obtain ⟨b,hb⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₂
    T.distinguished a hrho
  exact ⟨b,hb.symm⟩

private theorem shifted_quotient_bottom_filtration (X : ClassicalObject)
    (q : ℕ) (hq : 0 < q) (i m w : ℤ)
    (a : BiHom m w ((SyntheticCategory.biShift (0,i)).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))) :
    FiltrationAtLeast model.syntheticTower (w-m-i) a := by
  let A : SyntheticObject := .shift (0,i) (.quotient q (.nu X))
  let u : ℤ := w-m-i
  have hzero (j : ℤ) (hj : j < u) :
      IsZero (((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (j,m+j,w)).eInfty) := by
    have hz := finite_infinity_zero_outside X q hq j (m+j) (w-i) (by dsimp [u] at hj; omega)
    let e := towerInfinityIso (model.convergence (.quotient q (.nu X))) (model.convergence A)
      ((essShift (0,i)).filtered (.quotient q (.nu X)) (m,w-i)) j
    have he := hz.of_iso e.symm
    simpa only [e,A,Prod.fst_add,Prod.snd_add,add_zero,sub_add_cancel] using he
  have ha0 := filtration_at_zero model.syntheticTower _ m w a
  by_cases hu : u≤0
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) hu ha0
  · exact (filtration_iff_of_infinity_zero (model.convergence A) 0 u m w (by omega)
      (fun j _ hj => hzero j hj) a).mp ha0

/-- Divide the source in the actual finite lambda triangle and carry its
normalized image through the same naturality square. The resulting image
has the bottom filtration of the smaller quotient. No cancellation of lambda
and no reflection of a higher target filtration is asserted here. -/
private theorem normalized_finite_source_image_division (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (s t : ℤ)
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) q))
    (ha : FiltrationAtLeast model.syntheticTower (s+i) a) :
    ∃ b : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
        ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
          (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) (q-i))),
      b ≫ ((model.quotients.tower _).triangle hi hiq).lambdaMap = a ∧
      (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
        (finiteExtensionMap model X Y f (q-i))) ≫
          ((model.quotients.tower _).triangle hi hiq).lambdaMap =
        a ≫ finiteExtensionMap model X Y f q ∧
      FiltrationAtLeast model.syntheticTower (s+i+normalizedExponent model.classicalTower f)
        (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
          (finiteExtensionMap model X Y f (q-i))) := by
  let e : ℤ := normalizedExponent model.classicalTower f
  let A := (extensionSourceObject model X Y f).obj model.nu model.auxiliary
  let B := model.nu.functor.obj (Y.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let Ta := (model.quotients.tower A).triangle hi hiq
  let Tb := (model.quotients.tower B).triangle hi hiq
  obtain ⟨b,hb⟩ := normalized_finite_source_division X e i q hi hiq (t-s) (t+e) (s+i)
    (by omega) a ha
  let c := b≫F.map (finiteExtensionMap model X Y f (q-i))
  have hc : FiltrationAtLeast model.syntheticTower (s+i+e) c := by
    have h := shifted_quotient_bottom_filtration Y (q-i) (by omega) (-(i:ℤ)) (t-s) (t+e) c
    convert h using 1; omega
  have hcomm := (model.quotients.natural (model.normalizedMap X Y f).map).lambda_naturality hi hiq
  change F.map (finiteExtensionMap model X Y f (q-i))≫Tb.lambdaMap =
    Ta.lambdaMap≫finiteExtensionMap model X Y f q at hcomm
  change b≫Ta.lambdaMap=a at hb
  have he : c≫Tb.lambdaMap=a≫finiteExtensionMap model X Y f q := by
    dsimp only [c]
    rw [Category.assoc,hcomm,←Category.assoc,hb]
  exact ⟨b,hb,he,hc⟩

private theorem finite_normalized_image_filtration (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (s t : ℤ)
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) q))
    (ha : FiltrationAtLeast model.syntheticTower (s+i) a) :
    FiltrationAtLeast model.syntheticTower (s+i+normalizedExponent model.classicalTower f)
      (a≫finiteExtensionMap model X Y f q) := by
  obtain ⟨b,_,himage,hfil⟩ :=
    normalized_finite_source_image_division X Y f q i hi hiq s t a ha
  rw [←himage]
  exact map_preserves_filtration (model.convergentMap
    (.shift (0,-(i:ℤ)) (.quotient (q-i) (.nu Y))) (.quotient q (.nu Y))
    ((model.quotients.tower _).triangle hi hiq).lambdaMap)
    (t-s,t+normalizedExponent model.classicalTower f)
    (s+i+normalizedExponent model.classicalTower f) _ hfil

private theorem finite_crossing_target_bound (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (q : ℕ) (hq : 0 < q)
    (s t u v : ℤ) (hs : s < u) (huv : u ≤ v)
    (x : ((model.family.obj ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).sequence.ssData
      (u,(t-s)+u,t+normalizedExponent model.classicalTower f)).eInfty)
    (y : ((model.family.obj ((SyntheticObject.quotient q (.nu Y)).obj model.nu model.auxiliary)).sequence.ssData
      (u+(v-u),(t-s)+(u+(v-u)),t+normalizedExponent model.classicalTower f)).eInfty)
    (he : TowerEssentialExtension (model.convergentMap
      (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q))
      (t-s,t+normalizedExponent model.classicalTower f) u (v-u) x y) :
    u+normalizedExponent model.classicalTower f ≤ v := by
  have hiq := finite_crossing_source_bound X Y f q hq s t u v huv x y he
  let i := (u-s).toNat
  have hi : 0 < i := by dsimp only [i]; omega
  have hiz : (i:ℤ)=u-s := Int.toNat_of_nonneg (by omega)
  have hui : s+(i:ℤ)=u := by omega
  let A := (SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary
  let B := (SyntheticObject.quotient q (.nu Y)).obj model.nu model.auxiliary
  let p := (t-s,t+normalizedExponent model.classicalTower f)
  have hrel : TowerExtensionEquation (model.convergentMap
      (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q)) p u (v-u) x y := he.1
  obtain ⟨_,ar,br,hab,hax,hby⟩ := (tower_extension_iff _ _ _ _ _ _).mp hrel
  let α := ((model.syntheticTower.filtration A).F u p).arrow ar
  have hα : FiltrationAtLeast model.syntheticTower u α := by
    have hm : α ∈ ModuleCat.subobjectModule _ ((model.syntheticTower.filtration A).F u p) := ⟨ar,rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hm
  have himage := finite_normalized_image_filtration X Y f q i hi (by omega) s t α (by
    rw [hui]
    exact hα)
  by_contra hv
  have hhigh : FiltrationAtLeast model.syntheticTower (u+(v-u)+1)
      (α≫finiteExtensionMap model X Y f q) :=
    model.syntheticTower.filtrationSubmodule_antitone _ p (by omega) himage
  have hdiff : ((model.syntheticTower.filtration B).F (u+(v-u)) p).arrow br -
      ((model.syntheticTower.filtration B).F (u+(v-u)) p).arrow 0 ∈
      ModuleCat.subobjectModule _ ((model.syntheticTower.filtration B).F (u+(v-u)+1) p) := by
    rw [map_zero,sub_zero,←hab]
    change (α≫finiteExtensionMap model X Y f q) ∈
      ModuleCat.subobjectModule _ ((model.syntheticTower.filtration B).F (u+(v-u)+1) p)
    simp only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply]
    obtain ⟨c,hc⟩ := hhigh
    exact ⟨c,hc⟩
  have hzero := (element_grade_equal_iff (model.syntheticTower.filtration B)
    (u+(v-u)) p br 0).mpr hdiff
  simp only [map_zero] at hzero
  have hy : y=0 := by
    apply (infinityGradedIso (model.convergence (.quotient q (.nu Y))) p (u+(v-u))).toLinearEquiv.injective
    change (infinityGradedIso (model.convergence (.quotient q (.nu Y))) p (u+(v-u))).hom y =
      (infinityGradedIso (model.convergence (.quotient q (.nu Y))) p (u+(v-u))).hom 0
    rw [←hby,map_zero]
    exact hzero
  have hzrel : TowerExtensionEquation (model.convergentMap
      (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q)) p u (v-u) x 0 := by
    rw [←hy]
    exact hrel
  exact ((tower_essential_iff_no_zero _ _ _ _ _ _ hrel).mp he) hzrel

private theorem minimal_length_finite_tower_no_crossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (q : ℕ) (hq : 0 < q)
    (s t n : ℤ) (hn : n ≤ normalizedExponent model.classicalTower f) :
    TowerNoCrossing (model.convergentMap
      (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q))
      (t-s,t+normalizedExponent model.classicalTower f) s n := by
  intro u v hs huv hv x y he
  have hh := finite_crossing_target_bound X Y f q hq s t u v hs huv x y he
  omega

private theorem short_finite_crossing_position (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (q : ℕ) (hq : 0 < q)
    (s t n u v : ℤ) (hn : n ≤ normalizedExponent model.classicalTower f+1)
    (hs : s < u) (huv : u ≤ v) (hv : v ≤ s+n)
    (x : ((model.family.obj ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).sequence.ssData
      (u,(t-s)+u,t+normalizedExponent model.classicalTower f)).eInfty)
    (y : ((model.family.obj ((SyntheticObject.quotient q (.nu Y)).obj model.nu model.auxiliary)).sequence.ssData
      (u+(v-u),(t-s)+(u+(v-u)),t+normalizedExponent model.classicalTower f)).eInfty)
    (he : TowerEssentialExtension (model.convergentMap
      (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
      (finiteExtensionMap model X Y f q))
      (t-s,t+normalizedExponent model.classicalTower f) u (v-u) x y) :
    u=s+1 ∧ v=s+normalizedExponent model.classicalTower f+1 ∧
      n=normalizedExponent model.classicalTower f+1 := by
  have hh := finite_crossing_target_bound X Y f q hq s t u v hs huv x y he
  omega

end
end KIP126.ProofTools.Internal.Leibniz
