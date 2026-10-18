module
import all KIP126.ProofTools.GeneralizedMahowald.ShortSource
import all KIP126.ProofTools.GeneralizedMahowald.MayCorrection
import all KIP126.ProofTools.GeneralizedLeibniz.WeightedReverse
public import KIP126.ProofTools.Operations
import all KIP126.ProofTools.Operations

/-! Crossing comparison for the actual absolute boundary. All groups, maps,
and filtrations are those of the fixed synthetic Adams model. -/

section
namespace KIP126.ProofTools.Paper
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000

private theorem detected_grade_zero_of_higher_filtration
    (A : SyntheticObject) (s t w : ℤ)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,t,w))
    (a : BiHom (t-s) w (A.obj model.nu model.auxiliary))
    (ha : Detects (model.convergence A) (s,t,w) x a)
    (hhigh : FiltrationAtLeast model.syntheticTower (s+1) a) :
    HasInfinityRepresentative _ 2 (s,t,w) x 0 := by
  obtain ⟨e,he,b,hb,hbe⟩ := ha
  have hzero : e=0 := by
    apply ((model.convergence A).identification (s,t,w)).toLinearEquiv.injective
    change ((model.convergence A).identification (s,t,w)).hom e =
      ((model.convergence A).identification (s,t,w)).hom 0
    rw [map_zero, hbe]
    apply ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).toAssociatedGraded_eq_zero_iff
      s (t-s,w) b).mpr
    rw [hb]
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hhigh
  rwa [hzero] at he

private theorem differential_target_permanent
    (X : ClassicalObject) (k : ℕ) (hk : 0<k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y) :
    y∈permanentCycles model X (s+k+1,t+k) := by
  have hy := differential_target_boundary X (k+1) (by omega) _ _ x y hd
  obtain ⟨b,rfl⟩ := hy
  let E := (model.classical.obj (X.obj model.auxiliary)).ssData (s+k+1,t+k)
  let h : E.B (↑(((k:ℤ)+1)-1).toNat) ≤ E.Z ⊤ :=
    (E.B_mono le_top).trans (E.B_le_Z ⊤)
  refine ⟨(Subobject.ofLE _ _ h) b,?_⟩
  change (Subobject.ofLE _ _ h ≫ cycleLabel model X ⊤ (s+k+1,t+k)) b = _
  simp only [cycleLabel,boundaryLabel,E,←Category.assoc,Subobject.ofLE_comp_ofLE]

private theorem nonzero_differential_target_not_boundary
    (X : ClassicalObject) (r b : ℤ) (p q : ℤ×ℤ)
    (hb : 1≤b) (hbr : b≤r-1)
    (x : Ambient model X p) (y : Ambient model X q)
    (hd : HasNonzeroDifferential (model.classical.obj (X.obj model.auxiliary)) r p q x y) :
    y∉boundaries model X b q := by
  intro hy
  obtain ⟨hdeg,xr,yr,hx,hyrep,heq,hnonzero⟩ := hd
  have hd0 := boundary_target_zero model X r b p q hx.1 hbr x y hy
    ⟨hdeg,xr,yr,hx,hyrep,heq⟩
  obtain ⟨_,xr0,yr0,hx0,hy0,heq0⟩ := hd0
  have hxx := hx.unique hx0
  have hyy : yr=yr0 := heq.symm.trans (by simpa only [hxx] using heq0)
  have hz : yr0=0 := hy0.unique (RepresentsOnPage.zero (by omega))
  exact hnonzero (hyy.trans hz)

private theorem delta_image_high_of_no_crossing
    (X : ClassicalObject) (q : ℕ) (r s t : ℤ) (hr : 0≤r)
    (hnc : TowerNoCrossing (model.convergentMap
      (.quotient q (.nu X)) (.shift (1,-(q:ℤ)) (.nu X))
      (absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) q))
      (t-s,t) s r)
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : FiltrationAtLeast model.syntheticTower (s+1) a) :
    FiltrationAtLeast model.syntheticTower (s+r+1)
      (a≫absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) q) := by
  have H := tower_image_same_target_of_no_crossing (model.convergentMap
    (.quotient q (.nu X)) (.shift (1,-(q:ℤ)) (.nu X))
    (absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (t-s,t) s r hr hnc a 0 (by simpa only [sub_zero,FiltrationAtLeast,SyntheticObject.obj] using ha)
  simpa only [zero_comp,sub_zero,FiltrationAtLeast,SyntheticObject.obj] using H

private theorem crossing_differential_contradicts_delta_no_crossing
    (X : ClassicalObject) (q i k : ℕ) (hi : 0 < i) (hiq : i < q)
    (hik : q-i ≤ k) (r s t : ℤ) (hr : 0 ≤ r)
    (hv : s+(i:ℤ)+(k:ℤ)+1≤s+r)
    (hnc : TowerNoCrossing (model.convergentMap
      (.quotient q (.nu X)) (.shift (1,-(q:ℤ)) (.nu X))
      (absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) q))
      (t-s,t) s r)
    (x : Ambient model X (s+i,t+i))
    (y : Ambient model X (s+i+k+1,t+i+k))
    (hd : HasNonzeroDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s+i,t+i) (s+i+k+1,t+i+k) x y) : False := by
  have hk : 0<k := by omega
  have hd' : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s+i,t+i) (s+i+k+1,t+i+k) x y := by
    obtain ⟨h,xr,yr,hx,hy,he,_⟩ := hd
    exact ⟨h,xr,yr,hx,hy,he⟩
  obtain ⟨a,ha,had⟩ := differential_absolute_boundary X (q-i) k (by omega) hik
    (s+i) (t+i) x y hd' (differential_target_permanent X k hk _ _ x y hd')
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let a0 : BiHom (t-s) (t+i) (XModLambdaN A (q-i)) :=
    homotopyRegrade (by omega) rfl a
  let aS := verticalShiftEquiv (XModLambdaN A (q-i)) i (t-s) t a0
  let aL := aS≫((model.quotients.tower A).triangle hi hiq).lambdaMap
  have haf : FiltrationAtLeast model.syntheticTower (s+i) a0 := by
    have H := finite_bottom_filtration X (q-i) (by omega) (s+i) (t+i) a
    exact (regrade_filtration_iff _ _ _ _).mpr H
  have haS : FiltrationAtLeast model.syntheticTower (s+i) aS :=
    (vertical_shift_filtration_iff (.quotient (q-i) (.nu X)) i (t-s) t (s+i) a0).mpr haf
  have haL : FiltrationAtLeast model.syntheticTower (s+1) aL := by
    have H := map_preserves_filtration (model.convergentMap
      (.shift (0,-(i:ℤ)) (.quotient (q-i) (.nu X))) (.quotient q (.nu X))
      ((model.quotients.tower A).triangle hi hiq).lambdaMap)
      (t-s,t) (s+i) aS haS
    exact model.syntheticTower.filtrationSubmodule_antitone _ (t-s,t) (by omega) H
  have hlarge := delta_image_high_of_no_crossing X q r s t hr hnc aL haL
  have hsmall : FiltrationAtLeast model.syntheticTower (s+r+1)
      (aS≫(SyntheticCategory.biShift (0,-(i:ℤ))).map (absoluteBoundary A (q-i))) :=
    (divided_boundary_filtration_iff X i q hi hiq (t-s) t (s+r+1) aS).mp
      (by simpa only [aL,Category.assoc,A] using hlarge)
  rw [vertical_shift_comp] at hsmall
  have hsmall := (vertical_shift_filtration_iff (.shift (1,-((q-i:ℕ):ℤ)) (.nu X))
    i (t-s) t (s+r+1) (a0≫absoluteBoundary A (q-i))).mp hsmall
  have hsmall := (absolute_boundary_filtration_iff X (q-i) (t-s) (t+i) (s+r+1) a0).mp hsmall
  have transport_boundary (m m' w v : ℤ) (hm : m=m')
      (b : BiHom m w (XModLambdaN A (q-i))) :
      FiltrationAtLeast model.syntheticTower v
        (biSuspensionHomEquiv m' w (q-i:ℕ) A
          (homotopyRegrade hm rfl b≫XModLambdaN.proj A (q-i))) ↔
      FiltrationAtLeast model.syntheticTower v
        (biSuspensionHomEquiv m w (q-i:ℕ) A (b≫XModLambdaN.proj A (q-i))) := by
    subst m'; rfl
  have hnative := (transport_boundary ((t+i)-(s+i)) (t-s) (t+i) (s+r+1) (by omega) a).mp hsmall
  have hsmall : FiltrationAtLeast model.syntheticTower (s+i+k+1+1)
      (homotopyRegrade (m' := (t+i+k)-(s+i+k+1)) (by omega) rfl
        (biSuspensionHomEquiv ((t+i)-(s+i)) (t+i) (q-i:ℕ) A
          (a≫XModLambdaN.proj A (q-i)))) := by
    apply (regrade_filtration_iff _ _ _ _).mpr
    exact model.syntheticTower.filtrationSubmodule_antitone _
      (((t+i)-(s+i))-1,t+i+(q-i:ℕ))
      (by omega : s+(i:ℤ)+(k:ℤ)+1+1≤s+r+1) hnative
  have hzero := detected_grade_zero_of_higher_filtration (.nu X)
    (s+i+k+1) (t+i+k) (t+i+(q-i:ℕ)) _ _ had (by simpa only [A] using hsmall)
  have hyB : y∈boundaries model X (1+(t+i+k)-(t+i+(q-i:ℕ))) (s+i+k+1,t+i+k) := by
    have H := (KIP126.Literature.Standard.eInfinity_nu_labels X
      (s+i+k+1) (t+i+k) (t+i+(q-i:ℕ)) (by omega) y 0).mp hzero
    apply (CrossingLabels.subquotient_zero_iff _ _ ⟨y,H.1⟩).mp
    simpa only [map_zero] using H.2.symm
  exact nonzero_differential_target_not_boundary X (k+1)
    (1+(t+i+k)-(t+i+(q-i:ℕ))) _ _ (by omega) (by omega) x y hd hyB

/-- Actual synthetic crossing of the absolute boundary for the quotient
`νX/λ^(page-1)`, in the fixed stem and weight of a classical differential.
The essentiality and all source and target grades are taken in that one ESS. -/
@[expose] public def DeltaHasCrossing (X : ClassicalObject) (page : ℕ) (r s t : ℤ) : Prop :=
  ∃ u v : ℤ, s < u ∧ u ≤ v ∧ v ≤ s+r ∧ ∃ x y,
    TowerEssentialExtension (model.convergentMap
      (.quotient (page-1) (.nu X)) (.shift (1,-((page-1:ℕ):ℤ)) (.nu X))
      (XModLambdaN.proj (model.nu.functor.obj (X.obj model.auxiliary)) (page-1) ≫
        (Operations.biSuspensionIso (page-1:ℕ)
          (model.nu.functor.obj (X.obj model.auxiliary))).inv))
      (t-s,t) u (v-u) x y

private theorem delta_no_crossing_implies_classical
    (X : ClassicalObject) (page : ℕ) (r s t : ℤ)
    (hpage : 2 ≤ page) (hpr : (page:ℤ) ≤ r)
    (hnc : TowerNoCrossing (model.convergentMap
      (.quotient (page-1) (.nu X)) (.shift (1,-((page-1:ℕ):ℤ)) (.nu X))
      (absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) (page-1)))
      (t-s,t) s r) :
    NoCrossingOn model X r page (s,t) := by
  refine ⟨by omega,hpr,?_⟩
  rintro ⟨a,b,ha,har,hb,hbr,x,y,hd⟩
  let q : ℕ := page-1
  let i : ℕ := a.toNat
  let k : ℕ := (r-a-b-1).toNat
  have hqZ : (q:ℤ)=(page:ℤ)-1 := by dsimp [q]; omega
  have hiZ : (i:ℤ)=a := by dsimp [i]; omega
  have hkZ : (k:ℤ)=r-a-b-1 := by dsimp [k]; omega
  have H := crossing_differential_contradicts_delta_no_crossing X q i k
    (by omega) (by omega) (by omega) r s t (by omega) (by omega) hnc
  have hs : s+a+(k:ℤ)+1=s+r-b := by omega
  have ht : t+a+(k:ℤ)=t+r-b-1 := by omega
  have hl : (k:ℤ)+1=r-a-b := by omega
  rw [hiZ,hs,ht,hl] at H
  exact H x y hd

/-- AimPaper Proposition 4.16 (`prop:cross-dr-En`), with both directions
and the full classical range `2 ≤ page ≤ r`. The quotient exponent is
`page-1`, so `page=n+1` in the paper. -/
public theorem classical_crossing_iff_delta_crossing
    (X : ClassicalObject) (page : ℕ) (r s t : ℤ)
    (hpage : 2 ≤ page) (hpr : (page:ℤ) ≤ r) :
    HasCrossingOn model X r page (s,t) ↔ DeltaHasCrossing X page r s t := by
  classical
  have hdef : DeltaHasCrossing X page r s t ↔
      ¬TowerNoCrossing (model.convergentMap
        (.quotient (page-1) (.nu X)) (.shift (1,-((page-1:ℕ):ℤ)) (.nu X))
        (absoluteBoundary (model.nu.functor.obj (X.obj model.auxiliary)) (page-1)))
        (t-s,t) s r := by
    constructor
    · rintro ⟨u,v,hu,huv,hv,x,y,hess⟩ hn
      exact hn u v hu huv hv x y
        (by simpa only [Operations.biSuspensionIso,absoluteBoundary] using hess)
    · intro hn
      by_contra hnot
      apply hn
      intro u v hu huv hv x y hess
      apply hnot
      exact ⟨u,v,hu,huv,hv,x,y,
        by simpa only [Operations.biSuspensionIso,absoluteBoundary] using hess⟩
  rw [hdef]
  constructor
  · intro hcross hnc
    exact (delta_no_crossing_implies_classical X page r s t hpage hpr hnc).2.2 hcross
  · intro hcross
    by_contra hnc
    exact hcross (classical_noCrossing_absolute_boundary X page r s t ⟨by omega,hpr,hnc⟩)

end
end KIP126.ProofTools.Paper
