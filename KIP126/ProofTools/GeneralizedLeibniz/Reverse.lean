module
import all KIP126.ProofTools.GeneralizedLeibniz.Survival
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingLabels

/-! The reverse absolute-boundary comparison used in AimPaper
Proposition `prop:6de7d130` and Theorem 6.1. Equal first restrictions force
the difference of adjacent absolute boundaries to be λ torsion of the exact
order giving the classical boundary indeterminacy. The higher-quotient lift
then identifies the differential target of any specified representative. -/

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

private theorem first_label_lift_permanent (X : ClassicalObject) (s t : ℤ)
    (y : Ambient model X (s,t))
    (α : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (hα : α ≫ XModLambdaN.incl _ 1 = firstLabel model X s t y ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    y ∈ permanentCycles model X (s,t) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let inv : A ⟶ nuZero model X := SyntheticCategory.biShift_zero.inv.app A
  have hfirst : quotientClass 1 (α ≫ inv) = firstLabel model X s t y := by
    dsimp only [quotientClass]
    rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hα,
      Category.assoc,←model.quotients.functoriality.map_comp]
    simp only [inv,A,Iso.hom_inv_id_app,model.quotients.functoriality.map_id,Category.comp_id]
  obtain ⟨z,hz⟩ := (KIP126.Literature.Standard.selected_permanent_lift X s t y).mpr
    ⟨α ≫ inv,hfirst⟩
  refine ⟨z,?_⟩
  have h := normalizeInitialProjection ((model.classical.obj (X.obj model.auxiliary)).ssData (s,t))
    (↑(2-(model.classical.obj (X.obj model.auxiliary)).r₀).toNat)
    ⊤ (by rw [model.classical.firstPage]; rfl) le_top
  exact (congrArg (fun f => f z) h).symm.trans hz

private theorem detected_zero_infinity (A : SyntheticObject) (p : Tridegree)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ p)
    (h : Detects (model.convergence A) p x 0) :
    HasInfinityRepresentative _ 2 p x 0 := by
  obtain ⟨e,he,a,ha,hga⟩ := h
  have haz : a = 0 := (ModuleCat.mono_iff_injective
    ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F p.1 (p.2.1-p.1,p.2.2)).arrow).mp
      inferInstance (ha.trans (map_zero _).symm)
  have hez : e = 0 := ((model.convergence A).identification p).toLinearEquiv.injective (by
    change ((model.convergence A).identification p).hom e =
      ((model.convergence A).identification p).hom 0
    rw [hga,haz,map_zero,map_zero])
  rwa [hez] at he

private theorem first_label_lambda_zero_boundary (X : ClassicalObject) (s t : ℤ)
    (k : ℕ) (hk : 0 < k) (y : Ambient model X (s,t))
    (α : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (hα : α ≫ XModLambdaN.incl _ 1 = firstLabel model X s t y ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (hz : lambdaMultiply k α = 0) :
    y ∈ boundaries model X (k+1) (s,t) := by
  have hy := first_label_lift_permanent X s t y α hα
  have hd := nu_lambda_detects X k hk s t y hy α hα
  rw [hz] at hd
  have he := detected_zero_infinity (.nu X) (s,t,t-k) _ hd
  have hclass := (KIP126.Literature.Standard.eInfinity_nu_labels X s t (t-k) (by omega) y 0).mp he
  have hb := (CrossingLabels.subquotient_zero_iff _ _ ⟨y,hclass.1⟩).mp (by
    rw [←hclass.2,map_zero])
  convert hb using 1
  congr 1
  omega

private theorem firstLabel_sub (X : ClassicalObject) (s t : ℤ)
    (x y : Ambient model X (s,t)) :
    firstLabel model X s t (x-y) = firstLabel model X s t x - firstLabel model X s t y := by
  have cast_sub (m w w' : ℤ) (A : SyntheticSpectrum) (hw : w = w')
      (he : BiHom m w A = BiHom m w' A) (a b : BiHom m w A) :
      he.mp (a-b) = he.mp a - he.mp b := by
    subst w'; rfl
  simp only [firstLabel,map_sub]
  exact cast_sub _ _ _ _ (Int.add_zero t) _ _ _

private theorem first_label_zero (X : ClassicalObject) (s t : ℤ)
    (y : Ambient model X (s,t))
    (hy : firstLabel model X s t y ≫ XModLambdaN.map
      (SyntheticCategory.biShift_zero.hom.app _) 1 = 0) : y = 0 := by
  have hfirst : (0 : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary))) ≫
      XModLambdaN.incl _ 1 = firstLabel model X s t y ≫ XModLambdaN.map
      (SyntheticCategory.biShift_zero.hom.app _) 1 := by rw [zero_comp,hy]
  have hp := first_label_lift_permanent X s t y 0 hfirst
  have hd := nu_first_label_detects X s t y hp 0 hfirst
  have he := detected_zero_infinity (.nu X) (s,t,t) _ hd
  have hc := (KIP126.Literature.Standard.eInfinity_nu_labels X s t t (by omega) y 0).mp he
  have hb := (CrossingLabels.subquotient_zero_iff _ _ ⟨y,hc.1⟩).mp (by rw [←hc.2,map_zero])
  simpa only [add_sub_cancel_right,boundaries_one,Submodule.mem_bot] using hb

private def boundaryRepresentative (X : ClassicalObject) (k : ℕ) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) k)) :
    BiHom ((t+k)-(s+k+1)) (t+k) (model.nu.functor.obj (X.obj model.auxiliary)) :=
  homotopyRegrade (by omega) rfl
    (biSuspensionHomEquiv (t-s) t k (model.nu.functor.obj (X.obj model.auxiliary))
      (a ≫ XModLambdaN.proj _ k))

private theorem boundaryRepresentative_sub (X : ClassicalObject) (k : ℕ) (s t : ℤ)
    (a b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) k)) :
    boundaryRepresentative X k s t (a-b) =
      boundaryRepresentative X k s t a - boundaryRepresentative X k s t b := by
  simp only [boundaryRepresentative,Preadditive.sub_comp,map_sub,regrade_precomp,Preadditive.comp_sub]

private theorem first_restriction_kernel_boundary_lambda_zero (X : ClassicalObject)
    (k : ℕ) (hk : 0 < k) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) k))
    (ha : a ≫ (model.quotients.tower _).rho 1 k hk = 0) :
    lambdaMultiply (k-1) (boundaryRepresentative X k s t a) = 0 := by
  have hres := absolute_boundary_restriction X 1 k hk (t-s) t a
  rw [ha,zero_comp,map_zero] at hres
  have hzero : lambdaMultiply (k-1)
      (biSuspensionHomEquiv (t-s) t k (model.nu.functor.obj (X.obj model.auxiliary))
        (a ≫ XModLambdaN.proj _ k)) = 0 := by
    simpa only [regrade_precomp,comp_eq_zero_iff_of_epi] using hres.symm
  dsimp only [boundaryRepresentative]
  rw [lambda_regrade,hzero]
  simp only [regrade_precomp,comp_zero]

private theorem adjacent_boundary_labels_congruent (X : ClassicalObject)
    (k : ℕ) (hk : 0 < k) (s t : ℤ)
    (a b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) k))
    (hab : a ≫ (model.quotients.tower _).rho 1 k hk =
      b ≫ (model.quotients.tower _).rho 1 k hk)
    (y z : Ambient model X (s+k+1,t+k))
    (hy : boundaryRepresentative X k s t a ≫ XModLambdaN.incl _ 1 =
      firstLabel model X (s+k+1) (t+k) y ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (hz : boundaryRepresentative X k s t b ≫ XModLambdaN.incl _ 1 =
      firstLabel model X (s+k+1) (t+k) z ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    y-z ∈ boundaries model X k (s+k+1,t+k) := by
  have hfirst : boundaryRepresentative X k s t (a-b) ≫ XModLambdaN.incl _ 1 =
      firstLabel model X (s+k+1) (t+k) (y-z) ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
    rw [boundaryRepresentative_sub,Preadditive.sub_comp,hy,hz,firstLabel_sub,Preadditive.sub_comp]
  by_cases hk1 : k=1
  · subst k
    have hab' : a=b := by simpa only [(model.quotients.tower _).rho_id,Category.comp_id] using hab
    have hzero : y-z=0 := first_label_zero X (s+(1:ℕ)+1) (t+(1:ℕ)) (y-z) (by
      rw [←hfirst,hab',sub_self]
      simp only [boundaryRepresentative,zero_comp,map_zero,regrade_precomp,comp_zero])
    rw [hzero]
    exact Submodule.zero_mem _
  have hmul := first_restriction_kernel_boundary_lambda_zero X k hk s t (a-b) (by
    rw [Preadditive.sub_comp,hab,sub_self])
  have hb := first_label_lambda_zero_boundary X (s+k+1) (t+k) (k-1) (by omega) (y-z)
    (boundaryRepresentative X k s t (a-b)) hfirst hmul
  simpa only [Nat.cast_sub hk,Nat.cast_one,sub_add_cancel] using hb

private theorem adjacent_boundary_differential (X : ClassicalObject)
    (k : ℕ) (hk : 0 < k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) k))
    (ha : a ≫ (model.quotients.tower _).rho 1 k hk =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (hy : boundaryRepresentative X k s t a ≫ XModLambdaN.incl _ 1 =
      firstLabel model X (s+k+1) (t+k) y ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  have hx := first_label_lift_cycles X k hk s t x a ha
  have hreach := (isCycle_iff_reaches model X (k+1) (by omega) (s,t) x).mp
    ⟨by omega,by simpa only [add_sub_cancel_right] using hx⟩
  obtain ⟨b,hb,hdb⟩ := KIP126.Literature.Standard.bhs_bockstein X k hk s t x hreach
  let z := bocksteinLabel model X k hk s t b
  obtain ⟨a0,ha0,hz⟩ := adjacent_absolute_boundary X k hk s t x z hdb
  have hcong := adjacent_boundary_labels_congruent X k hk s t a a0 (ha.trans ha0.symm) y z hy hz
  exact (differentialAt_of_congruent model X
    (⟨by omega,hdb⟩ : DifferentialAt model X (k+1) (s,t) (s+k+1,t+k) x z)
    ⟨by omega,by simpa only [add_sub_cancel_right] using hcong⟩).2

private theorem firstLabel_surjective (X : ClassicalObject) (s t : ℤ) :
    Function.Surjective (firstLabel model X s t) := by
  have cast_surjective (m w w' : ℤ) (A : SyntheticSpectrum) (hw : w = w')
      (he : BiHom m w A = BiHom m w' A) : Function.Surjective he.mp := by
    subst w'; exact Function.surjective_id
  have hs := (cast_surjective (t-s) (t+0) t (XModLambdaN (nuZero model X) 1)
    (Int.add_zero t) (by simp)).comp (model.firstQuotient X 0 s t).symm.surjective
  exact hs

private theorem nu_first_label_exists (X : ClassicalObject) (s t : ℤ)
    (α : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary))) :
    ∃ y : Ambient model X (s,t),
      α ≫ XModLambdaN.incl _ 1 = firstLabel model X s t y ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  obtain ⟨y,hy⟩ := firstLabel_surjective X s t
    (α ≫ XModLambdaN.incl A 1 ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app A) 1)
  refine ⟨y,?_⟩
  rw [hy,Category.assoc,Category.assoc,←model.quotients.functoriality.map_comp,
    Iso.inv_hom_id_app,model.quotients.functoriality.map_id]
  simp only [Functor.id_obj,Category.comp_id]
  rfl

private theorem nu_detected_labels_congruent (X : ClassicalObject) (s t w : ℤ)
    (hw : w ≤ t) (y z : Ambient model X (s,t))
    (α : BiHom (t-s) w (model.nu.functor.obj (X.obj model.auxiliary)))
    (hy : Detects (model.convergence (.nu X)) (s,t,w) (nuWeightLabel model X s t w hw y) α)
    (hz : Detects (model.convergence (.nu X)) (s,t,w) (nuWeightLabel model X s t w hw z) α) :
    y-z ∈ boundaries model X (1+t-w) (s,t) := by
  obtain ⟨ey,hey,a,ha,hga⟩ := hy
  obtain ⟨ez,hez,b,hb,hgb⟩ := hz
  have hab : a = b := (ModuleCat.mono_iff_injective
    ((model.syntheticTower.filtration (model.nu.functor.obj (X.obj model.auxiliary))).F s (t-s,w)).arrow).mp
      inferInstance (ha.trans hb.symm)
  have heq : ey = ez := ((model.convergence (.nu X)).identification (s,t,w)).toLinearEquiv.injective (by
    change ((model.convergence (.nu X)).identification (s,t,w)).hom ey =
      ((model.convergence (.nu X)).identification (s,t,w)).hom ez
    rw [hga,hgb,hab])
  obtain ⟨hyp,hycl⟩ := (KIP126.Literature.Standard.eInfinity_nu_labels X s t w hw y ey).mp hey
  obtain ⟨hzp,hzcl⟩ := (KIP126.Literature.Standard.eInfinity_nu_labels X s t w hw z ez).mp hez
  have hequal : subquotientClass (permanentCycles model X (s,t)) (boundaries model X (1+t-w) (s,t)) ⟨y,hyp⟩ =
      subquotientClass (permanentCycles model X (s,t)) (boundaries model X (1+t-w) (s,t)) ⟨z,hzp⟩ := by
    rw [←hycl,←hzcl,heq]
  have hzero : subquotientClass (permanentCycles model X (s,t)) (boundaries model X (1+t-w) (s,t))
      (⟨y,hyp⟩ - ⟨z,hzp⟩) = 0 := by rw [map_sub,hequal,sub_self]
  exact (CrossingLabels.subquotient_zero_iff _ _ _).mp hzero

private theorem detects_filtration (A : SyntheticObject) (p : Tridegree)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ p)
    (a : BiHom (p.2.1-p.1) p.2.2 (A.obj model.nu model.auxiliary))
    (ha : Detects (model.convergence A) p x a) : FiltrationAtLeast model.syntheticTower p.1 a := by
  obtain ⟨e,he,b,hb,hgb⟩ := ha
  have hm : a ∈ ModuleCat.subobjectModule _ ((model.syntheticTower.filtration
      (A.obj model.nu model.auxiliary)).F p.1 (p.2.1-p.1,p.2.2)) := ⟨b,hb⟩
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hm

private theorem boundary_detects_differential (X : ClassicalObject)
    (i k : ℕ) (hi : 0 < i) (hik : i ≤ k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : a ≫ (model.quotients.tower _).rho 1 i hi =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1)
    (hy : Detects (model.convergence (.nu X)) (s+k+1,t+k,t+i)
      (nuWeightLabel model X (s+k+1) (t+k) (t+i) (by omega) y)
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv (t-s) t i (model.nu.functor.obj (X.obj model.auxiliary))
          (a ≫ XModLambdaN.proj _ i)))) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  have hfil : FiltrationAtLeast model.syntheticTower (s+k+1)
      (biSuspensionHomEquiv (t-s) t i A (a ≫ XModLambdaN.proj A i)) := by
    have hf := detects_filtration (.nu X) (s+k+1,t+k,t+i) _ _ hy
    have transport (m m' w s : ℤ) (hm : m=m') (a : BiHom m w A) :
        FiltrationAtLeast model.syntheticTower s (homotopyRegrade hm rfl a) ↔
          FiltrationAtLeast model.syntheticTower s a := by subst m'; rfl
    exact (transport _ _ _ _ _ _).mp hf
  obtain ⟨b,hb⟩ : ∃ b : BiHom (t-s) t (XModLambdaN A k),
      b ≫ (model.quotients.tower A).rho i k hik = a := by
    rcases hik.eq_or_lt with rfl | hlt
    · exact ⟨a,by rw [(model.quotients.tower A).rho_id,Category.comp_id]⟩
    · exact absolute_boundary_filtration_lift X i k hi hlt s t a hfil
  have hbfirst : b ≫ (model.quotients.tower A).rho 1 k (by omega) =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 := by
    rw [←(model.quotients.tower A).rho_comp hi hik,←Category.assoc,hb]
    exact ha
  let β := boundaryRepresentative X k s t b
  obtain ⟨z,hz⟩ := nu_first_label_exists X (s+k+1) (t+k) β
  have hp := first_label_lift_permanent X (s+k+1) (t+k) z β hz
  have hdz := adjacent_boundary_differential X k (by omega) s t x z b hbfirst hz
  have hzdet : Detects (model.convergence (.nu X)) (s+k+1,t+k,t+i)
      (nuWeightLabel model X (s+k+1) (t+k) (t+i) (by omega) z)
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv (t-s) t i A (a ≫ XModLambdaN.proj A i))) := by
    rw [←hb]
    by_cases hik' : i=k
    · subst i
      simpa only [β,boundaryRepresentative,A,(model.quotients.tower A).rho_id,Category.comp_id] using
        nu_first_label_detects X (s+k+1) (t+k) z hp β hz
    have hlam := nu_lambda_detects X (k-i) (by omega) (s+k+1) (t+k) z hp β hz
    have hind : (s+k+1,t+k,(t+k)-(k-i:ℕ))=(s+k+1,t+k,t+i) :=
      Prod.ext rfl (Prod.ext rfl (by dsimp; omega))
    have hlam := detects_transport hind _ _ hlam
    convert hlam using 1
    · have transport (w w' : ℤ) (hw : w=w') (hw₁ : w≤t+k) (hw₂ : w'≤t+k)
          (h : (s+k+1,t+k,w)=(s+k+1,t+k,w')) :
          regradeE2 h (nuWeightLabel model X (s+k+1) (t+k) w hw₁ z) =
            nuWeightLabel model X (s+k+1) (t+k) w' hw₂ z := by subst w'; rfl
      exact (transport _ _ (by omega) _ _ hind).symm
    · rw [absolute_boundary_restriction]
      dsimp only [β,boundaryRepresentative]
      rw [lambda_regrade]
      simp only [regrade_precomp,←Category.assoc,eqToHom_trans]
  have hcong := nu_detected_labels_congruent X (s+k+1) (t+k) (t+i) (by omega) y z _ hy hzdet
  have hboundary : y-z ∈ boundaries model X k (s+k+1,t+k) :=
    boundaries_monotone model X (s+k+1,t+k) (by omega) hcong
  exact (differentialAt_of_congruent model X
    (⟨by omega,hdz⟩ : DifferentialAt model X (k+1) (s,t) (s+k+1,t+k) x z)
    ⟨by omega,by simpa only [add_sub_cancel_right] using hboundary⟩).2

end
end KIP126.ProofTools.Internal.Leibniz
