module
import all KIP126.ProofTools.GeneralizedMahowald.Sphere
import all KIP126.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.ProofTools.GeneralizedMahowald.KernelTriangles
import all KIP126.ProofTools.GeneralizedMahowald.Adjacent
import all KIP126.ProofTools.GeneralizedMahowald.NoReturn
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.StretchingRepresentatives
/-! The forward comparison between a classical differential and the absolute
λ-quotient boundary used in AimPaper Proposition `prop:6de7d130` and Theorem 6.1.
All representatives, λ powers, filtrations and E∞ labels use the fixed model.
The crossing conversion and reverse comparison are separate, unfinished parts
of GL1/GL2; these helpers do not invoke either pending paper theorem. -/

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
set_option maxHeartbeats 6000000

private theorem nu_bottom_filtration (X : ClassicalObject) (s t : ℤ)
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary))) :
    FiltrationAtLeast model.syntheticTower s a := by
  have hzero := filtration_at_zero model.syntheticTower _ (t-s) t a
  by_cases hs : s ≤ 0
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (t-s,t) hs hzero
  · exact (filtration_iff_of_infinity_zero (model.convergence (.nu X))
      0 s (t-s) t (by omega)
      (fun k _ hk => nu_infinity_zero_above X k (t-s+k) t (by omega)) a).mp hzero

private theorem nu_projection_infinity_injective (X : ClassicalObject) (q : ℕ) (hq : 0<q)
    (s t w : ℤ) (hw : 0≤t-w ∧ t-w<q) :
    Function.Injective ((model.family.map (XModLambdaN.incl
      (model.nu.functor.obj (X.obj model.auxiliary)) q)).eInftyMap (s,t,w)) := by
  intro x y hxy
  apply (KIP126.Literature.Standard.infinityNuWindow X (s,t) w (by omega)).injective
  apply subquotientMap_injective (permanentCycles_le_cycles model X (s,t) ((q:ℤ)-t+w))
  have hx := KIP126.Literature.Standard.eInfinity_rho_nu X q hq (s,t) w hw x
  have hy := KIP126.Literature.Standard.eInfinity_rho_nu X q hq (s,t) w hw y
  exact hx.symm.trans ((congrArg (KIP126.Literature.Standard.infinityFiniteWindow X q hq (s,t) w hw) hxy).trans hy)

private theorem nu_first_label_detects (X : ClassicalObject) (s t : ℤ)
    (x : Ambient model X (s,t)) (hx : x ∈ permanentCycles model X (s,t))
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1 = firstLabel model X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (model.convergence (.nu X)) (s,t,t)
      (nuWeightLabel model X s t t (by omega) x) a := by
  let e := (KIP126.Literature.Standard.infinityNuWindow X (s,t) t (by omega)).symm
    (subquotientClass (permanentCycles model X (s,t)) (boundaries model X (1+t-t) (s,t)) ⟨x,hx⟩)
  have he : HasInfinityRepresentative _ 2 (s,t,t) (nuWeightLabel model X s t t (by omega) x) e := by
    apply (KIP126.Literature.Standard.eInfinity_nu_labels X s t t (by omega) x e).mpr
    exact ⟨hx,(KIP126.Literature.Standard.infinityNuWindow X (s,t) t (by omega)).apply_symm_apply _⟩
  apply detects_reflect (.nu X) (.quotient 1 (.nu X)) (XModLambdaN.incl _ 1)
    (s,t,t) (nu_projection_infinity_injective X 1 (by omega) s t t (by omega))
    _ e he a (nu_bottom_filtration X s t a)
  have hz := zero_weight_label X 1 s t x
  change familyPageMap model.family (XModLambdaN.incl _ 1) 2 (s,t,t)
    (nuWeightLabel model X s t t (by omega) x) = _ at hz
  have hd := first_label_detects_unshifted X 1 (by omega) s t x (a ≫ XModLambdaN.incl _ 1) (by
    rw [(model.quotients.tower _).rho_id, Category.comp_id]
    exact ha)
  exact (congrArg (fun z => Detects (model.convergence (.quotient 1 (.nu X))) (s,t,t) z
    (a ≫ XModLambdaN.incl _ 1)) hz).mpr hd

private theorem cofiber_boundary_projection (X : ClassicalObject)
    (i j : ℕ) (hi : 0 < i) (hij : i < j) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i)) :
    biSuspensionHomEquiv m w i (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (j-i))
      (a ≫ ((model.quotients.tower _).triangle hi hij).delta) =
    biSuspensionHomEquiv m w i (model.nu.functor.obj (X.obj model.auxiliary))
      (a ≫ XModLambdaN.proj _ i) ≫ XModLambdaN.incl _ (j-i) := by
  rw [selected_delta_evaluation_eq_cofiber X i j _ m w a, ←Category.assoc]
  exact bi_susp_natural model.quotients.coherence m w i _ _

private theorem adjacent_absolute_boundary (X : ClassicalObject)
    (k : ℕ) (hk : 0<k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y) :
    ∃ a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) k),
      a ≫ (model.quotients.tower _).rho 1 k hk =
        firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      (homotopyRegrade (by omega) rfl
        (biSuspensionHomEquiv (t-s) t k (model.nu.functor.obj (X.obj model.auxiliary))
          (a ≫ XModLambdaN.proj _ k))) ≫ XModLambdaN.incl _ 1 =
        firstLabel model X (s+k+1) (t+k) y ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  obtain ⟨a,ha,had⟩ := adjacent_mahowald_case X k hk s t x y hd
  dsimp only at had
  let δ : XModLambdaN A k ⟶ ((SyntheticCategory.biShift (0,-(k:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
    simpa only [show k.succ-k=1 by omega] using ((model.quotients.tower A).triangle hk (Nat.lt_succ_self k)).delta
  have hp : biSuspensionHomEquiv (t-s) t k (XModLambdaN A 1) (a≫δ) =
      biSuspensionHomEquiv (t-s) t k A (a≫XModLambdaN.proj A k) ≫ XModLambdaN.incl A 1 := by
    have h := cofiber_boundary_projection X k (k+1) hk (Nat.lt_succ_self k) (t-s) t a
    have transport (q : ℕ) (hq : q=1)
        (d : XModLambdaN A k ⟶ ((SyntheticCategory.biShift (0,-(k:ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧)
        (he : (XModLambdaN A k ⟶ ((SyntheticCategory.biShift (0,-(k:ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧) =
          (XModLambdaN A k ⟶ ((SyntheticCategory.biShift (0,-(k:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧))
        (hd : biSuspensionHomEquiv (t-s) t k (XModLambdaN A q) (a≫d) =
          biSuspensionHomEquiv (t-s) t k A (a≫XModLambdaN.proj A k) ≫ XModLambdaN.incl A q) :
        biSuspensionHomEquiv (t-s) t k (XModLambdaN A 1) (a≫he.mp d) =
          biSuspensionHomEquiv (t-s) t k A (a≫XModLambdaN.proj A k) ≫ XModLambdaN.incl A 1 := by
      subst q
      exact hd
    exact transport (k+1-k) (by omega) _ _ h
  let b := firstLabel model X (s+k+1) (t+k) y ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1
  have hb := first_label_detects_unshifted X 1 (by omega) (s+k+1) (t+k) y b (by
    rw [(model.quotients.tower _).rho_id,Category.comp_id])
  have heq := finite_top_detection_unique X 1 (by omega) (s+k+1) (t+k) (t+k) (by omega)
    _ _ b had hb
  have hdet : homotopyRegrade (show (t-s)-1=(t+k)-(s+k+1) by omega) rfl
      (biSuspensionHomEquiv (t-s) t k (XModLambdaN A 1) (a≫δ)) = b := heq
  rw [hp,regrade_comp] at hdet
  exact ⟨a,ha,hdet⟩

private theorem nu_lambda_detects (X : ClassicalObject) (k : ℕ) (hk : 0 < k)
    (s t : ℤ) (y : Ambient model X (s,t))
    (hy : y ∈ permanentCycles model X (s,t))
    (α : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (hα : α ≫ XModLambdaN.incl _ 1 = firstLabel model X s t y ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (model.convergence (.nu X)) (s,t,t-k)
      (nuWeightLabel model X s t (t-k) (by omega) y) (lambdaMultiply k α) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  have ha := nu_first_label_detects X s t y hy α hα
  have hsource : (s,t,t)=(s,(t-s)+s,t) := by simp
  have hstem := detects_transport hsource _ _ ha
  let L : ((SyntheticObject.shift (0,-(k:ℤ)) (.nu X)).obj model.nu model.auxiliary) ⟶ A := lambdaPow k A
  have hmap := shifted_map_detects (.nu X) (.nu X) (0,-(k:ℤ)) (t-s,t) s L
    (regradeE2 hsource (nuWeightLabel model X s t t (by omega) y)) α hstem
  have hindex : (s,((t-s,t)+(0,-(k:ℤ))).1+s,((t-s,t)+(0,-(k:ℤ))).2) =
      (s,t,t-k) := by ext <;> simp [sub_eq_add_neg]
  have hmap := detects_transport hindex _ _ hmap
  obtain ⟨e,he,b,hb,hgb⟩ := hmap
  obtain ⟨e0,he0,_⟩ := ha
  have heStem := representative_transport hsource _ _ he0
  have heMap := shifted_representative_map (.nu X) (.nu X)
    (0,-(k:ℤ)) (t-s,t) s L _ _ heStem
  have heMap := representative_transport hindex _ _ heMap
  have heq := he.unique heMap
  have heq' : e = KIP126.Literature.Standard.infinityLambda (.nu X) k (s,t) t e0 := by
    convert heq using 1
    simp only [KIP126.Literature.Standard.infinityLambda,
      InfinityShiftCoordinates.lambdaMap, show k ≠ 0 by omega, ↓reduceDIte,
      InfinityShiftCoordinates.shift, infinityShift, Iso.trans_hom, ModuleCat.comp_apply,
      eqToIso.hom, KIP126.Literature.Standard.infinityShiftData,
      KIP126.Literature.Standard.infinityShift_comparison]
    exact (infinity_map_regrade L hindex _).symm
  have hlabel : HasInfinityRepresentative _ 2 (s,t,t-k)
      (nuWeightLabel model X s t (t-k) (by omega) y)
      (KIP126.Literature.Standard.infinityLambda (.nu X) k (s,t) t e0) := by
    apply (KIP126.Literature.Standard.eInfinity_nu_labels X s t (t-k) (by omega) y _).mpr
    refine ⟨hy,?_⟩
    rw [KIP126.Literature.Standard.eInfinity_lambda_nu X k (s,t) t (by omega)]
    have he0' := (KIP126.Literature.Standard.eInfinity_nu_labels X s t t (by omega) y e0).mp he0
    rw [he0'.2]
    rfl
  have heFinal : HasInfinityRepresentative _ 2 (s,t,t-k)
      (nuWeightLabel model X s t (t-k) (by omega) y) e := by
    rw [heq']
    exact hlabel
  refine ⟨e,heFinal,b,?_,hgb⟩
  convert hb using 1
  simp only [regrade_precomp, L, shiftHomotopyClass, lambdaMultiply,
    Category.assoc]
  simp only [A]
  erw [lambdaPow_naturality k α]
  simp only [←Category.assoc,eqToHom_trans]

private theorem absolute_boundary_restriction (X : ClassicalObject)
    (i k : ℕ) (hik : i ≤ k) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) k)) :
    biSuspensionHomEquiv m w i (model.nu.functor.obj (X.obj model.auxiliary))
      ((a ≫ (model.quotients.tower _).rho i k hik) ≫ XModLambdaN.proj _ i) =
    homotopyRegrade rfl (by omega)
      (lambdaMultiply (k-i) (biSuspensionHomEquiv m w k
        (model.nu.functor.obj (X.obj model.auxiliary)) (a ≫ XModLambdaN.proj _ k))) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  rw [model.quotients.restriction,Category.assoc,quotient_restriction_boundary,←Category.assoc]
  have h := bi_susp_lambda_transition model.quotients.coherence i k hik m w A
    (biSuspensionHomEquiv m w k A (a ≫ XModLambdaN.proj A k))
  simpa only [AddEquiv.symm_apply_apply] using h

private theorem lambda_regrade {m m' w w' : ℤ} {A : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (k : ℕ) (a : BiHom m w A) :
    lambdaMultiply k (homotopyRegrade hm hw a) =
      homotopyRegrade hm (congrArg (fun z : ℤ => z-(k:ℤ)) hw) (lambdaMultiply k a) := by
  subst m'; subst w'
  rfl

private theorem differential_absolute_boundary (X : ClassicalObject)
    (i k : ℕ) (hi : 0 < i) (hik : i ≤ k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y ∈ permanentCycles model X (s+k+1,t+k)) :
    ∃ a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i),
      a ≫ (model.quotients.tower _).rho 1 i hi =
        firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      Detects (model.convergence (.nu X)) (s+k+1,t+k,t+i)
        (nuWeightLabel model X (s+k+1) (t+k) (t+i) (by omega) y)
        (homotopyRegrade (by dsimp; omega) rfl
          (biSuspensionHomEquiv (t-s) t i (model.nu.functor.obj (X.obj model.auxiliary))
            (a ≫ XModLambdaN.proj _ i))) := by
  obtain ⟨a,ha,had⟩ := adjacent_absolute_boundary X k (by omega) s t x y hd
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let α : BiHom ((t+k)-(s+k+1)) (t+k) A :=
    homotopyRegrade (by omega) rfl
      (biSuspensionHomEquiv (t-s) t k A (a ≫ XModLambdaN.proj A k))
  have hα : α ≫ XModLambdaN.incl A 1 =
      firstLabel model X (s+k+1) (t+k) y ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 := had
  refine ⟨a ≫ (model.quotients.tower A).rho i k hik,?_,?_⟩
  · rw [Category.assoc,(model.quotients.tower A).rho_comp hi hik]
    exact ha
  by_cases hik' : i=k
  · subst i
    have hz := nu_first_label_detects X (s+k+1) (t+k) y hy α hα
    simp only [A, (model.quotients.tower _).rho_id,Category.comp_id]
    exact hz
  have hlam := nu_lambda_detects X (k-i) (by omega) (s+k+1) (t+k) y hy α hα
  have hind : (s+k+1,t+k,(t+k)-(k-i:ℕ))=(s+k+1,t+k,t+i) := Prod.ext rfl (Prod.ext rfl (by dsimp; omega))
  have hlam := detects_transport hind _ _ hlam
  convert hlam using 1
  · have transport (w w' : ℤ) (hw : w=w') (hw₁ : w≤t+k) (hw₂ : w'≤t+k)
        (h : (s+k+1,t+k,w)=(s+k+1,t+k,w')) :
        regradeE2 h (nuWeightLabel model X (s+k+1) (t+k) w hw₁ y) =
          nuWeightLabel model X (s+k+1) (t+k) w' hw₂ y := by
      subst w'
      rfl
    exact (transport _ _ (by omega) _ _ hind).symm
  · rw [absolute_boundary_restriction]
    dsimp only [α]
    rw [lambda_regrade]
    simp only [regrade_precomp,←Category.assoc,eqToHom_trans]
    rfl

end
end KIP126.ProofTools.Internal.Leibniz
