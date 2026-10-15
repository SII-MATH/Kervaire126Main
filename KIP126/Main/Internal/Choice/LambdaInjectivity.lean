module

public import KIP126.Main.Conditions
public import KIP126.Def.ProofTools.Operations

/-! Lambda injectivity from the original proved Main/Solution/Computation/Lambda
at bbac1fc05843 (MIT). The fixed upstream BHS comparisons and separatedness
supply their original mathematical roles; no new proof input is added. -/
@[expose] section
namespace KIP126.Main.Internal.Choice
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 10000

private def lambdaAction (m n : ℤ) (X : SyntheticSpectrum) :
    BiHom m n X → BiHom m (n - 1) X := by
  intro f
  have heq : (m, n) + (0, -1) = (m, n - 1) := by
    ext <;> simp [sub_eq_add_neg]
  refine eqToHom ?_ ≫
    (SyntheticCategory.biShift_comp (m, n) (0, -1)).inv.app S_0_0 ≫
      SyntheticCategory.lam.app (Smn m n) ≫ f
  simp only [Smn]
  rw [heq]

private def LambdaInjectiveAt (m w : ℤ) (X : SyntheticSpectrum) : Prop :=
  Function.Injective (lambdaAction m w X)
private def LambdaPowersInjectiveAt (m w : ℤ) (X : SyntheticSpectrum) : Prop :=
  ∀ k : ℕ, Function.Injective (fun a : BiHom m w X => lambdaMultiply k a)

private theorem lambda_powers_injective_of_lower_weights
    (coh : BiShiftCoherence SyntheticSpectrum) (m wt : ℤ) (X : SyntheticSpectrum)
    (h : ∀ wt' : ℤ, wt' ≤ wt → LambdaInjectiveAt m wt' X) :
    LambdaPowersInjectiveAt m wt X := by
  have one (k : ℕ) : Function.Injective (fun a :
      (SyntheticCategory.biShift (0,-(k : ℤ))).obj (Smn (Syn := SyntheticSpectrum) m wt) ⟶ X =>
      SyntheticCategory.lam.app _ ≫ a) := by
    let e : Smn (Syn := SyntheticSpectrum) m (wt-k) ≅
        (SyntheticCategory.biShift (0,-(k : ℤ))).obj (Smn m wt) :=
      eqToIso (by dsimp only [Smn]; congr 1; simp [sub_eq_add_neg]) ≪≫
        ((SyntheticCategory.biShift_comp (m,wt) (0,-(k : ℤ))).app S_0_0).symm
    intro a b hab
    apply (cancel_epi e.hom).mp
    apply h (wt-k) (by omega)
    dsimp only [lambdaAction]
    have hc : SyntheticCategory.lam.app (Smn (Syn := SyntheticSpectrum) m (wt-k)) ≫ (e.hom ≫ a) =
        SyntheticCategory.lam.app (Smn (Syn := SyntheticSpectrum) m (wt-k)) ≫ (e.hom ≫ b) := by
      have hn := SyntheticCategory.lam.naturality e.hom
      dsimp only [Functor.id_map] at hn
      rw [← Category.assoc, ← Category.assoc, ← hn]
      simpa only [Category.assoc] using
        congrArg (fun z => (SyntheticCategory.biShift (0,-1)).map e.hom ≫ z) hab
    exact congrArg (fun z => _ ≫ _ ≫ z) hc
  have powers (k : ℕ) : Function.Injective (fun a : BiHom m wt X =>
      lambdaPow k (Smn m wt) ≫ a) := by
    induction k with
    | zero =>
      intro a b hab
      exact (cancel_epi (SyntheticCategory.biShift_zero.hom.app (Smn m wt))).mp hab
    | succ k ih =>
      intro a b hab
      apply ih
      apply one k
      rw [lambdaPow_add coh k 1 (k+1) rfl, lambdaPow_one coh] at hab
      have hc := (cancel_epi ((lambdaShiftAddIso k 1 (k+1) rfl).inv.app (Smn (Syn := SyntheticSpectrum) m wt))).mp
        (by simpa only [Category.assoc] using hab)
      have hn := SyntheticCategory.lam.naturality (lambdaPow k (Smn (Syn := SyntheticSpectrum) m wt))
      dsimp only [Functor.id_map] at hn
      change (SyntheticCategory.biShift (0,-1)).map (lambdaPow k (Smn m wt)) ≫
        (SyntheticCategory.lam.app (Smn m wt) ≫ a) =
        (SyntheticCategory.biShift (0,-1)).map (lambdaPow k (Smn m wt)) ≫
        (SyntheticCategory.lam.app (Smn m wt) ≫ b) at hc
      rw [← Category.assoc, ← Category.assoc] at hc
      rw [hn] at hc
      simpa only [Category.assoc] using hc
  intro k a b hab
  apply powers k
  dsimp only [lambdaMultiply] at hab
  have hc := (cancel_epi (eqToHom (by congr 1; simp))).mp hab
  exact (cancel_epi ((SyntheticCategory.biShift_comp (m,wt) (0,-(k : ℤ))).inv.app S_0_0)).mp
    (by simpa only [Category.assoc] using hc)

private theorem selected_homotopyMap_injective_of_eInfty
    (X Y : SyntheticObject) (f : X.obj model.nu model.auxiliary ⟶ Y.obj model.nu model.auxiliary)
    (m w : ℤ)
    (hinj : ∀ s : ℕ, Function.Injective
      ((model.family.functor.map f).eInftyMap (s,m+s,w))) :
    Function.Injective (syntheticHomotopyMap f (m,w)) := by
  have hker (a : BiHom m w (X.obj model.nu model.auxiliary))
      (ha : a ≫ f = 0) : a = 0 := by
    apply KIP126.AdamsSynthetic.Standard.synthetic_homotopy_separated X m w a
    intro s
    induction s with
    | zero =>
      refine ⟨a ≫ (model.syntheticTower.tower _).zeroIso.inv, ?_⟩
      change (a ≫ (model.syntheticTower.tower _).zeroIso.inv) ≫
        (model.syntheticTower.tower _).projection 0 = a
      simp only [AbstractAdamsTower.projection,Int.toNat_zero,AbstractAdamsTower.map_self,
        Category.id_comp,Category.assoc,Iso.inv_hom_id,Category.comp_id]
      erw [Category.id_comp, Iso.inv_hom_id, Category.comp_id]
    | succ s ih =>
      have h := KIP126.ProofTools.Operations.next_filtration_of_infinity_injective
        (model.convergentMap X Y f) (m,w) s (hinj s) a ih (by
          rw [ha]
          exact Submodule.zero_mem _)
      simpa only [Nat.cast_add,Nat.cast_one,FiltrationAtLeast] using h
  intro a b hab
  apply sub_eq_zero.mp
  exact hker (a-b) (by change (syntheticHomotopyMap f (m,w)) (a-b) = 0; rw [map_sub,hab,sub_self])

private theorem paper_boundaries_step (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
    (hd : (model.classical.obj (X.obj model.auxiliary)).d r
      (p-(model.classical.obj (X.obj model.auxiliary)).diffDeg r) = 0) :
    boundaries model X r p = boundaries model X (r-1) p := by
  let E := model.classical.obj (X.obj model.auxiliary)
  have hb := boundaries_succ_of_zero E r (by dsimp only [E]; rw [model.classical.firstPage]; exact hr)
    (p-E.diffDeg r) hd
  rw [sub_add_cancel] at hb
  have hfirst : E.r₀ = 2 := model.classical.firstPage _
  rw [hfirst] at hb
  have hi : (r-1).toNat = (r-2).toNat+1 := by omega
  have hi' : (r-1-1).toNat = (r-2).toNat := by congr 1; omega
  unfold boundaries boundaryLabel
  dsimp only
  rw [hi,hi']
  let q0 : (E.ssData p).page 0 ⟶ E.Page 2 p :=
    eqToHom (by simp only [Page,hfirst,sub_self,Int.toNat_zero,Nat.cast_zero])
  have hcongr (B B' : Subobject (E.ssData p).V)
      (hB : B ≤ (E.ssData p).Z 0) (hB' : B' ≤ (E.ssData p).Z 0)
      (heq : B=B') :
      LinearMap.range (Subobject.ofLE B _ hB ≫ (E.ssData p).pageπ 0 ≫
        q0).hom =
      LinearMap.range (Subobject.ofLE B' _ hB' ≫ (E.ssData p).pageπ 0 ≫
        q0).hom := by
    subst B'
    rfl
  exact hcongr _ _ _ _ hb

private theorem subquotient_map_injective_of_boundary_eq {R A : Type*}
    [Ring R] [AddCommGroup A] [Module R A] (Z B B' : Submodule R A)
    (hB : B ≤ B') (heq : B=B') :
    Function.Injective (subquotientMap (le_refl Z) hB) := by
  subst B'
  have hid (x : E2Subquotient Z B) : subquotientMap (le_refl Z) hB x = x := by
    refine Submodule.Quotient.induction_on (B.comap Z.subtype) x ?_
    intro a
    rfl
  intro x y h
  rw [hid,hid] at h
  exact h

private theorem nu_lambda_injective_from_source (X : ClassicalObject) (m wt : ℤ)
    (hsource : NoOutgoingAt (model.classical.obj (X.obj model.auxiliary))
      (wt-m-2) (wt-1)) :
    LambdaInjectiveAt m wt (model.nu.functor.obj (X.obj model.auxiliary)) := by
  have bhs_lambdaMap_injective (s : ℤ) :
      Function.Injective (KIP126.Literature.Standard.infinityLambda (.nu X) 1 (s,m+s) wt) := by
    let E := model.classical.obj (X.obj model.auxiliary)
    by_cases hw : wt ≤ m+s
    · have hr : 2 ≤ 2+(m+s)-wt := by omega
      have hidx : (s,m+s)-E.diffDeg (2+(m+s)-wt) = (wt-m-2,wt-1) := by
        rw [show E.diffDeg (2+(m+s)-wt) = (2+(m+s)-wt,2+(m+s)-wt-1) from model.classical.differentialDegree _ _]
        ext <;> dsimp <;> omega
      have hd : E.d (2+(m+s)-wt) ((s,m+s)-E.diffDeg (2+(m+s)-wt)) = 0 := by
        rw [hidx]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        exact hsource _ hr y
      have hB := paper_boundaries_step X (2+(m+s)-wt) hr (s,m+s) hd
      have hB' : boundaries model X (1+(m+s)-wt) (s,m+s) =
          boundaries model X (1+(m+s)-(wt-1)) (s,m+s) := by
        convert hB.symm using 1 <;> congr 1 <;> omega
      have hq := subquotient_map_injective_of_boundary_eq
        (permanentCycles model X (s,m+s)) _ _
        (boundaries_monotone model X (s,m+s) (show 1+(m+s)-wt ≤ 1+(m+s)-(wt-1) by omega)) hB'
      intro x y hxy
      apply (KIP126.Literature.Standard.infinityNuWindow X (s,m+s) wt hw).injective
      apply hq
      have hx := KIP126.Literature.Standard.eInfinity_lambda_nu X 1 (s,m+s) wt hw x
      have hy := KIP126.Literature.Standard.eInfinity_lambda_nu X 1 (s,m+s) wt hw y
      exact hx.symm.trans ((congrArg (KIP126.Literature.Standard.infinityNuWindow
        X (s,m+s) (wt-1) (by omega)) hxy).trans hy)
    · have hz : Subsingleton (nuEInftyModel model X (s,m+s) wt) := by
        simp only [nuEInftyModel,hw,ite_false]
        infer_instance
      intro x y _
      apply (KIP126.Literature.Standard.eInfinity_nu X (s,m+s) wt).injective
      exact hz.elim _ _
  have actual_lambda_eMap_injective (s : ℤ) :
      Function.Injective (((model.family.functor.map
        (lambdaPow 1 (model.nu.functor.obj (X.obj model.auxiliary)))).eInftyMap
          (s,m+s,wt-1)).hom) := by
    let e := KIP126.Literature.Standard.infinityShiftData.shift model (.nu X) 1 (s,m+s) wt
    have hl : KIP126.Literature.Standard.infinityLambda (.nu X) 1 (s,m+s) wt =
        e.hom ≫ (model.family.map (lambdaPow 1 (model.nu.functor.obj (X.obj model.auxiliary)))).eInftyMap (s,m+s,wt-1) := by
      simp only [KIP126.Literature.Standard.infinityLambda,InfinityShiftCoordinates.lambdaMap,
        Nat.one_ne_zero, ↓reduceDIte]
      rfl
    intro x y hxy
    apply e.symm.toLinearEquiv.injective
    apply bhs_lambdaMap_injective s
    rw [hl]
    simp only [ModuleCat.comp_apply]
    have hx := e.toLinearEquiv.apply_symm_apply x
    have hy := e.toLinearEquiv.apply_symm_apply y
    change e.hom (e.inv x) = x at hx
    change e.hom (e.inv y) = y at hy
    change (model.family.map (lambdaPow 1 (model.nu.functor.obj (X.obj model.auxiliary)))).eInftyMap
      (s,m+s,wt-1) (e.hom (e.inv x)) =
      (model.family.map (lambdaPow 1 (model.nu.functor.obj (X.obj model.auxiliary)))).eInftyMap
      (s,m+s,wt-1) (e.hom (e.inv y))
    rw [hx,hy]
    exact hxy
  have lambda_action_injective_of_actual_map
      (Y : SyntheticSpectrum) (m w : ℤ)
      (hinj : Function.Injective (syntheticHomotopyMap (SyntheticCategory.lam.app Y) (m,w-1))) :
      LambdaInjectiveAt m w Y := by
    let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum) (0,-1)
    let e : Smn (Syn := SyntheticSpectrum) m (w-1) ≅ F.obj (Smn m w) :=
      eqToIso (by dsimp only [Smn]; congr 1; simp [sub_eq_add_neg]) ≪≫
        ((SyntheticCategory.biShift_comp (m,w) (0,-1)).app S_0_0).symm
    intro a b hab
    have hc : SyntheticCategory.lam.app (Smn (Syn := SyntheticSpectrum) m w) ≫ a =
        SyntheticCategory.lam.app (Smn (Syn := SyntheticSpectrum) m w) ≫ b := by
      dsimp only [lambdaAction] at hab
      have hc := (cancel_epi (eqToHom (by congr 1; simp))).mp hab
      exact (cancel_epi ((SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0)).mp
        (by simpa only [Category.assoc] using hc)
    apply (SyntheticCategory.biShift_fullyFaithful (Syn := SyntheticSpectrum) (0,-1)).map_injective
    apply (cancel_epi e.hom).mp
    apply hinj
    change (e.hom ≫ F.map a) ≫ SyntheticCategory.lam.app Y =
      (e.hom ≫ F.map b) ≫ SyntheticCategory.lam.app Y
    rw [Category.assoc,Category.assoc,SyntheticCategory.lam.naturality,
      SyntheticCategory.lam.naturality]
    simpa only [Functor.id_map,Category.assoc] using congrArg (fun z => e.hom ≫ z) hc
  apply lambda_action_injective_of_actual_map
  apply selected_homotopyMap_injective_of_eInfty (.shift (0,-1) (.nu X)) (.nu X)
  intro s
  have h := actual_lambda_eMap_injective s
  rw [lambdaPow_one model.quotients.coherence] at h
  exact h

private theorem nu_lambda_powers_injective_of_source_halfplane
    (X : ClassicalObject) (m wgt : ℤ)
    (hsource : ∀ q : ℤ, q ≤ wgt-m-2 →
      NoOutgoingAt (model.classical.obj (X.obj model.auxiliary)) q (q+m+1)) :
    LambdaPowersInjectiveAt m wgt (model.nu.functor.obj (X.obj model.auxiliary)) := by
  apply lambda_powers_injective_of_lower_weights model.quotients.coherence m wgt
  intro wt hwt
  apply nu_lambda_injective_from_source X m wt
  simpa only [show wt-m-2+m+1 = wt-1 by omega] using hsource (wt-m-2) (by omega)

end
end KIP126.Main.Internal.Choice
end
