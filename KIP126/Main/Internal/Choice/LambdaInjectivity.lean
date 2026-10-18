module

public import KIP126.Main.Conditions
public import KIP126.ProofTools.Operations

/-! Lambda injectivity from the actual cofiber triangle. The first-quotient
kernel source has the indicated classical bidegree; permanent labels lift
through ν by the existing selected BHS comparison, so their connecting map
vanishes. No separation of an untruncated object is used. -/
@[expose] section
namespace KIP126.Main.Internal.Choice
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
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

private theorem nu_first_quotient_label_surjective (X : ClassicalObject) (s t : ℤ) :
    Function.Surjective (firstLabel model X s t) := by
  let Q := XModLambdaN (nuZero model X) 1
  have hcast : BiHom (t-s) (t+0) Q = BiHom (t-s) t Q := by rw [add_zero]
  intro b
  refine ⟨model.firstQuotient X 0 s t ((Equiv.cast hcast).symm b), ?_⟩
  change (Equiv.cast hcast) ((model.firstQuotient X 0 s t).symm
    ((model.firstQuotient X 0 s t) ((Equiv.cast hcast).symm b))) = b
  rw [LinearEquiv.symm_apply_apply,Equiv.apply_symm_apply]

private theorem nu_first_quotient_lift_of_permanent
    (X : ClassicalObject) (s t : ℤ)
    (hperm : ∀ x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t),
      IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) (s,t) x)
    (b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)) :
    ∃ c : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)),
      c ≫ XModLambdaN.incl _ 1 = b := by
  let e := SyntheticCategory.biShift_zero.app (model.nu.functor.obj (X.obj model.auxiliary))
  let b₀ := b ≫ XModLambdaN.map e.inv 1
  have hsurj : Function.Surjective (firstLabel model X s t) := by
    let Q := XModLambdaN (nuZero model X) 1
    have hcast : BiHom (t-s) (t+0) Q = BiHom (t-s) t Q := by rw [add_zero]
    intro b
    refine ⟨model.firstQuotient X 0 s t ((Equiv.cast hcast).symm b), ?_⟩
    change (Equiv.cast hcast) ((model.firstQuotient X 0 s t).symm
      ((model.firstQuotient X 0 s t) ((Equiv.cast hcast).symm b))) = b
    rw [LinearEquiv.symm_apply_apply,Equiv.apply_symm_apply]
  obtain ⟨x,hb₀⟩ := hsurj b₀
  have hp : ClassicalPermanentCycle model X (s,t) x := hperm x
  obtain ⟨c,hc⟩ := (KIP126.Literature.Standard.selected_permanent_lift X s t x).mp hp
  change c ≫ XModLambdaN.incl _ 1 = firstLabel model X s t x at hc
  refine ⟨c ≫ e.hom, ?_⟩
  rw [Category.assoc, XModLambdaN.incl_naturality, ←Category.assoc, hc]
  rw [hb₀]
  dsimp only [b₀]
  rw [Category.assoc, ←model.quotients.functoriality.map_comp, Iso.inv_hom_id,
    model.quotients.functoriality.map_id]
  simp only [Functor.id_obj,Category.comp_id]

private theorem lambda_kernel_zero_of_first_quotient_lifts
    (Y : SyntheticSpectrum) (m w : ℤ)
    (hlift : ∀ b : BiHom (m+1) w (XModLambdaN Y 1),
      ∃ c : BiHom (m+1) w Y, c ≫ XModLambdaN.incl Y 1 = b)
    (a : BiHom m w ((SyntheticCategory.biShift (0,-1)).obj Y))
    (ha : a ≫ SyntheticCategory.lam.app Y = 0) : a = 0 := by
  let F := shiftFunctor SyntheticSpectrum (1:ℤ)
  have hshift : F.map a ≫ F.map (lambdaPow 1 Y) = 0 := by
    rw [←Functor.map_comp,lambdaPow_one model.quotients.coherence,ha,Functor.map_zero]
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle Y 1).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished Y 1) (F.map a) hshift
  let eS : Smn (Syn:=SyntheticSpectrum) (m+1) w ≅ F.obj (Smn m w) :=
    ((biShiftAddIso (m,w) (1,0) (m+1,w) (by ext <;> simp)).app S_0_0).symm ≪≫
      (SyntheticCategory.biShift_compat 1).app (Smn m w)
  obtain ⟨c,hc⟩ := hlift (eS.hom ≫ b)
  have hboundary : (eS.hom ≫ b) ≫ XModLambdaN.proj Y 1 = 0 := by
    rw [←hc,Category.assoc,XModLambdaN.incl_comp_proj,comp_zero]
  have hz : F.map a = 0 := by
    apply (cancel_epi eS.hom).mp
    rw [hb]
    simpa [F,XModLambdaN.cofiberTriangle,Category.assoc] using hboundary
  exact F.map_injective (by simpa only [Functor.map_zero] using hz)


private theorem lambda_shifted_finite_high_filtration_zero
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (δ : ℤ × ℤ) (m w s : ℤ)
    (hs : (q:ℤ) ≤ (m-δ.1)+s-(w-δ.2))
    (a : BiHom m w ((SyntheticCategory.biShift δ).obj
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)))
    (ha : FiltrationAtLeast model.syntheticTower s a) : a=0 := by
  let p : ℤ × ℤ := (m-δ.1,w-δ.2)
  have hp : p+δ=(m,w) := by ext <;> simp [p]
  let e : FilteredPieceIso (model.convergence (.quotient q (.nu X))).filtration
      (model.convergence (.shift δ (.quotient q (.nu X)))).filtration p (m,w) :=
    hp ▸ (KIP126.AdamsSynthetic.Standard.essShift δ).filtered (.quotient q (.nu X)) p
  have hmem : a ∈ ModuleCat.subobjectModule _
      ((model.convergence (.shift δ (.quotient q (.nu X)))).filtration.F s (m,w)) := by
    simpa only [SyntheticTowerConvergence.filtration,
      SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast,SyntheticObject.obj] using ha
  obtain ⟨x,hx⟩ := hmem
  have hcomm := ConcreteCategory.congr_hom (e.symm.level_arrow s) x
  simp only [ModuleCat.comp_apply, FilteredPieceIso.symm] at hcomm
  have hm : e.ambient.inv a ∈ ModuleCat.subobjectModule _
      ((model.convergence (.quotient q (.nu X))).filtration.F s p) := by
    refine ⟨(e.level s).inv x,?_⟩
    change ((model.convergence (.quotient q (.nu X))).filtration.F s p).arrow
      ((e.level s).inv x) = e.ambient.inv a
    simpa only [hx,Iso.symm_hom] using hcomm
  have hb : FiltrationAtLeast model.syntheticTower s (e.ambient.inv a) := by
    simpa only [SyntheticTowerConvergence.filtration,
      SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hm
  have hz := KIP126.ProofTools.Internal.Mahowald.finite_high_filtration_zero X q hq p.1 p.2 s hs
    (e.ambient.inv a) hb
  apply (ModuleCat.mono_iff_injective e.ambient.inv).mp inferInstance
  simpa only [map_zero] using hz


private theorem lambda_boundary_no_return (X : ClassicalObject) (q : ℕ) (hq : 0<q)
    (m w : ℤ)
    (c : BiHom m w ((SyntheticCategory.biShift (1,-(q:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary))))
    (z : (SyntheticCategory.biShift (1,-(q:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
        XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) : c ≫ z = 0 := by
  let A : SyntheticObject := .shift (1,-(q:ℤ)) (.nu X)
  let B : SyntheticObject := .quotient q (.nu X)
  let L : ℤ := w-m+1+q
  have hzA (k : ℤ) (hk : k<L) :
      IsZero (((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (k,m+k,w)).eInfty) := by
    haveI : Subsingleton (nuEInftyModel model X (k,m-1+k) (w+q)) := by
      simp only [nuEInftyModel,show ¬ w+(q:ℤ)≤(k,m-1+k).2 by dsimp [L] at hk ⊢; omega,ite_false]
      infer_instance
    haveI : Subsingleton (((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData
        (k,m-1+k,w+q)).eInfty) :=
      (KIP126.Literature.Standard.eInfinity_nu X (k,m-1+k) (w+q)).injective.subsingleton
    have hz := ModuleCat.isZero_of_subsingleton (((model.family.obj
      (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData (k,m-1+k,w+q)).eInfty)
    let e := towerInfinityIso (model.convergence (.nu X)) (model.convergence A)
      ((KIP126.AdamsSynthetic.Standard.essShift (1,-(q:ℤ))).filtered (.nu X) (m-1,w+q)) k
    have he := hz.of_iso e.symm
    simpa only [e,A,Prod.fst_add,Prod.snd_add,sub_add_cancel,add_neg_cancel_right] using he
  have hc0 : FiltrationAtLeast model.syntheticTower 0 c := by
    refine ⟨c ≫ (model.syntheticTower.tower _).zeroIso.inv, ?_⟩
    change (c ≫ (model.syntheticTower.tower _).zeroIso.inv) ≫
      (model.syntheticTower.tower _).projection 0 = c
    simp only [AbstractAdamsTower.projection,Int.toNat_zero,AbstractAdamsTower.map_self]
    erw [Category.assoc,Category.id_comp,Iso.inv_hom_id,Category.comp_id]
  have hcL : FiltrationAtLeast model.syntheticTower L c := by
    by_cases hL : L≤0
    · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) hL hc0
    · exact (filtration_iff_of_infinity_zero (model.convergence A) 0 L m w
        (by omega) (fun k _ hk => hzA k hk) c).mp hc0
  have hcz := map_preserves_filtration (model.convergentMap A B z) (m,w) L c hcL
  exact finite_high_filtration_zero X q hq m w L (by dsimp [L]; omega) (c≫z) hcz

private theorem lambda_quotient_maps_equal_on_spheres
    (X : ClassicalObject) (q : ℕ) (hq : 0<q)
    (f g : XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q ⟶
      XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)
    (hfg : XModLambdaN.incl _ q ≫ f = XModLambdaN.incl _ q ≫ g)
    (m w : ℤ) (c : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    c ≫ f = c ≫ g := by
  let Y := model.nu.functor.obj (X.obj model.auxiliary)
  have hzero : XModLambdaN.incl Y q ≫ (f-g) = 0 := by
    rw [Preadditive.comp_sub,hfg,sub_self]
  obtain ⟨z,hz⟩ := (XModLambdaN.cofiberTriangle Y q).yoneda_exact₃
    (XModLambdaN.cofiberTriangle_distinguished Y q) (f-g) hzero
  let e := (KIP126.ProofTools.Internal.Mahowald.biSuspensionIso (q:ℤ) Y).symm
  have hn := lambda_boundary_no_return X q hq m w
    ((c ≫ XModLambdaN.proj Y q) ≫ e.hom) (e.inv ≫ z)
  have hn' : (c ≫ XModLambdaN.proj Y q) ≫ z = 0 := by
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using hn
  apply sub_eq_zero.mp
  rw [←Preadditive.comp_sub,hz,←Category.assoc]
  exact hn'

private theorem lambda_first_quotient_delta_evaluation
    (X : ClassicalObject) (i j : ℕ)
    (T : LambdaRhoDeltaTriangle (model.nu.functor.obj (X.obj model.auxiliary)) i j)
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i)) :
    a ≫ T.delta = a ≫ XModLambdaN.proj (model.nu.functor.obj (X.obj model.auxiliary)) i ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map
          (XModLambdaN.incl (model.nu.functor.obj (X.obj model.auxiliary)) (j-i))) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  obtain ⟨c,hc,hδ⟩ := complete_distinguished_triangle_morphism
    (XModLambdaN.cofiberTriangle A i) (Triangle.mk T.lambdaMap T.rho T.delta)
    (XModLambdaN.cofiberTriangle_distinguished A i) T.distinguished
    ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i)))
    (XModLambdaN.incl A j) T.lambda_quotient.symm
  change XModLambdaN A i ⟶ XModLambdaN A i at c
  change XModLambdaN.incl A i ≫ c = XModLambdaN.incl A j ≫ T.rho at hc
  have hc' : XModLambdaN.incl A i ≫ c = XModLambdaN.incl A i ≫ 𝟙 _ := by
    rw [hc,T.rho_quotient,Category.comp_id]
  have hac : a ≫ c = a := by
    simpa only [Category.comp_id] using
      lambda_quotient_maps_equal_on_spheres X i T.i_pos c (𝟙 _) hc' m w a
  change XModLambdaN.proj A i ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) =
    c ≫ T.delta at hδ
  calc
    a ≫ T.delta = (a ≫ c) ≫ T.delta := by rw [hac]
    _ = a ≫ XModLambdaN.proj A i ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) := by
      rw [Category.assoc,←hδ]

private theorem lambda_zero_shift_delta_evaluation
    (X : ClassicalObject) (i j : ℕ) (hi : 0 < i) (hij : i < j) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (nuZero model X) i)) :
    a ≫ ((model.quotients.tower (nuZero model X)).triangle hi hij).delta =
    a ≫ XModLambdaN.proj (nuZero model X) i ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map
          (XModLambdaN.incl (nuZero model X) (j-i))) := by
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  let e : nuZero model X ≅ V := SyntheticCategory.biShift_zero.app V
  let eQ := (model.quotients.functoriality.functor (j-i)).mapIso e
  let post := (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
    ((SyntheticCategory.biShift (0,-(i:ℤ))).mapIso eQ)
  apply (cancel_mono post.hom).mp
  change (a ≫ ((model.quotients.tower (nuZero model X)).triangle hi hij).delta) ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.map e.hom (j-i))) = _
  rw [Category.assoc, ←(model.quotients.natural e.hom).delta_naturality hi hij,
    ←Category.assoc, lambda_first_quotient_delta_evaluation X i j _ m w]
  simp only [Category.assoc, post, eQ, Functor.mapIso_hom,
    LambdaQuotientFunctoriality.functor]
  rw [←Category.assoc (XModLambdaN.map e.hom i),XModLambdaN.proj_naturality]
  have hmap := congrArg (fun f => (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((SyntheticCategory.biShift (0,-(i:ℤ))).map f))
    (XModLambdaN.incl_naturality e.hom (j-i))
  simp only [Functor.map_comp] at hmap
  simpa only [Category.assoc] using congrArg
    (fun f => a ≫ XModLambdaN.proj (nuZero model X) i ≫ f) hmap


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
  intro a b hab
  apply sub_eq_zero.mp
  apply lambda_kernel_zero_of_first_quotient_lifts
    (model.nu.functor.obj (X.obj model.auxiliary)) m (wt-1)
  · have hperm (x : (model.classical.obj (X.obj model.auxiliary)).Page 2
        (wt-m-2,wt-1)) :
        IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) (wt-m-2,wt-1) x := by
      apply isPermanentCycle_of_reachesPage _ 2
        (by rw [model.classical.firstPage]) _ x
        ⟨x,RepresentsOnPage.self_two x⟩
      intro r hr
      ext y
      exact hsource r hr y
    have hlift := nu_first_quotient_lift_of_permanent X (wt-m-2) (wt-1) hperm
    rw [show wt-1-(wt-m-2)=m+1 by omega] at hlift
    exact hlift
  · change (a-b) ≫ SyntheticCategory.lam.app _ = 0
    rw [Preadditive.sub_comp]
    exact sub_eq_zero.mpr hab

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
