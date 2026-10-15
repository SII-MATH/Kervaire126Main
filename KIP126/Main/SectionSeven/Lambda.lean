module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Proofs
public import KIP126.Def.Algebra.Filtration.Data
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Def.ClassicalAdams.SphereVanishing.Proofs
public import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
public import KIP126.Computation.Hypotheses.Joint
public import KIP126.Computation.LinCoordinates.Certificates.SphereAndCofiber.LowStemDifferentials
public import KIP126.Main.SectionSeven.High125

@[expose] public section

/-! Precise finite/weight-window derivations. The relevant raw degrees are
already selected, including empty bases. No new permanent-cycle claim is
added to C. All unfinished mathematical proofs remain explicit here. -/
namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Synthetic.SpectralSequence
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  {D : AdamsComparison H M Syn} {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
  {η : BiHom 1 2 (S_0_0 : Syn)}

private theorem realization_additive : D.recovery.realization.Additive := by
  letI := D.recovery.adjunction.isLeftAdjoint
  letI := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts D.recovery.realization
  exact Functor.additive_of_preservesBinaryBiproducts _
private theorem realization_injective_of_lambda_powers
    (kernel : KIP126.Literature.AdamsSynthetic.RealizationKernel D) (X : SyntheticObject) (m wt : ℤ)
    (h : LambdaPowersInjectiveAt m wt (X.obj D.nu D.hopfAndDetector)) :
    Function.Injective (fun a : BiHom m wt (X.obj D.nu D.hopfAndDetector) =>
      D.recovery.realization.map a) := by
  letI := realization_additive (D := D)
  intro a b hab
  apply sub_eq_zero.mp
  obtain ⟨k, hk⟩ := (kernel X m wt (a-b)).mp (by simp only [Functor.map_sub, hab, sub_self])
  apply h k
  simpa only [lambdaMultiply, Category.comp_id, Category.assoc, Limits.comp_zero] using hk

omit [HasFunctorialCofiber (C := Syn)] in
private theorem lambda_h0_map_zero_iff
    {T : Type*} [Category T] [Preadditive T] (R : Syn ⥤ T) [R.Additive]
    (coh : BiShiftCoherence Syn) (h0 : BiHom 0 1 (S_0_0 : Syn))
    (hlambda : lambdaMultiply 1 h0 = KIP126.Literature.AdamsSynthetic.syntheticTwo)
    (b : BiHom 62 70 (S_0_0 : Syn)) :
    R.map (lambdaMultiply 1 (sphereProduct h0 b)) = 0 ↔ R.map (b+b) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
    let F := SyntheticCategory.biShift (Syn := Syn) (62,70)
    have ht : R.map (F.map (lambdaMultiply 1 h0) ≫ b) = 0 ↔
        R.map (F.map (SyntheticCategory.lam.app (Smn 0 1))) ≫ R.map (F.map h0) ≫ R.map b = 0 := by
      simp only [lambdaMultiply, lambdaPow_one coh, F, eqToHom_refl,
        Functor.map_comp, Category.id_comp, Category.assoc, Limits.comp_eq_zero_iff_of_epi]
    simp only [lambdaMultiply, lambdaPow_one coh, eqToHom_refl,
      Functor.map_comp, Category.id_comp, Limits.comp_eq_zero_iff_of_epi]
    dsimp only [sphereProduct]
    have hn := SyntheticCategory.lam.naturality
      ((SyntheticCategory.biShift_comp (0,1) (62,70)).inv.app (S_0_0 : Syn))
    simp only [Prod.mk_add_mk, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
    erw [← hn]
    simp only [Functor.map_comp, Category.assoc, Limits.comp_eq_zero_iff_of_epi]
    erw [coh.lambda_comm (62,70) (Smn 0 1)]
    simp only [Functor.map_comp, Category.assoc, Limits.comp_eq_zero_iff_of_epi]
    change R.map (F.map (SyntheticCategory.lam.app (Smn 0 1))) ≫
      R.map (F.map h0) ≫ R.map b = 0 ↔ _
    rw [← ht, hlambda]
    simp only [KIP126.Literature.AdamsSynthetic.syntheticTwo, Functor.id_obj, Functor.map_comp, two_smul, Functor.map_add,
      Category.assoc, Preadditive.add_comp,
      ← Preadditive.comp_add, Limits.comp_eq_zero_iff_of_epi]

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Degreewise E∞ injectivity controls actual homotopy through every tower
filtration level; separatedness removes the infinite-filtration kernel. -/
private theorem homotopyMap_injective_of_eInfty
    (X Y : SyntheticObject) (f : X.obj D.nu D.hopfAndDetector ⟶ Y.obj D.nu D.hopfAndDetector)
    (m w : ℤ)
    (hinj : ∀ s : ℕ, Function.Injective
      ((D.family.functor.map f).eInftyMap (s,m+s,w))) :
    Function.Injective (syntheticHomotopyMap f (m,w)) := by
  have filtered_kernel_step
      {A B : (ℤ × ℤ) → ModuleCat.{v} ℤ} (F : Filtration A) (G : Filtration B)
      (f : FilteredMorphism F G) (s : ℤ) (i : ℤ × ℤ)
      (hinj : Function.Injective (f.inducedGrMap s i))
      (a : (Subobject.underlying.obj (F.F s i) : ModuleCat ℤ))
      (ha : f.map i ((F.F s i).arrow a) = 0) :
      (F.F s i).arrow a ∈ (ModuleCat.subobjectModule (A i)) (F.F (s+1) i) := by
    let phi := (f.compat s i).choose
    have hp0 : phi a = 0 := by
      apply (ModuleCat.mono_iff_injective (G.F s i).arrow).mp inferInstance
      have hp := ConcreteCategory.congr_hom (f.compat s i).choose_spec a
      change (G.F s i).arrow (phi a) = f.map i ((F.F s i).arrow a) at hp
      rw [hp,ha,map_zero]
    have hcomm : F.toAssociatedGraded s i ≫ f.inducedGrMap s i = phi ≫ G.toAssociatedGraded s i := by
      unfold Filtration.toAssociatedGraded FilteredMorphism.inducedGrMap Filtration.inducedAssocGradedMap
      exact cokernel.π_desc _ _ _
    have hga : F.toAssociatedGraded s i a = 0 := by
      apply hinj
      have hh := ConcreteCategory.congr_hom hcomm a
      change f.inducedGrMap s i (F.toAssociatedGraded s i a) = G.toAssociatedGraded s i (phi a) at hh
      rw [hh,hp0,map_zero,map_zero]
    exact (subobject_cokernel_π_eq_zero_iff (F.F (s+1) i) (F.F s i) (F.mono s i) a).mp hga
  have convergence_graded_injective
      {E₁ E₂ : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ × ℤ)}
      {A B : (ℤ × ℤ) → ModuleCat.{v} ℤ} {F : Filtration A} {G : Filtration B}
      {conv₁ : Convergence E₁ A F} {conv₂ : Convergence E₂ B G}
      (c : ConvergenceMorphism conv₁ conv₂) (i : ℤ × ℤ × ℤ)
      (hi : Function.Injective (c.eMap i)) :
      Function.Injective (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat
        (conv₁.reindex i).1 (conv₁.reindex i).2) := by
    intro x y hxy
    let g := (conv₂.iso i).hom ≫ G.transportGraded (congrFun c.reindex_eq i).symm
    have hg : Function.Injective g := by
      haveI : IsIso (G.transportGraded (congrFun c.reindex_eq i).symm) := by
        dsimp only [Filtration.transportGraded]
        infer_instance
      exact (ModuleCat.mono_iff_injective g).mp inferInstance
    apply (conv₁.iso i).toLinearEquiv.symm.injective
    apply hi
    apply hg
    have hcomm (z : F.associatedGraded (conv₁.reindex i).1 (conv₁.reindex i).2) :
        g (c.eMap i ((conv₁.iso i).inv z)) =
        Filtration.inducedAssocGradedMap c.aMap c.filtration_compat
          (conv₁.reindex i).1 (conv₁.reindex i).2 z := by
      have h := ConcreteCategory.congr_hom (c.iso_compat i) ((conv₁.iso i).inv z)
      change g (c.eMap i ((conv₁.iso i).inv z)) =
        Filtration.inducedAssocGradedMap c.aMap c.filtration_compat
          (conv₁.reindex i).1 (conv₁.reindex i).2 ((conv₁.iso i).hom ((conv₁.iso i).inv z)) at h
      have hz : (conv₁.iso i).hom ((conv₁.iso i).inv z) = z :=
        (conv₁.iso i).toLinearEquiv.apply_symm_apply z
      rwa [hz] at h
    change g (c.eMap i ((conv₁.iso i).inv x)) = g (c.eMap i ((conv₁.iso i).inv y))
    rw [hcomm,hcomm]
    exact hxy
  obtain ⟨c,hcA,hcE⟩ := D.comparisonCompatible.convergence_natural X Y f
  let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (X.obj D.nu D.hopfAndDetector)
  let G := towerFiltration (nuCoefficientUnit H.unit D.nu) (Y.obj D.nu D.hopfAndDetector)
  let g : FilteredMorphism F G := ⟨c.aMap,c.filtration_compat⟩
  have hker (a : BiHom m w (X.obj D.nu D.hopfAndDetector))
      (ha : syntheticHomotopyMap f (m,w) a = 0) : a = 0 := by
    apply D.homotopySeparated X m w a
    intro s
    induction s with
    | zero =>
      refine ⟨a,?_⟩
      change a ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) _ 0 0 _ = a
      rw [adamsTowerMap_self]
      change a ≫ 𝟙 _ = a
      exact Category.comp_id a
    | succ s ih =>
      have hm : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy
          (X.obj D.nu D.hopfAndDetector) (m,w))) (F.F s (m,w)) := by
        simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ih
      obtain ⟨a',ha'⟩ := hm
      have hgr : Function.Injective (g.inducedGrMap s (m,w)) := by
        have hh := convergence_graded_injective c (s,m+s,w) (by
          rw [hcE]
          exact hinj s)
        change Function.Injective (Filtration.inducedAssocGradedMap c.aMap
          c.filtration_compat s (m,w))
        change Function.Injective (Filtration.inducedAssocGradedMap c.aMap
          c.filtration_compat s (m+s-s,w)) at hh
        have hdeg : (m+(s:ℤ)-(s:ℤ),w) = (m,w) := by congr 1; omega
        rw [hdeg] at hh
        exact hh
      have hstep := filtered_kernel_step F G g s (m,w) hgr a' (by
        change c.aMap (m,w) ((F.F s (m,w)).arrow a') = 0
        rw [ha',hcA]
        exact ha)
      rw [ha'] at hstep
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,Nat.cast_add,Nat.cast_one,
        FiltrationAtLeast] using hstep
  intro a b hab
  apply sub_eq_zero.mp
  exact hker (a-b) (by rw [map_sub,hab,sub_self])

open CategoryTheory.Limits KIP126.Classical.Adams.PageRepresentatives in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxRecDepth 10000 in
/-- BHS identifies λ with a boundary-quotient map. The given source rules
out exactly the new boundary, and the actual λ map is injective on homotopy. -/
private theorem nu_lambda_injective_from_source
    (A : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D) (X : ClassicalObject)
    (m wt : ℤ)
    (hsource : NoOutgoingAt (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector))
      (wt-m-2) (wt-1)) :
    LambdaInjectiveAt m wt (D.nu.functor.obj (X.obj D.hopfAndDetector)) := by
  have paper_boundaries_step (H : Mod2EilenbergMacLane (C:=C)) (X : C)
      (r : ℤ) (hr : 2≤r) (p : ℤ×ℤ)
      (hd : (adamsTowerInternalSpectralSequence H.unit X).d r
        (p-(adamsTowerInternalSpectralSequence H.unit X).diffDeg r) = 0) :
      boundaries H X r p = boundaries H X (r-1) p := by
    let E := adamsTowerInternalSpectralSequence H.unit X
    have hb := boundaries_succ_of_zero E r hr (p-E.diffDeg r) hd
    rw [sub_add_cancel] at hb
    have hi : (r-1).toNat=(r-2).toNat+1 := by omega
    have hi' : (r-1-1).toNat=(r-2).toNat := by congr 1; omega
    change (E.ssData p).B ↑((r-2).toNat+1) = (E.ssData p).B ↑(r-2).toNat at hb
    unfold boundaries boundaryMap
    dsimp only
    rw [hi,hi']
    change LinearMap.range (Subobject.ofLE ((E.ssData p).B ↑((r-2).toNat+1)) _ _ ≫ (E.ssData p).pageπ 0).hom =
      LinearMap.range (Subobject.ofLE ((E.ssData p).B ↑(r-2).toNat) _ _ ≫ (E.ssData p).pageπ 0).hom
    have hcongr (B B' : Subobject (E.ssData p).V)
        (hB : B ≤ (E.ssData p).Z 0) (hB' : B' ≤ (E.ssData p).Z 0)
        (heq : B=B') :
        LinearMap.range (Subobject.ofLE B _ hB ≫ (E.ssData p).pageπ 0).hom =
        LinearMap.range (Subobject.ofLE B' _ hB' ≫ (E.ssData p).pageπ 0).hom := by
      subst B'
      rfl
    exact hcongr _ _ _ _ hb
  have permanent_map_injective_of_boundary_eq
      (H : Mod2EilenbergMacLane (C:=C)) (X : C) {b b' : ℤ}
      (hb : b≤b') (p : ℤ×ℤ)
      (heq : boundaries H X b p = boundaries H X b' p) :
      Function.Injective (permanentQuotientMap H X hb p) := by
    have hinj (Z B B' : Submodule ℤ (Ambient H X p)) (hB : B≤B') (he : B=B') :
        Function.Injective (KIP126.Algebra.NestedQuotient.map (le_refl Z) hB) := by
      subst B'
      exact KIP126.Algebra.NestedQuotient.cycle_map_injective (le_refl Z)
    exact hinj _ _ _ (boundaries_monotone H X p hb) heq
  have bhs_lambdaMap_injective
      (A : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D) (X : ClassicalObject)
      (m wt : ℤ)
      (hsource : NoOutgoingAt (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector))
        (wt-m-2) (wt-1)) (s : ℤ) :
      Function.Injective (A.eInfty.weightShift.lambdaMap
        (D.nu.functor.obj (X.obj D.hopfAndDetector)) 1 (s,m+s) wt) := by
    let E := adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector)
    by_cases hw : wt ≤ m+s
    · have hr : 2 ≤ 2+(m+s)-wt := by omega
      have hidx : (s,m+s)-E.diffDeg (2+(m+s)-wt) = (wt-m-2,wt-1) := by
        change (s,m+s)-(2+(m+s)-wt,2+(m+s)-wt-1) = _
        ext <;> dsimp <;> omega
      have hd : E.d (2+(m+s)-wt) ((s,m+s)-E.diffDeg (2+(m+s)-wt)) = 0 := by
        rw [hidx]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        exact hsource _ hr y
      have hB := paper_boundaries_step H (X.obj D.hopfAndDetector) (2+(m+s)-wt) hr (s,m+s) hd
      have hB' : boundaries H (X.obj D.hopfAndDetector) (1+(m+s)-wt) (s,m+s) =
          boundaries H (X.obj D.hopfAndDetector) (1+(m+s)-(wt-1)) (s,m+s) := by
        convert hB.symm using 1 <;> congr 1 <;> omega
      have hq := permanent_map_injective_of_boundary_eq H (X.obj D.hopfAndDetector)
        (show 1+(m+s)-wt ≤ 1+(m+s)-(wt-1) by omega) (s,m+s) hB'
      intro x y hxy
      apply (A.eInfty.presentation.nuWindow (X.obj D.hopfAndDetector) (s,m+s) wt hw).injective
      apply hq
      have hx := A.eInfty.maps.lambda_nu (X.obj D.hopfAndDetector) 1 (s,m+s) wt hw x
      have hy := A.eInfty.maps.lambda_nu (X.obj D.hopfAndDetector) 1 (s,m+s) wt hw y
      exact hx.symm.trans ((congrArg (A.eInfty.presentation.nuWindow
        (X.obj D.hopfAndDetector) (s,m+s) (wt-1) (by omega)) hxy).trans hy)
    · have hz : Subsingleton (nuEInftyModel H (X.obj D.hopfAndDetector) (s,m+s) wt) := by
        simp only [nuEInftyModel,hw,ite_false]
        infer_instance
      intro x y hxy
      apply (A.eInfty.presentation.nu (X.obj D.hopfAndDetector) (s,m+s) wt).injective
      exact hz.elim _ _
  have bhs_actual_lambda_eMap_injective
      (A : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D) (X : ClassicalObject)
      (m wt : ℤ)
      (hsource : NoOutgoingAt (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector))
        (wt-m-2) (wt-1)) (s : ℤ) :
      Function.Injective (((D.family.functor.map
        (lambdaPow 1 (D.nu.functor.obj (X.obj D.hopfAndDetector)))).eInftyMap
          (s,m+s,wt-1)).hom) := by
    let e := A.eInfty.weightShift.lowerIso (D.nu.functor.obj (X.obj D.hopfAndDetector)) 1 (s,m+s) wt
    intro x y hxy
    apply e.injective
    apply bhs_lambdaMap_injective A X m wt hsource s
    change ((D.family.functor.map (lambdaPow 1 (D.nu.functor.obj (X.obj D.hopfAndDetector)))).eInftyMap
        (s,m+s,wt-1)).hom (e.symm (e x)) =
      ((D.family.functor.map (lambdaPow 1 (D.nu.functor.obj (X.obj D.hopfAndDetector)))).eInftyMap
        (s,m+s,wt-1)).hom (e.symm (e y))
    simpa only [LinearEquiv.symm_apply_apply] using hxy
  have lambda_action_injective_of_actual_map
      (X : Syn) (m w : ℤ)
      (hinj : Function.Injective
        (syntheticHomotopyMap (SyntheticCategory.lam.app X) (m,w-1))) :
      LambdaInjectiveAt m w X := by
    let F := SyntheticCategory.biShift (Syn := Syn) (0,-1)
    let e : Smn (Syn := Syn) m (w-1) ≅ F.obj (Smn m w) :=
      eqToIso (by dsimp only [Smn]; congr 1; simp [sub_eq_add_neg]) ≪≫
        ((SyntheticCategory.biShift_comp (m,w) (0,-1)).app S_0_0).symm
    intro a b hab
    have hc : SyntheticCategory.lam.app (Smn (Syn := Syn) m w) ≫ a =
        SyntheticCategory.lam.app (Smn (Syn := Syn) m w) ≫ b := by
      dsimp only [lambdaAction] at hab
      have hc := (cancel_epi (eqToHom (by congr 1; simp))).mp hab
      exact (cancel_epi ((SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0)).mp
        (by simpa only [Category.assoc] using hc)
    apply (SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (0,-1)).map_injective
    apply (cancel_epi e.hom).mp
    apply hinj
    change (e.hom ≫ F.map a) ≫ SyntheticCategory.lam.app X =
      (e.hom ≫ F.map b) ≫ SyntheticCategory.lam.app X
    rw [Category.assoc,Category.assoc,SyntheticCategory.lam.naturality,
      SyntheticCategory.lam.naturality]
    simpa only [Functor.id_map,Category.assoc] using congrArg (fun z => e.hom ≫ z) hc
  apply lambda_action_injective_of_actual_map
  apply homotopyMap_injective_of_eInfty
    (D := D) (.shift (0,-1) (.nu X)) (.nu X)
  intro s
  have h := bhs_actual_lambda_eMap_injective A X m wt hsource s
  rw [lambdaPow_one D.shiftCoherence] at h
  exact h

/-- BHS A.9/A.11 map compatibility and separated synthetic filtration.
In homotopy degree (m,wgt), the associated-graded kernel of lambda is
B_(2+t-wgt)/B_(1+t-wgt); its incoming source has
(s-r,t-r+1)=(wgt-m-2,wgt-1). Hence exactly this one classical source
component controls injectivity. The proof must also pass from associated
graded injectivity to actual homotopy, using D's Hausdorffness. -/
theorem lambda_injective_of_source
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (m wgt : ℤ)
    (hsource : NoOutgoingAt (sequence D .sphere) (wgt-m-2) (wgt-1)) :
    LambdaInjectiveAt m wgt (S_0_0 : Syn) := by
  set_option backward.isDefEq.respectTransparency false in
    intro a b hab
    apply (cancel_mono D.nu.unitIso.inv).mp
    apply nu_lambda_injective_from_source A.synthetic .sphere m wgt hsource
    dsimp only [lambdaAction]
    have hh := congrArg (fun z => z ≫ D.nu.unitIso.inv) hab
    simpa only [lambdaAction,Category.assoc] using hh

/-- Each iteration lowers the weight. Requiring the entire lower source
half-plane makes the all-power statement explicit and prevents silently
iterating a one-step result only known at a single weight. -/
theorem lambda_powers_injective_of_source_halfplane
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (m wgt : ℤ)
    (hsource : ∀ q : ℤ, q ≤ wgt-m-2 → NoOutgoingAt (sequence D .sphere) q (q+m+1)) :
    LambdaPowersInjectiveAt m wgt (S_0_0 : Syn) := by
  apply lambda_powers_injective_of_lower_weights D.shiftCoherence m wgt
  intro wt hwt
  apply lambda_injective_of_source A m wt
  simpa only [show wt - m - 2 + m + 1 = wt - 1 by omega] using
    hsource (wt-m-2) (by omega)

-- Keep the existing named arguments for public API compatibility.
set_option linter.unusedVariables false in
/-- The exact all-power torsion exclusion used for arbitrary theta5 choices. -/
theorem lambda_powers_injective_62_64
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G) :
    LambdaPowersInjectiveAt 62 64 (S_0_0 : Syn) := by
  apply lambda_powers_injective_of_source_halfplane A
  intro q hq
  simpa [add_assoc] using no_outgoing_stem63_nonpositive (D := D) q (by omega)

/-- Actual localization-map injectivity at the theta degree, obtained from
all-power lambda injectivity plus the sourced realization-kernel theorem.
The map is D's existing functor on these exact sphere hom groups. -/
theorem realization_injective_62_64
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G) :
    Function.Injective (fun a : BiHom 62 64 (S_0_0 : Syn) => D.recovery.realization.map a) := by
  exact realization_injective_of_lambda_powers A.synthetic.realization_kernel
    .sphere 62 64 (lambda_powers_injective_62_64 A I)

-- Keep the existing named arguments for public API compatibility.

-- Keep the existing named arguments for public API compatibility.
set_option linter.unusedVariables false in
/-- The genuine synthetic order-two assertion is a derived theorem. It
uses IWX's classical exponent-two result, the realization comparison and
62/64 injectivity; it is not identified with Xu's distinguished existence. -/
theorem theta5_choice_order_two
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G)
    (theta : BiHom 62 64 (S_0_0 : Syn))
    (htheta : ThetaChoice M D.toAdamsComparisonData theta) : theta + theta = 0 := by
  letI := realization_additive (D := D)
  apply realization_injective_62_64 A I
  simp only [Functor.map_add, Functor.map_zero]
  let α : HomotopyGroup (C := C) 62 SphereSpectrum :=
    (A.realization.coordinates.sphere 62 64).hom ≫ D.recovery.realization.map theta ≫
      D.recovery.realization.map D.nu.unitIso.inv ≫ D.recovery.nuRealizationIso.hom.app SphereSpectrum
  have h := A.classical.stem62_exponent_two α
  apply (cancel_epi (A.realization.coordinates.sphere 62 64).hom).mp
  apply (cancel_mono (D.recovery.realization.map D.nu.unitIso.inv)).mp
  apply (cancel_mono ((D.recovery.nuRealizationIso.app SphereSpectrum).hom)).mp
  erw [Preadditive.comp_add, Preadditive.add_comp, Preadditive.add_comp,
    Limits.comp_zero, Limits.zero_comp, Limits.zero_comp]
  repeat erw [Category.assoc]
  exact h
open CategoryTheory.Limits KIP126.Classical.Adams.PageRepresentatives in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxRecDepth 10000 in
/-- The distinct window needed for the B lift in Lemma 7.16. This is
NOT injectivity at weight70 or weight71. The selected stem63 sources
q<=7 include d4 at q7 (row512), d2 at q6 (row494), and the finite
permanent-cycle bounds at q3,6,7. Their incoming torsion in weight71
has zero lambda image in weight70. The proof must use both finite
staircases and the tail vanishing/actual separated filtration. -/
theorem lambda_kills_realization_kernel_62_71
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G)
    (V : SphereVanishingLine H) (a : BiHom 62 71 (S_0_0 : Syn))
    (ha : D.recovery.realization.map a = 0) : lambdaMultiply 1 a = 0 := by
  have paper_boundaries_step (H : Mod2EilenbergMacLane (C:=C)) (X : C)
      (r : ℤ) (hr : 2≤r) (p : ℤ×ℤ)
      (hd : (adamsTowerInternalSpectralSequence H.unit X).d r
        (p-(adamsTowerInternalSpectralSequence H.unit X).diffDeg r) = 0) :
      boundaries H X r p = boundaries H X (r-1) p := by
    let E := adamsTowerInternalSpectralSequence H.unit X
    have hb := boundaries_succ_of_zero E r hr (p-E.diffDeg r) hd
    rw [sub_add_cancel] at hb
    have hi : (r-1).toNat=(r-2).toNat+1 := by omega
    have hi' : (r-1-1).toNat=(r-2).toNat := by congr 1; omega
    change (E.ssData p).B ↑((r-2).toNat+1) = (E.ssData p).B ↑(r-2).toNat at hb
    unfold boundaries boundaryMap
    dsimp only
    rw [hi,hi']
    change LinearMap.range (Subobject.ofLE ((E.ssData p).B ↑((r-2).toNat+1)) _ _ ≫ (E.ssData p).pageπ 0).hom =
      LinearMap.range (Subobject.ofLE ((E.ssData p).B ↑(r-2).toNat) _ _ ≫ (E.ssData p).pageπ 0).hom
    have hcongr (B B' : Subobject (E.ssData p).V)
        (hB : B ≤ (E.ssData p).Z 0) (hB' : B' ≤ (E.ssData p).Z 0)
        (heq : B=B') :
        LinearMap.range (Subobject.ofLE B _ hB ≫ (E.ssData p).pageπ 0).hom =
        LinearMap.range (Subobject.ofLE B' _ hB' ≫ (E.ssData p).pageπ 0).hom := by
      subst B'
      rfl
    exact hcongr _ _ _ _ hb
  have permanent_map_injective_of_boundary_eq
      (H : Mod2EilenbergMacLane (C:=C)) (X : C) {b b' : ℤ}
      (hb : b≤b') (p : ℤ×ℤ)
      (heq : boundaries H X b p = boundaries H X b' p) :
      Function.Injective (permanentQuotientMap H X hb p) := by
    have hinj (Z B B' : Submodule ℤ (Ambient H X p)) (hB : B≤B') (he : B=B') :
        Function.Injective (KIP126.Algebra.NestedQuotient.map (le_refl Z) hB) := by
      subst B'
      exact KIP126.Algebra.NestedQuotient.cycle_map_injective (le_refl Z)
    exact hinj _ _ _ (boundaries_monotone H X p hb) heq
  have bhs_high_lambdaMap_injective
      (A : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D) (I : AdamsComputationTheorems D L G)
      (V : SphereVanishingLine H) (wt : ℤ) (hwt : wt≤70) (s : ℤ) (hs : 9≤s) :
      Function.Injective (A.eInfty.weightShift.lambdaMap
        (D.nu.functor.obj (SphereSpectrum)) 1 (s,62+s) wt) := by
    let E := adamsTowerInternalSpectralSequence H.unit (SphereSpectrum)
    by_cases hw : wt ≤ 62+s
    · have hr : 2 ≤ 2+(62+s)-wt := by omega
      have hidx : (s,62+s)-E.diffDeg (2+(62+s)-wt) = (wt-62-2,wt-1) := by
        change (s,62+s)-(2+(62+s)-wt,2+(62+s)-wt-1) = _
        ext <;> dsimp <;> omega
      have hd : E.d (2+(62+s)-wt) ((s,62+s)-E.diffDeg (2+(62+s)-wt)) = 0 := by
        rw [hidx]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        have hout : (sequence D .sphere).d (2+(62+s)-wt) (wt-62-2,wt-62-2+63)=0 := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          exact stem63_no_late_differentials I V (wt-62-2) (by omega) (2+(62+s)-wt) (by omega) z
        have hpair : (wt-62-2,wt-62-2+63)=(wt-62-2,wt-1) := by ext <;> dsimp; omega
        rw [hpair] at hout
        exact ConcreteCategory.congr_hom hout y
      have hB := paper_boundaries_step H (SphereSpectrum) (2+(62+s)-wt) hr (s,62+s) hd
      have hB' : boundaries H (SphereSpectrum) (1+(62+s)-wt) (s,62+s) =
          boundaries H (SphereSpectrum) (1+(62+s)-(wt-1)) (s,62+s) := by
        convert hB.symm using 1 <;> congr 1 <;> omega
      have hq := permanent_map_injective_of_boundary_eq H (SphereSpectrum)
        (show 1+(62+s)-wt ≤ 1+(62+s)-(wt-1) by omega) (s,62+s) hB'
      intro x y hxy
      apply (A.eInfty.presentation.nuWindow (SphereSpectrum) (s,62+s) wt hw).injective
      apply hq
      have hx := A.eInfty.maps.lambda_nu (SphereSpectrum) 1 (s,62+s) wt hw x
      have hy := A.eInfty.maps.lambda_nu (SphereSpectrum) 1 (s,62+s) wt hw y
      exact hx.symm.trans ((congrArg (A.eInfty.presentation.nuWindow
        (SphereSpectrum) (s,62+s) (wt-1) (by omega)) hxy).trans hy)
    · have hz : Subsingleton (nuEInftyModel H (SphereSpectrum) (s,62+s) wt) := by
        simp only [nuEInftyModel,hw,ite_false]
        infer_instance
      intro x y hxy
      apply (A.eInfty.presentation.nu (SphereSpectrum) (s,62+s) wt).injective
      exact hz.elim _ _
  have bhs_high_actual_lambda_eMap_injective
      (A : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D) (I : AdamsComputationTheorems D L G)
      (V : SphereVanishingLine H) (wt : ℤ) (hwt : wt≤70) (s : ℤ) (hs : 9≤s) :
      Function.Injective (((D.family.functor.map
        (lambdaPow 1 (D.nu.functor.obj SphereSpectrum))).eInftyMap
          (s,62+s,wt-1)).hom) := by
    let e := A.eInfty.weightShift.lowerIso (D.nu.functor.obj SphereSpectrum) 1 (s,62+s) wt
    intro x y hxy
    apply e.injective
    apply bhs_high_lambdaMap_injective A I V wt hwt s hs
    change ((D.family.functor.map (lambdaPow 1 (D.nu.functor.obj SphereSpectrum))).eInftyMap
        (s,62+s,wt-1)).hom (e.symm (e x)) =
      ((D.family.functor.map (lambdaPow 1 (D.nu.functor.obj SphereSpectrum))).eInftyMap
        (s,62+s,wt-1)).hom (e.symm (e y))
    simpa only [LinearEquiv.symm_apply_apply] using hxy
  have shifted_weight71_filtration9
      (A : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D) (j : ℤ)
      (a : BiHom 62 (71+j) ((SyntheticCategory.biShift (0,j)).obj (D.nu.functor.obj SphereSpectrum))) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 9 a := by
    let X : SyntheticObject := .shift (0,j) (.nu .sphere)
    have hzero (s : ℤ) (hs : 0≤s) (hs9 : s<9) :
        IsZero (((D.family.obj (X.obj D.nu D.hopfAndDetector)).sequence.ssData (s,62+s,71+j)).eInfty) := by
      have hmodel : Subsingleton (nuEInftyModel H SphereSpectrum (s,62+s) 71) := by
        simp only [nuEInftyModel,show ¬(71:ℤ)≤(s,62+s).2 by dsimp; omega,ite_false]
        infer_instance
      have hnu : Subsingleton (((D.family.obj (D.nu.functor.obj SphereSpectrum)).sequence.ssData (s,62+s,71)).eInfty) :=
        (A.eInfty.presentation.nu SphereSpectrum (s,62+s) 71).injective.subsingleton
      exact ModuleCat.isZero_iff_subsingleton.mpr
        ((A.eInfty.weightShift.iso (D.nu.functor.obj SphereSpectrum) j (s,62+s) 71).injective.subsingleton)
    apply ((D.convergence X).filtrationAtLeast_iff_of_eInfty_isZero 0 9 62 (71+j)
      (by norm_num) hzero a).mp
    refine ⟨a,?_⟩
    change a ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) _ 0 0 _ = a
    rw [adamsTowerMap_self]
    change a ≫ 𝟙 _ = a
    exact Category.comp_id a
  have filtered_kernel_step
      {A B : (ℤ × ℤ) → ModuleCat.{v} ℤ} (F : Filtration A) (G : Filtration B)
      (f : FilteredMorphism F G) (s : ℤ) (i : (ℤ × ℤ))
      (hinj : Function.Injective (f.inducedGrMap s i))
      (a : (Subobject.underlying.obj (F.F s i) : ModuleCat ℤ))
      (ha : f.map i ((F.F s i).arrow a) = 0) :
      (F.F s i).arrow a ∈ (ModuleCat.subobjectModule (A i)) (F.F (s+1) i) := by
    let phi := (f.compat s i).choose
    have hp0 : phi a = 0 := by
      apply (ModuleCat.mono_iff_injective (G.F s i).arrow).mp inferInstance
      have hp := ConcreteCategory.congr_hom (f.compat s i).choose_spec a
      change (G.F s i).arrow (phi a) = f.map i ((F.F s i).arrow a) at hp
      rw [hp,ha,map_zero]
    have hcomm : F.toAssociatedGraded s i ≫ f.inducedGrMap s i = phi ≫ G.toAssociatedGraded s i := by
      unfold Filtration.toAssociatedGraded FilteredMorphism.inducedGrMap Filtration.inducedAssocGradedMap
      exact cokernel.π_desc _ _ _
    have hga : F.toAssociatedGraded s i a = 0 := by
      apply hinj
      have hh := ConcreteCategory.congr_hom hcomm a
      change f.inducedGrMap s i (F.toAssociatedGraded s i a) = G.toAssociatedGraded s i (phi a) at hh
      rw [hh,hp0,map_zero,map_zero]
    exact (subobject_cokernel_π_eq_zero_iff (F.F (s+1) i) (F.F s i) (F.mono s i) a).mp hga
  have convergence_graded_injective
        {E₁ E₂ : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ × ℤ)}
        {A B : (ℤ × ℤ) → ModuleCat.{v} ℤ} {F : Filtration A} {G : Filtration B}
        {conv₁ : Convergence E₁ A F} {conv₂ : Convergence E₂ B G}
      (c : ConvergenceMorphism conv₁ conv₂) (i : ℤ × ℤ × ℤ)
      (hi : Function.Injective (c.eMap i)) :
      Function.Injective (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat
        (conv₁.reindex i).1 (conv₁.reindex i).2) := by
    intro x y hxy
    let g := (conv₂.iso i).hom ≫ G.transportGraded (congrFun c.reindex_eq i).symm
    have hg : Function.Injective g := by
      haveI : IsIso (G.transportGraded (congrFun c.reindex_eq i).symm) := by
        dsimp only [Filtration.transportGraded]
        infer_instance
      exact (ModuleCat.mono_iff_injective g).mp inferInstance
    apply (conv₁.iso i).toLinearEquiv.symm.injective
    apply hi
    apply hg
    have hcomm (z : F.associatedGraded (conv₁.reindex i).1 (conv₁.reindex i).2) :
        g (c.eMap i ((conv₁.iso i).inv z)) =
        Filtration.inducedAssocGradedMap c.aMap c.filtration_compat
          (conv₁.reindex i).1 (conv₁.reindex i).2 z := by
      have h := ConcreteCategory.congr_hom (c.iso_compat i) ((conv₁.iso i).inv z)
      change g (c.eMap i ((conv₁.iso i).inv z)) =
        Filtration.inducedAssocGradedMap c.aMap c.filtration_compat
          (conv₁.reindex i).1 (conv₁.reindex i).2 ((conv₁.iso i).hom ((conv₁.iso i).inv z)) at h
      have hz : (conv₁.iso i).hom ((conv₁.iso i).inv z) = z :=
        (conv₁.iso i).toLinearEquiv.apply_symm_apply z
      rwa [hz] at h
    change g (c.eMap i ((conv₁.iso i).inv x)) = g (c.eMap i ((conv₁.iso i).inv y))
    rw [hcomm,hcomm]
    exact hxy
  have selected_homotopyMap_kernel_zero_from_f9
      (X Y : SyntheticObject) (f : X.obj D.nu D.hopfAndDetector ⟶ Y.obj D.nu D.hopfAndDetector)
      (m w : ℤ)
      (hinj : ∀ s : ℕ, 9≤s → Function.Injective
        ((D.family.functor.map f).eInftyMap (s,m+s,w)))
      (a : BiHom m w (X.obj D.nu D.hopfAndDetector))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 9 a)
      (haf : a ≫ f=0) : a=0 := by
    obtain ⟨c,hcA,hcE⟩ := D.comparisonCompatible.convergence_natural X Y f
    let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (X.obj D.nu D.hopfAndDetector)
    let G := towerFiltration (nuCoefficientUnit H.unit D.nu) (Y.obj D.nu D.hopfAndDetector)
    let g : FilteredMorphism F G := ⟨c.aMap,c.filtration_compat⟩
    apply D.homotopySeparated X m w a
    intro s
    induction s with
    | zero =>
      exact towerFiltrationSubmodule_antitone (nuCoefficientUnit H.unit D.nu)
        (X.obj D.nu D.hopfAndDetector) (m,w) (by omega : (0:ℤ)≤9) ha
    | succ s ih =>
      by_cases hs : s<9
      · exact towerFiltrationSubmodule_antitone (nuCoefficientUnit H.unit D.nu)
          (X.obj D.nu D.hopfAndDetector) (m,w) (by omega : ((s+1:ℕ):ℤ)≤9) ha
      · have hm : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy
            (X.obj D.nu D.hopfAndDetector) (m,w))) (F.F s (m,w)) := by
          simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ih
        obtain ⟨a',ha'⟩ := hm
        have hgr : Function.Injective (g.inducedGrMap s (m,w)) := by
          have hh := convergence_graded_injective c (s,m+s,w) (by
            rw [hcE]
            exact hinj s (by omega))
          change Function.Injective (Filtration.inducedAssocGradedMap c.aMap
            c.filtration_compat s (m,w))
          change Function.Injective (Filtration.inducedAssocGradedMap c.aMap
            c.filtration_compat s (m+s-s,w)) at hh
          have hdeg : (m+(s:ℤ)-(s:ℤ),w)=(m,w) := by congr 1; omega
          rw [hdeg] at hh
          exact hh
        have hstep := filtered_kernel_step F G g s (m,w) hgr a' (by
          change c.aMap (m,w) ((F.F s (m,w)).arrow a')=0
          rw [ha',hcA]
          exact haf)
        rw [ha'] at hstep
        simpa only [F,towerFiltration,OrderIso.apply_symm_apply,Nat.cast_add,Nat.cast_one,
          FiltrationAtLeast] using hstep
  have restriction_lift_zero
      (n : ℕ) {Y X : Syn} (a : Y ⟶ X)
      (h : (SyntheticCategory.biShift (lambdaDegree (n+1))).map a ≫
        lambdaRestrictionSourceMap 1 (n+1) (by omega) X = 0) :
      lambdaPow n Y ≫ a = 0 := by
    rw [lambdaRestrictionSourceMap_naturality] at h
    simp only [lambdaRestrictionSourceMap, Category.assoc] at h
    have hp := (Limits.comp_eq_zero_iff_of_epi
      ((lambdaShiftAddIso n 1 (n+1) (by omega)).inv.app Y)).mp h
    rw [← Functor.map_comp] at hp
    have hz : lambdaPow (n+1-1) Y ≫ a = 0 := by
      apply (SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (lambdaDegree 1)).map_injective
      simpa only [Functor.map_zero] using hp
    rw [show n+1-1=n by omega] at hz
    exact hz
  have restriction_lift_lambda
      (coh : BiShiftCoherence Syn) (n : ℕ) {Y X : Syn} (a : Y ⟶ X) :
      ((SyntheticCategory.biShift (lambdaDegree (n+1))).map a ≫
        lambdaRestrictionSourceMap 1 (n+1) (by omega) X) ≫
          SyntheticCategory.lam.app X = lambdaPow (n+1) Y ≫ a := by
    calc
      _ = (SyntheticCategory.biShift (lambdaDegree (n+1))).map a ≫ lambdaPow (n+1) X := by
        simpa only [lambdaPow_one coh, Category.assoc] using
          congrArg (fun g => (SyntheticCategory.biShift (lambdaDegree (n+1))).map a ≫ g)
            (lambdaRestrictionSourceMap_commutes coh 1 (n+1) (by omega) X)
      _ = _ := lambdaPow_naturality (n+1) a
  have actual_postcomp_filtration
      (X Y : SyntheticObject) (f : X.obj D.nu D.hopfAndDetector ⟶ Y.obj D.nu D.hopfAndDetector)
      (s m w : ℤ) (a : BiHom m w (X.obj D.nu D.hopfAndDetector))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s (a ≫ f) := by
    obtain ⟨c,hcA,hcE⟩ := D.comparisonCompatible.convergence_natural X Y f
    let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (X.obj D.nu D.hopfAndDetector)
    let G := towerFiltration (nuCoefficientUnit H.unit D.nu) (Y.obj D.nu D.hopfAndDetector)
    have hm : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy
        (X.obj D.nu D.hopfAndDetector) (m,w))) (F.F s (m,w)) := by
      simpa only [F,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using ha
    obtain ⟨a',ha'⟩ := hm
    have hb : (a ≫ f) ∈ (ModuleCat.subobjectModule (syntheticHomotopy
        (Y.obj D.nu D.hopfAndDetector) (m,w))) (G.F s (m,w)) := by
      refine ⟨(c.filtration_compat s (m,w)).choose a', ?_⟩
      have hh := ConcreteCategory.congr_hom (c.filtration_compat s (m,w)).choose_spec a'
      change (G.F s (m,w)).arrow ((c.filtration_compat s (m,w)).choose a') =
        c.aMap (m,w) ((F.F s (m,w)).arrow a') at hh
      rw [ha'] at hh
      exact hh.trans (by rw [hcA]; rfl)
    simpa only [G,towerFiltration,OrderIso.apply_symm_apply,FiltrationAtLeast] using hb
  have lambda_power_descent_step
      (f9 : ∀ k : ℤ, ∀ a : BiHom 62 (71+k)
        ((SyntheticCategory.biShift (0,k)).obj (D.nu.functor.obj SphereSpectrum)),
          FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 9 a)
      (ker : ∀ w : ℤ, w ≤ 69 →
        ∀ b : BiHom 62 w ((SyntheticCategory.biShift (0,-1)).obj
          (D.nu.functor.obj SphereSpectrum)),
        FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 9 b →
        b ≫ SyntheticCategory.lam.app _ = 0 → b = 0)
      (n : ℕ) (hn : 1≤n)
      (a : BiHom 62 71 (D.nu.functor.obj SphereSpectrum))
      (ha : lambdaMultiply (n+1) a=0) : lambdaMultiply n a=0 := by
    let X := D.nu.functor.obj (SphereSpectrum (C := C))
    let F := SyntheticCategory.biShift (Syn := Syn) (lambdaDegree (n+1))
    let e : Smn (Syn := Syn) 62 (71-((n+1:ℕ):ℤ)) ≅ F.obj (Smn 62 71) :=
      eqToIso (by dsimp only [Smn]; congr 1) ≪≫
        ((SyntheticCategory.biShift_comp (62,71) (0,-((n+1 : ℕ):ℤ))).app S_0_0).symm
    let z : BiHom 62 (71-((n+1:ℕ):ℤ)) (F.obj X) := e.hom ≫ F.map a
    let R := lambdaRestrictionSourceMap 1 (n+1) (by omega) X
    let b : BiHom 62 (71-((n+1:ℕ):ℤ)) ((SyntheticCategory.biShift (0,-1)).obj X) := z ≫ R
    have hz9 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 9 z := by
      have hh := f9 (-((n+1:ℕ):ℤ))
      rw [← sub_eq_add_neg] at hh
      exact hh z
    have hb9 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 9 b :=
      actual_postcomp_filtration (.shift (lambdaDegree (n+1)) (.nu .sphere))
        (.shift (0,-1) (.nu .sphere)) R 9 62 (71-((n+1:ℕ):ℤ)) z hz9
    have hblam : b ≫ SyntheticCategory.lam.app X=0 := by
      have hh := congrArg (fun g => e.hom ≫ g)
        (restriction_lift_lambda D.shiftCoherence n a)
      have heq : b ≫ SyntheticCategory.lam.app X = lambdaMultiply (n+1) a := by
        simpa only [b,z,e,F,R,X,lambdaMultiply,Iso.trans_hom,Iso.symm_hom,Iso.app_inv,eqToIso.hom,Category.assoc] using hh
      exact heq.trans ha
    have hb0 : b=0 := ker (71-((n+1:ℕ):ℤ)) (by omega) b hb9 hblam
    have hR : F.map a ≫ R=0 := by
      apply (Limits.comp_eq_zero_iff_of_epi e.hom).mp
      simpa only [b,z,Category.assoc] using hb0
    have hn0 := restriction_lift_zero n a hR
    change _ ≫ _ ≫ (lambdaPow n (Smn 62 71) ≫ a) = 0
    rw [hn0]
    simp only [Limits.comp_zero]
  have hker (w : ℤ) (hw : w≤69)
      (b : BiHom 62 w ((SyntheticCategory.biShift (0,-1)).obj (D.nu.functor.obj SphereSpectrum)))
      (hb : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 9 b)
      (hf : b ≫ SyntheticCategory.lam.app _=0) : b=0 := by
    apply selected_homotopyMap_kernel_zero_from_f9 (.shift (0,-1) (.nu .sphere))
      (.nu .sphere) (lambdaPow 1 (D.nu.functor.obj SphereSpectrum)) 62 w _ b hb
    · rw [lambdaPow_one D.shiftCoherence]
      exact hf
    · intro s hs
      have hh := bhs_high_actual_lambda_eMap_injective A.synthetic I V (w+1) (by omega) s (by omega)
      rw [show w+1-1=w by omega] at hh
      exact hh
  let aNu : BiHom 62 71 (D.nu.functor.obj SphereSpectrum) := a ≫ D.nu.unitIso.inv
  obtain ⟨k,hk⟩ := (A.synthetic.realization_kernel (.nu .sphere) 62 71 aNu).mp (by
    change D.recovery.realization.map (a ≫ D.nu.unitIso.inv)=0
    rw [Functor.map_comp,ha,Limits.zero_comp])
  have hdesc : ∀ k : ℕ, lambdaMultiply k aNu=0 → lambdaMultiply 1 aNu=0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      cases k with
      | zero =>
        have ha0 : aNu=0 := by
          simpa only [lambdaMultiply,lambdaPow,Category.assoc,
            Limits.comp_eq_zero_iff_of_epi] using hk
        simp only [ha0,lambdaMultiply,Limits.comp_zero]
      | succ k =>
        cases k with
        | zero => exact hk
        | succ k =>
          apply ih (k+1) (by omega)
          exact lambda_power_descent_step
            (shifted_weight71_filtration9 A.synthetic) hker (k+1) (by omega) aNu hk
  have hnu := hdesc k hk
  apply (cancel_mono D.nu.unitIso.inv).mp
  rw [Limits.zero_comp]
  simpa only [aNu,lambdaMultiply,Category.assoc] using hnu

/-- The precise synthetic exponent-two consequence used for B at weight70.
Classical IWX exponent two first kills realization(h0*b); the preceding
window kills lambda*(h0*b)=2*b. This does not assume lambda-injectivity
at (62,70), which the selected d2 data would contradict. -/
theorem two_torsion_62_70
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G)
    (V : SphereVanishingLine H) (b : BiHom 62 70 (S_0_0 : Syn)) : b + b = 0 := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
    letI := realization_additive (D := D)
    have hb : D.recovery.realization.map (b+b) = 0 := by
      rw [Functor.map_add]
      let α : HomotopyGroup (C := C) 62 SphereSpectrum :=
        (A.realization.coordinates.sphere 62 70).hom ≫ D.recovery.realization.map b ≫
          D.recovery.realization.map D.nu.unitIso.inv ≫ D.recovery.nuRealizationIso.hom.app SphereSpectrum
      have h := A.classical.stem62_exponent_two α
      apply (cancel_epi (A.realization.coordinates.sphere 62 70).hom).mp
      apply (cancel_mono (D.recovery.realization.map D.nu.unitIso.inv)).mp
      apply (cancel_mono ((D.recovery.nuRealizationIso.app SphereSpectrum).hom)).mp
      erw [Preadditive.comp_add, Preadditive.add_comp, Preadditive.add_comp,
        Limits.comp_zero, Limits.zero_comp, Limits.zero_comp]
      repeat erw [Category.assoc]
      exact h
    have hl := (lambda_h0_map_zero_iff D.recovery.realization D.shiftCoherence
      A.toda.h0 A.toda.lambda_h0 b).mpr hb
    have hp : D.recovery.realization.map (sphereProduct A.toda.h0 b) = 0 := by
      have hm : lambdaMultiply 1 (sphereProduct A.toda.h0 b) =
          lambdaMultiply 1 (𝟙 (Smn (Syn := Syn) 62 71)) ≫ sphereProduct A.toda.h0 b := by
        simp only [lambdaMultiply, Category.assoc, Category.id_comp]
        rfl
      have hc := congrArg (fun z => (A.realization.coordinates.sphere 62 70).hom ≫ z) hl
      rw [hm, Functor.map_comp, ← Category.assoc] at hc
      erw [A.realization.coordinates.lambda 62 71 1] at hc
      exact (Limits.comp_eq_zero_iff_of_epi (A.realization.coordinates.sphere 62 71).hom).mp
        (by simpa only [Limits.comp_zero] using hc)
    have hk := lambda_kills_realization_kernel_62_71 A I V (sphereProduct A.toda.h0 b) hp
    exact (lambda_h0_map_zero_iff (𝟭 Syn) D.shiftCoherence A.toda.h0 A.toda.lambda_h0 b).mp hk

/-- The BHS lambda-kernel argument on any object in the selected classical
closure.  The object is the actual `nu X`, not a renamed synthetic sphere.
All decreasing weights are included, and the passage from graded kernels
to homotopy uses `D.homotopySeparated` on `.nu X`. -/
theorem nu_lambda_powers_injective_of_source_halfplane
    (A : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D)
    (X : ClassicalObject) (m wgt : ℤ)
    (hsource : ∀ q : ℤ, q ≤ wgt-m-2 →
      NoOutgoingAt (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector))
        q (q+m+1)) :
    LambdaPowersInjectiveAt m wgt (D.nu.functor.obj (X.obj D.hopfAndDetector)) := by
  apply lambda_powers_injective_of_lower_weights D.shiftCoherence m wgt
  intro wt hwt
  apply nu_lambda_injective_from_source A X m wt
  simpa only [show wt-m-2+m+1 = wt-1 by omega] using
    hsource (wt-m-2) (by omega)

/-- BMQ/change-of-rings gives E2=0 in this entire nonpositive-filtration
half-plane of the same completed tmf. It is not a sphere computation. -/
theorem detector_no_outgoing_stem63_nonpositive
    (low : KIP126.Literature.AdamsSynthetic.TmfLowFiltration63 D)
    (q : ℤ) (hq : q ≤ 0) :
    NoOutgoingAt (adamsTowerInternalSpectralSequence H.unit D.hopfAndDetector.detector)
      q (q+63) := by
  intro r hr x
  have hz : Subsingleton
      ((adamsTowerInternalSpectralSequence H.unit D.hopfAndDetector.detector).Page r
        (q, q+63)) :=
    adamsTowerInternal_page_subsingleton_of_le H.unit D.hopfAndDetector.detector
      2 r q (q+63) (by omega) hr (by simpa [add_comm] using low q hq)
  rw [hz.elim x 0, map_zero]

/-- All finite lambda powers are injective at (62,64) for synthetic tmf.
This is a Main deduction from the sourced low-filtration tmf calculation
and the BHS comparisons, rather than an added tmf vanishing assumption. -/
theorem detector_lambda_powers_injective_62_64
    (A : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D)
    (low : KIP126.Literature.AdamsSynthetic.TmfLowFiltration63 D) :
    LambdaPowersInjectiveAt 62 64 (D.nu.functor.obj D.hopfAndDetector.detector) := by
  apply nu_lambda_powers_injective_of_source_halfplane A .detector
  intro q hq
  simpa [ClassicalObject.obj, add_assoc] using
    detector_no_outgoing_stem63_nonpositive low q (by omega)

/-- Injectivity of the actual realization functor at the required tmf
degree. It additionally uses `A.realization_kernel` on `.nu .detector`;
an associated-graded comparison by itself does not imply this conclusion. -/
theorem detector_realization_injective_62_64
    (A : KIP126.Literature.AdamsSynthetic.SyntheticComparisonTheorems D)
    (low : KIP126.Literature.AdamsSynthetic.TmfLowFiltration63 D) :
    Function.Injective (fun a : BiHom 62 64 (D.nu.functor.obj D.hopfAndDetector.detector) =>
      D.recovery.realization.map a) := by
  exact realization_injective_of_lambda_powers A.realization_kernel
    (.nu .detector) 62 64 (detector_lambda_powers_injective_62_64 A low)

end
end KIP126.Computation.SphereAndCofiber
