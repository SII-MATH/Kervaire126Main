module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Proofs
public import KIP126.Def.Algebra.Filtration.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Predicates
public import KIP126.Def.ClassicalAdams.SphereVanishing.Proofs
public import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
public import KIP126.Main.ExternalHypotheses.Data
public import KIP126.Main.Computation.SphereAndCofiber
public import KIP126.Main.Computation.High125

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
set_option backward.isDefEq.respectTransparency false in
omit [HasFunctorialCofiber (C := Syn)] in
private theorem lambda_powers_injective_of_lower_weights
    (coh : BiShiftCoherence Syn) (m wt : ℤ) (X : Syn)
    (h : ∀ wt' : ℤ, wt' ≤ wt → LambdaInjectiveAt m wt' X) :
    LambdaPowersInjectiveAt m wt X := by
  have one (k : ℕ) : Function.Injective (fun a :
      (SyntheticCategory.biShift (0,-(k : ℤ))).obj (Smn (Syn := Syn) m wt) ⟶ X =>
      SyntheticCategory.lam.app _ ≫ a) := by
    let e : Smn (Syn := Syn) m (wt-k) ≅
        (SyntheticCategory.biShift (0,-(k : ℤ))).obj (Smn m wt) :=
      eqToIso (by dsimp only [Smn]; congr 1; simp [sub_eq_add_neg]) ≪≫
        ((SyntheticCategory.biShift_comp (m,wt) (0,-(k : ℤ))).app S_0_0).symm
    intro a b hab
    apply (cancel_epi e.hom).mp
    apply h (wt-k) (by omega)
    dsimp only [lambdaAction]
    have hc : SyntheticCategory.lam.app (Smn (Syn := Syn) m (wt-k)) ≫ (e.hom ≫ a) =
        SyntheticCategory.lam.app (Smn (Syn := Syn) m (wt-k)) ≫ (e.hom ≫ b) := by
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
      have hc := (cancel_epi ((lambdaShiftAddIso k 1 (k+1) rfl).inv.app (Smn (Syn := Syn) m wt))).mp
        (by simpa only [Category.assoc] using hab)
      have hn := SyntheticCategory.lam.naturality (lambdaPow k (Smn (Syn := Syn) m wt))
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

set_option backward.isDefEq.respectTransparency false in
private theorem realize_detector {m wt : ℤ} (R : KIP126.Literature.AdamsSynthetic.RealizationCoordinates D)
    (a : BiHom m wt (S_0_0 : Syn)) :
    KIP126.Literature.AdamsSynthetic.realizeNu D R .sphere (a ≫ D.nu.unitIso.inv) ≫ D.hopfAndDetector.detectorUnit =
      KIP126.Literature.AdamsSynthetic.realizeNu D R .detector (a ≫ KIP126.Literature.AdamsSynthetic.detectorMap D) := by
  have hn := D.recovery.nuRealizationIso.hom.naturality D.hopfAndDetector.detectorUnit
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [KIP126.Literature.AdamsSynthetic.realizeNu, KIP126.Literature.AdamsSynthetic.detectorMap, ClassicalObject.obj, Functor.map_comp, Category.assoc]
  rw [← hn]

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

/-- Filtration zero vanishes by the existing Eilenberg--Mac Lane sphere
calculation, and negative filtration vanishes in the actual tower. This
half-plane does not require a computation input. -/
theorem no_outgoing_stem63_nonpositive
    (q : ℤ) (hq : q ≤ 0) : NoOutgoingAt (sequence D .sphere) q (q+63) := by
  intro r _ x
  have hzero : Subsingleton ((sequence D .sphere).Page r (q, q+63)) := by
    by_cases hq0 : q = 0
    · subst q
      exact sphereAdamsInternal_filtration_zero_subsingleton H r 63 (by decide)
    · exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum
        r q (q+63) (by omega)
  rw [hzero.elim x 0, map_zero]

/-- E2 is empty at stem125, AF0..4; negative AF is zero. This covers
weights <=130 in synthetic stem124, hence all iterates starting at 128. -/
theorem no_outgoing_stem125_low (I : AdamsComputationTheorems D L G)
    (q : ℤ) (hq : q ≤ 4) : NoOutgoingAt (sequence D .sphere) q (q+125) := by
  set_option maxRecDepth 10000 in
    intro r hr x
    have hz : Subsingleton ((sequence D .sphere).Page r (q,q+125)) := by
      by_cases hneg : q < 0
      · exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r q (q+125) hneg
      · have hq0 : 0 ≤ q := by omega
        have hd : (⟨.sphere, q.toNat, (q+125).toNat, []⟩ : Raw.Degree) ∈ Raw.degrees := by
          interval_cases q <;> simp [Raw.degrees]
        obtain ⟨e, _⟩ := I.basis _ hd
        change Page D .sphere q.toNat (q+125).toNat ≃ₗ[ℤ]
          (Fin 0 →₀ KIP126.Algebra.F2) at e
        have he : Subsingleton (Page D .sphere q.toNat (q+125).toNat) :=
          e.injective.subsingleton
        apply adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r q (q+125) (by omega) hr
        simpa only [Page, sequence, object, ClassicalObject.obj, Int.toNat_of_nonneg hq0, Int.toNat_of_nonneg (by omega : 0 ≤ q+125),
          Int.toNat_of_nonneg] using he
    rw [hz.elim x 0, map_zero]

attribute [local irreducible] KIP126.LinE2.homogeneousPart
  adamsTowerSSData adamsTowerInternalD in
/-- The whole (3,129) component is the d2 target h0*h6^2 (S0_ss 2380).
Square-zero gives zero outgoing d2; later pages vanish. No assertion about
the unresolved class h6^2 at (2,128) is used. -/
theorem no_outgoing_stem126_af3 (I : AdamsComputationTheorems D L G) : NoOutgoingAt (sequence D .sphere) 3 129 := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
  set_option maxRecDepth 10000 in
    let E := sequence D .sphere
    have hm : (⟨.sphere, .equation, 2, 1, 128, [0], 3, 129, [0], "S0_AdamsE2_ss", 2380⟩ : Raw.Claim) ∈ Raw.claims := by
      unfold Raw.claims
      iterate 151 apply List.mem_cons_of_mem
      exact List.mem_cons_self
    have hrow := I.adamsStatements _ hm
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x, hx, y, hy, h⟩ := hrow
    have hdecode : I.interpretation.coordinateSum .sphere 3 129 [0] =
        some (I.interpretation.basis .sphere 3 129 0) := by
      have hv : Raw.coordinatesValid Raw.degrees .sphere 3 129 [0] = true := by decide
      simp [E2Interpretation.coordinateSum, hv]
    have hy' : y = I.interpretation.basis .sphere 3 129 0 :=
      Option.some.inj (hy.symm.trans hdecode)
    have hd : E.d 2 (1,128) x = I.interpretation.basis .sphere 3 129 0 := by
      obtain ⟨_, hd⟩ := h.eq_on_page_two
      simp only [eqToHom_refl, Category.comp_id] at hd
      dsimp only [E] at ⊢
      exact hd.trans hy'
    have hdeg : (⟨.sphere, 3, 129, ["0,1,69,2"]⟩ : Raw.Degree) ∈ Raw.degrees := by
      unfold Raw.degrees
      iterate 108 apply List.mem_cons_of_mem
      exact List.mem_cons_self
    obtain ⟨e, he⟩ := I.basis _ hdeg
    change E.Page 2 (3,129) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 3 129 i.val at he
    have hs : Function.Surjective (E.d 2 (1,128)) := by
      intro y
      suffices hall : ∀ f : Fin 1 →₀ KIP126.Algebra.F2, ∃ z, E.d 2 (1,128) z = e.symm f by
        simpa only [LinearEquiv.symm_apply_apply] using hall (e y)
      intro f
      induction f using Finsupp.induction with
      | zero => exact ⟨0, by simp⟩
      | @single_add i a f hi ha ih =>
        have hi0 : i = 0 := Fin.eq_zero i
        subst i
        obtain ⟨z, hz⟩ := ih
        fin_cases a
        · exact ⟨z, by simpa using hz⟩
        · refine ⟨x+z, ?_⟩
          rw [map_add, hd, hz, map_add]
          change I.interpretation.basis .sphere 3 129 0 + e.symm f =
            e.symm (Finsupp.single 0 1) + e.symm f
          rw [he]
          rfl
    intro r hr y
    by_cases hr2 : r=2
    · subst r
      obtain ⟨z, rfl⟩ := hs y
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (1,128)) z
    · have hp3 : Subsingleton (E.Page 3 (3,129)) := by
        let S := E.pageShortComplex 2 ((3,129)-E.diffDeg 2)
        have hsf : Function.Surjective S.f := hs
        have hexa : S.Exact := by
          exact S.moduleCat_exact_iff.mpr (fun z _ => hsf z)
        have hzero := (S.exact_iff_isZero_homology).mp hexa
        exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 2 (3,129)
          (by change (2:ℤ)≤2; omega)).isZero_iff.mpr hzero)
      have hz := adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 3 r 3 129
        (by omega) (by omega) hp3
      rw [hz.elim y 0, map_zero]


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

/-- The torsion exclusion used when estimating theta5 squared in Prop.7.8.
This statement concerns (124,128), not the distinct (125,130) normalization. -/
theorem lambda_powers_injective_124_128
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G) :
    LambdaPowersInjectiveAt 124 128 (S_0_0 : Syn) := by
  apply lambda_powers_injective_of_source_halfplane A
  intro q hq
  simpa [add_assoc] using no_outgoing_stem125_low I q (by omega)

/-- Only one multiplication by lambda is needed for the finite BX shift.
No all-power assertion or localization injectivity in (125,130) is made. -/
theorem lambda_injective_125_130
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G) :
    LambdaInjectiveAt 125 130 (S_0_0 : Syn) := by
  exact lambda_injective_of_source A 125 130 (no_outgoing_stem126_af3 I)

/-- Actual localization-map injectivity at the theta degree, obtained from
all-power lambda injectivity plus the sourced realization-kernel theorem.
The map is D's existing functor on these exact sphere hom groups. -/
theorem realization_injective_62_64
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G) :
    Function.Injective (fun a : BiHom 62 64 (S_0_0 : Syn) => D.recovery.realization.map a) := by
  exact realization_injective_of_lambda_powers A.synthetic.realization_kernel
    .sphere 62 64 (lambda_powers_injective_62_64 A I)

/-- Same actual localization conclusion for theta5 squared. -/
theorem realization_injective_124_128
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G) :
    Function.Injective (fun a : BiHom 124 128 (S_0_0 : Syn) => D.recovery.realization.map a) := by
  exact realization_injective_of_lambda_powers A.synthetic.realization_kernel
    .sphere 124 128 (lambda_powers_injective_124_128 A I)

-- Keep the existing named arguments for public API compatibility.
set_option linter.unusedVariables false in
/-- The exact quotient-zero equivalence sufficient to normalize BX.
The proof uses the actual lambda cofiber triangles and one-step injectivity
at (125,130). It does not strengthen the source finite criterion to an
untruncated theorem or assume all choices have zero indeterminacy. -/
theorem bx_finite_lambda_normalization
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G)
    (r : ℕ) (hr : 1 ≤ r) (a : BiHom 125 130 (S_0_0 : Syn)) :
    (quotientClass r a = 0 ↔ quotientClass (r+1) (lambdaMultiply 1 a) = 0) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
    let S := (S_0_0 : Syn)
    let Y := Smn (Syn := Syn) 125 130
    let F := SyntheticCategory.biShift (Syn := Syn) (0,-1)
    let e := (lambdaShiftAddIso r 1 (r+1) rfl).app S
    have lift_iff {Y : Syn} (n : ℕ) (b : Y ⟶ S) :
        b ≫ XModLambdaN.incl S n = 0 ↔ ∃ c, b = c ≫ lambdaPow n S := by
      constructor
      · exact Pretriangulated.Triangle.coyoneda_exact₂ (XModLambdaN.cofiberTriangle S n)
          (XModLambdaN.cofiberTriangle_distinguished S n) b
      · rintro ⟨c, rfl⟩
        simp only [Category.assoc, XModLambdaN.lambdaPow_comp_incl, Limits.comp_zero]
    have hinj : Function.Injective (fun b : Y ⟶ S => SyntheticCategory.lam.app Y ≫ b) := by
      intro b c hbc
      apply lambda_injective_125_130 A I
      dsimp only [lambdaAction]
      simpa only [Category.assoc] using congrArg (fun z => _ ≫ _ ≫ z) hbc
    change a ≫ XModLambdaN.incl S r = 0 ↔ _
    have hq : quotientClass (r+1) (lambdaMultiply 1 a) = 0 ↔
        (SyntheticCategory.lam.app Y ≫ a) ≫ XModLambdaN.incl S (r+1) = 0 := by
      simp only [quotientClass, lambdaMultiply, lambdaPow_one D.shiftCoherence,
        eqToHom_refl, Category.id_comp, Category.assoc, Limits.comp_eq_zero_iff_of_epi]
      rfl
    rw [hq, lift_iff, lift_iff]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨F.map c ≫ e.hom, ?_⟩
      have hn := SyntheticCategory.lam.naturality (c ≫ lambdaPow r S)
      dsimp only [Functor.id_map] at hn
      rw [← hn]
      simp only [lambdaPow_add D.shiftCoherence r 1 (r+1) rfl, lambdaPow_one D.shiftCoherence,
        Functor.map_comp, Category.assoc, e]
      change F.map c ≫ F.map (lambdaPow r S) ≫ SyntheticCategory.lam.app S =
        F.map c ≫ e.hom ≫ e.inv ≫ F.map (lambdaPow r S) ≫ SyntheticCategory.lam.app S
      rw [e.hom_inv_id_assoc]
    · rintro ⟨b, hb⟩
      let c := (SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (0,-1)).preimage (b ≫ e.inv)
      have hc : F.map c = b ≫ e.inv :=
        (SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (0,-1)).map_preimage _
      refine ⟨c, hinj ?_⟩
      change SyntheticCategory.lam.app Y ≫ a =
        SyntheticCategory.lam.app Y ≫ (c ≫ lambdaPow r S)
      rw [hb]
      have hn := SyntheticCategory.lam.naturality (c ≫ lambdaPow r S)
      dsimp only [Functor.id_map] at hn
      rw [← hn, Functor.map_comp, Category.assoc]
      change b ≫ lambdaPow (r+1) S = F.map c ≫ F.map (lambdaPow r S) ≫ SyntheticCategory.lam.app S
      rw [hc, lambdaPow_add D.shiftCoherence r 1 (r+1) rfl, lambdaPow_one D.shiftCoherence]
      simp only [e, Category.assoc]
      rfl


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
open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxRecDepth 10000 in
/-- The complete stem-63 bases in filtrations 1 through 6 leave only
permanent classes after d₂; nonpositive filtrations vanish. -/
private theorem stem63_no_late_differentials (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
    (q : ℤ) (hq : q≤6) (r : ℤ) (hr : 3≤r)
    (a : (sequence D .sphere).Page r (q,q+63)) :
    (sequence D .sphere).d r (q,q+63) a=0 := by
  have represents_unique {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
        {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a b : E.Page r p}
      (ha : RepresentsOnPage E r p x a) (hb : RepresentsOnPage E r p x b) : a = b := by
    obtain ⟨hr, z, hz, hza⟩ := ha
    obtain ⟨_, z', hz', hzb⟩ := hb
    let D := E.ssData p
    let n : WithTop ℕ := ↑(2 - E.r₀).toNat
    let m : WithTop ℕ := ↑(r - E.r₀).toNat
    have hnm : n ≤ m := by
      dsimp only [n, m]
      exact_mod_cast (show (2-E.r₀).toNat ≤ (r-E.r₀).toNat by omega)
    apply sub_eq_zero.mp
    rw [← hza, ← hzb, ← map_sub]
    apply (subobject_cokernel_π_eq_zero_iff (D.B m) (D.Z m) (D.B_le_Z m) _).mpr
    have heq : D.pageπ n ((Subobject.ofLE _ _ (D.Z_anti hnm)) (z-z')) = 0 := by
      change (Subobject.ofLE _ _ (D.Z_anti hnm) ≫ D.pageπ n) (z-z') = 0
      rw [map_sub, hz, hz', sub_self]
    have hh := (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) _).mp heq
    have he : (D.Z n).arrow ((Subobject.ofLE _ _ (D.Z_anti hnm)) (z-z')) =
        (D.Z m).arrow (z-z') := ConcreteCategory.congr_hom (Subobject.ofLE_arrow (D.Z_anti hnm)) _
    rw [he] at hh
    exact (ModuleCat.subobjectModule D.V).monotone (D.B_mono hnm) hh
  have represents_d_zero_of_later {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
        {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {t : ℤ} (hr0 : E.r₀ ≤ r) (hrt : r < t)
      {a : E.Page r p} (ha : RepresentsOnPage E r p x a)
      (ht : ReachesPage E t p x) : E.d r p a = 0 := by
    obtain ⟨b, ht2, z, hz, _⟩ := ht
    let D := E.ssData p
    let nt : WithTop ℕ := ↑(t-E.r₀).toNat
    let nr : WithTop ℕ := ↑(r-E.r₀).toNat
    let ns : WithTop ℕ := ↑((r-E.r₀).toNat+1)
    have hrs : nr ≤ ns := by
      dsimp only [nr, ns]
      exact_mod_cast (show (r-E.r₀).toNat ≤ (r-E.r₀).toNat+1 by omega)
    have hst : ns ≤ nt := by
      dsimp only [ns, nt]
      exact_mod_cast (show (r-E.r₀).toNat+1 ≤ (t-E.r₀).toNat by omega)
    let zr := (Subobject.ofLE (D.Z nt) (D.Z nr) (D.Z_anti (hrs.trans hst))) z
    have hrep : RepresentsOnPage E r p x (D.pageπ nr zr) := by
      refine ⟨ha.1, zr, ?_, rfl⟩
      dsimp only [zr]
      rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
      exact hz
    rw [represents_unique ha hrep]
    change D.pageπ nr zr ∈ LinearMap.ker (E.d r p).hom
    rw [← subobjectModule_kernel, E.Z_succ r p hr0, subobjectModule_image]
    refine ⟨(Subobject.ofLE (D.Z nt) (D.Z ns) (D.Z_anti hst)) z, ?_⟩
    change (Subobject.ofLE (D.Z ns) (D.Z nr) (D.Z_anti hrs) ≫ D.pageπ nr)
      ((Subobject.ofLE (D.Z nt) (D.Z ns) (D.Z_anti hst)) z) = D.pageπ nr zr
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    rfl
  have permanent_reaches {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
      {p : ℤ×ℤ} {x : E.Page 2 p} (hx : IsPermanentCycle E p x)
      (r : ℤ) (hr : 2≤r) : ReachesPage E r p x := by
    obtain ⟨z,hz⟩ := hx
    let A := E.ssData p
    let zr := (Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-E.r₀).toNat) (A.Z_anti le_top)) z
    refine ⟨A.pageπ _ zr,hr,zr,?_,rfl⟩
    dsimp only [zr]
    rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz
  have rep2_self {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
      {p : ℤ×ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    let A := E.ssData p
    haveI : Epi (A.pageπ ↑(2-E.r₀).toNat) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ↑(2-E.r₀).toNat)).mp inferInstance x
    exact ⟨by decide,z,by simp only [Subobject.ofLE_refl,Category.id_comp]; rfl,rfl⟩
  have permanent_zero {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
      {p : ℤ×ℤ} : IsPermanentCycle E p 0 := ⟨0,map_zero _⟩
  have late_zero_of_kernel_permanent
      (E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)) (hE : E.r₀≤2) (p : ℤ×ℤ)
      (hker : ∀ x : E.Page 2 p, E.d 2 p x=0 → IsPermanentCycle E p x)
      (r : ℤ) (hr : 3≤r) (a : E.Page r p) : E.d r p a=0 := by
    let A := E.ssData p
    haveI : Epi (A.pageπ ↑(r-E.r₀).toNat) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ↑(r-E.r₀).toNat)).mp inferInstance a
    let x : E.Page 2 p := (Subobject.ofLE _ _ (A.Z_anti (by
      exact_mod_cast (show (2-E.r₀).toNat≤(r-E.r₀).toNat by omega))) ≫ A.pageπ _) z
    have hx : RepresentsOnPage E r p x a := ⟨by omega,z,rfl,hz⟩
    have hd : E.d 2 p x=0 := represents_d_zero_of_later hE (by omega) (rep2_self x) ⟨a,hx⟩
    exact represents_d_zero_of_later (by omega) (by omega : r<r+1) hx
      (permanent_reaches (hker x hd) (r+1) (by omega))
  have kernel_perm_fin1
      {E : KIP126.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)} {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2))
      (hn : E.d 2 p (e.symm (Finsupp.single 0 1)) ≠ 0)
      (x : E.Page 2 p) (hx : E.d 2 p x=0) : IsPermanentCycle E p x := by
    have he : e x = Finsupp.single 0 (e x 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0)) := by rw [← he,LinearEquiv.symm_apply_apply]
    generalize hc : e x 0 = a at hxe
    fin_cases a
    · simp only [show (⟨0,by decide⟩:KIP126.Algebra.F2)=0 from rfl,Finsupp.single_zero,map_zero] at hxe
      rw [hxe]
      exact permanent_zero (E:=E) (p:=p)
    · change x=e.symm (Finsupp.single 0 1) at hxe
      exact (hn (hxe ▸ hx)).elim
  have kernel_perm_fin2
      {E : KIP126.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)} (hE : E.r₀≤2) {p : ℤ×ℤ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Algebra.F2))
      (hp : IsPermanentCycle E p (e.symm (Finsupp.single 0 1)))
      (hn : E.d 2 p (e.symm (Finsupp.single 1 1)) ≠ 0)
      (x : E.Page 2 p) (hx : E.d 2 p x=0) : IsPermanentCycle E p x := by
    have hd0 : E.d 2 p (e.symm (Finsupp.single 0 1))=0 :=
      represents_d_zero_of_later hE (by decide : (2:ℤ)<3) (rep2_self _) (permanent_reaches hp 3 (by decide))
    have he : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [← he,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0 = a at hxe
    generalize hc1 : e x 1 = b at hxe
    fin_cases a <;> fin_cases b
    all_goals simp only [show (⟨0,by decide⟩:KIP126.Algebra.F2)=0 from rfl,show (⟨1,by decide⟩:KIP126.Algebra.F2)=1 from rfl,Finsupp.single_zero,map_zero,zero_add,add_zero,map_add] at hxe
    · rw [hxe]; exact permanent_zero (E:=E) (p:=p)
    · exact (hn (by simpa only [hxe] using hx)).elim
    · rw [hxe]; exact hp
    · exact (hn (by simpa only [hxe,map_add,hd0,zero_add] using hx)).elim
  have stem63_q1_late (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
      (r : ℤ) (hr : 3≤r) (a : (sequence D .sphere).Page r (1,64)) :
      (sequence D .sphere).d r (1,64) a=0 := by
    let E := sequence D .sphere
    obtain ⟨e,he⟩ := I.basis ⟨.sphere, 1, 64, ["69,1"]⟩ (by
      unfold Raw.degrees
      iterate 85 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (1,64) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 1 64 i.val at he
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 3, 65, ["0,1,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 102 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (3,65) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at f
    change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 3 65 i.val at hf
    have hdiff : HasDifferential E 2 (1,64) (3,65)
        (I.interpretation.basis .sphere 1 64 0) (I.interpretation.basis .sphere 3 65 0) := by
      have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 1, 64, [0], 3, 65, [0], "S0_AdamsE2_ss", 401⟩ (by
        unfold Raw.claims
        iterate 142 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,h⟩ := hrow
      change HasDifferential E 2 (1,64) (3,65) x y at h
      have vx : Raw.coordinatesValid Raw.degrees .sphere 1 64 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 3 65 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [← hx,← hy] at h
      exact h
    have es : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 1 64 0 := he 0
    have ft : f.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 3 65 0 := hf 0
    have hn : E.d 2 (1,64) (e.symm (Finsupp.single 0 1)) ≠ 0 := by
      rw [es]
      have hd : E.d 2 (1,64) (I.interpretation.basis .sphere 1 64 0) =
          I.interpretation.basis .sphere 3 65 0 := hdiff.eq_on_page_two.choose_spec
      rw [hd,← ft]
      intro hz
      have hh := congrArg (fun z => f z 0) hz
      simp at hh
    exact late_zero_of_kernel_permanent E (by change (2:ℤ)≤2; omega) (1,64)
      (kernel_perm_fin1 e hn) r hr a
  have stem63_q2_late (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
      (r : ℤ) (hr : 3≤r) (a : (sequence D .sphere).Page r (2,65)) :
      (sequence D .sphere).d r (2,65) a=0 := by
    let E := sequence D .sphere
    obtain ⟨e,he⟩ := I.basis ⟨.sphere, 2, 65, ["0,1,69,1"]⟩ (by
      unfold Raw.degrees
      iterate 95 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (2,65) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 2 65 i.val at he
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 4, 66, ["0,2,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 113 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (4,66) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at f
    change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 4 66 i.val at hf
    have hdiff : HasDifferential E 2 (2,65) (4,66)
        (I.interpretation.basis .sphere 2 65 0) (I.interpretation.basis .sphere 4 66 0) := by
      have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 2, 65, [0], 4, 66, [0], "S0_AdamsE2_ss", 417⟩ (by
        unfold Raw.claims
        iterate 145 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,h⟩ := hrow
      change HasDifferential E 2 (2,65) (4,66) x y at h
      have vx : Raw.coordinatesValid Raw.degrees .sphere 2 65 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 4 66 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [← hx,← hy] at h
      exact h
    have es : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 2 65 0 := he 0
    have ft : f.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 4 66 0 := hf 0
    have hn : E.d 2 (2,65) (e.symm (Finsupp.single 0 1)) ≠ 0 := by
      rw [es]
      have hd : E.d 2 (2,65) (I.interpretation.basis .sphere 2 65 0) =
          I.interpretation.basis .sphere 4 66 0 := hdiff.eq_on_page_two.choose_spec
      rw [hd,← ft]
      intro hz
      have hh := congrArg (fun z => f z 0) hz
      simp at hh
    exact late_zero_of_kernel_permanent E (by change (2:ℤ)≤2; omega) (2,65)
      (kernel_perm_fin1 e hn) r hr a
  have stem63_q3_late (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
      (r : ℤ) (hr : 3≤r) (a : (sequence D .sphere).Page r (3,66)) :
      (sequence D .sphere).d r (3,66) a=0 := by
    let E := sequence D .sphere
    obtain ⟨e,he⟩ := I.basis ⟨.sphere, 3, 66, ["1,1,18,2", "0,2,69,1"]⟩ (by
      unfold Raw.degrees
      iterate 103 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (3,66) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 3 66 i.val at he
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 5, 67, ["76,1", "1,1,70,1", "0,3,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 121 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (5,67) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Algebra.F2) at f
    change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 5 67 i.val at hf
    have hdiff : HasDifferential E 2 (3,66) (5,67)
        (I.interpretation.basis .sphere 3 66 1) (I.interpretation.basis .sphere 5 67 2) := by
      have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 3, 66, [1], 5, 67, [2], "S0_AdamsE2_ss", 437⟩ (by
        unfold Raw.claims
        iterate 150 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,h⟩ := hrow
      change HasDifferential E 2 (3,66) (5,67) x y at h
      have vx : Raw.coordinatesValid Raw.degrees .sphere 3 66 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 5 67 [2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [← hx,← hy] at h
      exact h
    have es : e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 3 66 1 := he 1
    have ft : f.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 5 67 2 := hf 2
    have hn : E.d 2 (3,66) (e.symm (Finsupp.single 1 1)) ≠ 0 := by
      rw [es]
      have hd : E.d 2 (3,66) (I.interpretation.basis .sphere 3 66 1) =
          I.interpretation.basis .sphere 5 67 2 := hdiff.eq_on_page_two.choose_spec
      rw [hd,← ft]
      intro hz
      have hh := congrArg (fun z => f z 2) hz
      simp at hh
    have hp : IsPermanentCycle E (3,66) (e.symm (Finsupp.single 0 1)) := by
      have es0 : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 3 66 0 := he 0
      rw [es0]
      apply permanent_cycle_of_reaches1000 V 3 66 (by norm_num) (by norm_num)
      have hrow := I.adamsStatements ⟨.sphere, .reaches, 1000, 3, 66, [0], 3, 66, [], "S0_AdamsE2_ss", 436⟩ (by
        unfold Raw.claims
        iterate 149 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,h⟩ := hrow
      have vx : Raw.coordinatesValid Raw.degrees .sphere 3 66 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [← hx] at h
      exact h
    exact late_zero_of_kernel_permanent E (by change (2:ℤ)≤2; omega) (3,66)
      (kernel_perm_fin2 (by change (2:ℤ)≤2; omega) e hp hn) r hr a
  have stem63_q4_late (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
      (r : ℤ) (hr : 3≤r) (a : (sequence D .sphere).Page r (4,67)) :
      (sequence D .sphere).d r (4,67) a=0 := by
    let E := sequence D .sphere
    obtain ⟨e,he⟩ := I.basis ⟨.sphere, 4, 67, ["0,3,69,1"]⟩ (by
      unfold Raw.degrees
      iterate 114 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (4,67) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 4 67 i.val at he
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 6, 68, ["18,1,24,1", "0,4,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 131 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (6,68) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Algebra.F2) at f
    change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 6 68 i.val at hf
    have hdiff : HasDifferential E 2 (4,67) (6,68)
        (I.interpretation.basis .sphere 4 67 0) (I.interpretation.basis .sphere 6 68 1) := by
      have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 4, 67, [0], 6, 68, [1], "S0_AdamsE2_ss", 455⟩ (by
        unfold Raw.claims
        iterate 155 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,h⟩ := hrow
      change HasDifferential E 2 (4,67) (6,68) x y at h
      have vx : Raw.coordinatesValid Raw.degrees .sphere 4 67 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 6 68 [1] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [← hx,← hy] at h
      exact h
    have es : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 4 67 0 := he 0
    have ft : f.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 6 68 1 := hf 1
    have hn : E.d 2 (4,67) (e.symm (Finsupp.single 0 1)) ≠ 0 := by
      rw [es]
      have hd : E.d 2 (4,67) (I.interpretation.basis .sphere 4 67 0) =
          I.interpretation.basis .sphere 6 68 1 := hdiff.eq_on_page_two.choose_spec
      rw [hd,← ft]
      intro hz
      have hh := congrArg (fun z => f z 1) hz
      simp at hh
    exact late_zero_of_kernel_permanent E (by change (2:ℤ)≤2; omega) (4,67)
      (kernel_perm_fin1 e hn) r hr a
  have stem63_q5_late (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
      (r : ℤ) (hr : 3≤r) (a : (sequence D .sphere).Page r (5,68)) :
      (sequence D .sphere).d r (5,68) a=0 := by
    let E := sequence D .sphere
    obtain ⟨e,he⟩ := I.basis ⟨.sphere, 5, 68, ["0,4,69,1"]⟩ (by
      unfold Raw.degrees
      iterate 122 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (5,68) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 5 68 i.val at he
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 7, 69, ["0,5,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 142 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (7,69) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at f
    change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 69 i.val at hf
    have hdiff : HasDifferential E 2 (5,68) (7,69)
        (I.interpretation.basis .sphere 5 68 0) (I.interpretation.basis .sphere 7 69 0) := by
      have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 5, 68, [0], 7, 69, [0], "S0_AdamsE2_ss", 471⟩ (by
        unfold Raw.claims
        iterate 162 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,h⟩ := hrow
      change HasDifferential E 2 (5,68) (7,69) x y at h
      have vx : Raw.coordinatesValid Raw.degrees .sphere 5 68 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 7 69 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [← hx,← hy] at h
      exact h
    have es : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 5 68 0 := he 0
    have ft : f.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 7 69 0 := hf 0
    have hn : E.d 2 (5,68) (e.symm (Finsupp.single 0 1)) ≠ 0 := by
      rw [es]
      have hd : E.d 2 (5,68) (I.interpretation.basis .sphere 5 68 0) =
          I.interpretation.basis .sphere 7 69 0 := hdiff.eq_on_page_two.choose_spec
      rw [hd,← ft]
      intro hz
      have hh := congrArg (fun z => f z 0) hz
      simp at hh
    exact late_zero_of_kernel_permanent E (by change (2:ℤ)≤2; omega) (5,68)
      (kernel_perm_fin1 e hn) r hr a
  have stem63_q6_late (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H)
      (r : ℤ) (hr : 3≤r) (a : (sequence D .sphere).Page r (6,69)) :
      (sequence D .sphere).d r (6,69) a=0 := by
    let E := sequence D .sphere
    obtain ⟨e,he⟩ := I.basis ⟨.sphere, 6, 69, ["1,1,76,1", "0,5,69,1"]⟩ (by
      unfold Raw.degrees
      iterate 132 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (6,69) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Algebra.F2) at e
    change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 6 69 i.val at he
    obtain ⟨f,hf⟩ := I.basis ⟨.sphere, 8, 70, ["83,1", "82,1", "0,6,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 155 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (8,70) ≃ₗ[ℤ] (Fin 3 →₀ KIP126.Algebra.F2) at f
    change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 8 70 i.val at hf
    have hdiff : HasDifferential E 2 (6,69) (8,70)
        (I.interpretation.basis .sphere 6 69 1) (I.interpretation.basis .sphere 8 70 2) := by
      have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 6, 69, [1], 8, 70, [2], "S0_AdamsE2_ss", 494⟩ (by
        unfold Raw.claims
        iterate 169 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,h⟩ := hrow
      change HasDifferential E 2 (6,69) (8,70) x y at h
      have vx : Raw.coordinatesValid Raw.degrees .sphere 6 69 [1] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 8 70 [2] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [← hx,← hy] at h
      exact h
    have es : e.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 6 69 1 := he 1
    have ft : f.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 8 70 2 := hf 2
    have hn : E.d 2 (6,69) (e.symm (Finsupp.single 1 1)) ≠ 0 := by
      rw [es]
      have hd : E.d 2 (6,69) (I.interpretation.basis .sphere 6 69 1) =
          I.interpretation.basis .sphere 8 70 2 := hdiff.eq_on_page_two.choose_spec
      rw [hd,← ft]
      intro hz
      have hh := congrArg (fun z => f z 2) hz
      simp at hh
    have hp : IsPermanentCycle E (6,69) (e.symm (Finsupp.single 0 1)) := by
      have es0 : e.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 6 69 0 := he 0
      rw [es0]
      apply permanent_cycle_of_reaches1000 V 6 69 (by norm_num) (by norm_num)
      have hrow := I.adamsStatements ⟨.sphere, .reaches, 1000, 6, 69, [0], 6, 69, [], "S0_AdamsE2_ss", 493⟩ (by
        unfold Raw.claims
        iterate 168 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,h⟩ := hrow
      have vx : Raw.coordinatesValid Raw.degrees .sphere 6 69 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
      rw [← hx] at h
      exact h
    exact late_zero_of_kernel_permanent E (by change (2:ℤ)≤2; omega) (6,69)
      (kernel_perm_fin2 (by change (2:ℤ)≤2; omega) e hp hn) r hr a
  by_cases hq0 : q≤0
  · exact no_outgoing_stem63_nonpositive q hq0 r (by omega) a
  interval_cases q
  · exact stem63_q1_late I V r hr a
  · exact stem63_q2_late I V r hr a
  · exact stem63_q3_late I V r hr a
  · exact stem63_q4_late I V r hr a
  · exact stem63_q5_late I V r hr a
  · exact stem63_q6_late I V r hr a

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

/-- BMQ supplies one class with nonzero tmf image. Replacing it by an arbitrary
class with the same leading term uses the Main higher-filtration argument. -/
theorem high125_detector_nonzero
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
    (a : HomotopyGroup (C := C) 125 SphereSpectrum)
    (ha : TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (G.high125 M) a) : a ≫ D.hopfAndDetector.detectorUnit ≠ 0 := by
  obtain ⟨_, b, hb, hnonzero⟩ := A.tmf.high125_detected
  have heq : a = b := high125_detected_choice_unique I V S a b
    (by simpa only [high125_label I] using ha)
    (by simpa only [high125_label I] using hb)
  simpa only [heq] using hnonzero

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

/-- The synthetic Hurewicz vanishing used in Proposition 7.8.
Classical θ₅ vanishing is transported along the fixed unit and realization
comparisons; tmf injectivity then eliminates the possible λ-torsion lift. -/
theorem synthetic_theta5_detector_zero
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G)
    (theta : BiHom 62 64 (S_0_0 : Syn))
    (htheta : ThetaChoice M D.toAdamsComparisonData theta) :
    theta ≫ KIP126.Literature.AdamsSynthetic.detectorMap D = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    letI := realization_additive (D := D)
    let a : BiHom 62 64 (KIP126.Literature.AdamsSynthetic.nuZero D .sphere) :=
      theta ≫ D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _
    have ha : quotientClass 1 a = KIP126.Literature.AdamsSynthetic.firstLabel D .sphere 2 64 (Sphere.Internal.hiSquare H M 5) := by
      apply (D.firstQuotient SphereSpectrum 0 2 64).injective
      change (D.firstQuotient SphereSpectrum 0 2 64) (quotientClass 1 a) =
        (D.firstQuotient SphereSpectrum 0 2 64)
          ((D.firstQuotient SphereSpectrum 0 2 64).symm (Sphere.Internal.hiSquare H M 5))
      rw [AddEquiv.apply_symm_apply, ← htheta]
      change (D.firstQuotient SphereSpectrum 0 2 64) _ =
        (D.firstQuotient SphereSpectrum 0 2 64)
          (quotientClass 1 theta ≫ XModLambdaN.map
            (D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _) 1)
      apply congrArg (D.firstQuotient SphereSpectrum 0 2 64)
      simp only [a, quotientClass, Category.assoc, XModLambdaN.incl_naturality,
        D.quotientFunctoriality.map_comp]
    have hd := A.realization.detection.detection .sphere 2 64
      (Sphere.Internal.hiSquare H M 5) a A.classical.theta5_exists.1 ha
    have he : KIP126.Literature.AdamsSynthetic.realizeNuZero D A.realization.coordinates .sphere a =
        KIP126.Literature.AdamsSynthetic.realizeNu D A.realization.coordinates .sphere (theta ≫ D.nu.unitIso.inv) := by
      simp only [KIP126.Literature.AdamsSynthetic.realizeNuZero, a, ClassicalObject.obj, Category.assoc, Iso.inv_hom_id_app,
        Functor.id_obj, Category.comp_id]
    rw [he] at hd
    have hz := A.tmf.theta5_vanishes _ hd
    rw [realize_detector] at hz
    apply detector_realization_injective_62_64 A.synthetic A.tmf.low_filtration_63
    change D.recovery.realization.map (theta ≫ KIP126.Literature.AdamsSynthetic.detectorMap D) = D.recovery.realization.map 0
    rw [Functor.map_zero]
    apply (cancel_epi (A.realization.coordinates.sphere 62 64).hom).mp
    apply (cancel_mono (D.recovery.nuRealizationIso.app D.hopfAndDetector.detector).hom).mp
    dsimp only [KIP126.Literature.AdamsSynthetic.realizeNu, ClassicalObject.obj] at hz
    erw [Limits.comp_zero, Limits.zero_comp, Category.assoc]
    exact hz


/-- The synthetic tmf image used in the high-filtration contradiction.
The product and unit are the ones bound by `A.algebra.detector`, on D's
chosen completed tmf; no separate homotopy-ring model is selected. -/
theorem synthetic_eta_theta5_square_detector_zero
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G)
    (theta : BiHom 62 64 (S_0_0 : Syn))
    (htheta : ThetaChoice M D.toAdamsComparisonData theta) :
    sphereProduct η (sphereProduct theta theta) ≫
      KIP126.Literature.AdamsSynthetic.detectorMap D = 0 := by
  have h := synthetic_theta5_detector_zero A theta htheta
  dsimp only [sphereProduct]
  simp only [Smn] at h
  simp only [Smn, Category.assoc]
  rw [h]
  erw [Limits.comp_zero, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero]
  rfl

/-- The complete synthetic detector argument of Proposition 7.8. The
weight130 exhaustion first gives a classical G detector for every nonzero
F15 element; the same actual realization/unit comparison and tmf source
then contradict zero detector image. No all-power injectivity at weight130
or unqualified classical E5 vanishing is assumed. -/
theorem detector_injective_125_130_filtration15
    (A : KIP126.Literature.AdamsSynthetic.AdamsSyntheticTheorems D η G) (I : AdamsComputationTheorems D L G)
    (V : SphereVanishingLine H) (S : ClassicalSphereSeparated H)
    (a : BiHom 125 130 (S_0_0 : Syn))
    (ha : KIP126.Synthetic.SpectralSequence.FiltrationAtLeast
      (nuCoefficientUnit H.unit D.nu) 15 a)
    (hz : a ≫ KIP126.Literature.AdamsSynthetic.detectorMap D = 0) : a = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    letI := realization_additive (D := D)
    by_contra hne
    have hd := high125_weight130_nonzero_classical_detection I A.synthetic A.realization V
      A.tmf.high125_detected.1 a ha hne
    have hn := high125_detector_nonzero A I V S
      (KIP126.Literature.AdamsSynthetic.realizeNu D A.realization.coordinates .sphere
        (a ≫ D.nu.unitIso.inv)) hd
    apply hn
    rw [realize_detector, hz]
    simp only [KIP126.Literature.AdamsSynthetic.realizeNu, Functor.map_zero,
      Limits.comp_zero, Limits.zero_comp]


end
end KIP126.Computation.SphereAndCofiber
