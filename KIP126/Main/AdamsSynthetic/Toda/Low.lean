module

public import KIP126.Main.AdamsSynthetic.Context
import KIP126.Main.Literature.SourceComparisons.RealizationKernel
import KIP126.Def.Comparison.ClassicalSynthetic.RealizationTower.Proofs
import KIP126.Def.ClassicalAdams.TowerNaturality.Proofs
import KIP126.Def.ClassicalAdams.TowerNaturality.Unit.Proofs
import KIP126.Def.ClassicalAdams.TowerResolution.Proofs
import KIP126.Def.ClassicalAdams.MapFiltration.Predicates
import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Proofs
import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
import KIP126.Def.Synthetic.Context.Coherence.Proofs
import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
import KIP126.Def.Synthetic.Localization.Recovery.Proofs
import KIP126.Def.SpectralSequence.Permanence.Proofs
import KIP126.Def.StableHomotopy.Context.Mapping.Data
import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace KIP126.Main.AdamsSynthetic.Toda

open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Literature.AdamsSynthetic

set_option maxHeartbeats 12000000 in
/-- The low-degree synthetic Toda bracket used in Section 7. -/
theorem low_bracket : TripleToda literature.sources.sourceComparisons.todaSource.h0 etaClass
    literature.sources.sourceComparisons.todaSource.h0 (sphereProduct (m := 1) (n := 2) (k := 1) (l := 2) etaClass etaClass) :=
  set_option maxHeartbeats 6000000 in by
  -- Identify the Toda value with η² by low-degree cobar calculations
  -- and coactions on the two-cell and three-cell cofibers.
  open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
    CategoryTheory.MonoidalCategory KIP126.StableHomotopy
    KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
    KIP126.SpectralSequence in
  set_option backward.isDefEq.respectTransparency false in
  set_option maxHeartbeats 2000000 in
  classical
  let Syn := KIP126.Def.standardSyntheticContext.Syn
  let H := KIP126.Def.standardHF2AdamsContext.stableContext.hf2
  let D := adamsComparison
  -- §2.1: use the specified cocycles and the same detection convergence.
  open KIP126.Steenrod.Milnor in
  let C := KIP126.Def.standardHF2AdamsContext.stableContext.Spectrum
  let M := KIP126.Def.standardHF2AdamsContext.milnorCoordinates.toMilnor
  have length_zero_trivial (t : ℕ) (ht : t ≠ 0) : Subsingleton (cochains 0 t) := by
    have hz (x : cochains 0 t) : x = 0 := by
      apply Subtype.ext
      change x.val = 0
      by_contra h
      exact ht (MvPolynomial.IsWeightedHomogeneous.inj_right h x.property.1
        (MvPolynomial.isWeightedHomogeneous_of_isEmpty
          (R := KIP126.Algebra.F2) weight x.val))
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩

  have hi_nonzero (i : ℕ) : Sphere.Internal.hi H M i ≠ 0 := by
    intro hz
    have hz' : MilnorCohomology.hi H M i = 0 := by
      apply (MilnorCohomology.comparison H M 1 (2 ^ i)).injective
      simpa only [map_zero, MilnorCohomology.comparison_hi] using hz
    obtain ⟨b, hb⟩ := (MilnorCohomology.hi_eq_zero_iff H M i).mp hz'
    haveI := length_zero_trivial (2 ^ i) (pow_ne_zero _ (by decide))
    have hb0 : b = 0 := Subsingleton.elim _ _
    rw [hb0, map_zero] at hb
    have hp := congrArg Subtype.val hb.symm
    exact pow_ne_zero _ (MvPolynomial.X_ne_zero ((0 : Fin 1), 0)) hp

  have detection_first_nonzero (d : ℤ)
      (c : TowerDetection.Convergence H.unit (SphereSpectrum : C))
      (x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (1, d))
      (hx : x ≠ 0) (α : HomotopyGroup (d - 1) (SphereSpectrum : C))
      (hdet : TowerDetection.Detects c (1, d) x α) :
      AdamsFiltrationAtLeast H α 1 ∧ ¬ AdamsFiltrationAtLeast H α 2 := by
    let E := adamsTowerInternalSpectralSequence H.unit (SphereSpectrum : C)
    let T := E.ssData (1, d)
    let F := TowerDetection.filtration H.unit (SphereSpectrum : C)
    obtain ⟨z, hz, a, ha, hgr⟩ := hdet
    have hmem : α ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum 1 (d - 1) := by
      have hm : (F.F 1 (d - 1)).arrow a ∈
          (ModuleCat.subobjectModule _) (F.F 1 (d - 1)) := ⟨a, rfl⟩
      rw [ha] at hm
      simpa only [F, TowerDetection.filtration, OrderIso.apply_symm_apply] using hm
    refine ⟨hmem, ?_⟩
    intro hnext
    have hgr0 : F.toAssociatedGraded 1 (d - 1) a = 0 := by
      apply (subobject_cokernel_π_eq_zero_iff (F.F 2 (d - 1))
        (F.F 1 (d - 1)) (F.mono 1 (d - 1)) a).mpr
      rw [ha]
      have hnmem : α ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum 2 (d - 1) := hnext
      simpa only [F, TowerDetection.filtration, OrderIso.apply_symm_apply] using hnmem
    have hz0 : T.pageπ ⊤ z = 0 := by
      apply (ModuleCat.mono_iff_injective (c.identification (1, d)).hom).mp inferInstance
      rw [map_zero]
      exact hgr.trans hgr0
    have hb : T.B ⊤ = T.B 0 := by
      apply boundaries_top_eq_of_d_eq_zero E 2 (by rfl)
      intro r hr
      haveI : Subsingleton (E.Page r ((1, d) - E.diffDeg r)) :=
        adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum
          r (1 - r) (d - (r - 1)) (by omega)
      ext q
      have hq : q = 0 := Subsingleton.elim _ _
      simp only [hq, map_zero]
    have hzmem := (subobject_cokernel_π_eq_zero_iff (T.B ⊤) (T.Z ⊤)
      (T.B_le_Z ⊤) z).mp hz0
    rw [hb] at hzmem
    apply hx
    rw [← hz]
    apply (subobject_cokernel_π_eq_zero_iff (T.B 0) (T.Z 0)
      (T.B_le_Z 0) ((Subobject.ofLE _ _ (T.Z_anti le_top)) z)).mpr
    change (Subobject.ofLE _ _ (T.Z_anti le_top) ≫ (T.Z 0).arrow) z ∈ _
    rwa [Subobject.ofLE_arrow]
  have two_filtration := detection_first_nonzero 1
    literature.sources.sourceComparisons.classicalSource.convergence
    (Sphere.Internal.hi H M 0) (hi_nonzero 0) _ literature.theorems.classical_two_detection
  have eta_filtration := detection_first_nonzero 2
    literature.sources.sourceComparisons.classicalSource.convergence
    (Sphere.Internal.hi H M 1) (hi_nonzero 1) _ literature.theorems.classical_eta_detection
  have eta_nonzero : literature.sources.sourceComparisons.classicalSource.eta ≠ 0 := by
    intro hzero
    apply eta_filtration.2
    refine ⟨0, ?_⟩
    simp only [zero_comp, hzero]
  -- §6.2.2: E₂^{0,3} vanishes because HF₂ has no degree-three homotopy.
  have critical : Subsingleton
      ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 2 (0,3)) := by
    haveI := H.homotopy_vanishes 3 (by decide)
    let e : KIP126.StableHomotopy.HomotopyGroup 3 (H.HF2 ⊗ SphereSpectrum) ≃+
        KIP126.StableHomotopy.HomotopyGroup 3 H.HF2 :=
      ((homotopyGroupFunctor 3).mapIso (ρ_ H.HF2)).addCommGroupIsoToAddEquiv
    have hcoeff : Subsingleton (KIP126.StableHomotopy.HomotopyGroup 3 (H.HF2 ⊗ SphereSpectrum)) :=
      e.injective.subsingleton
    haveI : Subsingleton (KIP126.StableHomotopy.HomotopyGroup (3 - (0 : ℕ))
        (H.HF2 ⊗ adamsTower H.unit SphereSpectrum 0)) := by
      simpa only [Nat.cast_zero, sub_zero, adamsTower] using hcoeff
    have hone : Subsingleton (adamsPage H.unit SphereSpectrum 1 (by decide) 0 3) :=
      (adamsPageOneHomologyEquiv H.unit SphereSpectrum 0 3).injective.subsingleton
    haveI := adamsPage_subsingleton_of_le H.unit SphereSpectrum 1 2
      (by decide) (by decide) (by decide) 0 3 hone
    exact (adamsTowerSSDataPageIso H.unit SphereSpectrum 0 3 0).toLinearEquiv.injective.subsingleton
  -- StageInput_hlow.md §§6.2–6.3: include the critical filtration-zero case.
  have lambda_injective (wt : ℤ) (hw : wt ≤ 4) :
      LambdaInjectiveAt 2 wt (S_0_0 : Syn) := by
    letI := D.shiftAdditive (0,-1)
    letI := (SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (0,-1)).faithful
    let U := (SyntheticCategory.biShift (0,-1)).obj (Smn (Syn := Syn) 2 wt)
    let T := XModLambdaN.cofiberTriangle (S_0_0 : Syn) 1
    let e₀ : U ≅ Smn (Syn := Syn) 2 (wt-1) :=
      (SyntheticCategory.biShift_comp (2,wt) (0,-1)).app S_0_0 ≪≫
        eqToIso (by congr 1 <;> simp [sub_eq_add_neg])
    let e₁ : U⟦(1 : ℤ)⟧ ≅ Smn (Syn := Syn) 3 (wt-1) :=
      (shiftFunctor Syn (1 : ℤ)).mapIso e₀ ≪≫
        (SyntheticCategory.biShift_compat (Syn := Syn) 1).symm.app _ ≪≫
        (SyntheticCategory.biShift_comp (2,wt-1) (1,0)).app S_0_0 ≪≫
        eqToIso (by congr 1 <;> simp)
    have hQ : ∀ q : U⟦(1 : ℤ)⟧ ⟶ T.obj₃, q = 0 := by
      intro q
      haveI : Subsingleton (PageRepresentatives.Ambient H SphereSpectrum (wt-4,wt-1)) := by
        by_cases he : wt = 4
        · subst wt
          exact critical
        · exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum
            2 (wt-4) (wt-1) (by omega)
      have hz : ∀ a : BiHom 3 (wt-1) (XModLambdaN (S_0_0 : Syn) 1), a = 0 := by
        intro a
        have hp : wt - 1 - (wt-4) = 3 := by omega
        have hsub : Subsingleton (BiHom (wt-1-(wt-4)) (wt-1)
            (XModLambdaN (S_0_0 : Syn) 1)) :=
          (D.sphereFirstQuotient (wt-4) (wt-1)).injective.subsingleton
        rw [hp] at hsub
        exact @Subsingleton.elim _ hsub a 0
      apply (cancel_epi e₁.inv).mp
      simpa only [comp_zero] using hz (e₁.inv ≫ q)
    intro a b hab
    have hpre : SyntheticCategory.lam.app (Smn (Syn := Syn) 2 wt) ≫ (a-b) = 0 := by
      rw [Preadditive.comp_sub]
      apply sub_eq_zero.mpr
      simpa only [lambdaAction, Category.assoc, cancel_epi] using hab
    have hf : (SyntheticCategory.biShift (0,-1)).map (a-b) ≫ T.mor₁ = 0 := by
      change (SyntheticCategory.biShift (0,-1)).map (a-b) ≫ lambdaPow 1 S_0_0 = 0
      rw [lambdaPow_one D.shiftCoherence]
      rw [SyntheticCategory.lam.naturality]
      exact hpre
    have hfs : ((SyntheticCategory.biShift (0,-1)).map (a-b))⟦(1 : ℤ)⟧' ≫
        T.mor₁⟦(1 : ℤ)⟧' = 0 := by
      rw [← Functor.map_comp, hf, Functor.map_zero]
    obtain ⟨q,hq⟩ := T.coyoneda_exact₁
      (HasFunctorialCofiber.cofib_distinguished _) _ hfs
    have hz : ((SyntheticCategory.biShift (0,-1)).map (a-b))⟦(1 : ℤ)⟧' = 0 := by
      rw [hq, hQ q, zero_comp]
    have hz' : (SyntheticCategory.biShift (0,-1)).map (a-b) = 0 := by
      apply (shiftFunctor Syn (1 : ℤ)).map_injective
      simpa only [Functor.map_zero] using hz
    apply sub_eq_zero.mp
    apply (SyntheticCategory.biShift (0,-1)).map_injective
    simpa only [Functor.map_zero] using hz'

  -- §6.4: powers of lambda retain all chosen shift isomorphisms.
  have lambda_powers_injective_of_lower_weights
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

  -- §§6.5–6.6: use the kernel theorem on the same literature witness.
  have realization_injective : Function.Injective (fun a : BiHom 2 4 (S_0_0 : Syn) =>
      D.recovery.realization.map a) := by
    letI := D.recovery.adjunction.isLeftAdjoint
    letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts D.recovery.realization
    letI := Functor.additive_of_preservesBinaryBiproducts D.recovery.realization
    have kernel := KIP126.Main.Literature.SourceComparisons.realizationKernel_of_source
      D literature.sources.sourceComparisons.kernelSource literature.theorems.realizationKernel
      literature.sources.sourceComparisons.kernelComparison
    have hi := lambda_powers_injective_of_lower_weights D.shiftCoherence 2 4
      (S_0_0 : Syn) lambda_injective
    intro a b hab
    change D.recovery.realization.map a = D.recovery.realization.map b at hab
    have hz : D.recovery.realization.map (a-b) = 0 := by
      rw [Functor.map_sub, hab, sub_self]
    obtain ⟨k, hk⟩ := (kernel .sphere 2 4 (a-b)).mp hz
    apply sub_eq_zero.mp
    apply hi k
    simpa only [lambdaMultiply, comp_zero] using hk
  -- §7.1: construct a value of the specified cone-based Toda relation.
  let h : BiHom 0 1 (S_0_0 : Syn) := literature.sources.sourceComparisons.todaSource.h0
  have hh : sphereProduct h etaClass = 0 := literature.theorems.toda_h0_eta
  have heh : sphereProduct etaClass h = 0 := by
    rw [D.sphereProductCommutative 1 2 0 1 etaClass h]
    simp only [mul_zero, Int.natAbs_zero, pow_zero, one_smul, hh]
    rfl
  letI := D.shiftAdditive (0,1)
  let f := (SyntheticCategory.biShift (1,3)).map h
  let g := (SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app (S_0_0 : Syn) ≫
    (SyntheticCategory.biShift (0,1)).map etaClass
  have hraw : (SyntheticCategory.biShift (1,2)).map h ≫ etaClass = 0 := by
    apply (cancel_epi ((SyntheticCategory.biShift_comp (0,1) (1,2)).inv.app
      (S_0_0 : Syn))).mp
    simpa only [sphereProduct, Category.assoc, comp_zero] using hh
  have hfg : f ≫ g = 0 := by
    dsimp only [f, g]
    erw [← Category.assoc, (SyntheticCategory.biShift_comp (1,2) (0,1)).inv.naturality]
    dsimp only [Functor.comp_map]
    rw [Category.assoc, ← Functor.map_comp, hraw, Functor.map_zero, comp_zero]
  have hgh : g ≫ h = 0 := by
    simpa only [g, sphereProduct, Category.assoc] using heh
  obtain ⟨Q, i, p, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f i p
  obtain ⟨b, hb⟩ := T.yoneda_exact₂ hT g hfg
  have hib : i ≫ b = g := hb.symm
  have hib0 : i ≫ (b ≫ h) = 0 := by
    rw [← Category.assoc, hib, hgh]
  obtain ⟨x, hx⟩ := T.yoneda_exact₃ hT (b ≫ h) hib0
  have hx' : Toda.Relation x f g h := ⟨Q, i, p, hT, b, hib, hx.symm⟩
  let u : BiHom 2 4 (S_0_0 : Syn) := (tripleTodaSource 0 1 1 2 0 1).hom ≫ x
  have hu : TripleToda h etaClass h u := by
    change Toda.Relation ((tripleTodaSource 0 1 1 2 0 1).inv ≫
      ((tripleTodaSource 0 1 1 2 0 1).hom ≫ x)) f g h
    simpa only [Iso.inv_hom_id_assoc] using hx'
  -- §§1–5 and 7.2–7.3: identify the realized value using the low cobar
  -- calculation and the two-cell and three-cell coaction calculations.
  have hreal : D.recovery.realization.map u =
      D.recovery.realization.map (sphereProduct etaClass etaClass) := by
    have classical_smalls :
        (∀ a b : HomotopyGroup (1 : ℤ)
          (SphereSpectrum (C := KIP126.Classical.Adams.standardFoundation.Spectrum)),
          a ≠ 0 → b ≠ 0 → a = b) ∧
        (∀ a b : HomotopyGroup (2 : ℤ)
          (SphereSpectrum (C := KIP126.Classical.Adams.standardFoundation.Spectrum)),
          a ≠ 0 → b ≠ 0 → a = b) := by
      open scoped BigOperators in
      open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
        CategoryTheory.MonoidalCategory KIP126.StableHomotopy
        KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
        KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
        KIP126.SpectralSequence KIP126.AdamsSynthetic KIP126.Literature.AdamsSynthetic
        KIP126.Steenrod.Milnor MvPolynomial in
      set_option maxHeartbeats 4000000 in
      exact by
        classical
        -- Markdown §1: a generator of index at least 2 has weight at least 7.
        have low_support (d : ℕ →₀ ℕ) (hd : slotWeight d ≤ 4) :
            d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
          have hz (j : ℕ) (hj : 2 ≤ j) : d j = 0 := by
            by_contra hn
            have hw := Finsupp.le_weight_of_ne_zero'
              (fun j : ℕ => 2 ^ (j + 1) - 1) hn
            have hp : 2 ^ 3 ≤ 2 ^ (j + 1) :=
              Nat.pow_le_pow_right (by decide) (by omega)
            change 2 ^ (j + 1) - 1 ≤ slotWeight d at hw
            norm_num at hp
            omega
          ext j
          rcases j with _ | _ | j
          · simp
          · simp
          · simp [hz (j + 2) (by omega)]

        have low_weight (d : ℕ →₀ ℕ) (hd : slotWeight d ≤ 4) :
            slotWeight d = d 0 + 3 * d 1 := by
          conv_lhs => rw [low_support d hd]
          simp [slotWeight, map_add, Finsupp.weight_single, mul_comm]

        have weight_one (d : ℕ →₀ ℕ) (hd : slotWeight d = 1) :
            d = Finsupp.single 0 1 := by
          have hw := low_weight d (by omega)
          have h0 : d 0 = 1 := by omega
          have h1 : d 1 = 0 := by omega
          rw [low_support d (by omega), h0, h1]
          simp

        have weight_two (d : ℕ →₀ ℕ) (hd : slotWeight d = 2) :
            d = Finsupp.single 0 2 := by
          have hw := low_weight d (by omega)
          have h0 : d 0 = 2 := by omega
          have h1 : d 1 = 0 := by omega
          rw [low_support d (by omega), h0, h1]
          simp

        have weight_three (d : ℕ →₀ ℕ) (hd : slotWeight d = 3) :
            d = Finsupp.single 0 3 ∨ d = Finsupp.single 1 1 := by
          have hw := low_weight d (by omega)
          by_cases h1 : d 1 = 0
          · left
            have h0 : d 0 = 3 := by omega
            rw [low_support d (by omega), h0, h1]
            simp
          · right
            have h0 : d 0 = 0 := by omega
            have h1' : d 1 = 1 := by omega
            rw [low_support d (by omega), h0, h1']
            simp

        have weight_four (d : ℕ →₀ ℕ) (hd : slotWeight d = 4) :
            d = Finsupp.single 0 4 ∨
              d = Finsupp.single 0 1 + Finsupp.single 1 1 := by
          have hw := low_weight d (by omega)
          by_cases h1 : d 1 = 0
          · left
            have h0 : d 0 = 4 := by omega
            rw [low_support d (by omega), h0, h1]
            simp
          · right
            have h0 : d 0 = 1 := by omega
            have h1' : d 1 = 1 := by omega
            rw [low_support d (by omega), h0, h1']

        have slot_positive (d : ℕ →₀ ℕ) (hd : d ≠ 0) : 1 ≤ slotWeight d := by
          apply Nat.one_le_iff_ne_zero.mpr
          have hp : 0 < slotWeight d := by
            change 0 < d.sum (fun j n => n • (2 ^ (j + 1) - 1))
            apply Finsupp.sum_pos _ hd
            intro j hj
            have hn : 0 < d j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
            have hw : 0 < 2 ^ (j + 1) - 1 := by
              have hh : 2 ≤ 2 ^ (j + 1) := by
                rw [pow_succ]
                have := Nat.one_le_pow j 2 (by decide)
                omega
              omega
            exact Nat.mul_pos hn hw
          omega

        -- The degree excess over the word length controls all individual letters.
        have word_excess {s k : ℕ} (d : MilnorWord s ((s : ℤ) + k)) :
            ∑ i : Fin s, (slotWeight (d.val i) - 1) = k := by
          have hs : ∑ i : Fin s, slotWeight (d.val i) = s + k := by
            have ht := d.property.1
            dsimp only [wordDegree] at ht
            exact_mod_cast ht
          have he : (∑ i : Fin s, (slotWeight (d.val i) - 1)) + s = s + k := by
            calc
              _ = ∑ i : Fin s, ((slotWeight (d.val i) - 1) + 1) := by
                simp [Finset.sum_add_distrib]
              _ = ∑ i : Fin s, slotWeight (d.val i) := by
                apply Finset.sum_congr rfl
                intro i hi
                have hp := slot_positive (d.val i) (d.property.2 i)
                omega
              _ = s + k := hs
          omega

        have word_slot_bound {s k : ℕ} (d : MilnorWord s ((s : ℤ) + k))
            (i : Fin s) : slotWeight (d.val i) ≤ k + 1 := by
          have hb : slotWeight (d.val i) - 1 ≤
              ∑ j : Fin s, (slotWeight (d.val j) - 1) :=
            Finset.single_le_sum (f := fun j : Fin s => slotWeight (d.val j) - 1)
              (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
          rw [word_excess d] at hb
          have hp := slot_positive (d.val i) (d.property.2 i)
          omega

        -- Markdown §1.2: all stem-one words have a single U=[x²] slot.
        have stem_one_word {s : ℕ} (d : MilnorWord s ((s : ℤ) + 1)) :
            ∃ i : Fin s, d.val i = Finsupp.single 0 2 ∧
              ∀ j : Fin s, j ≠ i → d.val j = Finsupp.single 0 1 := by
          let e : Fin s → ℕ := fun i => slotWeight (d.val i) - 1
          have he : ∑ i, e i = 1 := word_excess d
          obtain ⟨i, hi, hei⟩ := Finset.sum_pos_iff.mp (show 0 < ∑ i, e i by omega)
          have hbi : e i ≤ ∑ j, e j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
          have hei' : e i = 1 := by omega
          have hw : slotWeight (d.val i) = 2 := by
            have hp := slot_positive (d.val i) (d.property.2 i)
            dsimp only [e] at hei'
            omega
          refine ⟨i, weight_two _ hw, ?_⟩
          intro j hji
          have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin s)) e hi
          have hz : ∑ k ∈ Finset.univ.erase i, e k = 0 := by omega
          have hej : e j = 0 := by
            have hb : e j ≤ ∑ k ∈ Finset.univ.erase i, e k :=
              Finset.single_le_sum (fun k _ => Nat.zero_le _) (by simp [hji])
            omega
          apply weight_one
          have hp := slot_positive (d.val j) (d.property.2 j)
          dsimp only [e] at hej
          omega

        -- Markdown §1.3: one degree-three letter, or exactly two degree-two letters.
        have stem_two_word {s : ℕ} (d : MilnorWord s ((s : ℤ) + 2)) :
            (∃ i : Fin s,
              (d.val i = Finsupp.single 0 3 ∨ d.val i = Finsupp.single 1 1) ∧
              ∀ j : Fin s, j ≠ i → d.val j = Finsupp.single 0 1) ∨
            (∃ i j : Fin s, i ≠ j ∧ d.val i = Finsupp.single 0 2 ∧
              d.val j = Finsupp.single 0 2 ∧
              ∀ l : Fin s, l ≠ i → l ≠ j → d.val l = Finsupp.single 0 1) := by
          let e : Fin s → ℕ := fun i => slotWeight (d.val i) - 1
          have he : ∑ i, e i = 2 := word_excess d
          obtain ⟨i, hi, hei⟩ := Finset.sum_pos_iff.mp (show 0 < ∑ i, e i by omega)
          have hbi : e i ≤ ∑ j, e j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
          have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin s)) e hi
          by_cases hei2 : e i = 2
          · left
            have hw : slotWeight (d.val i) = 3 := by
              have hp := slot_positive (d.val i) (d.property.2 i)
              dsimp only [e] at hei2
              omega
            refine ⟨i, weight_three _ hw, ?_⟩
            intro j hji
            have hz : ∑ k ∈ Finset.univ.erase i, e k = 0 := by omega
            have hej : e j = 0 := by
              have hb : e j ≤ ∑ k ∈ Finset.univ.erase i, e k :=
                Finset.single_le_sum (fun k _ => Nat.zero_le _) (by simp [hji])
              omega
            apply weight_one
            have hp := slot_positive (d.val j) (d.property.2 j)
            dsimp only [e] at hej
            omega
          · right
            have hei1 : e i = 1 := by omega
            have he' : ∑ k ∈ Finset.univ.erase i, e k = 1 := by omega
            obtain ⟨j, hj, hej⟩ := Finset.sum_pos_iff.mp
              (show 0 < ∑ k ∈ Finset.univ.erase i, e k by omega)
            have hji : j ≠ i := (Finset.mem_erase.mp hj).1
            have hbj : e j ≤ ∑ k ∈ Finset.univ.erase i, e k :=
              Finset.single_le_sum (fun k _ => Nat.zero_le _) hj
            have hej1 : e j = 1 := by omega
            have hwi : slotWeight (d.val i) = 2 := by
              have hp := slot_positive (d.val i) (d.property.2 i)
              dsimp only [e] at hei1
              omega
            have hwj : slotWeight (d.val j) = 2 := by
              have hp := slot_positive (d.val j) (d.property.2 j)
              dsimp only [e] at hej1
              omega
            refine ⟨i, j, Ne.symm hji, weight_two _ hwi, weight_two _ hwj, ?_⟩
            intro l hli hlj
            have hsum' := Finset.sum_erase_add (Finset.univ.erase i) e hj
            have hz : ∑ k ∈ (Finset.univ.erase i).erase j, e k = 0 := by omega
            have hel : e l = 0 := by
              have hb : e l ≤ ∑ k ∈ (Finset.univ.erase i).erase j, e k :=
                Finset.single_le_sum (fun k _ => Nat.zero_le _) (by simp [hli, hlj])
              omega
            apply weight_one
            have hp := slot_positive (d.val l) (d.property.2 l)
            dsimp only [e] at hel
            omega

        -- An actual finite basis index for all of C^{s,s+1}, including s=0.
        let stemOneWord (s : ℕ) (i : Fin s) : MilnorWord s ((s : ℤ) + 1) :=
          ⟨fun j => Finsupp.single 0 (1 + if j = i then 1 else 0), by
            constructor
            · simp [wordDegree, slotWeight, Finsupp.weight_single, Finset.sum_add_distrib]
            · intro j
              apply Finsupp.single_ne_zero.mpr
              omega⟩

        have stemOneWord_surjective (s : ℕ) : Function.Surjective (stemOneWord s) := by
          intro d
          obtain ⟨i, hi, hrest⟩ := stem_one_word d
          refine ⟨i, ?_⟩
          apply Subtype.ext
          funext j
          by_cases hji : j = i
          · subst j
            simpa only [stemOneWord, if_pos rfl, ite_true] using hi.symm
          · simpa [stemOneWord, hji] using (hrest j hji).symm

        have stemOneWord_injective (s : ℕ) : Function.Injective (stemOneWord s) := by
          intro i j hij
          by_contra hne
          have h := congrArg (fun d : MilnorWord s ((s : ℤ) + 1) => d.val i 0) hij
          simp [stemOneWord, hne] at h

        let stemOneWordEquiv (s : ℕ) :
            Fin s ≃ MilnorWord s ((s : ℤ) + 1) :=
          Equiv.ofBijective (stemOneWord s)
            ⟨stemOneWord_injective s, stemOneWord_surjective s⟩

        have positiveMonomial_one_subsingleton : Subsingleton (PositiveMonomial 1) := by
          constructor
          intro a b
          apply Subtype.ext
          have ha : slotWeight a.val = 1 := by exact_mod_cast a.property.1
          have hb : slotWeight b.val = 1 := by exact_mod_cast b.property.1
          exact (weight_one a.val ha).trans (weight_one b.val hb).symm

        have positiveMonomial_two_subsingleton : Subsingleton (PositiveMonomial 2) := by
          constructor
          intro a b
          apply Subtype.ext
          have ha : slotWeight a.val = 2 := by exact_mod_cast a.property.1
          have hb : slotWeight b.val = 2 := by exact_mod_cast b.property.1
          exact (weight_two a.val ha).trans (weight_two b.val hb).symm

        let x : TensorPower 1 := X (0, 0)
        let u : TensorPower 1 := X (0, 0) ^ 2
        let p : TensorPower 1 := X (0, 1)
        let q : TensorPower 1 := X (0, 0) ^ 3 + X (0, 1)
        let t : TensorPower 1 := X (0, 0) * X (0, 1)
        let z : TensorPower 1 := X (0, 0) ^ 4

        have dx : differentialPolynomial 1 x = 0 := by
          simpa [x, hiPolynomial] using hiPolynomial_differential 0

        have du : differentialPolynomial 1 u = 0 := by
          simpa [u, hiPolynomial] using hiPolynomial_differential 1

        have dz : differentialPolynomial 1 z = 0 := by
          simpa [z, hiPolynomial] using hiPolynomial_differential 2

        -- Markdown §1: dP = UX for the actual normalized-polynomial differential.
        have dp : differentialPolynomial 1 p = cupPolynomial u x := by
          simp [differentialPolynomial, p, u, x, cupPolynomial, insertLeft, insertRight,
            splitSlot, coproductGenerator, xi, Fin.sum_univ_succ, Finset.sum_range_succ]
          ring_nf
          simp [CharTwo.two_eq_zero]

        -- Q = [x³+y] is the second degree-three basis vector.
        have dq : differentialPolynomial 1 q = cupPolynomial x u := by
          have hc (a b : TensorPower 2) : (a + b) ^ 3 =
              a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 := by
            calc
              _ = (a ^ 2 + b ^ 2) * (a + b) := by rw [pow_succ, CharTwo.add_sq]
              _ = _ := by ring
          simp [differentialPolynomial, q, u, x, cupPolynomial, insertLeft, insertRight,
            splitSlot, coproductGenerator, xi, Fin.sum_univ_succ, Finset.sum_range_succ, hc]
          ring_nf
          simp [CharTwo.two_eq_zero]

        -- The only nonzero incoming degree-four differential is E+UU.
        have dt : differentialPolynomial 1 t =
            cupPolynomial q x + cupPolynomial u u + cupPolynomial x p := by
          simp [differentialPolynomial, t, q, u, x, p, cupPolynomial, insertLeft, insertRight,
            splitSlot, coproductGenerator, xi, Fin.sum_univ_succ, Finset.sum_range_succ]
          ring_nf
          simp [CharTwo.two_eq_zero]

        let xc : cochains 1 1 :=
          ⟨x, by
            change IsCochain 1 x
            simpa [x, hiPolynomial] using hiPolynomial_mem 0⟩

        let uc : cochains 1 2 :=
          ⟨u, by
            change IsCochain 2 u
            simpa [u, hiPolynomial] using hiPolynomial_mem 1⟩

        let pc : cochains 1 3 := ⟨p, by
          constructor
          · simpa [p, weight] using
              (isWeightedHomogeneous_X (R := ZMod 2) (@weight 1) (0, 1))
          · change p ∈ (⨅ slot : Fin 1, LinearMap.ker (augmentSlot slot).toLinearMap)
            rw [Submodule.mem_iInf]
            intro slot
            have hs : slot = 0 := Subsingleton.elim _ _
            subst slot
            simp [LinearMap.mem_ker, augmentSlot, p]⟩

        let qc : cochains 1 3 := ⟨q, by
          constructor
          · have hh := (isWeightedHomogeneous_X (R := ZMod 2) (@weight 1) (0, 0)).pow 3
            have hp := pc.property.1
            change IsWeightedHomogeneous weight p 3 at hp
            have hh' : IsWeightedHomogeneous weight ((X ((0 : Fin 1), 0) : TensorPower 1) ^ 3) 3 :=
              by simpa [weight] using hh
            exact hh'.add hp
          · change q ∈ (⨅ slot : Fin 1, LinearMap.ker (augmentSlot slot).toLinearMap)
            rw [Submodule.mem_iInf]
            intro slot
            have hs : slot = 0 := Subsingleton.elim _ _
            subst slot
            simp [LinearMap.mem_ker, augmentSlot, q]⟩

        let tc : cochains 1 4 := ⟨t, by
          constructor
          · have h := (isWeightedHomogeneous_X (R := ZMod 2) (@weight 1) (0, 0)).mul
              (isWeightedHomogeneous_X (R := ZMod 2) (@weight 1) (0, 1))
            simpa [t, weight] using h
          · change t ∈ (⨅ slot : Fin 1, LinearMap.ker (augmentSlot slot).toLinearMap)
            rw [Submodule.mem_iInf]
            intro slot
            have hs : slot = 0 := Subsingleton.elim _ _
            subst slot
            simp [LinearMap.mem_ker, augmentSlot, t]⟩

        have dxc : differential 1 1 xc = 0 := Subtype.ext dx
        have duc : differential 1 2 uc = 0 := Subtype.ext du
        have dpc : differential 1 3 pc = cup uc xc := Subtype.ext dp
        have dqc : differential 1 3 qc = cup xc uc := Subtype.ext dq
        have dtc : differential 1 4 tc = cup qc xc + cup uc uc + cup xc pc :=
          Subtype.ext dt

        let xpow : (s : ℕ) → cochains s s :=
          Nat.rec
            (⟨1, by
              constructor
              · change IsWeightedHomogeneous (@weight 0) (1 : TensorPower 0) 0
                exact isWeightedHomogeneous_one (R := ZMod 2) (@weight 0)
              · change (1 : TensorPower 0) ∈
                  (⨅ slot : Fin 0, LinearMap.ker (augmentSlot slot).toLinearMap)
                rw [Submodule.mem_iInf]
                intro slot
                exact Fin.elim0 slot⟩ : cochains 0 0)
            (fun s v => cup v xc)

        have dxpow (s : ℕ) : differential s s (xpow s) = 0 := by
          induction s with
          | zero =>
            apply Subtype.ext
            simp [differential, xpow, differentialPolynomial, insertLeft, insertRight,
              CharTwo.add_self_eq_zero]
          | succ s ih =>
            change differential _ _ (cup (xpow s) xc) = 0
            simp only [differential_cup, ih, dxc, cup_zero_left, cup_zero_right,
              map_zero, zero_add]

        have cup_reindex_left {s s' t t' n m : ℕ} (hs : s = s') (ht : t = t')
            (a : cochains s t) (b : cochains n m) :
            cup (reindex hs ht a) b = reindex (by omega) (by omega) (cup a b) := by
          subst s'
          subst t'
          rfl

        have reindex_trans {s s' s'' t t' t'' : ℕ}
            (hs : s = s') (ht : t = t') (hs' : s' = s'') (ht' : t' = t'')
            (a : cochains s t) :
            reindex hs' ht' (reindex hs ht a) = reindex (hs.trans hs') (ht.trans ht') a := by
          subst s'
          subst s''
          subst t'
          subst t''
          rfl

        -- Markdown §1.2 and §1.3: the surrounding X factors are all MilnorCohomology.cycles.
        have differential_sandwich {s t : ℕ} (a b : ℕ) (w : cochains s t) :
            differential (a + s + b) (a + t + b) (cup (cup (xpow a) w) (xpow b)) =
              reindex (by omega) rfl
                (cup (cup (xpow a) (differential s t w)) (xpow b)) := by
          rw [differential_cup, dxpow, cup_zero_right, map_zero, add_zero,
            differential_cup, dxpow, cup_zero_left, map_zero, zero_add,
            cup_reindex_left, reindex_trans]

        -- Explicit arbitrary-length boundary words, directly matching §1.2.
        have p_boundary (a b : ℕ) :
            differential (a + 1 + b) (a + 3 + b) (cup (cup (xpow a) pc) (xpow b)) =
              reindex (by omega) rfl (cup (cup (xpow a) (cup uc xc)) (xpow b)) := by
          rw [differential_sandwich, dpc]

        have q_boundary (a b : ℕ) :
            differential (a + 1 + b) (a + 3 + b) (cup (cup (xpow a) qc) (xpow b)) =
              reindex (by omega) rfl (cup (cup (xpow a) (cup xc uc)) (xpow b)) := by
          rw [differential_sandwich, dqc]

        have t_boundary (a b : ℕ) :
            differential (a + 1 + b) (a + 4 + b) (cup (cup (xpow a) tc) (xpow b)) =
              reindex (by omega) rfl
                (cup (cup (xpow a) (cup qc xc + cup uc uc + cup xc pc)) (xpow b)) := by
          rw [differential_sandwich, dtc]

        have reindex_cup_val_general {s s' t t' n m : ℕ}
            (hs : s + s' = n) (ht : t + t' = m) (a : cochains s t) (b : cochains s' t') :
            (reindex hs ht (cup a b)).val =
              blockRename (n := n) 0 (by omega) a.val * blockRename s (by omega) b.val := by
          subst n
          subst m
          exact cupPolynomial_blocks a.val b.val

        have cup_assoc {s s' s'' t t' t'' : ℕ}
            (a : cochains s t) (b : cochains s' t') (c : cochains s'' t'') :
            reindex (Nat.add_assoc s s' s'') (Nat.add_assoc t t' t'') (cup (cup a b) c) =
              cup a (cup b c) := by
          apply Subtype.ext
          rw [reindex_cup_val_general]
          change blockRename 0 _ (cupPolynomial a.val b.val) *
            blockRename (s + s') _ c.val = cupPolynomial a.val (cupPolynomial b.val c.val)
          simp only [cupPolynomial_blocks, map_mul, blockRename_comp, Nat.zero_add, Nat.add_zero]
          ring

        have cup_add_left {s s' t t' : ℕ}
            (a b : cochains s t) (c : cochains s' t') :
            cup (a + b) c = cup a c + cup b c := by
          apply Subtype.ext
          simp [cup, cupPolynomial, map_add, add_mul]

        have cup_add_right {s s' t t' : ℕ}
            (a : cochains s t) (b c : cochains s' t') :
            cup a (b + c) = cup a b + cup a c := by
          apply Subtype.ext
          simp [cup, cupPolynomial, map_add, mul_add]

        have xpow_val (s : ℕ) : (xpow s).val = ∏ i : Fin s, X (i, 0) := by
          induction s with
          | zero => simp [xpow]
          | succ s ih =>
            change cupPolynomial (xpow s).val xc.val = _
            rw [cupPolynomial, ih, map_prod]
            simp only [rename_X, xc, x]
            have hc (i : Fin s) : i.castAdd 1 = i.castSucc := Fin.ext rfl
            have hz : (0 : Fin 1).natAdd s = Fin.last s := Fin.ext (by simp)
            simpa only [hc, hz] using
              (Fin.prod_univ_castSucc (fun i : Fin (s + 1) => X (i, 0))).symm

        have xpow_cup (a b : ℕ) : cup (xpow a) (xpow b) = xpow (a + b) := by
          apply Subtype.ext
          change cupPolynomial (xpow a).val (xpow b).val = (xpow (a + b)).val
          rw [cupPolynomial, xpow_val, xpow_val, xpow_val, map_prod, map_prod]
          simp only [rename_X]
          exact (Fin.prod_univ_add (fun i : Fin (a + b) => X (i, 0))).symm

        -- This is the polynomial of the unique-U word at position a.
        have single_u_val (a b : ℕ) :
            (cup (cup (xpow a) uc) (xpow b)).val =
              (xpow (a + 1 + b)).val * X ((⟨a, by omega⟩ : Fin (a + 1 + b)), 0) := by
          have hx : cup (cup (xpow a) xc) (xpow b) = xpow (a + 1 + b) :=
            xpow_cup (a + 1) b
          rw [← hx]
          change cupPolynomial (cupPolynomial (xpow a).val uc.val) (xpow b).val =
            cupPolynomial (cupPolynomial (xpow a).val xc.val) (xpow b).val * _
          simp only [cupPolynomial, uc, xc, u, x, map_mul, map_pow, rename_X]
          have hi : ((0 : Fin 1).natAdd a).castAdd b =
              (⟨a, by omega⟩ : Fin (a + 1 + b)) := Fin.ext (by simp)
          rw [hi]
          ring

        -- Pure cobar words have one polynomial exponent in each tensor factor.

        have pure_word_exponents {s : ℕ} (e : Fin s → ℕ) :
            (slotExponentsEquiv s).symm (fun i => Finsupp.single 0 (e i)) =
              ∑ i : Fin s, Finsupp.single (i, 0) (e i) := by
          apply (slotExponentsEquiv s).injective
          rw [Equiv.apply_symm_apply]
          funext i
          ext j
          change Finsupp.single 0 (e i) j =
            (∑ k : Fin s, Finsupp.single (k, 0) (e k)) (i, j)
          by_cases hj : j = 0
          · subst j
            simp [Finsupp.single_apply]
          · simp [Finsupp.single_apply, hj, Ne.symm hj]

        have pure_word_polynomial {s : ℕ} (e : Fin s → ℕ) :
            (monomial ((slotExponentsEquiv s).symm (fun i => Finsupp.single 0 (e i))) 1 :
              TensorPower s) = ∏ i : Fin s, X (i, 0) ^ e i := by
          rw [pure_word_exponents, monomial_sum_one]
          simp only [← X_pow_eq_monomial]

        have unique_u_polynomial {s : ℕ} (i : Fin s) :
            (monomial ((slotExponentsEquiv s).symm
              (fun j => Finsupp.single 0 (1 + if j = i then 1 else 0))) 1 : TensorPower s) =
              (xpow s).val * X (i, 0) := by
          rw [pure_word_polynomial, xpow_val]
          simp only [pow_add, pow_one, Finset.prod_mul_distrib]
          congr 1
          simp [apply_ite]

        have stem_one_word_polynomial {s t : ℕ} (d : MilnorWord s t)
            (ht : t = s + 1) :
            ∃ i : Fin s, ((cochainsWordEquiv s t).symm (Finsupp.single d 1)).val =
              (xpow s).val * X (i, 0) := by
          have hd : wordDegree d.val = (s : ℤ) + 1 := by
            rw [d.property.1, ht]
            push_cast
            rfl
          let d' : MilnorWord s ((s : ℤ) + 1) := ⟨d.val, hd, d.property.2⟩
          obtain ⟨i, hi⟩ := stemOneWord_surjective s d'
          refine ⟨i, ?_⟩
          rw [cochainsWordEquiv_symm_single_val]
          have hv : d.val = fun j => Finsupp.single 0 (1 + if j = i then 1 else 0) :=
            (congrArg Subtype.val hi).symm
          rw [hv]
          exact unique_u_polynomial i

        -- The exceptional stem-one cochain space already has exactly two elements.
        let degree_one_two_equiv : cochains 1 2 ≃ₗ[ZMod 2] ZMod 2 :=
          (cochainsWordEquiv 1 2).trans
            ((Finsupp.domLCongr (R := ZMod 2) (stemOneWordEquiv 1).symm).trans
              (Finsupp.uniqueLinearEquiv (ZMod 2) (ZMod 2) (0 : Fin 1)))

        have degree_one_two_card : Nat.card (cochains 1 2) = 2 := by
          rw [Nat.card_congr degree_one_two_equiv.toEquiv]
          exact Nat.card_eq_fintype_card

        -- A boundary predicate retaining the source length, including integer-grade transports.
        let Boundary {s t : ℕ} (w : cochains s t) : Prop :=
          ∃ (n : ℕ) (h : n + 1 = s) (v : cochains n t),
            reindex h rfl (differential n t v) = w

        have boundary_reindex {s s' t t' : ℕ} (hs : s = s') (ht : t = t')
            {w : cochains s t} (hw : Boundary w) : Boundary (reindex hs ht w) := by
          subst s'
          subst t'
          exact hw

        have boundary_cup_cycle {s s' t t' : ℕ} {w : cochains s t} (hw : Boundary w)
            (v : cochains s' t') (hv : differential s' t' v = 0) : Boundary (cup w v) := by
          obtain ⟨n, hs, a, ha⟩ := hw
          subst s
          change differential n t a = w at ha
          subst w
          refine ⟨n + s', by omega, cup a v, ?_⟩
          rw [differential_cup, hv, cup_zero_right, map_zero, add_zero, reindex_trans]
          rfl

        have cycle_cup_boundary {s s' t t' : ℕ} (v : cochains s t)
            (hv : differential s t v = 0) {w : cochains s' t'} (hw : Boundary w) :
            Boundary (cup v w) := by
          obtain ⟨n, hs, a, ha⟩ := hw
          subst s'
          change differential n t' a = w at ha
          subst w
          refine ⟨s + n, by omega, cup v a, ?_⟩
          rw [differential_cup, hv, cup_zero_left, map_zero, zero_add, reindex_trans]
          rfl

        have ux_boundary : Boundary (cup uc xc) := ⟨1, rfl, pc, dpc⟩
        have xu_boundary : Boundary (cup xc uc) := ⟨1, rfl, qc, dqc⟩

        have xpow_one : xpow 1 = xc := by
          apply Subtype.ext
          simp [xpow, cup, cupPolynomial, xc, x]

        have boundary_assoc_left {s s' s'' t t' t'' : ℕ}
            (a : cochains s t) (b : cochains s' t') (c : cochains s'' t'')
            (h : Boundary (cup a (cup b c))) : Boundary (cup (cup a b) c) := by
          have hh := boundary_reindex (Nat.add_assoc s s' s'').symm
            (Nat.add_assoc t t' t'').symm h
          rw [← cup_assoc, reindex_trans] at hh
          exact hh

        have single_u_boundary (a b : ℕ) (hab : 1 ≤ a + b) :
            Boundary (cup (cup (xpow a) uc) (xpow b)) := by
          cases a with
          | zero =>
            obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ b)
            have hb := boundary_cup_cycle ux_boundary (xpow c) (dxpow c)
            have hb' := boundary_reindex (Nat.add_assoc 1 1 c) (Nat.add_assoc 2 1 c) hb
            rw [cup_assoc, ← xpow_one, xpow_cup] at hb'
            have hh := cycle_cup_boundary (xpow 0) (dxpow 0) hb'
            have hh' := boundary_assoc_left (xpow 0) uc (xpow (1 + c)) hh
            exact hh'
          | succ a =>
            have hb := cycle_cup_boundary (xpow a) (dxpow a) xu_boundary
            have hb' := boundary_assoc_left (xpow a) xc uc hb
            exact boundary_cup_cycle hb' (xpow b) (dxpow b)

        have reindex_unique_u_val {s s' t t' : ℕ} (hs : s = s') (ht : t = t')
            (w : cochains s t) (i : Fin s)
            (hw : w.val = (xpow s).val * X (i, 0)) :
            (reindex hs ht w).val = (xpow s').val * X (Fin.cast hs i, 0) := by
          subst s'
          subst t'
          exact hw

        have basis_boundary (n : ℕ) (d : MilnorWord (n + 2) ((n + 3 : ℕ) : ℤ)) :
            Boundary ((cochainsWordEquiv (n + 2) (n + 3)).symm (Finsupp.single d 1)) := by
          obtain ⟨i, hi⟩ := stem_one_word_polynomial d (by omega)
          let a := i.val
          let b := n + 1 - i.val
          have hi' := i.isLt
          have hs : a + 1 + b = n + 2 := by dsimp [a, b]; omega
          have ht : a + 2 + b = n + 3 := by dsimp [a, b]; omega
          have hab : 1 ≤ a + b := by dsimp [a, b]; omega
          have hb := boundary_reindex hs ht (single_u_boundary a b hab)
          have he : reindex hs ht (cup (cup (xpow a) uc) (xpow b)) =
              (cochainsWordEquiv (n + 2) (n + 3)).symm (Finsupp.single d 1) := by
            apply Subtype.ext
            rw [reindex_unique_u_val hs ht _ _ (single_u_val a b), hi]
            congr 2
          rwa [he] at hb

        have boundary_mem_range {n t : ℕ} {w : cochains (n + 1) t} (hw : Boundary w) :
            w ∈ LinearMap.range (differential n t) := by
          obtain ⟨m, hm, v, hv⟩ := hw
          have hmn : m = n := by omega
          subst m
          exact ⟨v, hv⟩

        -- Markdown §1.2, for every filtration at least two: every stem-one cochain is a boundary.
        have stem_one_surjective (n : ℕ) : Function.Surjective (differential (n + 1) (n + 3)) := by
          intro w
          have hw : w ∈ LinearMap.range (differential (n + 1) (n + 3)) := by
            let e := cochainsWordEquiv (n + 2) (n + 3)
            have hgen (z : MilnorWord (n + 2) ((n + 3 : ℕ) : ℤ) →₀ ZMod 2) :
                e.symm z ∈ LinearMap.range (differential (n + 1) (n + 3)) := by
              induction z using Finsupp.induction_linear with
              | zero => simp
              | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
              | single d r =>
                have hd := boundary_mem_range (basis_boundary n d)
                have hr := Submodule.smul_mem (LinearMap.range (differential (n + 1) (n + 3))) r hd
                simpa only [e, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one] using hr
            simpa only [e, LinearEquiv.symm_apply_apply] using hgen (e w)
          exact hw

        -- The cobar cup product of cycles is a cycle.

        have cup_cycle {s s' t t' : ℕ} (a : cochains s t) (b : cochains s' t')
            (ha : differential s t a = 0) (hb : differential s' t' b = 0) :
            differential (s + s') (t + t') (cup a b) = 0 :=
          cup_isCycle a b ha hb

        have boundary_assoc_right {s s' s'' t t' t'' : ℕ}
            (a : cochains s t) (b : cochains s' t') (c : cochains s'' t'')
            (h : Boundary (cup (cup a b) c)) : Boundary (cup a (cup b c)) := by
          have hh := boundary_reindex (Nat.add_assoc s s' s'') (Nat.add_assoc t t' t'') h
          rwa [cup_assoc] at hh

        have boundary_xpow_u (a : ℕ) (ha : 1 ≤ a) : Boundary (cup (xpow a) uc) := by
          obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
          have h := cycle_cup_boundary (xpow a) (dxpow a) xu_boundary
          exact boundary_assoc_left (xpow a) xc uc h

        have boundary_u_xpow (a : ℕ) (ha : 1 ≤ a) : Boundary (cup uc (xpow a)) := by
          obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le ha
          have h := boundary_cup_cycle ux_boundary (xpow a) (dxpow a)
          have hh := boundary_assoc_right uc xc (xpow a) h
          rw [← xpow_one, xpow_cup] at hh
          exact hh

        -- Every R word in filtration at least three is a boundary (Markdown §1.3).
        have double_u_boundary (a b c : ℕ) (h : 1 ≤ a + b + c) :
            Boundary (cup (cup (xpow a) uc) (cup (xpow b) (cup uc (xpow c)))) := by
          by_cases ha : 1 ≤ a
          · apply boundary_cup_cycle (boundary_xpow_u a ha)
            exact cup_cycle _ _ (dxpow b) (cup_cycle _ _ duc (dxpow c))
          by_cases hb : 1 ≤ b
          · have hmid := boundary_cup_cycle (boundary_u_xpow b hb)
              (cup uc (xpow c)) (cup_cycle _ _ duc (dxpow c))
            have hmid' := boundary_assoc_right uc (xpow b) (cup uc (xpow c)) hmid
            have hall := cycle_cup_boundary (xpow a) (dxpow a) hmid'
            exact boundary_assoc_left (xpow a) uc (cup (xpow b) (cup uc (xpow c))) hall
          · have hc : 1 ≤ c := by omega
            have hright := cycle_cup_boundary (xpow b) (dxpow b) (boundary_u_xpow c hc)
            exact cycle_cup_boundary (cup (xpow a) uc) (cup_cycle _ _ (dxpow a) duc) hright

        have boundary_add {s t : ℕ} {a b : cochains s t}
            (ha : Boundary a) (hb : Boundary b) : Boundary (a + b) := by
          obtain ⟨n, hn, x, hx⟩ := ha
          obtain ⟨m, hm, y, hy⟩ := hb
          have hmn : m = n := by omega
          subst m
          refine ⟨n, hn, x + y, ?_⟩
          rw [map_add, map_add, hx, hy]

        have boundary_smul {s t : ℕ} {a : cochains s t} (r : ZMod 2)
            (ha : Boundary a) : Boundary (r • a) := by
          obtain ⟨n, hn, x, hx⟩ := ha
          refine ⟨n, hn, r • x, ?_⟩
          rw [map_smul, map_smul, hx]

        have boundary_add_cancel {s t : ℕ} {a b : cochains s t}
            (hab : Boundary (a + b)) (hb : Boundary b) : Boundary a := by
          have h := boundary_add hab hb
          have hbb : b + b = 0 := Subtype.ext (CharTwo.add_self_eq_zero b.val)
          simpa only [add_assoc, hbb, add_zero] using h

        -- The coefficient form of kernel normal form in §1.3.
        -- It applies over any module once the V-coordinate equations are established.
        have kernel_normal_form {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
            (n : ℕ) (P Q : Fin (n + 1) → V) (a b : Fin (n + 1) → ZMod 2)
            (ha : a 0 = 0) (hb : b (Fin.last n) = 0)
            (hab : ∀ i : Fin n, a i.succ = b i.castSucc) :
            (∑ i, a i • P i) + (∑ i, b i • Q i) =
              ∑ i : Fin n, b i.castSucc • (Q i.castSucc + P i.succ) := by
          rw [Fin.sum_univ_succ (fun i => a i • P i),
            Fin.sum_univ_castSucc (fun i => b i • Q i), ha, hb]
          simp only [zero_smul, zero_add, add_zero, hab, smul_add, Finset.sum_add_distrib]
          exact add_comm _ _

        have append_exponents {s r : ℕ} (d : Fin s → ℕ →₀ ℕ) (e : Fin r → ℕ →₀ ℕ) :
            (slotExponentsEquiv (s + r)).symm (Fin.addCases d e) =
              Finsupp.mapDomain (fun a : Fin s × ℕ => (a.1.castAdd r, a.2))
                ((slotExponentsEquiv s).symm d) +
              Finsupp.mapDomain (fun a : Fin r × ℕ => (a.1.natAdd s, a.2))
                ((slotExponentsEquiv r).symm e) := by
          let fl := fun a : Fin s × ℕ => (a.1.castAdd r, a.2)
          let fr := fun a : Fin r × ℕ => (a.1.natAdd s, a.2)
          have hl : Function.Injective fl := by
            rintro ⟨i, j⟩ ⟨k, l⟩ h
            exact Prod.ext (Fin.castAdd_injective s r (congrArg Prod.fst h))
              (congrArg (fun a : Fin (s + r) × ℕ => a.2) h)
          have hr : Function.Injective fr := by
            rintro ⟨i, j⟩ ⟨k, l⟩ h
            exact Prod.ext (Fin.natAdd_injective r s (congrArg Prod.fst h))
              (congrArg (fun a : Fin (s + r) × ℕ => a.2) h)
          have hd (i : Fin s) (j : ℕ) : (slotExponentsEquiv s).symm d (i, j) = d i j := by
            have h := congrArg (fun f : Fin s → ℕ →₀ ℕ => f i j)
              ((slotExponentsEquiv s).apply_symm_apply d)
            simpa only [slotExponentsEquiv_apply] using h
          have he (i : Fin r) (j : ℕ) : (slotExponentsEquiv r).symm e (i, j) = e i j := by
            have h := congrArg (fun f : Fin r → ℕ →₀ ℕ => f i j)
              ((slotExponentsEquiv r).apply_symm_apply e)
            simpa only [slotExponentsEquiv_apply] using h
          apply (slotExponentsEquiv (s + r)).injective
          rw [Equiv.apply_symm_apply]
          funext i
          ext j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i
          · simp only [Fin.addCases_left]
            change d i j =
              Finsupp.mapDomain fl ((slotExponentsEquiv s).symm d) (fl (i, j)) +
              Finsupp.mapDomain fr ((slotExponentsEquiv r).symm e) (fl (i, j))
            have hn : fl (i, j) ∉ Set.range fr := by
              rintro ⟨⟨k, l⟩, h⟩
              have hv := congrArg (fun z : Fin (s + r) × ℕ => z.1.val) h
              have hi := i.isLt
              dsimp [fl, fr] at hv
              omega
            rw [Finsupp.mapDomain_apply hl, Finsupp.mapDomain_notin_range _ _ hn, hd, add_zero]
          · simp only [Fin.addCases_right]
            change e i j =
              Finsupp.mapDomain fl ((slotExponentsEquiv s).symm d) (fr (i, j)) +
              Finsupp.mapDomain fr ((slotExponentsEquiv r).symm e) (fr (i, j))
            have hn : fr (i, j) ∉ Set.range fl := by
              rintro ⟨⟨k, l⟩, h⟩
              have hv := congrArg (fun z : Fin (s + r) × ℕ => z.1.val) h
              have hk := k.isLt
              dsimp [fl, fr] at hv
              omega
            rw [Finsupp.mapDomain_notin_range _ _ hn, Finsupp.mapDomain_apply hr, he, zero_add]

        have cup_word_polynomial {s r : ℕ} (d : Fin s → ℕ →₀ ℕ)
            (e : Fin r → ℕ →₀ ℕ) :
            cupPolynomial (monomial ((slotExponentsEquiv s).symm d) 1)
              (monomial ((slotExponentsEquiv r).symm e) 1) =
              monomial ((slotExponentsEquiv (s + r)).symm (Fin.addCases d e)) 1 := by
          rw [cupPolynomial, rename_monomial, rename_monomial, monomial_mul, one_mul,
            append_exponents]

        -- Transfer the cobar cohomology calculations to the Adams E₂ page.

        have cohomology_stem_one_zero (n : ℕ) :
            Subsingleton (MilnorCohomology.Cohomology H M (n + 2) (n + 3)) := by
          have hz (z : MilnorCohomology.Cohomology H M (n + 2) (n + 3)) : z = 0 := by
            obtain ⟨x, rfl⟩ := (MilnorCohomology.boundariesInCycles H M (n + 2) (n + 3)).mkQ_surjective z
            apply (MilnorCohomology.classOf_eq_zero_iff H M x).mpr
            exact stem_one_surjective n x.val
          exact ⟨fun a b => (hz a).trans (hz b).symm⟩

        have e2_stem_one_zero (n : ℕ) :
            Subsingleton (E2 H SphereSpectrum ((n + 2 : ℕ) : ℤ) ((n + 3 : ℕ) : ℤ)) := by
          letI := cohomology_stem_one_zero n
          exact (MilnorCohomology.comparison H M (n + 2) (n + 3)).symm.injective.subsingleton

        have all_e2_stem_one_zero (j : ℤ) (hj : 0 ≤ j) (hj1 : j ≠ 1) :
            Subsingleton (E2 H SphereSpectrum j (1 + j)) := by
          lift j to ℕ using hj
          cases j with
          | zero =>
            letI : IsEmpty (MilnorWord 0 (1 : ℤ)) := ⟨fun d => by
              have hd := milnorWord_zero_degree d
              norm_num at hd⟩
            letI : Subsingleton (cochains 0 1) := (cochainsWordEquiv 0 1).injective.subsingleton
            letI : Subsingleton (MilnorCohomology.Cohomology H M 0 1) := inferInstance
            exact (MilnorCohomology.comparison H M 0 1).symm.injective.subsingleton
          | succ j =>
            cases j with
            | zero => exact (hj1 rfl).elim
            | succ n =>
              simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
                add_assoc, add_comm, add_left_comm] using e2_stem_one_zero n

        have cochain_stem_one_nonzero_unique (x y : cochains 1 2) (hx : x ≠ 0) (hy : y ≠ 0) :
            x = y := by
          have hf (r : ZMod 2) : r = 0 ∨ r = 1 := by fin_cases r <;> simp
          have hxe : degree_one_two_equiv x ≠ 0 :=
            fun h => hx (degree_one_two_equiv.map_eq_zero_iff.mp h)
          have hye : degree_one_two_equiv y ≠ 0 :=
            fun h => hy (degree_one_two_equiv.map_eq_zero_iff.mp h)
          apply degree_one_two_equiv.injective
          exact ((hf _).resolve_left hxe).trans ((hf _).resolve_left hye).symm

        have cohomology_stem_one_nonzero_unique
            (x y : MilnorCohomology.Cohomology H M 1 2) (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
          obtain ⟨a, rfl⟩ := (MilnorCohomology.boundariesInCycles H M 1 2).mkQ_surjective x
          obtain ⟨b, rfl⟩ := (MilnorCohomology.boundariesInCycles H M 1 2).mkQ_surjective y
          have ha : a.val ≠ 0 := by
            intro h
            have ha0 : a = 0 := Subtype.ext h
            exact hx (by rw [ha0, map_zero])
          have hb : b.val ≠ 0 := by
            intro h
            have hb0 : b = 0 := Subtype.ext h
            exact hy (by rw [hb0, map_zero])
          have hab : a = b := Subtype.ext (cochain_stem_one_nonzero_unique a.val b.val ha hb)
          exact congrArg _ hab

        have e2_stem_one_nonzero_unique (x y : E2 H SphereSpectrum 1 2)
            (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
          let e := MilnorCohomology.comparison H M 1 2
          apply e.symm.injective
          exact cohomology_stem_one_nonzero_unique _ _
            (fun h => hx (e.symm.map_eq_zero_iff.mp h))
            (fun h => hy (e.symm.map_eq_zero_iff.mp h))

        -- Express the low-stem cobar words as tensor monomials.

        let mono {s : ℕ} (d : Fin s → ℕ →₀ ℕ) : TensorPower s :=
          monomial ((slotExponentsEquiv s).symm d) 1

        have xpow_mono (a : ℕ) : (xpow a).val = mono (fun _ => Finsupp.single 0 1) := by
          dsimp only [mono]
          rw [pure_word_polynomial, xpow_val]
          simp

        have single_slot_exponents (j n : ℕ) :
            (slotExponentsEquiv 1).symm (fun _ => Finsupp.single j n) =
              Finsupp.single (0, j) n := by
          apply (slotExponentsEquiv 1).injective
          rw [Equiv.apply_symm_apply]
          funext i
          fin_cases i
          ext k
          simp [slotExponentsEquiv, Finsupp.single_apply]

        have one_slot_mono (j n : ℕ) :
            mono (fun _ : Fin 1 => Finsupp.single j n) = X (0, j) ^ n := by
          dsimp only [mono]
          rw [single_slot_exponents, ← X_pow_eq_monomial]

        have pc_mono : pc.val = mono (fun _ : Fin 1 => Finsupp.single 1 1) := by
          simp [pc, p, one_slot_mono]

        have uc_mono : uc.val = mono (fun _ : Fin 1 => Finsupp.single 0 2) := by
          simp [uc, u, one_slot_mono]

        let x3c : cochains 1 3 := qc + pc

        have x3c_mono : x3c.val = mono (fun _ : Fin 1 => Finsupp.single 0 3) := by
          simp [x3c, qc, pc, q, p, one_slot_mono, CharTwo.add_cancel_right]

        have single_letter_tuple (a b : ℕ) (letter : ℕ →₀ ℕ) :
            Fin.addCases
              (Fin.addCases (fun _ : Fin a => Finsupp.single 0 1) (fun _ : Fin 1 => letter))
              (fun _ : Fin b => Finsupp.single 0 1) =
              fun i : Fin (a + 1 + b) => if i.val = a then letter else Finsupp.single 0 1 := by
          funext i
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i
          · simp only [Fin.addCases_left]
            refine Fin.addCases (fun i => ?_) (fun i => ?_) i
            · have hi := i.isLt
              simp [Fin.addCases_left, show i.val ≠ a by omega]
            · have hi : i = 0 := Subsingleton.elim _ _
              subst i
              simp [Fin.addCases_right]
          · have hi := i.isLt
            simp [Fin.addCases_right, show a + 1 + i.val ≠ a by omega]

        -- A specified exceptional slot is exactly the cup word prescribed in §1.
        have single_letter_value {k s t : ℕ} (a b : ℕ) (w : cochains 1 k)
            (letter : ℕ →₀ ℕ) (hw : w.val = mono (fun _ : Fin 1 => letter))
            (hs : a + 1 + b = s) (ht : a + k + b = t)
            (d : Fin s → ℕ →₀ ℕ)
            (hd : ∀ i : Fin s, d i = if i.val = a then letter else Finsupp.single 0 1) :
            (reindex hs ht (cup (cup (xpow a) w) (xpow b))).val = mono d := by
          subst s
          subst t
          change cupPolynomial (cupPolynomial (xpow a).val w.val) (xpow b).val = mono d
          rw [xpow_mono, xpow_mono, hw]
          change cupPolynomial (cupPolynomial (mono _) (mono _)) (mono _) = mono d
          simp only [mono, cup_word_polynomial]
          rw [single_letter_tuple]
          congr 2
          apply congrArg (slotExponentsEquiv _).symm
          funext i
          exact (hd i).symm

        have double_letter_tuple (a b c : ℕ) :
            Fin.addCases (Fin.addCases (fun _ : Fin a => Finsupp.single 0 1)
              (fun _ : Fin 1 => Finsupp.single 0 2))
              (Fin.addCases (fun _ : Fin b => Finsupp.single 0 1)
                (Fin.addCases (fun _ : Fin 1 => Finsupp.single 0 2)
                  (fun _ : Fin c => Finsupp.single 0 1))) =
              fun i : Fin (a + 1 + (b + (1 + c))) =>
                if i.val = a ∨ i.val = a + 1 + b then Finsupp.single 0 2 else Finsupp.single 0 1 := by
          funext i
          refine Fin.addCases (fun i => ?_) (fun i => ?_) i
          · simp only [Fin.addCases_left]
            refine Fin.addCases (fun i => ?_) (fun i => ?_) i
            · have hi := i.isLt
              simp [Fin.addCases_left, show i.val ≠ a by omega, show i.val ≠ a + 1 + b by omega]
            · have hi : i = 0 := Subsingleton.elim _ _
              subst i
              simp [Fin.addCases_right]
          · simp only [Fin.addCases_right]
            refine Fin.addCases (fun i => ?_) (fun i => ?_) i
            · have hi := i.isLt
              simp [Fin.addCases_left, show a + 1 + i.val ≠ a by omega,
                show a + 1 + i.val ≠ a + 1 + b by omega, show i.val ≠ b by omega]
            · simp only [Fin.addCases_right]
              refine Fin.addCases (fun i => ?_) (fun i => ?_) i
              · have hi : i = 0 := Subsingleton.elim _ _
                subst i
                simp [Fin.addCases_left, Nat.add_assoc]
              · have hi := i.isLt
                simp [Fin.addCases_right, show a + 1 + (b + (1 + i.val)) ≠ a by omega,
                  show a + 1 + (b + (1 + i.val)) ≠ a + 1 + b by omega]

        have double_u_value {s t : ℕ} (a b c : ℕ)
            (hs : a + 1 + (b + (1 + c)) = s) (ht : a + 2 + (b + (2 + c)) = t)
            (d : Fin s → ℕ →₀ ℕ)
            (hd : ∀ i : Fin s, d i =
              if i.val = a ∨ i.val = a + 1 + b then Finsupp.single 0 2 else Finsupp.single 0 1) :
            (reindex hs ht
              (cup (cup (xpow a) uc) (cup (xpow b) (cup uc (xpow c))))).val = mono d := by
          subst s
          subst t
          change cupPolynomial (cupPolynomial (xpow a).val uc.val)
            (cupPolynomial (xpow b).val (cupPolynomial uc.val (xpow c).val)) = mono d
          rw [xpow_mono, xpow_mono, xpow_mono, uc_mono]
          simp only [mono, cup_word_polynomial]
          rw [double_letter_tuple]
          congr 2
          apply congrArg (slotExponentsEquiv _).symm
          funext i
          exact (hd i).symm

        let oneAt (s : ℕ) (i : Fin s) (w : cochains 1 3) : cochains s (s + 2) :=
          reindex (by have hi := i.isLt; omega) (by have hi := i.isLt; omega)
            (cup (cup (xpow i.val) w) (xpow (s - 1 - i.val)))

        let pAt (s : ℕ) (i : Fin s) : cochains s (s + 2) := oneAt s i pc
        let qAt (s : ℕ) (i : Fin s) : cochains s (s + 2) := oneAt s i qc

        have x3At_eq (s : ℕ) (i : Fin s) : oneAt s i x3c = qAt s i + pAt s i := by
          simp only [oneAt, x3c, qAt, pAt, cup_add_right, cup_add_left, map_add]

        let Pair (s : ℕ) := {ij : Fin s × Fin s // ij.1 < ij.2}

        let rAt (s : ℕ) (ij : Pair s) : cochains s (s + 2) :=
          reindex (by have hi := ij.val.1.isLt; have hj := ij.val.2.isLt
                      have hij := ij.property; omega)
            (by have hi := ij.val.1.isLt; have hj := ij.val.2.isLt
                have hij := ij.property; omega)
            (cup (cup (xpow ij.val.1.val) uc)
              (cup (xpow (ij.val.2.val - ij.val.1.val - 1))
                (cup uc (xpow (s - ij.val.2.val - 1)))))

        have rAt_boundary (s : ℕ) (hs : 3 ≤ s) (ij : Pair s) : Boundary (rAt s ij) := by
          apply boundary_reindex
          apply double_u_boundary
          have hi := ij.val.1.isLt
          have hj := ij.val.2.isLt
          have hij := ij.property
          omega

        let generators (s : ℕ) : Submodule (ZMod 2) (cochains s (s + 2)) :=
          Submodule.span (ZMod 2) (Set.range (pAt s) ∪ Set.range (qAt s) ∪ Set.range (rAt s))

        have pAt_mem (s : ℕ) (i : Fin s) : pAt s i ∈ generators s :=
          Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩))

        have qAt_mem (s : ℕ) (i : Fin s) : qAt s i ∈ generators s :=
          Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩))

        have rAt_mem (s : ℕ) (ij : Pair s) : rAt s ij ∈ generators s :=
          Submodule.subset_span (Or.inr ⟨ij, rfl⟩)

        have oneAt_matches {s : ℕ} (i : Fin s) (w : cochains 1 3) (letter : ℕ →₀ ℕ)
            (hw : w.val = mono (fun _ : Fin 1 => letter)) (d : Fin s → ℕ →₀ ℕ)
            (hi : d i = letter) (hrest : ∀ j, j ≠ i → d j = Finsupp.single 0 1) :
            (oneAt s i w).val = mono d := by
          apply single_letter_value _ _ _ _ hw
          intro j
          by_cases hji : j = i
          · subst j
            simp [hi]
          · have hv : j.val ≠ i.val := fun h => hji (Fin.ext h)
            simp [hv, hrest j hji]

        have rAt_matches {s : ℕ} (i j : Fin s) (hij : i < j)
            (d : Fin s → ℕ →₀ ℕ) (hi : d i = Finsupp.single 0 2)
            (hj : d j = Finsupp.single 0 2)
            (hrest : ∀ k, k ≠ i → k ≠ j → d k = Finsupp.single 0 1) :
            (rAt s ⟨(i, j), hij⟩).val = mono d := by
          apply double_u_value
          intro k
          have hij' : i.val < j.val := hij
          have he : i.val + 1 + (j.val - i.val - 1) = j.val := by omega
          rw [he]
          by_cases hki : k = i
          · subst k
            simp [hi]
          by_cases hkj : k = j
          · subst k
            simp [hj]
          · have hvi : k.val ≠ i.val := fun h => hki (Fin.ext h)
            have hvj : k.val ≠ j.val := fun h => hkj (Fin.ext h)
            simp [hvi, hvj, hrest k hki hkj]

        -- Exhaustive stem-two span: this is the P,Q,R list from Markdown §1.3.
        have generators_top (s : ℕ) : generators s = ⊤ := by
          apply top_unique
          intro w hw
          let e := cochainsWordEquiv s (s + 2)
          have hsingle (d : MilnorWord s ((s + 2 : ℕ) : ℤ)) : e.symm (Finsupp.single d 1) ∈ generators s := by
            have hd : wordDegree d.val = (s : ℤ) + 2 := by simpa using d.property.1
            let d' : MilnorWord s ((s : ℤ) + 2) := ⟨d.val, hd, d.property.2⟩
            rcases stem_two_word d' with ⟨i, hi, hrest⟩ | ⟨i, j, hij, hi, hj, hrest⟩
            · rcases hi with hi | hi
              · have heq : e.symm (Finsupp.single d 1) = oneAt s i x3c := by
                  apply Subtype.ext
                  rw [cochainsWordEquiv_symm_single_val]
                  exact (oneAt_matches i x3c _ x3c_mono d.val hi hrest).symm
                rw [heq, x3At_eq]
                exact Submodule.add_mem _ (qAt_mem s i) (pAt_mem s i)
              · have heq : e.symm (Finsupp.single d 1) = pAt s i := by
                  apply Subtype.ext
                  rw [cochainsWordEquiv_symm_single_val]
                  exact (oneAt_matches i pc _ pc_mono d.val hi hrest).symm
                rw [heq]
                exact pAt_mem s i
            · rcases lt_or_gt_of_ne hij with hij | hji
              · have heq : e.symm (Finsupp.single d 1) = rAt s ⟨(i, j), hij⟩ := by
                  apply Subtype.ext
                  rw [cochainsWordEquiv_symm_single_val]
                  exact (rAt_matches i j hij d.val hi hj hrest).symm
                rw [heq]
                exact rAt_mem s _
              · have heq : e.symm (Finsupp.single d 1) = rAt s ⟨(j, i), hji⟩ := by
                  apply Subtype.ext
                  rw [cochainsWordEquiv_symm_single_val]
                  exact (rAt_matches j i hji d.val hj hi (fun k hkj hki => hrest k hki hkj)).symm
                rw [heq]
                exact rAt_mem s _
          have hgen (z : MilnorWord s ((s + 2 : ℕ) : ℤ) →₀ ZMod 2) : e.symm z ∈ generators s := by
            induction z using Finsupp.induction_linear with
            | zero => simpa only [map_zero] using (generators s).zero_mem
            | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
            | single d r =>
              have hr := Submodule.smul_mem (generators s) r (hsingle d)
              simpa only [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one] using hr
          simpa only [LinearEquiv.symm_apply_apply] using hgen (e w)

        have differential_reindex {s s' t t' : ℕ} (hs : s = s') (ht : t = t')
            (w : cochains s t) :
            differential s' t' (reindex hs ht w) =
              reindex (congrArg (fun n => n + 1) hs) ht (differential s t w) := by
          subst s'
          subst t'
          rfl

        have two_x_value (a b : ℕ) :
            cup (cup (xpow a) (cup xc xc)) (xpow b) = xpow (a + 2 + b) := by
          have hxx : cup xc xc = xpow 2 := by
            calc
              cup xc xc = cup (xpow 1) (xpow 1) := by rw [xpow_one]
              _ = xpow 2 := xpow_cup 1 1
          rw [hxx, xpow_cup a 2, xpow_cup (a + 2) b]

        have two_u_left_val (a b : ℕ) :
            (cup (cup (xpow a) (cup uc xc)) (xpow b)).val =
              (xpow (a + 2 + b)).val * X ((⟨a, by omega⟩ : Fin (a + 2 + b)), 0) := by
          rw [← two_x_value a b]
          change cupPolynomial (cupPolynomial (xpow a).val (cupPolynomial uc.val xc.val)) (xpow b).val =
            cupPolynomial (cupPolynomial (xpow a).val (cupPolynomial xc.val xc.val)) (xpow b).val * _
          simp only [cupPolynomial, uc, xc, u, x, map_mul, map_pow, rename_X]
          have hi : (((0 : Fin 1).castAdd 1).natAdd a).castAdd b =
              (⟨a, by omega⟩ : Fin (a + 2 + b)) := Fin.ext (by simp)
          rw [hi]
          ring

        have two_u_right_val (a b : ℕ) :
            (cup (cup (xpow a) (cup xc uc)) (xpow b)).val =
              (xpow (a + 2 + b)).val * X ((⟨a + 1, by omega⟩ : Fin (a + 2 + b)), 0) := by
          rw [← two_x_value a b]
          change cupPolynomial (cupPolynomial (xpow a).val (cupPolynomial xc.val uc.val)) (xpow b).val =
            cupPolynomial (cupPolynomial (xpow a).val (cupPolynomial xc.val xc.val)) (xpow b).val * _
          simp only [cupPolynomial, uc, xc, u, x, map_mul, map_pow, rename_X]
          have hi : (((0 : Fin 1).natAdd 1).natAdd a).castAdd b =
              (⟨a + 1, by omega⟩ : Fin (a + 2 + b)) := Fin.ext (by simp)
          rw [hi]
          ring

        let wordNat (s : ℕ) (i : Fin s) : MilnorWord s ((s + 1 : ℕ) : ℤ) :=
          ⟨(stemOneWord s i).val, by
            constructor
            · simpa only [Nat.cast_add, Nat.cast_one] using (stemOneWord s i).property.1
            · exact (stemOneWord s i).property.2⟩

        have wordNat_bijective (s : ℕ) : Function.Bijective (wordNat s) := by
          constructor
          · intro i j hij
            apply stemOneWord_injective s
            exact Subtype.ext (congrArg Subtype.val hij)
          · intro d
            let d' : MilnorWord s ((s : ℤ) + 1) :=
              ⟨d.val, by simpa only [Nat.cast_add, Nat.cast_one] using d.property.1, d.property.2⟩
            obtain ⟨i, hi⟩ := stemOneWord_surjective s d'
            exact ⟨i, Subtype.ext (congrArg Subtype.val hi)⟩

        let wordNatEquiv (s : ℕ) : Fin s ≃ MilnorWord s ((s + 1 : ℕ) : ℤ) :=
          Equiv.ofBijective (wordNat s) (wordNat_bijective s)

        let vAt (s : ℕ) (i : Fin (s + 1)) : cochains (s + 1) (s + 2) :=
          (cochainsWordEquiv (s + 1) (s + 2)).symm (Finsupp.single (wordNat (s + 1) i) 1)

        have vAt_val (s : ℕ) (i : Fin (s + 1)) :
            (vAt s i).val = (xpow (s + 1)).val * X (i, 0) := by
          dsimp only [vAt]
          rw [cochainsWordEquiv_symm_single_val]
          exact unique_u_polynomial i

        let vEquiv (s : ℕ) :
            (Fin (s + 1) →₀ ZMod 2) ≃ₗ[ZMod 2] cochains (s + 1) (s + 2) :=
          (Finsupp.domLCongr (R := ZMod 2) (wordNatEquiv (s + 1))).trans
            (cochainsWordEquiv (s + 1) (s + 2)).symm

        have vEquiv_single (s : ℕ) (i : Fin (s + 1)) :
            vEquiv s (Finsupp.single i 1) = vAt s i := by
          simp [vEquiv, vAt, Finsupp.domLCongr, wordNatEquiv]
          rfl

        have dpAt (s : ℕ) (i : Fin s) :
            differential s (s + 2) (pAt s i) = vAt s i.castSucc := by
          unfold pAt oneAt
          rw [differential_reindex, differential_sandwich, dpc, reindex_trans]
          apply Subtype.ext
          rw [reindex_unique_u_val _ _ _ _ (two_u_left_val i.val (s - 1 - i.val)), vAt_val]
          congr 2

        have dqAt (s : ℕ) (i : Fin s) :
            differential s (s + 2) (qAt s i) = vAt s i.succ := by
          unfold qAt oneAt
          rw [differential_reindex, differential_sandwich, dqc, reindex_trans]
          apply Subtype.ext
          rw [reindex_unique_u_val _ _ _ _ (two_u_right_val i.val (s - 1 - i.val)), vAt_val]
          congr 2

        have drAt (s : ℕ) (ij : Pair s) : differential s (s + 2) (rAt s ij) = 0 := by
          unfold rAt
          rw [differential_reindex]
          have hc := cup_cycle (cup (xpow ij.val.1.val) uc)
            (cup (xpow (ij.val.2.val - ij.val.1.val - 1))
              (cup uc (xpow (s - ij.val.2.val - 1))))
            (cup_cycle _ _ (dxpow _) duc)
            (cup_cycle _ _ (dxpow _) (cup_cycle _ _ duc (dxpow _)))
          rw [hc, map_zero]

        have cup_reindex_right {s s' t t' n m : ℕ} (hs : s = s') (ht : t = t')
            (a : cochains n m) (b : cochains s t) :
            cup a (reindex hs ht b) = reindex (by omega) (by omega) (cup a b) := by
          subst s'
          subst t'
          rfl

        have sandwich_suffix_x {k : ℕ} (a b : ℕ) (w : cochains 1 k) :
            reindex (by omega) (by omega) (cup (cup (xpow a) (cup w xc)) (xpow b)) =
              cup (cup (xpow a) w) (xpow (1 + b)) := by
          rw [← cup_assoc (xpow a) w xc, cup_reindex_left, reindex_trans,
            cup_assoc, ← xpow_one, xpow_cup]

        have sandwich_prefix_x {k : ℕ} (a b : ℕ) (w : cochains 1 k) :
            reindex (by omega) (by omega) (cup (cup (xpow a) (cup xc w)) (xpow b)) =
              cup (cup (xpow (a + 1)) w) (xpow b) := by
          rw [← cup_assoc (xpow a) xc w, cup_reindex_left, reindex_trans]
          rfl

        have sandwich_uu (a b : ℕ) :
            reindex (by omega) (by omega) (cup (cup (xpow a) (cup uc uc)) (xpow b)) =
              cup (cup (xpow a) uc) (cup uc (xpow b)) := by
          rw [← cup_assoc (xpow a) uc uc, cup_reindex_left, reindex_trans, cup_assoc]

        have blockRename_zero {s : ℕ} (w : TensorPower s) :
            blockRename (n := s) 0 (by omega) w = w := by
          have hf : (fun a : Fin s × ℕ =>
              ((⟨0 + a.1.val, by have hi := a.1.isLt; omega⟩ : Fin s), a.2)) = id := by
            funext a
            apply Prod.ext
            · exact Fin.ext (by simp)
            · rfl
          simp only [blockRename, hf, rename_id]
          rfl

        have cup_xpow_zero {s t : ℕ} (w : cochains s t) :
            reindex (Nat.zero_add s) (Nat.zero_add t) (cup (xpow 0) w) = w := by
          apply Subtype.ext
          rw [reindex_cup_val_general]
          simp only [xpow, Nat.rec_zero, Subtype.coe_mk, map_one, one_mul, blockRename_zero]

        have cup_xpow_zero' {s t : ℕ} (w : cochains s t) :
            cup (xpow 0) w = reindex (Nat.zero_add s).symm (Nat.zero_add t).symm w := by
          apply (reindex (Nat.zero_add s) (Nat.zero_add t)).injective
          simpa only [reindex_trans, reindex_rfl] using cup_xpow_zero w

        -- Explicit transports keep all degree-dependent instances fixed while replacing lengths.
        have reindex_tail_congr {s t : ℕ} (a k b b' : ℕ) (w : cochains 1 k)
            (hb : b = b') (hs : a + 1 + b = s) (ht : a + k + b = t)
            (hs' : a + 1 + b' = s) (ht' : a + k + b' = t) :
            reindex hs ht (cup (cup (xpow a) w) (xpow b)) =
              reindex hs' ht' (cup (cup (xpow a) w) (xpow b')) := by
          subst b'
          rfl

        have reindex_double_u_congr {s t : ℕ} (a b b' c c' : ℕ)
            (hb : b = b') (hc : c = c')
            (hs : a + 1 + (b + (1 + c)) = s) (ht : a + 2 + (b + (2 + c)) = t)
            (hs' : a + 1 + (b' + (1 + c')) = s) (ht' : a + 2 + (b' + (2 + c')) = t) :
            reindex hs ht (cup (cup (xpow a) uc) (cup (xpow b) (cup uc (xpow c)))) =
              reindex hs' ht' (cup (cup (xpow a) uc) (cup (xpow b') (cup uc (xpow c')))) := by
          subst b'
          subst c'
          rfl

        have t_relation (a b : ℕ) :
            Boundary (qAt (a + b + 2) ⟨a, by omega⟩ +
              pAt (a + b + 2) ⟨a + 1, by omega⟩ +
              rAt (a + b + 2) ⟨(⟨a, by omega⟩, ⟨a + 1, by omega⟩), by
                change a < a + 1
                omega⟩) := by
          let s := a + b + 2
          let i : Fin s := ⟨a, by dsimp [s]; omega⟩
          let j : Fin s := ⟨a + 1, by dsimp [s]; omega⟩
          let e : cochains (a + 2 + b) (a + 4 + b) ≃ₗ[ZMod 2] cochains s (s + 2) :=
            reindex (by dsimp [s]; omega) (by dsimp [s]; omega)
          let qraw := cup (cup (xpow a) (cup qc xc)) (xpow b)
          let rraw := cup (cup (xpow a) (cup uc uc)) (xpow b)
          let praw := cup (cup (xpow a) (cup xc pc)) (xpow b)
          have hb : Boundary (qraw + rraw + praw) := by
            refine ⟨a + 1 + b, by omega, cup (cup (xpow a) tc) (xpow b), ?_⟩
            simp only [t_boundary, cup_add_right, cup_add_left, map_add,
              reindex_trans, reindex_rfl]
            rfl
          have heq : e qraw = qAt s i := by
            let f : cochains (a + 1 + (1 + b)) (a + 3 + (1 + b)) ≃ₗ[ZMod 2]
                cochains s (s + 2) := reindex (by dsimp [s]; omega) (by dsimp [s]; omega)
            have hn : e qraw = f (cup (cup (xpow a) qc) (xpow (1 + b))) := by
              simpa only [e, qraw, f, reindex_trans] using congrArg f (sandwich_suffix_x a b qc)
            exact hn.trans (reindex_tail_congr a 3 (1 + b) (s - 1 - a) qc
              (by dsimp [s]; omega) _ _ _ _)
          have hep : e praw = pAt s j := by
            let f : cochains (a + 1 + 1 + b) (a + 1 + 3 + b) ≃ₗ[ZMod 2]
                cochains s (s + 2) := reindex (by dsimp [s]; omega) (by dsimp [s]; omega)
            have hn : e praw = f (cup (cup (xpow (a + 1)) pc) (xpow b)) := by
              simpa only [e, praw, f, reindex_trans] using congrArg f (sandwich_prefix_x a b pc)
            exact hn.trans (reindex_tail_congr (a + 1) 3 b (s - 1 - (a + 1)) pc
              (by dsimp [s]; omega) _ _ _ _)
          have her : e rraw = rAt s ⟨(i, j), by change a < a + 1; omega⟩ := by
            let f : cochains (a + 1 + (0 + (1 + b))) (a + 2 + (0 + (2 + b))) ≃ₗ[ZMod 2]
                cochains s (s + 2) := reindex (by dsimp [s]; omega) (by dsimp [s]; omega)
            have hn : e rraw = f (cup (cup (xpow a) uc) (cup (xpow 0) (cup uc (xpow b)))) := by
              dsimp [e, rraw, f]
              rw [cup_xpow_zero', cup_reindex_right, reindex_trans,
                ← sandwich_uu a b, reindex_trans]
            exact hn.trans (reindex_double_u_congr a 0 (a + 1 - a - 1) b (s - (a + 1) - 1)
              (by omega) (by dsimp [s]; omega) _ _ _ _)
          have hh := boundary_reindex (show a + 2 + b = s by dsimp [s]; omega)
            (show a + 4 + b = s + 2 by dsimp [s]; omega) hb
          change Boundary (e (qraw + rraw + praw)) at hh
          rw [map_add, map_add, heq, her, hep] at hh
          convert hh using 1 <;> abel

        have t_adjacent (n : ℕ) (i : Fin (n + 1)) :
            Boundary (qAt (n + 2) i.castSucc + pAt (n + 2) i.succ +
              rAt (n + 2) ⟨(i.castSucc, i.succ), by
                change i.val < i.val + 1
                omega⟩) := by
          rcases i with ⟨a, ha⟩
          obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (show a ≤ n by omega)
          exact t_relation a b

        /- The P/Q differential has consecutive coordinate columns. Modulo a
        submodule containing every adjacent relation and every R generator, the
        quotient map factors through that differential. Hence it kills MilnorCohomology.cycles. -/
        have ker_le_of_consecutive_generators
            {M : Type} {N : Type} {ι : Type}
            [AddCommGroup M] [Module (ZMod 2) M]
            [AddCommGroup N] [Module (ZMod 2) N]
            (n : ℕ) (d : M →ₗ[ZMod 2] N)
            (P Q : Fin (n + 1) → M) (R : ι → M)
            (e : (Fin (n + 2) →₀ ZMod 2) ≃ₗ[ZMod 2] N)
            (hgen : Submodule.span (ZMod 2)
              (Set.range P ∪ Set.range Q ∪ Set.range R) = ⊤)
            (hP : ∀ i, d (P i) = e (Finsupp.single i.castSucc 1))
            (hQ : ∀ i, d (Q i) = e (Finsupp.single i.succ 1))
            (hR : ∀ i, d (R i) = 0)
            (B : Submodule (ZMod 2) M)
            (hBR : ∀ i, R i ∈ B)
            (hBE : ∀ i : Fin n, Q i.castSucc + P i.succ ∈ B) :
            LinearMap.ker d ≤ B := by
          classical
          have hdouble (x : M ⧸ B) : x + x = 0 := by
            simpa only [add_smul, one_smul] using
              (show ((1 : ZMod 2) + 1) • x = 0 by
                rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul])
          have hPQ (i : Fin n) : B.mkQ (Q i.castSucc) = B.mkQ (P i.succ) := by
            have hz : B.mkQ (Q i.castSucc) + B.mkQ (P i.succ) = 0 := by
              rw [← map_add]
              exact (Submodule.Quotient.mk_eq_zero B).mpr (hBE i)
            calc
              B.mkQ (Q i.castSucc) =
                  (B.mkQ (Q i.castSucc) + B.mkQ (P i.succ)) + B.mkQ (P i.succ) := by
                rw [add_assoc, hdouble, add_zero]
              _ = B.mkQ (P i.succ) := by rw [hz, zero_add]
          let representatives : Fin (n + 2) → M ⧸ B :=
            Fin.cases (B.mkQ (P 0)) (fun i => B.mkQ (Q i))
          let L : N →ₗ[ZMod 2] M ⧸ B :=
            (Finsupp.linearCombination (ZMod 2) representatives).comp e.symm.toLinearMap
          have hLP (i : Fin (n + 1)) : L (d (P i)) = B.mkQ (P i) := by
            rw [hP]
            simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe,
              LinearEquiv.symm_apply_apply, Finsupp.linearCombination_single, one_smul]
            refine Fin.cases ?_ (fun j => ?_) i
            · rfl
            · change B.mkQ (Q j.castSucc) = B.mkQ (P j.succ)
              exact hPQ j
          have hLQ (i : Fin (n + 1)) : L (d (Q i)) = B.mkQ (Q i) := by
            rw [hQ]
            simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe,
              LinearEquiv.symm_apply_apply, Finsupp.linearCombination_single, one_smul]
            rfl
          have hLR (i : ι) : L (d (R i)) = B.mkQ (R i) := by
            rw [hR, map_zero]
            exact ((Submodule.Quotient.mk_eq_zero B).mpr (hBR i)).symm
          have hfactor : L.comp d = B.mkQ := by
            apply LinearMap.ext_on hgen
            rintro x ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
            · exact hLP i
            · exact hLQ i
            · exact hLR i
          intro x hx
          apply (Submodule.Quotient.mk_eq_zero B).mp
          change B.mkQ x = 0
          rw [← hfactor, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]

        /- Markdown §1.3: the kernel is generated modulo MilnorCohomology.boundaries by the R words. -/
        have cycles_le_boundaries_sup_r (n : ℕ) :
            MilnorCohomology.cycles (n + 1) (n + 3) ≤ MilnorCohomology.boundaries (n + 1) (n + 3) ⊔
              Submodule.span (ZMod 2) (Set.range (rAt (n + 1))) := by
          let B := MilnorCohomology.boundaries (n + 1) (n + 3) ⊔
            Submodule.span (ZMod 2) (Set.range (rAt (n + 1)))
          change LinearMap.ker (differential (n + 1) (n + 3)) ≤ B
          apply ker_le_of_consecutive_generators n
            (differential (n + 1) (n + 3)) (pAt (n + 1)) (qAt (n + 1)) (rAt (n + 1))
            (vEquiv (n + 1)) (generators_top (n + 1))
          · intro i
            rw [dpAt, vEquiv_single]
          · intro i
            rw [dqAt, vEquiv_single]
          · exact drAt (n + 1)
          · intro i
            exact (show Submodule.span (ZMod 2) (Set.range (rAt (n + 1))) ≤ B from
              le_sup_right) (Submodule.subset_span ⟨i, rfl⟩)
          · intro i
            cases n with
            | zero => exact Fin.elim0 i
            | succ n =>
              let ij : Pair (n + 2) := ⟨(i.castSucc, i.succ), by
                change i.val < i.val + 1
                omega⟩
              have ht : qAt (n + 2) i.castSucc + pAt (n + 2) i.succ + rAt (n + 2) ij ∈ B :=
                (show MilnorCohomology.boundaries (n + 2) (n + 4) ≤ B from le_sup_left)
                  (boundary_mem_range (t_adjacent n i))
              have hr : rAt (n + 2) ij ∈ B :=
                (show Submodule.span (ZMod 2) (Set.range (rAt (n + 2))) ≤ B from
                  le_sup_right) (Submodule.subset_span ⟨ij, rfl⟩)
              have hh := B.add_mem ht hr
              have hrr : rAt (n + 2) ij + rAt (n + 2) ij = 0 :=
                Subtype.ext (CharTwo.add_self_eq_zero _)
              simpa only [add_assoc, hrr, add_zero] using hh

        /- In filtration one there is no R word at all. -/
        have cycles_one_le_boundaries : MilnorCohomology.cycles 1 3 ≤ MilnorCohomology.boundaries 1 3 := by
          have hr : Submodule.span (ZMod 2) (Set.range (rAt 1)) ≤ MilnorCohomology.boundaries 1 3 := by
            apply Submodule.span_le.mpr
            rintro z ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
            have hi := i.isLt
            have hj := j.isLt
            change i.val < j.val at hij
            omega
          exact (cycles_le_boundaries_sup_r 0).trans (sup_le le_rfl hr)

        /- For every filtration at least three, each R word is an actual boundary. -/
        have cycles_high_le_boundaries (n : ℕ) :
            MilnorCohomology.cycles (n + 3) (n + 5) ≤ MilnorCohomology.boundaries (n + 3) (n + 5) := by
          have hr : Submodule.span (ZMod 2) (Set.range (rAt (n + 3))) ≤
              MilnorCohomology.boundaries (n + 3) (n + 5) := by
            apply Submodule.span_le.mpr
            rintro z ⟨i, rfl⟩
            exact boundary_mem_range (rAt_boundary (n + 3) (by omega) i)
          exact (cycles_le_boundaries_sup_r (n + 2)).trans (sup_le le_rfl hr)

        /- In filtration two, the R words form a singleton, namely the ordered
        pair of slots (0,1). This retains the actual UU representative. -/
        have r_two_span_le_singleton :
            Submodule.span (ZMod 2) (Set.range (rAt 2)) ≤
              Submodule.span (ZMod 2) {rAt 2 ⟨(0, 1), by decide⟩} := by
          apply Submodule.span_le.mpr
          rintro z ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
          have hi : i = 0 := Fin.ext (by
            have hi := i.isLt
            have hj := j.isLt
            change i.val < j.val at hij
            omega)
          have hj : j = 1 := Fin.ext (by
            have hi := i.isLt
            have hj := j.isLt
            change i.val < j.val at hij
            omega)
          subst i
          subst j
          exact Submodule.mem_span_singleton_self _

        have cohomology_stem_two_one_zero : Subsingleton (MilnorCohomology.Cohomology H M 1 3) := by
          have hz (z : MilnorCohomology.Cohomology H M 1 3) : z = 0 := by
            obtain ⟨x, rfl⟩ := (MilnorCohomology.boundariesInCycles H M 1 3).mkQ_surjective z
            exact (MilnorCohomology.classOf_eq_zero_iff H M x).mpr (cycles_one_le_boundaries x.property)
          exact ⟨fun a b => (hz a).trans (hz b).symm⟩

        have cohomology_stem_two_high_zero (n : ℕ) :
            Subsingleton (MilnorCohomology.Cohomology H M (n + 3) (n + 5)) := by
          have hz (z : MilnorCohomology.Cohomology H M (n + 3) (n + 5)) : z = 0 := by
            obtain ⟨x, rfl⟩ := (MilnorCohomology.boundariesInCycles H M (n + 3) (n + 5)).mkQ_surjective z
            exact (MilnorCohomology.classOf_eq_zero_iff H M x).mpr (cycles_high_le_boundaries n x.property)
          exact ⟨fun a b => (hz a).trans (hz b).symm⟩

        have all_e2_stem_two_zero (j : ℤ) (hj : 0 ≤ j) (hj2 : j ≠ 2) :
            Subsingleton (E2 H SphereSpectrum j (2 + j)) := by
          lift j to ℕ using hj
          cases j with
          | zero =>
            letI : IsEmpty (MilnorWord 0 (2 : ℤ)) := ⟨fun d => by
              have hd := milnorWord_zero_degree d
              norm_num at hd⟩
            letI : Subsingleton (cochains 0 2) := (cochainsWordEquiv 0 2).injective.subsingleton
            letI : Subsingleton (MilnorCohomology.Cohomology H M 0 2) := inferInstance
            exact (MilnorCohomology.comparison H M 0 2).symm.injective.subsingleton
          | succ j =>
            cases j with
            | zero =>
              letI := cohomology_stem_two_one_zero
              exact (MilnorCohomology.comparison H M 1 3).symm.injective.subsingleton
            | succ j =>
              cases j with
              | zero => exact (hj2 rfl).elim
              | succ n =>
                letI := cohomology_stem_two_high_zero n
                change Subsingleton (E2 H SphereSpectrum ((n + 3 : ℕ) : ℤ)
                  (2 + ((n + 3 : ℕ) : ℤ)))
                have ht : (2 : ℤ) + ((n + 3 : ℕ) : ℤ) = ((n + 5 : ℕ) : ℤ) := by omega
                rw [ht]
                exact (MilnorCohomology.comparison H M (n + 3) (n + 5)).symm.injective.subsingleton

        /- Every diagonal class is either zero or the class of this particular UU
        word. No nonvanishing assertion is smuggled into the size bound. -/
        have cohomology_stem_two_nonzero_unique
            (x y : MilnorCohomology.Cohomology H M 2 4) (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
          let ij : Pair 2 := ⟨(0, 1), by decide⟩
          let r : MilnorCohomology.cycles 2 4 := ⟨rAt 2 ij, drAt 2 ij⟩
          have hcyc : MilnorCohomology.cycles 2 4 ≤ MilnorCohomology.boundaries 2 4 ⊔
              Submodule.span (ZMod 2) {r.val} :=
            (cycles_le_boundaries_sup_r 1).trans (sup_le_sup_left r_two_span_le_singleton _)
          have classify (z : MilnorCohomology.Cohomology H M 2 4) : z = 0 ∨ z = MilnorCohomology.classOf H M 2 4 r := by
            obtain ⟨a, rfl⟩ := (MilnorCohomology.boundariesInCycles H M 2 4).mkQ_surjective z
            change MilnorCohomology.classOf H M 2 4 a = 0 ∨ MilnorCohomology.classOf H M 2 4 a = MilnorCohomology.classOf H M 2 4 r
            obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp (hcyc a.property)
            obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hc
            have ha : a.val - k • r.val ∈ MilnorCohomology.boundaries 2 4 := by
              rw [← hbc, ← hk, add_sub_cancel_right]
              exact hb
            have he : MilnorCohomology.classOf H M 2 4 a = k • MilnorCohomology.classOf H M 2 4 r := by
              rw [← map_smul]
              exact (MilnorCohomology.classOf_eq_iff H M a (k • r)).mpr ha
            have hk01 : k = 0 ∨ k = 1 := by fin_cases k <;> simp
            rcases hk01 with rfl | rfl
            · left
              simpa only [zero_smul] using he
            · right
              simpa only [one_smul] using he
          exact ((classify x).resolve_left hx).trans ((classify y).resolve_left hy).symm

        have e2_stem_two_nonzero_unique (x y : E2 H SphereSpectrum 2 4)
            (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
          let e := MilnorCohomology.comparison H M 2 4
          apply e.symm.injective
          exact cohomology_stem_two_nonzero_unique _ _
            (fun h => hx (e.symm.map_eq_zero_iff.mp h))
            (fun h => hy (e.symm.map_eq_zero_iff.mp h))

        -- Concentration of E₂ in one filtration, with at most one nonzero
        -- class there, implies at most one nonzero class in the corresponding
        -- sphere homotopy group.
        have low_e2_to_small_homotopy (m : ℕ)
            (em : adamsComparison.nu.functor.obj (Sphere (m : ℤ)) ≅
              Smn (Syn := KIP126.Def.standardSyntheticContext.Syn) m m)
            (hvan : ∀ j : ℤ, 0 ≤ j → j ≠ (m : ℤ) →
              Subsingleton (E2 KIP126.Def.standardHF2AdamsContext.stableContext.hf2
                SphereSpectrum j ((m : ℤ) + j)))
            (hsmall : ∀ a b : E2 KIP126.Def.standardHF2AdamsContext.stableContext.hf2
                SphereSpectrum m ((m : ℤ) + m),
              a ≠ 0 → b ≠ 0 → a = b) :
            ∀ a b : HomotopyGroup (m : ℤ)
              (SphereSpectrum (C := KIP126.Classical.Adams.standardFoundation.Spectrum)),
              a ≠ 0 → b ≠ 0 → a = b := by
          classical
          let Syn := KIP126.Def.standardSyntheticContext.Syn
          let H := KIP126.Def.standardHF2AdamsContext.stableContext.hf2
          let D := adamsComparison
          let unit := nuCoefficientUnit H.unit D.nu
          let F := towerFiltration unit (S_0_0 : Syn)
          -- §5.3: a zero initial page forces every infinite-cycle class to vanish.
          have inf_zero (T : SSData (ModuleCat ℤ)) (hT : Subsingleton (T.page 0)) :
              IsZero T.eInfty := by
            letI := hT
            haveI : Epi (T.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
            haveI : Subsingleton T.eInfty := by
              refine ⟨fun a b => ?_⟩
              obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (T.pageπ ⊤)).mp inferInstance a
              obtain ⟨z', rfl⟩ := (ModuleCat.epi_iff_surjective (T.pageπ ⊤)).mp inferInstance b
              exact T.infinity_projection_eq_of_page_projection_eq 0 z z' (Subsingleton.elim _ _)
            exact ModuleCat.isZero_of_subsingleton _
          have inf_small (T : SSData (ModuleCat ℤ))
              (hT : ∀ a b : T.page 0, a ≠ 0 → b ≠ 0 → a = b) :
              ∀ a b : T.eInfty, a ≠ 0 → b ≠ 0 → a = b := by
            haveI : Epi (T.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
            intro a b ha hb
            obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (T.pageπ ⊤)).mp inferInstance a
            obtain ⟨z', hz'⟩ := (ModuleCat.epi_iff_surjective (T.pageπ ⊤)).mp inferInstance b
            let q := Subobject.ofLE _ _ (T.Z_anti (show (0 : WithTop ℕ) ≤ ⊤ from le_top)) ≫
              T.pageπ 0
            have hqz : q z ≠ 0 := by
              intro hq
              apply ha
              rw [← hz]
              have he := T.infinity_projection_eq_of_page_projection_eq 0 z 0
                (by simpa only [map_zero] using hq)
              simpa only [map_zero] using he
            have hqz' : q z' ≠ 0 := by
              intro hq
              apply hb
              rw [← hz']
              have he := T.infinity_projection_eq_of_page_projection_eq 0 z' 0
                (by simpa only [map_zero] using hq)
              simpa only [map_zero] using he
            rw [← hz, ← hz']
            exact T.infinity_projection_eq_of_page_projection_eq 0 z z'
              (hT (q z) (q z') hqz hqz')
          -- §5.2: choose k=j.toNat, so all nonnegative filtrations get weight m.
          have vanish_inf (j : ℤ) (hj : 0 ≤ j) (hjm : j ≠ (m : ℤ)) :
              IsZero ((D.family.sphere.sequence.ssData (j, (m : ℤ) + j, m)).eInfty) := by
            have hk : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
            let e : E2 H SphereSpectrum j ((m : ℤ) + j) ≃ₗ[ℤ]
                D.family.sphere.E₂ (j, (m : ℤ) + j, m) := by
              have he := D.sphereE2 j ((m : ℤ) + j) j.toNat
              have ht : (m : ℤ) + j - (j.toNat : ℤ) = m := by omega
              rw [ht] at he
              exact he
            letI := hvan j hj hjm
            have hs : Subsingleton (D.family.sphere.E₂ (j, (m : ℤ) + j, m)) :=
              e.symm.injective.subsingleton
            exact inf_zero _ hs
          have small_inf :
              ∀ a b : (D.family.sphere.sequence.ssData (m, (m : ℤ) + m, m)).eInfty,
                a ≠ 0 → b ≠ 0 → a = b := by
            apply inf_small
            let e : E2 H SphereSpectrum m ((m : ℤ) + m) ≃ₗ[ℤ]
                D.family.sphere.E₂ (m, (m : ℤ) + m, m) := by
              have he := D.sphereE2 m ((m : ℤ) + m) m
              rw [add_sub_cancel_right] at he
              exact he
            intro a b ha hb
            apply e.symm.injective
            apply hsmall
            · intro hz
              apply ha
              apply e.symm.injective
              simpa only [map_zero] using hz
            · intro hz
              apply hb
              apply e.symm.injective
              simpa only [map_zero] using hz
          -- §§5.4.1–5.4.3: the actual stage-zero tower map is the identity.
          have all_in_m (a : BiHom (m : ℤ) m (S_0_0 : Syn)) :
              FiltrationAtLeast unit m a := by
            apply (D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
              0 m m m (by omega) (fun j hj hjm => vanish_inf j hj (by omega)) a).mp
            refine ⟨a, ?_⟩
            change a ≫ adamsTowerMap unit (S_0_0 : Syn) 0 0 _ = a
            rw [adamsTowerMap_self]
            change a ≫ 𝟙 (S_0_0 : Syn) = a
            exact Category.comp_id a
          -- §5.4.4: use precisely the supplied synthetic homotopy separation.
          have tail_zero (a : BiHom (m : ℤ) m (S_0_0 : Syn))
              (ha : FiltrationAtLeast unit ((m : ℤ) + 1) a) : a = 0 := by
            apply D.sphereConvergence.eq_zero_of_eInfty_isZero_ge
              (m + 1) m m (D.homotopySeparated .sphere m m)
              (fun j hj => vanish_inf j (by omega) (by omega)) a
            simpa only [Nat.cast_add, Nat.cast_one] using ha
          let eg : (D.family.sphere.sequence.ssData (m, (m : ℤ) + m, m)).eInfty ≅
              F.associatedGraded m (m, m) := by
            simpa only [add_sub_cancel_right, SyntheticObject.obj,
              SyntheticAdamsFamily.sphere, F, unit, H] using
              D.sphereConvergence.identification (m, (m : ℤ) + m, m)
          have small_graded (a b : F.associatedGraded m (m, m))
              (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
            apply eg.symm.toLinearEquiv.injective
            apply small_inf
            · intro hz
              apply ha
              apply eg.symm.toLinearEquiv.injective
              simpa only [map_zero] using hz
            · intro hz
              apply hb
              apply eg.symm.toLinearEquiv.injective
              simpa only [map_zero] using hz
          -- §5.4.5: quotient projection is injective because its kernel is F^(m+1).
          have graded_kernel (z : (Subobject.underlying.obj (F.F m (m, m)) : ModuleCat ℤ))
              (hz : F.toAssociatedGraded m (m, m) z = 0) :
              (F.F m (m, m)).arrow z = 0 := by
            apply tail_zero
            have hb := (subobject_cokernel_π_eq_zero_iff
              (F.F ((m : ℤ) + 1) (m, m)) (F.F m (m, m)) (F.mono m (m, m)) z).mp hz
            simpa only [F, towerFiltration, FiltrationAtLeast,
              OrderIso.apply_symm_apply] using hb
          have lift_to_m (a : BiHom (m : ℤ) m (S_0_0 : Syn)) :
              ∃ z : (Subobject.underlying.obj (F.F m (m, m)) : ModuleCat ℤ),
                (F.F m (m, m)).arrow z = a := by
            have hm : a ∈ (ModuleCat.subobjectModule (syntheticHomotopy (S_0_0 : Syn) (m,m)))
                (F.F m (m,m)) := by
              simpa only [F, towerFiltration, FiltrationAtLeast,
                OrderIso.apply_symm_apply] using all_in_m a
            exact hm
          have small_synthetic (a b : BiHom (m : ℤ) m (S_0_0 : Syn))
              (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
            obtain ⟨za, hza⟩ := lift_to_m a
            obtain ⟨zb, hzb⟩ := lift_to_m b
            have hga : F.toAssociatedGraded m (m, m) za ≠ 0 := by
              intro hz
              exact ha (hza.symm.trans (graded_kernel za hz))
            have hgb : F.toAssociatedGraded m (m, m) zb ≠ 0 := by
              intro hz
              exact hb (hzb.symm.trans (graded_kernel zb hz))
            have hab := small_graded _ _ hga hgb
            have hk := graded_kernel (za - zb) (by rw [map_sub, hab, sub_self])
            apply sub_eq_zero.mp
            simpa only [map_sub, hza, hzb] using hk
          -- §5.5.2: ν is faithful via its specified realization left inverse.
          letI := D.nu.additive
          letI := D.recovery.nu_faithful
          let I (a : HomotopyGroup (m : ℤ) SphereSpectrum) : BiHom (m : ℤ) m (S_0_0 : Syn) :=
            em.inv ≫ D.nu.functor.map a ≫ D.nu.unitIso.hom
          have inj : Function.Injective I := by
            intro a b hab
            apply D.nu.functor.map_injective
            apply (cancel_epi em.inv).mp
            apply (cancel_mono D.nu.unitIso.hom).mp
            simpa only [I, Category.assoc] using hab
          have izero : I 0 = 0 := by
            simp only [I, Functor.map_zero, zero_comp, comp_zero]
          intro a b ha hb
          apply inj
          apply small_synthetic
          · intro hz
            exact ha (inj (hz.trans izero.symm))
          · intro hz
            exact hb (inj (hz.trans izero.symm))
        exact ⟨low_e2_to_small_homotopy 1 (nuSphereOne adamsComparison)
            all_e2_stem_one_zero e2_stem_one_nonzero_unique,
          low_e2_to_small_homotopy 2 (nuSphereTwo adamsComparison)
            all_e2_stem_two_zero e2_stem_two_nonzero_unique⟩
    letI := KIP126.Def.standardHF2AdamsContext.tensorStructure
    open scoped TensorProduct DirectSum in
    have low_cooperation_calculation :
        let R := KIP126.Def.standardHF2AdamsContext.cooperationStructure.ring
        let B := KIP126.Def.standardHF2AdamsContext.cooperationStructure.basis
        let K := KIP126.Def.standardHF2AdamsContext.cooperationStructure.kunneth
        letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
          fun i => mod2HomologyModule H R i H.HF2
        ((∀ (u2 : Mod2Cooperations H 2),
          cooperationMilnorPolynomial H R B 2 u2 = MvPolynomial.X ((0 : Fin 1), 0) ^ 2 →
          ∀ (a : Mod2Cooperations H 4),
          cooperationTensorDiagonal H R K 4 a ≠
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 4 a +
            DirectSum.lof (ZMod 2) ℤ _ 2 (u2 ⊗ₜ[ZMod 2] u2) +
            DirectSum.lof (ZMod 2) ℤ _ 4 (a ⊗ₜ[ZMod 2]
              (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                (sub_self (4 : ℤ)).symm) (cooperationUnit H))) ∧
        (∀ (x1 : Mod2Cooperations H 1) (u2 : Mod2Cooperations H 2),
          cooperationMilnorPolynomial H R B 1 x1 = MvPolynomial.X ((0 : Fin 1), 0) →
          cooperationMilnorPolynomial H R B 2 u2 = MvPolynomial.X ((0 : Fin 1), 0) ^ 2 →
          ∀ (a b : Mod2Cooperations H 3) (c : Mod2Cooperations H 4),
          cooperationTensorDiagonal H R K 3 a =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3 a +
            DirectSum.lof (ZMod 2) ℤ _ 2 (u2 ⊗ₜ[ZMod 2] x1) +
            DirectSum.lof (ZMod 2) ℤ _ 3 (a ⊗ₜ[ZMod 2]
              (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                (sub_self (3 : ℤ)).symm) (cooperationUnit H)) →
          cooperationTensorDiagonal H R K 3 b =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3 b +
            DirectSum.lof (ZMod 2) ℤ _ 1 (x1 ⊗ₜ[ZMod 2] u2) +
            DirectSum.lof (ZMod 2) ℤ _ 3 (b ⊗ₜ[ZMod 2]
              (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                (sub_self (3 : ℤ)).symm) (cooperationUnit H)) →
          cooperationTensorDiagonal H R K 4 c ≠
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 4 c +
            (DirectSum.lof (ZMod 2) ℤ
              (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (4 - i) H.HF2)
              1 (x1 ⊗ₜ[ZMod 2] a) +
            DirectSum.lof (ZMod 2) ℤ
              (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (4 - i) H.HF2)
              3 (b ⊗ₜ[ZMod 2] x1)) +
            DirectSum.lof (ZMod 2) ℤ _ 4 (c ⊗ₜ[ZMod 2]
              (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                (sub_self (4 : ℤ)).symm) (cooperationUnit H)))) ∧
        (∀ (d : ℤ) (p : PositiveMonomial d) (k : ℕ),
          (k = 1 ∨ k = 2) → p.val = Finsupp.single 0 k →
          mod2TensorCoaction H R K H.HF2 d (B.basis d p).val =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2)
              d (B.basis d p).val +
            DirectSum.lof (ZMod 2) ℤ _ d
              (((B.basis d p).val : mod2HomologyF2 H R d H.HF2) ⊗ₜ[ZMod 2]
              (LinearEquiv.cast (R := ZMod 2)
                (M := fun i => mod2HomologyF2 H R i H.HF2) (sub_self d).symm)
                (cooperationUnit H))) := by
      open scoped BigOperators TensorProduct DirectSum in
      open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
        KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor
        KIP126.Algebra MvPolynomial in
      set_option maxHeartbeats 4000000 in
      exact by
        classical
        let R := KIP126.Def.standardHF2AdamsContext.cooperationStructure.ring
        let B := KIP126.Def.standardHF2AdamsContext.cooperationStructure.basis
        let K := KIP126.Def.standardHF2AdamsContext.cooperationStructure.kunneth
        letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
          fun i => mod2HomologyModule H R i H.HF2
        letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) :=
          fun i => mod2HF2HomotopyModule H R i
        let x : TensorPower 1 := X (0, 0)
        let u : TensorPower 1 := X (0, 0) ^ 2
        let p : TensorPower 1 := X (0, 1)
        let q : TensorPower 1 := X (0, 0) ^ 3 + X (0, 1)
        let t : TensorPower 1 := X (0, 0) * X (0, 1)
        let z : TensorPower 1 := X (0, 0) ^ 4

        have dx : differentialPolynomial 1 x = 0 := by
          simpa [x, hiPolynomial] using hiPolynomial_differential 0

        have du : differentialPolynomial 1 u = 0 := by
          simpa [u, hiPolynomial] using hiPolynomial_differential 1

        have dz : differentialPolynomial 1 z = 0 := by
          simpa [z, hiPolynomial] using hiPolynomial_differential 2

        -- Markdown §1: dP = UX for the actual normalized-polynomial differential.
        have dp : differentialPolynomial 1 p = cupPolynomial u x := by
          simp [differentialPolynomial, p, u, x, cupPolynomial, insertLeft, insertRight,
            splitSlot, coproductGenerator, xi, Fin.sum_univ_succ, Finset.sum_range_succ]
          ring_nf
          simp [CharTwo.two_eq_zero]

        -- Q = [x³+y] is the second degree-three basis vector.
        have dq : differentialPolynomial 1 q = cupPolynomial x u := by
          have hc (a b : TensorPower 2) : (a + b) ^ 3 =
              a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 := by
            calc
              _ = (a ^ 2 + b ^ 2) * (a + b) := by rw [pow_succ, CharTwo.add_sq]
              _ = _ := by ring
          simp [differentialPolynomial, q, u, x, cupPolynomial, insertLeft, insertRight,
            splitSlot, coproductGenerator, xi, Fin.sum_univ_succ, Finset.sum_range_succ, hc]
          ring_nf
          simp [CharTwo.two_eq_zero]

        -- The only nonzero incoming degree-four differential is E+UU.
        have dt : differentialPolynomial 1 t =
            cupPolynomial q x + cupPolynomial u u + cupPolynomial x p := by
          simp [differentialPolynomial, t, q, u, x, p, cupPolynomial, insertLeft, insertRight,
            splitSlot, coproductGenerator, xi, Fin.sum_univ_succ, Finset.sum_range_succ]
          ring_nf
          simp [CharTwo.two_eq_zero]

        have low_exponents (d : (Fin 1 × ℕ) →₀ ℕ)
            (hd : Finsupp.weight weight d ≤ 4) :
            d = Finsupp.single (0,0) (d (0,0)) + Finsupp.single (0,1) (d (0,1)) := by
          apply singleSlot_exponents_eq_two
          intro j hj
          by_contra hn
          have hw := Finsupp.le_weight_of_ne_zero' weight hn
          have hp : 2 ^ 3 ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide) (by omega)
          change 2 ^ (j + 1) - 1 ≤ Finsupp.weight weight d at hw
          norm_num at hp
          omega

        have degree_four_monomial (d : (Fin 1 × ℕ) →₀ ℕ)
            (hd : Finsupp.weight weight d = 4) :
            monomial d (1 : F2) = z ∨ monomial d (1 : F2) = t := by
          have he := low_exponents d (by omega)
          have hd' : d (0,0) + 3 * d (0,1) = 4 :=
            (singleSlot_two_weight _ _).symm.trans ((congrArg (Finsupp.weight weight) he).symm.trans hd)
          by_cases hy : d (0,1) = 0
          · have hx : d (0,0) = 4 := by omega
            left
            rw [he, hx, hy]
            simp [z, X_pow_eq_monomial]
          · have hx : d (0,0) = 1 := by omega
            have hy' : d (0,1) = 1 := by omega
            right
            rw [he, hx, hy']
            simp [t, X, monomial_mul]

        let eps : TensorPower 2 →ₗ[F2] F2 :=
          lcoeff F2 (Finsupp.single (0,0) 2 + Finsupp.single (1,0) 2) +
            lcoeff F2 (Finsupp.single (0,0) 1 + Finsupp.single (1,1) 1)

        have eps_uu : eps (cupPolynomial u u) = 1 := by
          simp only [cupPolynomial, u, map_pow, rename_X]
          simp [eps, X_pow_eq_monomial, monomial_mul,
            coeff_monomial, Finsupp.ext_iff, Finsupp.single_apply]
          intro h
          have := h 0
          norm_num at this

        have eps_qx : eps (cupPolynomial q x) = 0 := by
          have hm : cupPolynomial q x =
              monomial (Finsupp.single (0,0) 3 + Finsupp.single (1,0) 1) (1 : F2) +
              monomial (Finsupp.single (0,1) 1 + Finsupp.single (1,0) 1) (1 : F2) := by
            simp only [cupPolynomial, q, x, map_add, map_pow, rename_X, add_mul]
            rw [X_pow_eq_monomial]
            simp [X, monomial_mul]
          have he (d : (Fin 2 × ℕ) →₀ ℕ) (h1 : d (0,0) ≠ 1) (h2 : d (0,0) ≠ 2) :
              eps (monomial d (1 : F2)) = 0 := by
            have hn1 : d ≠ Finsupp.single (0,0) 1 + Finsupp.single (1,1) 1 := by
              intro hd
              apply h1
              simpa using congrArg (fun e => e (0,0)) hd
            have hn2 : d ≠ Finsupp.single (0,0) 2 + Finsupp.single (1,0) 2 := by
              intro hd
              apply h2
              simpa using congrArg (fun e => e (0,0)) hd
            simp [eps, coeff_monomial, hn1, hn2]
          rw [hm, map_add, he _ (by norm_num) (by norm_num), he _ (by norm_num) (by norm_num), add_zero]

        have eps_xp : eps (cupPolynomial x p) = 1 := by
          simp only [cupPolynomial, x, p, rename_X]
          simp [eps, X, monomial_mul,
            coeff_monomial, Finsupp.ext_iff, Finsupp.single_apply]
          intro h
          have := h 0
          norm_num at this

        have eps_differential (b : cochains 1 4) : eps (differential 1 4 b).val = 0 := by
          let f := eps.comp ((differentialPolynomial 1).comp (cochains 1 4).subtype)
          have hf : f = 0 := by
            apply (cochainsMonomialBasis 1 4).ext
            intro d
            change eps (differentialPolynomial 1 (cochainsMonomialBasis 1 4 d).val) = 0
            rw [cochainsMonomialBasis_val]
            rcases degree_four_monomial d.val d.property.1 with h | h
            · rw [h, dz, map_zero]
            · rw [h, dt, map_add, map_add, eps_uu, eps_qx, eps_xp]
              decide
          exact LinearMap.congr_fun hf b

        have uu_not_boundary (b : cochains 1 4) :
            (differential 1 4 b).val ≠ cupPolynomial u u := by
          intro hb
          have h := eps_differential b
          rw [hb, eps_uu] at h
          exact one_ne_zero h

        have toda_not_boundary (b : cochains 1 4) :
            (differential 1 4 b).val ≠ cupPolynomial x p + cupPolynomial q x := by
          intro hb
          have h := eps_differential b
          rw [hb, map_add, eps_xp, eps_qx, add_zero] at h
          exact one_ne_zero h

        have degree_three_monomial (d : (Fin 1 × ℕ) →₀ ℕ)
            (hd : Finsupp.weight weight d = 3) :
            monomial d (1 : F2) = q + p ∨ monomial d (1 : F2) = p := by
          have he := low_exponents d (by omega)
          have hd' : d (0,0) + 3 * d (0,1) = 3 :=
            (singleSlot_two_weight _ _).symm.trans ((congrArg (Finsupp.weight weight) he).symm.trans hd)
          by_cases hy : d (0,1) = 0
          · have hx : d (0,0) = 3 := by omega
            left
            rw [he, hx, hy]
            simp [q, p, add_assoc, CharTwo.add_self_eq_zero, X_pow_eq_monomial]
          · have hx : d (0,0) = 0 := by omega
            have hy' : d (0,1) = 1 := by omega
            right
            rw [he, hx, hy']
            simp [p, X]

        let retractThree : TensorPower 2 →ₗ[F2] TensorPower 1 :=
          (lcoeff F2 (Finsupp.single (0,0) 1 + Finsupp.single (1,0) 2)).smulRight q +
            (lcoeff F2 (Finsupp.single (0,0) 2 + Finsupp.single (1,0) 1)).smulRight p

        have retractThree_xu : retractThree (cupPolynomial x u) = q := by
          have hne : (Finsupp.single ((0 : Fin 2),0) 1 + Finsupp.single (1,0) 2 :
              (Fin 2 × ℕ) →₀ ℕ) ≠ Finsupp.single (0,0) 2 + Finsupp.single (1,0) 1 := by
            intro he
            have := congrArg (fun e => e (0,0)) he
            norm_num at this
          simp only [cupPolynomial, x, u, map_pow, rename_X]
          rw [X_pow_eq_monomial]
          simp [retractThree, X, monomial_mul, coeff_monomial, hne]

        have retractThree_ux : retractThree (cupPolynomial u x) = p := by
          have hne : (Finsupp.single ((0 : Fin 2),0) 2 + Finsupp.single (1,0) 1 :
              (Fin 2 × ℕ) →₀ ℕ) ≠ Finsupp.single (0,0) 1 + Finsupp.single (1,0) 2 := by
            intro he
            have := congrArg (fun e => e (0,0)) he
            norm_num at this
          simp only [cupPolynomial, x, u, map_pow, rename_X]
          rw [X_pow_eq_monomial]
          simp [retractThree, X, monomial_mul, coeff_monomial, hne]

        have retractThree_differential (b : cochains 1 3) :
            retractThree (differential 1 3 b).val = b.val := by
          let f := retractThree.comp ((differentialPolynomial 1).comp (cochains 1 3).subtype)
          have hf : f = (cochains 1 3).subtype := by
            apply (cochainsMonomialBasis 1 3).ext
            intro d
            change retractThree (differentialPolynomial 1 (cochainsMonomialBasis 1 3 d).val) =
              (cochainsMonomialBasis 1 3 d).val
            rw [cochainsMonomialBasis_val]
            rcases degree_three_monomial d.val d.property.1 with h | h
            · rw [h, map_add, dq, dp, map_add, retractThree_xu, retractThree_ux]
            · rw [h, dp, retractThree_ux]
          exact LinearMap.congr_fun hf b

        have differential_three_injective : Function.Injective (differential 1 3) := by
          intro a b hab
          apply Subtype.ext
          rw [← retractThree_differential a, ← retractThree_differential b, hab]

        /- The basis index of the total-degree part of a tensor square. The first
        degree is retained, so distinct direct-sum summands are not identified. -/
        let MilnorPair (n : ℤ) := Σ i : ℤ, MilnorMonomial i × MilnorMonomial (n - i)

        /- Put the two exponent vectors in distinct slots of the existing model. -/
        let milnorPairExponents {n : ℤ} (d : MilnorPair n) : (Fin 2 × ℕ) →₀ ℕ :=
          d.2.1.val.mapDomain (fun j => ((0 : Fin 2), j)) +
            d.2.2.val.mapDomain (fun j => ((1 : Fin 2), j))

        /- The full basis derived from the already constructed linear coordinates,
        not an additional existence input. -/
        let cooperationMilnorBasis (n : ℤ) :
            Module.Basis (MilnorMonomial n) F2 (mod2HomologyF2 H R n H.HF2) :=
          Module.Basis.ofRepr (cooperationMilnorEquiv H R B n)

        /- Tensor the derived full bases and take the basis of their direct sum. -/
        let cooperationTensorMilnorBasis (n : ℤ) :
            Module.Basis (MilnorPair n) F2
              (cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n) :=
          letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
            fun i => mod2HomologyModule H R i H.HF2
          DFinsupp.basis fun i => (cooperationMilnorBasis i).tensorProduct (R := F2) (S := F2)
            (cooperationMilnorBasis (n - i))

        have milnorMonomialPolynomial_zero :
            milnorMonomialPolynomial zeroMilnorMonomial = 1 := by
          simp [milnorMonomialPolynomial, zeroMilnorMonomial]

        have cooperationMilnorPolynomial_unit :
            cooperationMilnorPolynomial H R B 0 (cooperationUnit H) = 1 := by
          simp [cooperationMilnorPolynomial, cooperationMilnorEquiv_unit,
            Finsupp.linearCombination_single, milnorMonomialPolynomial_zero]

        have cooperationMilnorPolynomial_reduced_basis (n : ℤ) (d : PositiveMonomial n) :
            cooperationMilnorPolynomial H R B n ((B.basis n) d).val =
              milnorMonomialPolynomial (⟨d.val, d.property.1⟩ : MilnorMonomial n) := by
          change Finsupp.linearCombination F2 milnorMonomialPolynomial
            (cooperationMilnorEquiv H R B n ((B.basis n) d).val) = _
          erw [cooperationMilnorEquiv_reduced_basis H R B n d]
          simp only [Finsupp.linearCombination_single, one_smul]

        have cooperationTensorMilnorPolynomial_lof_tmul (n i : ℤ)
            (a : Mod2Cooperations H i) (b : Mod2Cooperations H (n - i)) :
            letI : ∀ j, Module F2 (Mod2Cooperations H j) :=
              fun j => mod2HomologyModule H R j H.HF2
            cooperationTensorMilnorPolynomial H R B n (DirectSum.lof F2 ℤ _ i (a ⊗ₜ[F2] b)) =
              cupPolynomial (cooperationMilnorPolynomial H R B i a)
                (cooperationMilnorPolynomial H R B (n - i) b) := by
          simp only [cooperationTensorMilnorPolynomial, DirectSum.toModule_lof,
            LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
            cupPolynomial, AlgHom.toLinearMap_apply]
          rfl

        have milnorPairExponents_zero {n : ℤ} (d : MilnorPair n) (j : ℕ) :
            milnorPairExponents d (0, j) = d.2.1.val j := by
          have hi : Function.Injective (fun j : ℕ => ((0 : Fin 2), j)) := fun _ _ h =>
            congrArg Prod.snd h
          have hn : (0, j) ∉ Set.range (fun k : ℕ => ((1 : Fin 2), k)) := by simp
          simp only [milnorPairExponents, Finsupp.add_apply, Finsupp.mapDomain_apply hi,
            Finsupp.mapDomain_notin_range _ _ hn, add_zero]

        have milnorPairExponents_one {n : ℤ} (d : MilnorPair n) (j : ℕ) :
            milnorPairExponents d (1, j) = d.2.2.val j := by
          have hi : Function.Injective (fun j : ℕ => ((1 : Fin 2), j)) := fun _ _ h =>
            congrArg Prod.snd h
          have hn : (1, j) ∉ Set.range (fun k : ℕ => ((0 : Fin 2), k)) := by simp
          simp only [milnorPairExponents, Finsupp.add_apply, Finsupp.mapDomain_apply hi,
            Finsupp.mapDomain_notin_range _ _ hn, zero_add]

        /- The first exponent vector also recovers its summand degree by weight. -/
        have milnorPairExponents_injective (n : ℤ) :
            Function.Injective (milnorPairExponents (n := n)) := by
          rintro ⟨i, a, b⟩ ⟨i', a', b'⟩ h
          have ha : a.val = a'.val := by
            ext j
            have hh := congrArg (fun d => d (0, j)) h
            simpa only [milnorPairExponents_zero] using hh
          have hi : i = i' := a.property.symm.trans ((congrArg (fun d => (slotWeight d : ℤ)) ha).trans a'.property)
          subst i'
          have haa : a = a' := Subtype.ext ha
          have hb : b = b' := by
            apply Subtype.ext
            ext j
            have hh := congrArg (fun d => d (1, j)) h
            simpa only [milnorPairExponents_one] using hh
          cases haa
          cases hb
          rfl

        /- Concatenating two basis monomials gives their two-slot exponent vector. -/
        have cup_milnorMonomialPolynomial {n : ℤ} (d : MilnorPair n) :
            cupPolynomial (milnorMonomialPolynomial d.2.1) (milnorMonomialPolynomial d.2.2) =
              MvPolynomial.monomial (milnorPairExponents d) (1 : F2) := by
          simp only [cupPolynomial, milnorMonomialPolynomial, MvPolynomial.rename_monomial,
            ← Finsupp.mapDomain_comp, MvPolynomial.monomial_mul, mul_one]
          rfl

        have cooperationMilnorPolynomial_basis (n : ℤ) (d : MilnorMonomial n) :
            cooperationMilnorPolynomial H R B n (cooperationMilnorBasis n d) =
              milnorMonomialPolynomial d := by
          simp [cooperationMilnorBasis, Module.Basis.coe_ofRepr, cooperationMilnorPolynomial,
            Finsupp.linearCombination_single]

        /- Single-slot polynomial coordinates lose no cooperation classes. -/
        have cooperationMilnorPolynomial_injective (n : ℤ) :
            Function.Injective (cooperationMilnorPolynomial H R B n) := by
          have hi : Function.Injective (fun d : MilnorMonomial n =>
              d.val.mapDomain fun j => ((0 : Fin 1), j)) := by
            intro d e h
            apply Subtype.ext
            exact Finsupp.mapDomain_injective (fun _ _ h => congrArg Prod.snd h) h
          have hl := (MvPolynomial.basisMonomials (Fin 1 × ℕ) F2).linearIndependent.comp _ hi
          have hl' : LinearIndependent F2 (milnorMonomialPolynomial (n := n)) := hl
          exact hl'.finsuppLinearCombination_injective.comp (cooperationMilnorEquiv H R B n).injective

        have cooperationTensorMilnorBasis_apply (n : ℤ) (d : MilnorPair n) :
            letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
              fun i => mod2HomologyModule H R i H.HF2
            cooperationTensorMilnorBasis n d = DirectSum.lof F2 ℤ _ d.1
              (cooperationMilnorBasis d.1 d.2.1 ⊗ₜ[F2]
                cooperationMilnorBasis (n - d.1) d.2.2) := by
          change (cooperationTensorMilnorBasis n).repr.symm (Finsupp.single d 1) = _
          dsimp only [cooperationTensorMilnorBasis, DFinsupp.basis]
          erw [LinearEquiv.symm_trans_apply]
          simp only [LinearEquiv.symm_symm]
          erw [DFinsupp.mapRange.linearEquiv_symm]
          simp only [sigmaFinsuppLequivDFinsupp]
          erw [DFinsupp.mapRange.linearEquiv_apply]
          erw [sigmaFinsuppEquivDFinsupp_single]
          erw [DFinsupp.mapRange_single, Module.Basis.repr_symm_single_one,
            Module.Basis.tensorProduct_apply']
          rfl

        have cooperationTensorMilnorPolynomial_basis (n : ℤ) (d : MilnorPair n) :
            cooperationTensorMilnorPolynomial H R B n (cooperationTensorMilnorBasis n d) =
              MvPolynomial.monomial (milnorPairExponents d) (1 : F2) := by
          rw [cooperationTensorMilnorBasis_apply]
          erw [cooperationTensorMilnorPolynomial_lof_tmul]
          rw [cooperationMilnorPolynomial_basis, cooperationMilnorPolynomial_basis,
            cup_milnorMonomialPolynomial]

        /- The tensor polynomial map is faithful across all total-degree summands,
        not only within a chosen pair of factors. -/
        have cooperationTensorMilnorPolynomial_injective (n : ℤ) :
            Function.Injective (cooperationTensorMilnorPolynomial H R B n) := by
          apply LinearMap.injective_of_linearIndependent (cooperationTensorMilnorBasis n).span_eq
          have hl := (MvPolynomial.basisMonomials (Fin 2 × ℕ) F2).linearIndependent.comp _
            (milnorPairExponents_injective n)
          simpa only [Function.comp_def, cooperationTensorMilnorPolynomial_basis,
            MvPolynomial.coe_basisMonomials] using hl

        have cooperationPolynomial_cast (i j : ℤ) (h : i = j)
            (a : Mod2Cooperations H i) :
            cooperationMilnorPolynomial H R B j
              ((LinearEquiv.cast (R := F2) (M := fun k => mod2HomologyF2 H R k H.HF2) h) a) =
              cooperationMilnorPolynomial H R B i a := by
          subst j
          rfl

        have cooperationPolynomial_left_unit (n : ℤ) (a : Mod2Cooperations H n) :
            cooperationTensorMilnorPolynomial H R B n
              (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) n a) =
              insertLeft 1 (cooperationMilnorPolynomial H R B n a) := by
          rw [cooperationTensorUnit_apply, cooperationTensorMilnorPolynomial_lof_tmul,
            cooperationPolynomial_cast, cooperationMilnorPolynomial_unit]
          simp [cupPolynomial, insertLeft]

        have cooperationPolynomial_right_unit (n : ℤ) (a : Mod2Cooperations H n) :
            letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
              fun i => mod2HomologyModule H R i H.HF2
            cooperationTensorMilnorPolynomial H R B n
              (DirectSum.lof F2 ℤ _ n (a ⊗ₜ[F2]
                (LinearEquiv.cast (R := F2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                  (sub_self n).symm) (cooperationUnit H))) =
              insertRight 1 (cooperationMilnorPolynomial H R B n a) := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) :=
            fun i => mod2HomologyModule H R i H.HF2
          rw [cooperationTensorMilnorPolynomial_lof_tmul, cooperationPolynomial_cast,
            cooperationMilnorPolynomial_unit]
          simp only [cupPolynomial, map_one, mul_one]
          rfl

        let singleWordEquiv (t : ℤ) : PositiveMonomial t ≃ MilnorWord 1 t :=
          { toFun := fun a => ⟨fun _ => a.val, by simpa [wordDegree] using a.property.1,
              fun _ => a.property.2⟩
            invFun := fun d => ⟨d.val 0, by simpa [wordDegree] using d.property.1, d.property.2 0⟩
            left_inv := fun a => rfl
            right_inv := by
              intro d
              apply Subtype.ext
              funext i
              fin_cases i
              rfl }

        have singleWord_exponents (t : ℤ) (a : PositiveMonomial t) :
            (slotExponentsEquiv 1).symm (singleWordEquiv t a).val =
              a.val.mapDomain (fun j => ((0 : Fin 1), j)) := by
          have hi : Function.Injective (fun j : ℕ => ((0 : Fin 1), j)) := fun _ _ h =>
            congrArg Prod.snd h
          apply (slotExponentsEquiv 1).injective
          rw [Equiv.apply_symm_apply]
          funext i
          fin_cases i
          ext j
          simp [slotExponentsEquiv, singleWordEquiv, Finsupp.mapDomain_apply hi]

        let reducedCochainEquiv :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (n : ℕ),
            LinearMap.ker (cooperationCounitF2 H R n) ≃ₗ[F2] cochains 1 n := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro n
          exact (B.basis n).repr.trans
              ((Finsupp.domLCongr (R := F2) (singleWordEquiv n)).trans (cochainsWordEquiv 1 n).symm)

        have reducedCochainEquiv_val :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (n : ℕ)
            (a : LinearMap.ker (cooperationCounitF2 H R n)),
            (reducedCochainEquiv n a).val = cooperationMilnorPolynomial H R B n a.val := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro n a
          let f := (cochains 1 n).subtype.comp (reducedCochainEquiv n).toLinearMap
          let g := (cooperationMilnorPolynomial H R B n).comp
            (LinearMap.ker (cooperationCounitF2 H R n)).subtype
          have h : f = g := by
            apply (B.basis n).ext
            intro d
            change ((cochainsWordEquiv 1 n).symm
              (Finsupp.domLCongr (R := F2) (singleWordEquiv n)
                ((B.basis n).repr (B.basis n d)))).val =
              cooperationMilnorPolynomial H R B n (B.basis n d).val
            rw [Module.Basis.repr_self, Finsupp.domLCongr_single,
              cochainsWordEquiv_symm_single_val, singleWord_exponents,
              cooperationMilnorPolynomial_reduced_basis]
            rfl
          exact LinearMap.congr_fun h a

        let positiveReduced :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (n : ℕ) (hn : n ≠ 0) (a : Mod2Cooperations H n),
            LinearMap.ker (cooperationCounitF2 H R n) := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro n hn a
          haveI := H.homotopy_vanishes n (by exact_mod_cast hn)
          exact ⟨a, Subsingleton.elim _ _⟩

        let positiveCochain :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (n : ℕ) (hn : n ≠ 0) (a : Mod2Cooperations H n),
            cochains 1 n := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro n hn a
          exact reducedCochainEquiv n (positiveReduced n hn a)

        have positiveCochain_val :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (n : ℕ) (hn : n ≠ 0) (a : Mod2Cooperations H n),
            (positiveCochain n hn a).val = cooperationMilnorPolynomial H R B n a := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro n hn a
          exact reducedCochainEquiv_val n (positiveReduced n hn a)

        -- Only the supplied positive-basis coproduct is used here.
        have reduced_coproduct :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (hM : Mod2MilnorCoproductCompatible H R K B) (n : ℤ)
            (a : LinearMap.ker (cooperationCounitF2 H R n)),
            cooperationTensorMilnorPolynomial H R B n (cooperationTensorDiagonal H R K n a.val) =
              splitSlot (0 : Fin 1) (cooperationMilnorPolynomial H R B n a.val) := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro hM n a
          let f := ((cooperationTensorMilnorPolynomial H R B n).comp
            (cooperationTensorDiagonal H R K n)).comp (LinearMap.ker (cooperationCounitF2 H R n)).subtype
          let g := ((splitSlot (0 : Fin 1)).toLinearMap.comp
            (cooperationMilnorPolynomial H R B n)).comp (LinearMap.ker (cooperationCounitF2 H R n)).subtype
          have he : f = g := by
            apply (B.basis n).ext
            intro d
            change cooperationTensorMilnorPolynomial H R B n
              (cooperationTensorDiagonal H R K n (B.basis n d).val) =
              splitSlot (0 : Fin 1) (cooperationMilnorPolynomial H R B n (B.basis n d).val)
            rw [cooperationMilnorPolynomial_reduced_basis]
            exact hM n d
          exact LinearMap.congr_fun he a

        let reducedDiagonal :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (n : ℤ) (a : Mod2Cooperations H n),
            cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro n a
          exact cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) n a +
            cooperationTensorDiagonal H R K n a +
            DirectSum.lof F2 ℤ _ n (a ⊗ₜ[F2]
              (LinearEquiv.cast (R := F2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                (sub_self n).symm) (cooperationUnit H))

        have reducedDiagonal_eq_of (n : ℤ) (a : Mod2Cooperations H n)
            (d : cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n) :
            letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
            cooperationTensorDiagonal H R K n a =
              cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) n a + d +
              DirectSum.lof F2 ℤ _ n (a ⊗ₜ[F2]
                (LinearEquiv.cast (R := F2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                  (sub_self n).symm) (cooperationUnit H)) →
            reducedDiagonal n a = d := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          intro h
          have hdouble (z : cooperationTensor H R (fun i => mod2HomologyF2 H R i H.HF2) n) : z + z = 0 := by
            simpa only [add_smul, one_smul] using
              (show ((1 : F2) + 1) • z = 0 by rw [show (1 : F2) + 1 = 0 by decide, zero_smul])
          dsimp only [reducedDiagonal]
          rw [h]
          calc
            _ = (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) n a +
                cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) n a) + d +
                (DirectSum.lof F2 ℤ _ n (a ⊗ₜ[F2]
                  (LinearEquiv.cast (R := F2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                    (sub_self n).symm) (cooperationUnit H)) +
                 DirectSum.lof F2 ℤ _ n (a ⊗ₜ[F2]
                  (LinearEquiv.cast (R := F2) (M := fun i => mod2HomologyF2 H R i H.HF2)
                    (sub_self n).symm) (cooperationUnit H))) := by abel
            _ = d := by rw [hdouble, hdouble, zero_add, add_zero]

        have reducedDiagonal_polynomial :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (hM : Mod2MilnorCoproductCompatible H R K B)
            (n : ℕ) (hn : n ≠ 0) (a : Mod2Cooperations H n),
            cooperationTensorMilnorPolynomial H R B n (reducedDiagonal n a) =
              (differential 1 n (positiveCochain n hn a)).val := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro hM n hn a
          change cooperationTensorMilnorPolynomial H R B n (reducedDiagonal n a) =
            differentialPolynomial 1 (positiveCochain n hn a).val
          rw [positiveCochain_val n hn a]
          dsimp only [reducedDiagonal]
          rw [map_add, map_add, cooperationPolynomial_left_unit, cooperationPolynomial_right_unit]
          have hc := reduced_coproduct hM n (positiveReduced n hn a)
          change cooperationTensorMilnorPolynomial H R B n (cooperationTensorDiagonal H R K n a) =
            splitSlot (0 : Fin 1) (cooperationMilnorPolynomial H R B n a) at hc
          erw [hc]
          simp only [differentialPolynomial, LinearMap.add_apply, LinearMap.sum_apply,
            AlgHom.toLinearMap_apply, Fin.sum_univ_one]
          abel

        have square_obstruction :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (hM : Mod2MilnorCoproductCompatible H R K B)
            (u2 : Mod2Cooperations H 2) (hu : cooperationMilnorPolynomial H R B 2 u2 = u)
            (a : Mod2Cooperations H 4),
            reducedDiagonal 4 a ≠ DirectSum.lof F2 ℤ _ 2 (u2 ⊗ₜ[F2] u2) := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro hM u2 hu a
          intro ha
          have he := congrArg (cooperationTensorMilnorPolynomial H R B 4) ha
          erw [reducedDiagonal_polynomial hM 4 (by decide),
            cooperationTensorMilnorPolynomial_lof_tmul, hu] at he
          exact uu_not_boundary (positiveCochain 4 (by decide) a) he

        have toda_obstruction :
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          ∀ (hM : Mod2MilnorCoproductCompatible H R K B)
            (x1 : Mod2Cooperations H 1) (u2 : Mod2Cooperations H 2)
            (hx : cooperationMilnorPolynomial H R B 1 x1 = x)
            (hu : cooperationMilnorPolynomial H R B 2 u2 = u)
            (a b : Mod2Cooperations H 3) (c : Mod2Cooperations H 4)
            (ha : reducedDiagonal 3 a = DirectSum.lof F2 ℤ _ 2 (u2 ⊗ₜ[F2] x1))
            (hb : reducedDiagonal 3 b = DirectSum.lof F2 ℤ _ 1 (x1 ⊗ₜ[F2] u2)),
            reducedDiagonal 4 c ≠
              DirectSum.lof F2 ℤ
                (fun i => Mod2Cooperations H i ⊗[F2] mod2HomologyF2 H R (4 - i) H.HF2) 1 (x1 ⊗ₜ[F2] a) + DirectSum.lof F2 ℤ
                (fun i => Mod2Cooperations H i ⊗[F2] mod2HomologyF2 H R (4 - i) H.HF2) 3 (b ⊗ₜ[F2] x1) := by
          letI : ∀ i, Module F2 (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
          letI : ∀ i, Module F2 (HomotopyGroup i H.HF2) := fun i => mod2HF2HomotopyModule H R i
          intro hM x1 u2 hx hu a b c ha hb
          have hpa : cooperationMilnorPolynomial H R B 3 a = p := by
            have he := congrArg (cooperationTensorMilnorPolynomial H R B 3) ha
            erw [reducedDiagonal_polynomial hM 3 (by decide),
              cooperationTensorMilnorPolynomial_lof_tmul, hu, hx] at he
            have hr := congrArg retractThree he
            rw [retractThree_differential, positiveCochain_val 3 (by decide) a, retractThree_ux] at hr
            exact hr
          have hpb : cooperationMilnorPolynomial H R B 3 b = q := by
            have he := congrArg (cooperationTensorMilnorPolynomial H R B 3) hb
            erw [reducedDiagonal_polynomial hM 3 (by decide),
              cooperationTensorMilnorPolynomial_lof_tmul, hx, hu] at he
            have hr := congrArg retractThree he
            rw [retractThree_differential, positiveCochain_val 3 (by decide) b, retractThree_xu] at hr
            exact hr
          intro hc
          have he := congrArg (cooperationTensorMilnorPolynomial H R B 4) hc
          erw [reducedDiagonal_polynomial hM 4 (by decide), map_add,
            cooperationTensorMilnorPolynomial_lof_tmul, cooperationTensorMilnorPolynomial_lof_tmul,
            hx, hpa, hpb] at he
          exact toda_not_boundary (positiveCochain 4 (by decide) c) he
        have hM : Mod2MilnorCoproductCompatible H R K B :=
          KIP126.Def.standardHF2AdamsContext.cooperationStructure.coproduct
        constructor
        · constructor
          · intro u2 hu a ha
            apply square_obstruction hM u2 hu a
            exact reducedDiagonal_eq_of 4 a _ ha
          · intro x1 u2 hx hu a b c ha hb hc
            apply toda_obstruction hM x1 u2 hx hu a b c
              (reducedDiagonal_eq_of 3 a _ ha) (reducedDiagonal_eq_of 3 b _ hb)
            exact reducedDiagonal_eq_of 4 c _ hc
        · intro d pLow k hk hp
          have hp0 : milnorMonomialPolynomial (⟨pLow.val, pLow.property.1⟩ : MilnorMonomial d) =
              (MvPolynomial.X ((0 : Fin 1), 0)) ^ k := by
            simp only [milnorMonomialPolynomial, hp, Finsupp.mapDomain_single,
              MvPolynomial.X_pow_eq_monomial]
          apply cooperationTensorMilnorPolynomial_injective d
          change cooperationTensorMilnorPolynomial H R B d
            (cooperationTensorDiagonal H R K d (B.basis d pLow).val) = _
          rw [hM d pLow, map_add, cooperationPolynomial_left_unit,
            cooperationPolynomial_right_unit, cooperationMilnorPolynomial_reduced_basis d pLow, hp0]
          have hpow (a b : TensorPower 2) : (a + b) ^ k = a ^ k + b ^ k := by
            rcases hk with rfl | rfl
            · simp
            · exact add_pow_char_pow a b 2 1
          simp [splitSlot, coproductGenerator, xi, Finset.sum_range_succ,
            insertLeft, insertRight, hpow, add_comm]
    obtain ⟨low_cooperation_obstructions, low_basis_primitive⟩ := low_cooperation_calculation

    -- §§2–4: the actual mapping cones and their compatible coactions.
    open KIP126.Algebra in
    open scoped TensorProduct DirectSum in
    have firstLift_hurewicz_ne_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))  {X : C} (n : ℤ)
        (α : HomotopyGroup n X) (hn : ¬ AdamsFiltrationAtLeast H α 2)
        (a : HomotopyGroup n (adamsTower H.unit X 1))
        (ha : a ≫ adamsTowerMap H.unit X 0 1 (by decide) = α) :
        a ≫ adamsUnit H.unit (adamsTower H.unit X 1) ≠ 0 := by
      intro hz
      obtain ⟨a₂, ha₂⟩ := (adamsResolutionTriangle H.unit X 1).coyoneda_exact₂
        (adamsResolutionTriangle_distinguished H.unit X 1) a hz
      change a = a₂ ≫ adamsTowerStep H.unit X 1 at ha₂
      apply hn
      refine ⟨a₂, ?_⟩
      rw [adamsTowerMap_succ H.unit X 0 1 (by decide), ← Category.assoc, ← ha₂]
      exact ha

    have firstLift_reduced_ne_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  (d : ℤ)
        (α : HomotopyGroup (d - 1) (SphereSpectrum : C))
        (hn : ¬ AdamsFiltrationAtLeast H α 2)
        (a : HomotopyGroup (d - 1) (adamsTower H.unit SphereSpectrum 1))
        (ha : a ≫ adamsTowerMap H.unit SphereSpectrum 0 1 (by decide) = α) :
        sphereFirstTowerHomologyEquiv H R d
          (a ≫ adamsUnit H.unit (adamsTower H.unit SphereSpectrum 1)) ≠ 0 := by
      intro hz
      apply firstLift_hurewicz_ne_zero H (d - 1) α hn a ha
      exact (sphereFirstTowerHomologyEquiv H R d).map_eq_zero_iff.mp hz

    -- Markdown §2.4, factored from the finite monomial enumeration. The hp
    -- hypothesis is discharged for d=1 and d=2 by their actual monomial lists.

    have unique_nonzero_reduced {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  (B : Mod2ReducedMilnorBasis H R) (d : ℤ)
        (p : PositiveMonomial d) (hp : ∀ q : PositiveMonomial d, q = p) :
        letI := mod2HomologyModule H R d H.HF2
        letI := mod2HF2HomotopyModule H R d
        ∀ b : LinearMap.ker (cooperationCounitF2 H R d), b ≠ 0 → b = B.basis d p := by
      letI := mod2HomologyModule H R d H.HF2
      letI := mod2HF2HomotopyModule H R d
      intro b hb
      apply (B.basis d).repr.injective
      rw [Module.Basis.repr_self]
      have hc : (B.basis d).repr b p ≠ 0 := by
        intro hc
        apply hb
        apply (B.basis d).repr.injective
        ext q
        rw [hp q, hc, map_zero, Finsupp.zero_apply]
      have htwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      have hone : (B.basis d).repr b p = 1 := (htwo _).resolve_left hc
      ext q
      rw [hp q, hone, Finsupp.single_eq_same]

    -- The integer- and F₂-linear counit kernels have the same underlying maps,
    -- so both descriptions identify the cooperation determined by the boundary.

    have firstLift_cooperation_identification {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)
        (B : Mod2ReducedMilnorBasis H R) (d : ℤ)
        (p : PositiveMonomial d) (hp : ∀ q : PositiveMonomial d, q = p)
        (α : HomotopyGroup (d - 1) (SphereSpectrum : C))
        (hn : ¬ AdamsFiltrationAtLeast H α 2)
        (a : HomotopyGroup (d - 1) (adamsTower H.unit SphereSpectrum 1))
        (ha : a ≫ adamsTowerMap H.unit SphereSpectrum 0 1 (by decide) = α) :
        letI := mod2HomologyModule H R d H.HF2
        letI := mod2HF2HomotopyModule H R d
        (sphereFirstTowerHomologyEquiv H R d
          (a ≫ adamsUnit H.unit (adamsTower H.unit SphereSpectrum 1))).val =
            (B.basis d p).val := by
      letI := mod2HomologyModule H R d H.HF2
      letI := mod2HF2HomotopyModule H R d
      let b := sphereFirstTowerHomologyEquiv H R d
        (a ≫ adamsUnit H.unit (adamsTower H.unit SphereSpectrum 1))
      let b₂ : LinearMap.ker (cooperationCounitF2 H R d) := ⟨b.val, b.property⟩
      have hb₂ : b₂ ≠ 0 := by
        intro hz
        apply firstLift_reduced_ne_zero H R d α hn a ha
        apply Subtype.ext
        exact congrArg Subtype.val hz
      exact congrArg Subtype.val (unique_nonzero_reduced H R B d p hp b₂ hb₂)

    -- Markdown §2.5: the connecting homomorphism gives degreewise exactness
    -- for the homology of the specified cofiber sequence.

    let mod2HomologyConnecting {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ) :
        Mod2Homology H n T.Z →+ Mod2Homology H (n - 1) T.X :=
      connectingHomomorphism (T.map (tensorLeft H.HF2)) n

    let mod2HomologyConnectingF2 {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  (T : HoCofiberSequence (C := C)) (n : ℤ) :
        mod2HomologyF2 H R n T.Z →ₗ[ZMod 2] mod2HomologyF2 H R (n - 1) T.X :=
      letI := mod2HomologyModule H R n T.Z
      letI := mod2HomologyModule H R (n - 1) T.X
      (mod2HomologyConnecting H T n).toZModLinearMap 2

    have homology_bottom_injective {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : H.HF2 ◁ T.f = 0) :
        Function.Injective (Mod2Homology.pushforward H T.g n) := by
      let U := T.map (tensorLeft H.HF2)
      have hU : U.f = 0 := hf
      haveI : Mono U.g := (Triangle.mk U.f U.g U.h).mono₂ U.distinguished hU
      intro x y hxy
      exact (cancel_mono U.g).1 hxy

    have homology_connecting_surjective {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : H.HF2 ◁ T.f = 0) :
        Function.Surjective (mod2HomologyConnecting H T n) := by
      intro x
      exact (lesHomotopyExactH (T.map (tensorLeft H.HF2)) n x).mp (by
        change x ≫ (H.HF2 ◁ T.f) = 0
        rw [hf, comp_zero])

    have homology_connecting_injective {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hy : Subsingleton (Mod2Homology H n T.Y)) :
        Function.Injective (mod2HomologyConnecting H T n) := by
      apply (injective_iff_map_eq_zero (mod2HomologyConnecting H T n)).mpr
      intro z hz
      obtain ⟨y, hyz⟩ := (les_homotopy_exact_g (T.map (tensorLeft H.HF2)) n z).mp hz
      have hy0 : y = 0 := hy.elim _ _
      simpa only [hy0, map_zero] using hyz.symm

    let homology_top_equiv {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : H.HF2 ◁ T.f = 0)
        (hy : Subsingleton (Mod2Homology H n T.Y)) :
        mod2HomologyF2 H R n T.Z ≃ₗ[ZMod 2] mod2HomologyF2 H R (n - 1) T.X :=
      LinearEquiv.ofBijective (mod2HomologyConnectingF2 H R T n)
        ⟨homology_connecting_injective H T n hy,
          homology_connecting_surjective H T n hf⟩

    have homology_bottom_surjective {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hx : Subsingleton (Mod2Homology H (n - 1) T.X)) :
        Function.Surjective (Mod2Homology.pushforward H T.g n) := by
      intro z
      exact (les_homotopy_exact_g (T.map (tensorLeft H.HF2)) n z).mp (hx.elim _ _)

    let homology_bottom_equiv {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : H.HF2 ◁ T.f = 0)
        (hx : Subsingleton (Mod2Homology H (n - 1) T.X)) :
        mod2HomologyF2 H R n T.Y ≃ₗ[ZMod 2] mod2HomologyF2 H R n T.Z :=
      LinearEquiv.ofBijective (mod2HomologyF2Map H R T.g n).hom
        ⟨homology_bottom_injective H T n hf,
          homology_bottom_surjective H T n hx⟩

    have homology_middle_subsingleton {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hy : Subsingleton (Mod2Homology H n T.Y))
        (hx : Subsingleton (Mod2Homology H (n - 1) T.X)) :
        Subsingleton (Mod2Homology H n T.Z) := by
      letI := hx
      exact (homology_connecting_injective H T n hy).subsingleton

    -- Sphere support, for arbitrary signed degrees. This uses exactly the
    -- specified tensor/suspension comparison, not an alternate shift instance.

    let sphereHomologyShiftEquiv {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ]  (n m : ℤ) :
        Mod2Homology H n (Sphere (C := C) m) ≃ HomotopyGroup (n - m) H.HF2 := by
      let F := shiftFunctor C m
      let a : Sphere (C := C) n ≅ F.obj (Sphere (C := C) (n - m)) :=
        (shiftFunctorAdd' C (n - m) m n (by omega)).app SphereSpectrum
      let e : H.HF2 ⊗ Sphere (C := C) m ≅ F.obj H.HF2 :=
        ((tensorLeft H.HF2).commShiftIso m).app SphereSpectrum ≪≫
          F.mapIso (ρ_ H.HF2)
      exact (Iso.homCongr a e).trans (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm

    have sphereHomologyShiftSubsingleton {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (n m : ℤ) (hn : n ≠ m) :
        Subsingleton (Mod2Homology H n (Sphere (C := C) m)) := by
      letI := H.homotopy_vanishes (n - m) (sub_ne_zero.mpr hn)
      exact (sphereHomologyShiftEquiv H n m).injective.subsingleton

    have sphereHomologySubsingleton {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (n : ℤ) (hn : n ≠ 0) :
        Subsingleton (Mod2Homology H n (SphereSpectrum : C)) := by
      letI := H.homotopy_vanishes n hn
      let e : Mod2Homology H n (SphereSpectrum : C) ≃+ HomotopyGroup n H.HF2 :=
        ((homotopyGroupFunctor n).mapIso (ρ_ H.HF2)).addCommGroupIsoToAddEquiv
      exact e.injective.subsingleton

    -- Thus the actual two-cell cone has one bottom and one top degree,
    -- with their bases transported along the concrete i_* and ∂ maps above.

    have twoCell_otherDegrees {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
        (d : ℤ) (f : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (n : ℤ) (hn0 : n ≠ 0) (hnd : n ≠ d) :
        Subsingleton (Mod2Homology H n (HasFunctorialCofiber.cofib f)) := by
      exact homology_middle_subsingleton H (HoCofiberSequence.ofMorphism f) n
        (sphereHomologySubsingleton H n hn0)
        (sphereHomologyShiftSubsingleton H (n - 1) (d - 1) (by omega))

    let twoCell_bottom_equiv {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)
        (d : ℤ) (hd : d ≠ 0)
        (f : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (hf : H.HF2 ◁ f = 0) :
        mod2HomologyF2 H R 0 SphereSpectrum ≃ₗ[ZMod 2]
          mod2HomologyF2 H R 0 (HasFunctorialCofiber.cofib f) :=
      homology_bottom_equiv H R (HoCofiberSequence.ofMorphism f) 0 hf
        (sphereHomologyShiftSubsingleton H (-1) (d - 1) (by omega))

    let twoCell_top_equiv {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)
        (d : ℤ) (hd : d ≠ 0)
        (f : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (hf : H.HF2 ◁ f = 0) :
        mod2HomologyF2 H R d (HasFunctorialCofiber.cofib f) ≃ₗ[ZMod 2]
          mod2HomologyF2 H R (d - 1) (Sphere (C := C) (d - 1)) :=
      homology_top_equiv H R (HoCofiberSequence.ofMorphism f) d hf
        (sphereHomologySubsingleton H d hd)

    -- Markdown §2.5: complete (a,id) to the *actual* unit-fiber triangle.
    -- The unitor is left explicit so the connecting compatibility has no
    -- hidden change of coefficient object or suspension convention.

    have twoCell_comparison_to_unit {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (d : ℤ)
        (α : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (a : Sphere (C := C) (d - 1) ⟶ adamsTower H.unit SphereSpectrum 1)
        (ha : a ≫ adamsTowerMap H.unit SphereSpectrum 0 1 (by decide) = α) :
        ∃ φ : HasFunctorialCofiber.cofib α ⟶ H.HF2 ⊗ SphereSpectrum,
          HasFunctorialCofiber.cofibι α ≫ φ = adamsUnit H.unit SphereSpectrum ∧
          HasFunctorialCofiber.cofibδ α ≫ (shiftFunctor C (1 : ℤ)).map a =
            φ ≫ adamsResolutionConnecting H.unit SphereSpectrum 0 := by
      obtain ⟨φ, hφ, hδ⟩ := complete_distinguished_triangle_morphism
        (Triangle.mk α (HasFunctorialCofiber.cofibι α) (HasFunctorialCofiber.cofibδ α))
        (adamsResolutionTriangle H.unit SphereSpectrum 0)
        (HasFunctorialCofiber.cofib_distinguished α)
        (adamsResolutionTriangle_distinguished H.unit SphereSpectrum 0)
        a (𝟙 SphereSpectrum) (by
          change α ≫ 𝟙 SphereSpectrum = a ≫ adamsTowerStep H.unit SphereSpectrum 0
          simpa only [adamsTowerMap, adamsTowerComposite, eqToHom_refl,
            Category.id_comp, Category.comp_id] using ha.symm)
      refine ⟨φ, ?_, hδ⟩
      simpa only [Triangle.mk_mor₂, adamsResolutionTriangle, Triangle.mk,
        adamsTower, Category.id_comp] using hφ

    have twoCell_comparison_bottom {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
        {X : C} (i : SphereSpectrum ⟶ X) (φ : X ⟶ H.HF2)
        (hiφ : i ≫ φ = H.unit) :
        Mod2Homology.pushforward H φ 0
          (Mod2Homology.pushforward H i 0
            ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ adamsUnit H.unit SphereSpectrum)) =
          cooperationUnit H := by
      change (((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ adamsUnit H.unit SphereSpectrum) ≫
        H.HF2 ◁ i) ≫ H.HF2 ◁ φ = _
      rw [Category.assoc, Category.assoc, ← whiskerLeft_comp]
      erw [mod2AdamsUnit_naturality H (i ≫ φ)]
      rw [hiφ]
      simp [cooperationUnit, Mod2EilenbergMacLane.unit]

    have twoCell_comparison_connecting {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
        (d : ℤ) (α : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (a : Sphere (C := C) (d - 1) ⟶ adamsTower H.unit SphereSpectrum 1)
        (φ : HasFunctorialCofiber.cofib α ⟶ H.HF2 ⊗ SphereSpectrum)
        (hδ : HasFunctorialCofiber.cofibδ α ≫ (shiftFunctor C (1 : ℤ)).map a =
          φ ≫ adamsResolutionConnecting H.unit SphereSpectrum 0)
        (z : Mod2Homology H d (HasFunctorialCofiber.cofib α)) :
        adamsHomologyBoundary H SphereSpectrum d (Mod2Homology.pushforward H φ d z) =
          Mod2Homology.pushforward H a (d - 1)
            (mod2HomologyConnecting H (HoCofiberSequence.ofMorphism α) d z) := by
      let T := (HoCofiberSequence.ofMorphism α).map (tensorLeft H.HF2)
      let U := adamsHomologySequence H SphereSpectrum
      have hlast : (H.HF2 ◁ φ) ≫ U.h = T.h ≫ (H.HF2 ◁ a)⟦(1 : ℤ)⟧' := by
        change (H.HF2 ◁ φ) ≫ (H.HF2 ◁ adamsResolutionConnecting H.unit SphereSpectrum 0) ≫ _ =
          ((H.HF2 ◁ HasFunctorialCofiber.cofibδ α) ≫ _) ≫ _
        rw [← Category.assoc, ← whiskerLeft_comp, ← hδ, whiskerLeft_comp, Category.assoc]
        have hn := ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.naturality a
        change (H.HF2 ◁ (shiftFunctor C (1 : ℤ)).map a) ≫
            ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app
              (adamsTower H.unit SphereSpectrum 1) =
          ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app (Sphere (C := C) (d - 1)) ≫
            (shiftFunctor C (1 : ℤ)).map (H.HF2 ◁ a) at hn
        simpa only [Category.assoc, U, adamsHomologySequence,
          HoCofiberSequence.ofMorphism, adamsTower] using congrArg
          (fun f => (H.HF2 ◁ HasFunctorialCofiber.cofibδ α) ≫ f) hn
      exact connectingHomomorphism_naturality T U (H.HF2 ◁ a) (H.HF2 ◁ φ) hlast d z

    have twoCell_comparison_top_boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
        (d : ℤ) (α : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (a : Sphere (C := C) (d - 1) ⟶ adamsTower H.unit SphereSpectrum 1)
        (φ : HasFunctorialCofiber.cofib α ⟶ H.HF2 ⊗ SphereSpectrum)
        (hδ : HasFunctorialCofiber.cofibδ α ≫ (shiftFunctor C (1 : ℤ)).map a =
          φ ≫ adamsResolutionConnecting H.unit SphereSpectrum 0)
        (z : Mod2Homology H d (HasFunctorialCofiber.cofib α))
        (hz : mod2HomologyConnecting H (HoCofiberSequence.ofMorphism α) d z =
          adamsUnit H.unit (Sphere (C := C) (d - 1))) :
        adamsHomologyBoundary H SphereSpectrum d (Mod2Homology.pushforward H φ d z) =
          a ≫ adamsUnit H.unit (adamsTower H.unit SphereSpectrum 1) := by
      rw [twoCell_comparison_connecting H d α a φ hδ z, hz]
      exact mod2AdamsUnit_naturality H a

    have twoCell_comparison_top_cooperation {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)
        (d : ℤ) (hd : d ≠ 0)
        (α : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (a : Sphere (C := C) (d - 1) ⟶ adamsTower H.unit SphereSpectrum 1)
        (φ : HasFunctorialCofiber.cofib α ⟶ H.HF2 ⊗ SphereSpectrum)
        (hδ : HasFunctorialCofiber.cofibδ α ≫ (shiftFunctor C (1 : ℤ)).map a =
          φ ≫ adamsResolutionConnecting H.unit SphereSpectrum 0)
        (z : Mod2Homology H d (HasFunctorialCofiber.cofib α))
        (hz : mod2HomologyConnecting H (HoCofiberSequence.ofMorphism α) d z =
          adamsUnit H.unit (Sphere (C := C) (d - 1))) :
        Mod2Homology.pushforward H (φ ≫ (ρ_ H.HF2).hom) d z =
          (sphereFirstTowerHomologyEquiv H R d
            (a ≫ adamsUnit H.unit (adamsTower H.unit SphereSpectrum 1))).val := by
      rw [← twoCell_comparison_top_boundary H d α a φ hδ z hz,
        sphereFirstTowerHomologyEquiv_boundary]
      have hzero : adamsHomologyAction H R SphereSpectrum d
          (Mod2Homology.pushforward H φ d z) = 0 :=
        (sphereHomologySubsingleton H d hd).elim _ _
      rw [hzero, map_zero, sub_zero]
      change z ≫ H.HF2 ◁ (φ ≫ (ρ_ H.HF2).hom) =
        (z ≫ H.HF2 ◁ φ) ≫ H.HF2 ◁ (ρ_ H.HF2).hom
      rw [whiskerLeft_comp, Category.assoc]

    let sphereZeroCoordinate {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] (R : Mod2RingStructure H)  : mod2HomologyF2 H R 0 SphereSpectrum ≃ₗ[ZMod 2] ZMod 2 :=
      (sphereHomologyCoefficientF2Equiv H R 0).trans (mod2Pi0LinearEquiv H R)

    have sphereZeroCoordinate_unit {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  :
        sphereZeroCoordinate H R
          ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ adamsUnit H.unit SphereSpectrum) = 1 := by
      change H.pi0Equiv (((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫
        adamsUnit H.unit SphereSpectrum) ≫ (ρ_ H.HF2).hom) = 1
      have hu : adamsUnit H.unit (SphereSpectrum : C) ≫ (ρ_ H.HF2).hom = H.unit := by
        simp only [adamsUnit, Category.assoc, rightUnitor_naturality,
          ← unitors_equal, Iso.inv_hom_id_assoc]
      rw [Category.assoc, hu]
      simp [Mod2EilenbergMacLane.unit]

    have tensor_zero_of_first_filtration {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [MonoidalPreadditive C] [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  {X Y : C} (f : X ⟶ Y)
        (hf : AdamsFiltrationAtLeast H f 1) : H.HF2 ◁ f = 0 := by
      obtain ⟨l, hl⟩ := hf
      rw [← hl, whiskerLeft_comp,
        mod2_adamsTowerMap_eq_zero H R Y 0 1 (by decide), comp_zero]

    have tensorCoaction_apply {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (X : C) (n : ℤ) (x : Mod2Homology H n X) :
        mod2TensorCoaction H R K X n x = K.comparison X n (mod2CoactionMap H X n x) := rfl

    have tensorCoaction_counit {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (X : C) (n : ℤ) (x : Mod2Homology H n X) :
        cooperationTensorAugmentation H R (fun i => mod2HomologyF2 H R i X) n
          (mod2TensorCoaction H R K X n x) = x := by
      rw [tensorCoaction_apply, K.action_comparison]
      change (x ≫ mod2Coaction H X) ≫ mod2FreeAction H R X = x
      rw [Category.assoc, mod2Coaction_counit, Category.comp_id]

    have tensorCoaction_naturality {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  {X Y : C} (f : X ⟶ Y) (n : ℤ)
        (x : Mod2Homology H n X) :
        mod2TensorCoaction H R K Y n (Mod2Homology.pushforward H f n x) =
          cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X)
            (fun i => (mod2HomologyF2Map H R f i).hom) n
            (mod2TensorCoaction H R K X n x) := by
      rw [tensorCoaction_apply, ← mod2CoactionMap_naturality, K.naturality]
      rfl

    have tensorUnit_naturality {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
        (V : ℤ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        {W : ℤ → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 2) (W i)]
        (f : ∀ i, V i →ₗ[ZMod 2] W i) (n : ℤ) (x : V n) :
        cooperationTensorMap H R V f n (cooperationTensorUnit H R V n x) =
          cooperationTensorUnit H R W n (f n x) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      have hc (i j : ℤ) (h : i = j) (z : V i) :
          f j ((LinearEquiv.cast (R := ZMod 2) (M := V) h) z) =
            (LinearEquiv.cast (R := ZMod 2) (M := W) h) (f i z) := by
        subst j
        rfl
      simp [cooperationTensorUnit, cooperationTensorMap, gradedTensorMapRight]
      exact congrArg (fun z : W (n - 0) =>
        DirectSum.lof (ZMod 2) ℤ (fun i => Mod2Cooperations H i ⊗[ZMod 2] W (n - i)) 0
          (cooperationUnit H ⊗ₜ[ZMod 2] z)) (hc n (n - 0) (sub_zero n).symm x)

    -- Cancelling a fixed nonzero factor requires no axiom about this coaction.
    -- Here a concrete linear functional provides the inverse on elementary tensors.

    have pureTensorCoefficient_injective
        {A W : Type} [AddCommGroup A] [AddCommGroup W]
        [Module (ZMod 2) A] [Module (ZMod 2) W]
        (y : W) (ev : W →ₗ[ZMod 2] ZMod 2) (hy : ev y = 1) :
        Function.Injective (fun a : A => a ⊗ₜ[ZMod 2] y) := by
      intro a b hab
      have h := congrArg (fun z => TensorProduct.rid (ZMod 2) A (ev.lTensor A z)) hab
      simpa [hy] using h

    -- Markdown §2.5: once degree support gives a two-term coaction expansion,
    -- the actual triangle comparison φ identifies its unknown coefficient.
    -- All variables here are actual mod-2 homology classes/cooperations.

    have coaction_coefficient_identification {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
        {X : C} (φ : X ⟶ H.HF2) (d : ℤ)
        (ed : mod2HomologyF2 H R d X)
        (e0 : mod2HomologyF2 H R (d - d) X)
        (u0 : mod2HomologyF2 H R (d - d) H.HF2)
        (ev : mod2HomologyF2 H R (d - d) H.HF2 →ₗ[ZMod 2] ZMod 2)
        (hu0 : ev u0 = 1)
        (b c : mod2HomologyF2 H R d H.HF2)
        (hφd : Mod2Homology.pushforward H φ d ed = b)
        (hφ0 : Mod2Homology.pushforward H φ (d - d) e0 = u0)
        (hprimitive : mod2TensorCoaction H R K H.HF2 d b =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) d b +
            DirectSum.lof (ZMod 2) ℤ _ d (b ⊗ₜ[ZMod 2] u0))
        (hexpansion : mod2TensorCoaction H R K X d ed =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) d ed +
            DirectSum.lof (ZMod 2) ℤ _ d (c ⊗ₜ[ZMod 2] e0)) :
        c = b := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      have hnat := tensorCoaction_naturality H R K φ d ed
      rw [hφd, hprimitive, hexpansion, map_add] at hnat
      erw [tensorUnit_naturality H R (fun i => mod2HomologyF2 H R i X) (fun i => (mod2HomologyF2Map H R φ i).hom) d ed] at hnat
      change _ = cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) d
        (Mod2Homology.pushforward H φ d ed) + _ at hnat
      rw [hφd] at hnat
      have hsum := add_left_cancel hnat
      simp only [cooperationTensorMap, gradedTensorMapRight, DirectSum.lmap_lof,
        TensorProduct.map_tmul, LinearMap.id_apply] at hsum
      change DirectSum.lof (ZMod 2) ℤ
          (fun i => mod2HomologyF2 H R i H.HF2 ⊗[ZMod 2]
            mod2HomologyF2 H R (d - i) H.HF2) d (b ⊗ₜ[ZMod 2] u0) =
        DirectSum.lof (ZMod 2) ℤ
          (fun i => mod2HomologyF2 H R i H.HF2 ⊗[ZMod 2]
            mod2HomologyF2 H R (d - i) H.HF2) d
          (c ⊗ₜ[ZMod 2] Mod2Homology.pushforward H φ (d - d) e0) at hsum
      rw [hφ0] at hsum
      have ht : b ⊗ₜ[ZMod 2] u0 = c ⊗ₜ[ZMod 2] u0 := by
        have he := congrArg (fun z => z d) hsum
        simpa only [DirectSum.lof_apply] using he
      exact (pureTensorCoefficient_injective u0 ev hu0 ht).symm

    have directSum_two_decompose
        (A : ℤ → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module (ZMod 2) (A i)]
        (a b : ℤ) (hab : a ≠ b)
        (h : ∀ i, i ≠ a → i ≠ b → Subsingleton (A i)) (z : ⨁ i, A i) :
        z = DirectSum.lof (ZMod 2) ℤ A a (z a) + DirectSum.lof (ZMod 2) ℤ A b (z b) := by
      ext i
      by_cases hia : i = a
      · subst i
        change z a = (DirectSum.lof (ZMod 2) ℤ A a (z a)) a +
          (DirectSum.lof (ZMod 2) ℤ A b (z b)) a
        have hz : (DirectSum.lof (ZMod 2) ℤ A b (z b)) a = 0 :=
          DirectSum.of_eq_of_ne b a (z b) hab
        rw [DirectSum.lof_apply, hz, add_zero]
      · by_cases hib : i = b
        · subst i
          change z b = (DirectSum.lof (ZMod 2) ℤ A a (z a)) b +
            (DirectSum.lof (ZMod 2) ℤ A b (z b)) b
          have hz : (DirectSum.lof (ZMod 2) ℤ A a (z a)) b = 0 :=
            DirectSum.of_eq_of_ne a b (z a) (Ne.symm hab)
          rw [DirectSum.lof_apply, hz, zero_add]
        · letI := h i hia hib
          exact Subsingleton.elim _ _

    let cooperationZeroEquiv {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  : mod2HomologyF2 H R 0 H.HF2 ≃ₗ[ZMod 2] ZMod 2 := by
      letI := mod2HomologyModule H R 0 H.HF2
      letI := mod2HF2HomotopyModule H R 0
      have hs : Subsingleton (LinearMap.ker (cooperationCounitF2 H R 0)) := by
        letI : IsEmpty (PositiveMonomial 0) :=
          ⟨fun d => (lt_irrefl 0) (positiveMonomial_degree_pos d)⟩
        exact (B.basis 0).repr.injective.subsingleton
      have hinj : Function.Injective (cooperationCounitF2 H R 0) := by
        apply LinearMap.ker_eq_bot.mp
        apply bot_unique
        intro x hx
        change x = 0
        exact congrArg Subtype.val (hs.elim (⟨x, hx⟩ :
          LinearMap.ker (cooperationCounitF2 H R 0)) 0)
      exact (LinearEquiv.ofBijective (cooperationCounitF2 H R 0)
        ⟨hinj, cooperationCounit_surjective H R 0⟩).trans (mod2Pi0LinearEquiv H R)

    have cooperationZeroEquiv_unit {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  : cooperationZeroEquiv H R B (cooperationUnit H) = 1 := by
      change H.pi0Equiv (cooperationCounit H R 0 (cooperationUnit H)) = 1
      rw [cooperationCounit_unit, AddEquiv.apply_symm_apply]

    -- For a graded module supported only in degrees 0,d, every total-degree-d
    -- tensor has exactly a unit part and a coefficient times its bottom basis.
    -- No claim about a coaction is assumed in this linear-algebra decomposition.

    have cooperation_twoCell_decompose {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)
        (V : ℤ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (d : ℤ) (hd : d ≠ 0)
        (hV : ∀ i, i ≠ 0 → i ≠ d → Subsingleton (V i))
        (e0 : V (d - d) ≃ₗ[ZMod 2] ZMod 2)
        (z : cooperationTensor H R V d) :
        ∃ (w : V d) (c : mod2HomologyF2 H R d H.HF2),
          z = cooperationTensorUnit H R V d w +
            DirectSum.lof (ZMod 2) ℤ _ d (c ⊗ₜ[ZMod 2] e0.symm 1) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      let L : (mod2HomologyF2 H R 0 H.HF2 ⊗[ZMod 2] V (d - 0)) ≃ₗ[ZMod 2] V d :=
        ((TensorProduct.congr (cooperationZeroEquiv H R B)
          (LinearEquiv.refl (ZMod 2) (V (d - 0)))).trans
          (TensorProduct.lid (ZMod 2) (V (d - 0)))).trans
          (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero d))
      let T : (Mod2Cooperations H d ⊗[ZMod 2] V (d - d)) ≃ₗ[ZMod 2]
          Mod2Cooperations H d :=
        (TensorProduct.congr (LinearEquiv.refl (ZMod 2) _) e0).trans
          (TensorProduct.rid (ZMod 2) _)
      refine ⟨L (z 0), T (z d), ?_⟩
      have hdec := directSum_two_decompose
        (fun i => Mod2Cooperations H i ⊗[ZMod 2] V (d - i)) 0 d (Ne.symm hd)
        (fun i hi0 hid => by
          letI := hV (d - i) (by omega) (by omega)
          infer_instance) z
      have hcast (i j : ℤ) (h : i = j) (w : V j) :
          (LinearEquiv.cast (R := ZMod 2) (M := V) h)
            ((LinearEquiv.cast (R := ZMod 2) (M := V) h.symm) w) = w := by
        subst j
        rfl
      have hleft : z 0 = cooperationUnit H ⊗ₜ[ZMod 2]
          (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero d).symm) (L (z 0)) := by
        have hL (w : V d) : L (cooperationUnit H ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero d).symm) w) = w := by
          let cw := (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero d).symm) w
          have ht := TensorProduct.congr_tmul (cooperationZeroEquiv H R B)
            (LinearEquiv.refl (ZMod 2) (V (d - 0)))
            (cooperationUnit H : mod2HomologyF2 H R 0 H.HF2) cw
          have ht' := congrArg (fun z : ZMod 2 ⊗[ZMod 2] V (d - 0) =>
            (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero d))
              (TensorProduct.lid (ZMod 2) (V (d - 0)) z)) ht
          change L (cooperationUnit H ⊗ₜ[ZMod 2] cw) =
            (LinearEquiv.cast (R := ZMod 2) (M := V) (sub_zero d))
              ((cooperationZeroEquiv H R B (cooperationUnit H)) • cw) at ht'
          rw [cooperationZeroEquiv_unit H R B, one_smul] at ht'
          exact ht'.trans (hcast (d - 0) d (sub_zero d) w)
        apply L.injective
        rw [hL]
      have hright : z d = T (z d) ⊗ₜ[ZMod 2] e0.symm 1 := by
        have hT (a : Mod2Cooperations H d) : T (a ⊗ₜ[ZMod 2] e0.symm 1) = a := by
          dsimp only [T, LinearEquiv.trans_apply]
          rw [TensorProduct.congr_tmul]
          simp only [LinearEquiv.refl_apply, LinearEquiv.apply_symm_apply,
            TensorProduct.rid_tmul, one_smul]
        apply T.injective
        rw [hT]
      rw [hleft, hright] at hdec
      exact hdec

    have positiveTensor_augmentation_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
        (V : ℤ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (n k : ℤ) (hk : k ≠ 0) (a : Mod2Cooperations H k) (x : V (n - k)) :
        letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
          fun i => mod2HomologyModule H R i H.HF2
        cooperationTensorAugmentation H R V n
          (DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x)) = 0 := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
        fun i => mod2HF2HomotopyModule H R i
      simp only [cooperationTensorAugmentation, LinearMap.comp_apply,
        cooperationTensorCounit, gradedTensorMap_lof_tmul,
        cooperationCounitF2_eq_zero_of_ne H R k hk, LinearMap.zero_apply,
        TensorProduct.zero_tmul, map_zero]

    -- Markdown §2.5: the unit coefficient is forced by the *actual* counit.

    have twoCell_coaction_expansion {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  (K : Mod2CooperationKunneth H R)
        (X : C) (d : ℤ) (hd : d ≠ 0)
        (hX : ∀ i, i ≠ 0 → i ≠ d → Subsingleton (Mod2Homology H i X))
        (e0 : mod2HomologyF2 H R (d - d) X ≃ₗ[ZMod 2] ZMod 2)
        (ed : mod2HomologyF2 H R d X) :
        ∃ c : mod2HomologyF2 H R d H.HF2,
          mod2TensorCoaction H R K X d ed =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) d ed +
              DirectSum.lof (ZMod 2) ℤ _ d (c ⊗ₜ[ZMod 2] e0.symm 1) := by
      obtain ⟨w, c, hc⟩ := cooperation_twoCell_decompose H R B
        (fun i => mod2HomologyF2 H R i X) d hd hX e0
        (mod2TensorCoaction H R K X d ed)
      have he := congrArg (cooperationTensorAugmentation H R
        (fun i => mod2HomologyF2 H R i X) d) hc
      have hactual : cooperationTensorAugmentation H R
          (fun i => mod2HomologyF2 H R i X) d
          (mod2TensorCoaction H R K X d ed) = ed := by
        change cooperationTensorAugmentation H R _ d
          (K.comparison X d (mod2CoactionMap H X d ed)) = ed
        rw [K.action_comparison]
        change (ed ≫ mod2Coaction H X) ≫ mod2FreeAction H R X = ed
        rw [Category.assoc, mod2Coaction_counit, Category.comp_id]
      rw [hactual, map_add, cooperationTensorUnit_augmentation,
        positiveTensor_augmentation_zero H R _ d d hd, add_zero] at he
      exact ⟨c, he ▸ hc⟩

    have homologyPushforward_cast {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  {X Y : C} (f : X ⟶ Y)
        (i j : ℤ) (h : i = j) (x : mod2HomologyF2 H R i X) :
        Mod2Homology.pushforward H f j
          ((LinearEquiv.cast (R := ZMod 2) (M := fun k => mod2HomologyF2 H R k X) h) x) =
        (LinearEquiv.cast (R := ZMod 2) (M := fun k => mod2HomologyF2 H R k Y) h)
          (Mod2Homology.pushforward H f i x) := by
      subst j
      rfl

    have homologyCast_cancel {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)  (X : C) (i j : ℤ) (h : i = j)
        (x : mod2HomologyF2 H R j X) :
        (LinearEquiv.cast (R := ZMod 2) (M := fun k => mod2HomologyF2 H R k X) h)
          ((LinearEquiv.cast (R := ZMod 2) (M := fun k => mod2HomologyF2 H R k X) h.symm) x) = x := by
      subst j
      rfl

    -- This is the actual two-cell theorem required in Markdown §2.5.
    -- For d=1,2 the singleton hp and hprimitive are finite Milnor calculations
    -- for the same B and K; neither is a fresh coaction hypothesis on the cone.

    have twoCell_actual_coaction {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R) (K : Mod2CooperationKunneth H R)
        (d : ℤ) (hd : d ≠ 0) (p : PositiveMonomial d)
        (hp : ∀ q : PositiveMonomial d, q = p)
        (α : Sphere (C := C) (d - 1) ⟶ SphereSpectrum)
        (hF1 : AdamsFiltrationAtLeast H α 1)
        (hF2 : ¬ AdamsFiltrationAtLeast H α 2)
        (hprimitive :
          letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
            fun i => mod2HomologyModule H R i H.HF2
          mod2TensorCoaction H R K H.HF2 d (B.basis d p).val =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) d (B.basis d p).val +
            DirectSum.lof (ZMod 2) ℤ _ d
              (((B.basis d p).val : mod2HomologyF2 H R d H.HF2) ⊗ₜ[ZMod 2]
              (LinearEquiv.cast (R := ZMod 2)
                (M := fun i => mod2HomologyF2 H R i H.HF2) (sub_self d).symm)
                (cooperationUnit H))) :
        letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
          fun i => mod2HomologyModule H R i H.HF2
        ∃ (ed : mod2HomologyF2 H R d (HasFunctorialCofiber.cofib α))
          (q0 : mod2HomologyF2 H R 0 (HasFunctorialCofiber.cofib α) ≃ₗ[ZMod 2] ZMod 2),
          ed ≠ 0 ∧
          mod2HomologyConnecting H (HoCofiberSequence.ofMorphism α) d ed =
            adamsUnit H.unit (Sphere (C := C) (d - 1)) ∧
          q0 (Mod2Homology.pushforward H (HasFunctorialCofiber.cofibι α) 0
            ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ adamsUnit H.unit SphereSpectrum)) = 1 ∧
          mod2TensorCoaction H R K (HasFunctorialCofiber.cofib α) d ed =
            cooperationTensorUnit H R
              (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α)) d ed +
              DirectSum.lof (ZMod 2) ℤ _ d
                (((B.basis d p).val : mod2HomologyF2 H R d H.HF2) ⊗ₜ[ZMod 2]
                (LinearEquiv.cast (R := ZMod 2)
                  (M := fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α))
                  (sub_self d).symm) (q0.symm 1)) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
        fun i => mod2HF2HomotopyModule H R i
      have hα : H.HF2 ◁ α = 0 := tensor_zero_of_first_filtration H R α hF1
      obtain ⟨a, ha⟩ := hF1
      obtain ⟨φ', hiφ', hδ⟩ := twoCell_comparison_to_unit H d α a ha
      let φ := φ' ≫ (ρ_ H.HF2).hom
      have hiφ : HasFunctorialCofiber.cofibι α ≫ φ = H.unit := by
        dsimp only [φ]
        rw [← Category.assoc, hiφ']
        simp only [adamsUnit, Category.assoc, rightUnitor_naturality,
          ← unitors_equal, Iso.inv_hom_id_assoc]
      let Etop := twoCell_top_equiv H R d hd α hα
      let ed := Etop.symm (adamsUnit H.unit (Sphere (C := C) (d - 1)))
      have hed : mod2HomologyConnecting H
          (HoCofiberSequence.ofMorphism α) d ed =
            adamsUnit H.unit (Sphere (C := C) (d - 1)) :=
        Etop.apply_symm_apply _
      let Ebottom := twoCell_bottom_equiv H R d hd α hα
      let q0 := Ebottom.symm.trans (sphereZeroCoordinate H R)
      let s0 : mod2HomologyF2 H R 0 SphereSpectrum :=
        (shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ adamsUnit H.unit SphereSpectrum
      have hq0 : q0 (Mod2Homology.pushforward H (HasFunctorialCofiber.cofibι α) 0 s0) = 1 := by
        change sphereZeroCoordinate H R (Ebottom.symm (Ebottom s0)) = 1
        rw [Ebottom.symm_apply_apply]
        exact sphereZeroCoordinate_unit H R
      have hbottom : q0.symm 1 =
          Mod2Homology.pushforward H (HasFunctorialCofiber.cofibι α) 0 s0 := by
        apply q0.injective
        rw [q0.apply_symm_apply, hq0]
      have hφ0 : Mod2Homology.pushforward H φ 0 (q0.symm 1) = cooperationUnit H := by
        rw [hbottom]
        exact twoCell_comparison_bottom H (HasFunctorialCofiber.cofibι α) φ hiφ
      have hφd : Mod2Homology.pushforward H φ d ed = (B.basis d p).val := by
        calc
          _ = (sphereFirstTowerHomologyEquiv H R d
              (a ≫ adamsUnit H.unit (adamsTower H.unit SphereSpectrum 1))).val :=
            twoCell_comparison_top_cooperation H R d hd α a φ' hδ ed hed
          _ = _ := firstLift_cooperation_identification H R B d p hp α hF2 a ha
      have hneq : ed ≠ 0 := by
        intro hz
        have hz' : (B.basis d p).val = 0 := by simpa only [hz, map_zero] using hφd.symm
        exact (B.basis d).ne_zero p (Subtype.ext hz')
      let e0 : mod2HomologyF2 H R (d - d) (HasFunctorialCofiber.cofib α) ≃ₗ[ZMod 2] ZMod 2 :=
        (LinearEquiv.cast (R := ZMod 2)
          (M := fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α)) (sub_self d)).trans q0
      let u0 : mod2HomologyF2 H R (d - d) H.HF2 :=
        (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i H.HF2)
          (sub_self d).symm) (cooperationUnit H)
      let ev : mod2HomologyF2 H R (d - d) H.HF2 →ₗ[ZMod 2] ZMod 2 :=
        ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i H.HF2)
          (sub_self d)).trans (cooperationZeroEquiv H R B)).toLinearMap
      have hu0 : ev u0 = 1 := by
        simp only [ev, u0, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
          homologyCast_cancel H R H.HF2 (d-d) 0 (sub_self d) (cooperationUnit H)]
        exact cooperationZeroEquiv_unit H R B
      have hφe0 : Mod2Homology.pushforward H φ (d - d) (e0.symm 1) = u0 := by
        change Mod2Homology.pushforward H φ (d - d)
          ((LinearEquiv.cast (R := ZMod 2)
            (M := fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α))
            (sub_self d).symm) (q0.symm 1)) = u0
        rw [homologyPushforward_cast, hφ0]
      obtain ⟨c, hc⟩ := twoCell_coaction_expansion H R B K (HasFunctorialCofiber.cofib α)
        d hd (twoCell_otherDegrees H d α) e0 ed
      have hcb : c = (B.basis d p).val :=
        coaction_coefficient_identification H R K φ d ed (e0.symm 1) u0 ev hu0
          (B.basis d p).val c hφd hφe0 hprimitive hc
      rw [hcb] at hc
      exact ⟨ed, q0, hneq, hed, hq0, hc⟩

    let boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ) :
        Mod2Homology H n T.Z →+ Mod2Homology H (n - 1) T.X :=
      connectingHomomorphism (T.map (tensorLeft H.HF2)) n

    -- The later cone maps are only known to vanish on homology. No inference
    -- from degreewise vanishing to a zero underlying H-smash map is needed.

    have bottom_injective_of_homology_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : Mod2Homology.pushforward H T.f n = 0) :
        Function.Injective (Mod2Homology.pushforward H T.g n) := by
      apply (injective_iff_map_eq_zero (Mod2Homology.pushforward H T.g n)).mpr
      intro y hy
      obtain ⟨x, hx⟩ := (les_homotopy_exact_f (T.map (tensorLeft H.HF2)) n y).mp hy
      have hx0 : inducedMap (T.map (tensorLeft H.HF2)).f n x = 0 := by
        change Mod2Homology.pushforward H T.f n x = 0
        rw [hf, AddMonoidHom.zero_apply]
      exact hx.symm.trans hx0

    have boundary_surjective_of_homology_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : Mod2Homology.pushforward H T.f (n - 1) = 0) :
        Function.Surjective (boundary H T n) := by
      intro x
      apply (lesHomotopyExactH (T.map (tensorLeft H.HF2)) n x).mp
      change Mod2Homology.pushforward H T.f (n - 1) x = 0
      rw [hf, AddMonoidHom.zero_apply]

    have boundary_injective_of_target_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hy : Subsingleton (Mod2Homology H n T.Y)) :
        Function.Injective (boundary H T n) := by
      apply (injective_iff_map_eq_zero (boundary H T n)).mpr
      intro z hz
      obtain ⟨y, hyz⟩ := (les_homotopy_exact_g (T.map (tensorLeft H.HF2)) n z).mp hz
      have hy0 : y = 0 := hy.elim _ _
      simpa only [hy0, map_zero] using hyz.symm

    let boundaryEquiv_of_homology_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H)  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : Mod2Homology.pushforward H T.f (n - 1) = 0)
        (hy : Subsingleton (Mod2Homology H n T.Y)) :
        mod2HomologyF2 H R n T.Z ≃ₗ[ZMod 2] mod2HomologyF2 H R (n - 1) T.X := by
      letI := mod2HomologyModule H R n T.Z
      letI := mod2HomologyModule H R (n - 1) T.X
      exact LinearEquiv.ofBijective ((boundary H T n).toZModLinearMap 2)
        ⟨boundary_injective_of_target_zero H T n hy,
          boundary_surjective_of_homology_zero H T n hf⟩

    let bottomEquiv_of_homology_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H)  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (hf : Mod2Homology.pushforward H T.f n = 0)
        (hx : Subsingleton (Mod2Homology H (n - 1) T.X)) :
        mod2HomologyF2 H R n T.Y ≃ₗ[ZMod 2] mod2HomologyF2 H R n T.Z :=
      LinearEquiv.ofBijective (mod2HomologyF2Map H R T.g n).hom
        ⟨bottom_injective_of_homology_zero H T n hf, fun z =>
          (les_homotopy_exact_g (T.map (tensorLeft H.HF2)) n z).mp (hx.elim _ _)⟩

    have pushforward_zero_of_disjoint_support {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C]  {X Y : C} (f : X ⟶ Y) (n : ℤ)
        (h : Subsingleton (Mod2Homology H n X) ∨ Subsingleton (Mod2Homology H n Y)) :
        Mod2Homology.pushforward H f n = 0 := by
      ext x
      rcases h with hx | hy
      · rw [hx.elim x 0, map_zero, AddMonoidHom.zero_apply]
      · exact hy.elim _ _

    -- Markdown §4, third cone: t_* in degree zero is forced to vanish by
    -- j_* surjective and (j≫t)_*=2_*=0; this uses actual pushforwards.

    have pushforward_zero_of_surjective_precomposition {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C]
        {A X Y : C} (j : A ⟶ X) (t : X ⟶ Y) (n : ℤ)
        (hj : Function.Surjective (Mod2Homology.pushforward H j n))
        (hjt : Mod2Homology.pushforward H (j ≫ t) n = 0) :
        Mod2Homology.pushforward H t n = 0 := by
      ext x
      obtain ⟨a, rfl⟩ := hj x
      have h := congrArg (fun f : Mod2Homology H n A →+ Mod2Homology H n Y => f a) hjt
      simpa only [Mod2Homology.pushforward, inducedMap, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, whiskerLeft_comp, Category.assoc, AddMonoidHom.zero_apply] using h

    have twice_map_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H)  {X Y : C} (f : X ⟶ Y) (n : ℤ) :
        Mod2Homology.pushforward H (2 • f) n = 0 := by
      ext x
      change x ≫ (tensorLeft H.HF2).map (2 • f) = 0
      rw [Functor.map_nsmul, Preadditive.comp_nsmul]
      exact mod2Homology_two_nsmul_zero H R n Y _

    have homology_boundary_factor {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (x : Mod2Homology H n T.Z) :
        connectingHomomorphism (T.map (tensorLeft H.HF2)) n x =
          mod2HomologyDesuspend H T.X n (Mod2Homology.pushforward H T.h n x) := by
      rw [connectingHomomorphism_eq_desuspend]
      simp only [HoCofiberSequence.map,
        mod2HomologyDesuspend, homotopyDesuspend, Mod2Homology.pushforward, inducedMap,
        AddMonoidHom.comp_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        Functor.id_obj, eqToHom_refl, Category.id_comp, Category.comp_id]
      change (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
        (shiftFunctor C (-1)).map (x ≫ H.HF2 ◁ T.h ≫ _) ≫ _ =
          (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
            (shiftFunctor C (-1)).map ((x ≫ H.HF2 ◁ T.h) ≫ _) ≫ _
      rw [Category.assoc]
      rfl

    have mapped_boundary_comp {C : Type 1} [StableHomotopyCategory.{1,0} C]  (T : HoCofiberSequence (C := C))
        (F G : C ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ]
        [F.IsTriangulated] [G.IsTriangulated]
        (n : ℤ) (x : HomotopyGroup n (G.obj (F.obj T.Z))) :
        connectingHomomorphism ((T.map F).map G) n x =
          connectingHomomorphism (T.map (F ⋙ G)) n x := by
      have hlast : 𝟙 _ ≫ (T.map (F ⋙ G)).h =
          ((T.map F).map G).h ≫ (𝟙 (G.obj (F.obj T.X)))⟦(1 : ℤ)⟧' := by
        simp [HoCofiberSequence.map, Functor.commShiftIso_comp_hom_app,
          Functor.map_comp, Category.assoc]
      have h := connectingHomomorphism_naturality ((T.map F).map G) (T.map (F ⋙ G))
        (𝟙 _) (𝟙 _) hlast n x
      simpa [inducedMap] using h.symm

    have mapped_boundary_naturality {C : Type 1} [StableHomotopyCategory.{1,0} C]  (T : HoCofiberSequence (C := C))
        (F G : C ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ]
        [F.IsTriangulated] [G.IsTriangulated]
        (α : F ⟶ G) [α.CommShift ℤ] (n : ℤ) (x : HomotopyGroup n (F.obj T.Z)) :
        connectingHomomorphism (T.map G) n (inducedMap (α.app T.Z) n x) =
          inducedMap (α.app T.X) (n - 1) (connectingHomomorphism (T.map F) n x) := by
      apply connectingHomomorphism_naturality (T.map F) (T.map G)
        (α.app T.X) (α.app T.Z) (n := n) (z := x)
      change α.app T.Z ≫ G.map T.h ≫ (G.commShiftIso (1 : ℤ)).hom.app T.X =
        (F.map T.h ≫ (F.commShiftIso (1 : ℤ)).hom.app T.X) ≫ _
      rw [← Category.assoc, ← α.naturality T.h, Category.assoc,
        ← NatTrans.shift_app_comm, ← Category.assoc]

    have double_homology_boundary_factor {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T : HoCofiberSequence (C := C)) (n : ℤ)
        (x : Mod2Homology H n (H.HF2 ⊗ T.Z)) :
        connectingHomomorphism ((T.map (tensorLeft H.HF2)).map (tensorLeft H.HF2)) n x =
          mod2DoubleHomologyDesuspend H T.X n
            (Mod2Homology.pushforward H (H.HF2 ◁ T.h) n x) := by
      rw [homology_boundary_factor]
      change mod2HomologyDesuspend H (H.HF2 ⊗ T.X) n
        (x ≫ H.HF2 ◁ (H.HF2 ◁ T.h ≫ _)) =
          mod2HomologyDesuspend H (H.HF2 ⊗ T.X) n
            ((x ≫ H.HF2 ◁ (H.HF2 ◁ T.h)) ≫ H.HF2 ◁ _)
      rw [whiskerLeft_comp, Category.assoc]

    have coaction_boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  [(mod2UnitNatTrans H).CommShift ℤ]
        (T : HoCofiberSequence (C := C)) (n : ℤ) (x : Mod2Homology H n T.Z) :
        connectingHomomorphism ((T.map (tensorLeft H.HF2)).map (tensorLeft H.HF2)) n
          (mod2CoactionMap H T.Z n x) =
        mod2CoactionMap H T.X (n - 1)
          (connectingHomomorphism (T.map (tensorLeft H.HF2)) n x) := by
      let F := tensorLeft H.HF2
      let α : F ⟶ F ⋙ F := F.leftUnitor.inv ≫ Functor.whiskerRight (mod2UnitNatTrans H) F
      have h := mapped_boundary_naturality T F (F ⋙ F) α n x
      change connectingHomomorphism ((T.map F).map F) n _ = _
      rw [mapped_boundary_comp]
      convert! h using 1 <;>
        simp [α, F, mod2CoactionMap, mod2Coaction, mod2UnitNatTrans] <;> rfl

    let boundaryF2 {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H)  (T : HoCofiberSequence (C := C)) (n : ℤ) :
        mod2HomologyF2 H R n T.Z →ₗ[ZMod 2] mod2HomologyF2 H R (n - 1) T.X :=
      letI := mod2HomologyModule H R n T.Z
      letI := mod2HomologyModule H R (n - 1) T.X
      let f : Mod2Homology H n T.Z →+ Mod2Homology H (n - 1) T.X :=
        connectingHomomorphism (T.map (tensorLeft H.HF2)) n
      f.toZModLinearMap 2

    have tensorLowerMap_comp {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H)  (V W U : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, AddCommGroup (W i)] [∀ i, AddCommGroup (U i)]
        [∀ i, Module (ZMod 2) (V i)] [∀ i, Module (ZMod 2) (W i)] [∀ i, Module (ZMod 2) (U i)]
        (f : ∀ i, V i →ₗ[ZMod 2] W i) (g : ∀ i, W i →ₗ[ZMod 2] U (i - 1)) (n : ℤ) :
        (cooperationTensorLowerMap H R W U g n).comp (cooperationTensorMap H R V f n) =
          cooperationTensorLowerMap H R V U (fun i => (g i).comp (f i)) n := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) := fun i => mod2HomologyModule H R i H.HF2
      exact KIP126.Algebra.gradedTensorLowerMap_comp (Mod2Cooperations H) f g n

    have kunneth_boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        (T : HoCofiberSequence (C := C)) (n : ℤ)
        (x : Mod2Homology H n (H.HF2 ⊗ T.Z)) :
        K.comparison T.X (n - 1)
          (connectingHomomorphism ((T.map (tensorLeft H.HF2)).map (tensorLeft H.HF2)) n x) =
          cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i T.Z)
            (fun i => mod2HomologyF2 H R i T.X) (boundaryF2 H R T) n
            (K.comparison T.Z n x) := by
      rw [double_homology_boundary_factor, hK, K.naturality]
      have hg : (fun i => (mod2HomologyDesuspendF2 H R T.X i).comp
          ((mod2HomologyF2Map H R T.h i).hom)) = boundaryF2 H R T := by
        funext i
        ext z
        change mod2HomologyDesuspend H T.X i
          (Mod2Homology.pushforward H T.h i z) =
            connectingHomomorphism (T.map (tensorLeft H.HF2)) i z
        exact (homology_boundary_factor H T i z).symm
      rw [← LinearMap.comp_apply, tensorLowerMap_comp, hg]

    -- This is exactly the suspension/connecting compatibility used in §§3–4.

    have tensorCoaction_boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [MonoidalPreadditive C] (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  [(mod2UnitNatTrans H).CommShift ℤ]
        (hK : Mod2KunnethSuspensionCompatible H R K)
        (T : HoCofiberSequence (C := C)) (n : ℤ) (x : Mod2Homology H n T.Z) :
        mod2TensorCoaction H R K T.X (n - 1)
          (connectingHomomorphism (T.map (tensorLeft H.HF2)) n x) =
          cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i T.Z)
            (fun i => mod2HomologyF2 H R i T.X) (boundaryF2 H R T) n
            (mod2TensorCoaction H R K T.Z n x) := by
      rw [tensorCoaction_apply, ← coaction_boundary, kunneth_boundary H R K hK]
      rfl

    have compare_cones_of_factorization {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)]
        {A B X : C} (f : A ⟶ X) (g : B ⟶ X) (a : A ⟶ B)
        (ha : a ≫ g = f) :
        ∃ c : HasFunctorialCofiber.cofib f ⟶ HasFunctorialCofiber.cofib g,
          HasFunctorialCofiber.cofibι f ≫ c = HasFunctorialCofiber.cofibι g ∧
          HasFunctorialCofiber.cofibδ f ≫ (shiftFunctor C (1 : ℤ)).map a =
            c ≫ HasFunctorialCofiber.cofibδ g := by
      obtain ⟨c, hc, hδ⟩ := complete_distinguished_triangle_morphism
        (Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f))
        (Triangle.mk g (HasFunctorialCofiber.cofibι g) (HasFunctorialCofiber.cofibδ g))
        (HasFunctorialCofiber.cofib_distinguished f)
        (HasFunctorialCofiber.cofib_distinguished g) a (𝟙 X) (by
          change f ≫ 𝟙 X = a ≫ g
          simpa only [Category.comp_id] using ha.symm)
      refine ⟨c, ?_, hδ⟩
      change HasFunctorialCofiber.cofibι f ≫ c = 𝟙 X ≫ HasFunctorialCofiber.cofibι g at hc
      simpa only [Category.id_comp] using hc

    -- A zero composite gives the actual extension used to construct the
    -- three-cell object ruling out η²=0. Both cones are the selected cofibers.

    have double_cone_geometry {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)]
        {A B X : C} (f : A ⟶ B) (g : B ⟶ X) (hfg : f ≫ g = 0) :
        ∃ b : HasFunctorialCofiber.cofib f ⟶ X,
          HasFunctorialCofiber.cofibι f ≫ b = g ∧
          ∃ c : HasFunctorialCofiber.cofib g ⟶ HasFunctorialCofiber.cofib b,
            HasFunctorialCofiber.cofibι g ≫ c = HasFunctorialCofiber.cofibι b ∧
            HasFunctorialCofiber.cofibδ g ≫
                (shiftFunctor C (1 : ℤ)).map (HasFunctorialCofiber.cofibι f) =
              c ≫ HasFunctorialCofiber.cofibδ b := by
      obtain ⟨b, hb⟩ := (Triangle.mk f (HasFunctorialCofiber.cofibι f)
        (HasFunctorialCofiber.cofibδ f)).yoneda_exact₂
        (HasFunctorialCofiber.cofib_distinguished f) g hfg
      change g = HasFunctorialCofiber.cofibι f ≫ b at hb
      exact ⟨b, hb.symm, compare_cones_of_factorization g b
        (HasFunctorialCofiber.cofibι f) hb.symm⟩

    -- The actual Toda zero witness builds the four-cell object. No spectral
    -- sequence, Moss theorem, octahedral package, or independently chosen
    -- filtered object is substituted for these three cone triangles.

    have triple_cone_geometry {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)]
        {A B X Y : C} (f : A ⟶ B) (g : B ⟶ X) (h : X ⟶ Y)
        (hToda : KIP126.StableHomotopy.Toda.Relation 0 f g h) :
        ∃ (Q : C) (i : B ⟶ Q) (p : Q ⟶ A⟦(1 : ℤ)⟧)
          (_ : Triangle.mk f i p ∈ distTriang C)
          (b : Q ⟶ X) (t : HasFunctorialCofiber.cofib b ⟶ Y),
          i ≫ b = g ∧ b ≫ h = 0 ∧ HasFunctorialCofiber.cofibι b ≫ t = h ∧
          (∃ c : HasFunctorialCofiber.cofib g ⟶ HasFunctorialCofiber.cofib b,
            HasFunctorialCofiber.cofibι g ≫ c = HasFunctorialCofiber.cofibι b ∧
            HasFunctorialCofiber.cofibδ g ≫ (shiftFunctor C (1 : ℤ)).map i =
              c ≫ HasFunctorialCofiber.cofibδ b) ∧
          (∃ c : HasFunctorialCofiber.cofib h ⟶ HasFunctorialCofiber.cofib t,
            HasFunctorialCofiber.cofibι h ≫ c = HasFunctorialCofiber.cofibι t ∧
            HasFunctorialCofiber.cofibδ h ≫
                (shiftFunctor C (1 : ℤ)).map (HasFunctorialCofiber.cofibι b) =
              c ≫ HasFunctorialCofiber.cofibδ t) := by
      obtain ⟨Q, i, p, hT, b, hb, hb0⟩ := hToda
      have hbh : b ≫ h = 0 := by simpa only [comp_zero] using hb0.symm
      obtain ⟨t, ht⟩ := (Triangle.mk b (HasFunctorialCofiber.cofibι b)
        (HasFunctorialCofiber.cofibδ b)).yoneda_exact₂
        (HasFunctorialCofiber.cofib_distinguished b) h hbh
      change h = HasFunctorialCofiber.cofibι b ≫ t at ht
      exact ⟨Q, i, p, hT, b, t, hb, hbh, ht.symm,
        compare_cones_of_factorization g b i hb,
        compare_cones_of_factorization h t (HasFunctorialCofiber.cofibι b) ht.symm⟩

    have tensor_rank_one
        {A V : Type} [AddCommGroup A] [AddCommGroup V]
        [Module (ZMod 2) A] [Module (ZMod 2) V]
        (q : V ≃ₗ[ZMod 2] ZMod 2) (z : A ⊗[ZMod 2] V) :
        ∃ a : A, z = a ⊗ₜ[ZMod 2] q.symm 1 := by
      let e : A ⊗[ZMod 2] V ≃ₗ[ZMod 2] A :=
        (TensorProduct.congr (LinearEquiv.refl (ZMod 2) A) q).trans
          (TensorProduct.rid (ZMod 2) A)
      refine ⟨e z, ?_⟩
      apply e.injective
      change e z = TensorProduct.rid (ZMod 2) A
        (TensorProduct.congr (LinearEquiv.refl (ZMod 2) A) q
          (e z ⊗ₜ[ZMod 2] q.symm 1))
      rw [TensorProduct.congr_tmul]
      simp only [LinearEquiv.refl_apply, LinearEquiv.apply_symm_apply,
        TensorProduct.rid_tmul, one_smul]

    -- Finite-cell support implies a complete expansion, including every
    -- coefficient allowed by the degree. Used for (0,2,4) and (0,1,3,4).

    have directSum_supported_decomposition
        (A : ℤ → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module (ZMod 2) (A i)]
        (S : Finset ℤ) (hS : ∀ i, i ∉ S → Subsingleton (A i))
        (z : ⨁ i, A i) :
        z = ∑ i ∈ S, DirectSum.lof (ZMod 2) ℤ A i (z i) := by
      classical
      have hs : z.support ⊆ S := by
        intro i hi
        by_contra his
        exact (DFinsupp.mem_support_iff.mp hi) ((hS i his).elim _ _)
      calc
        z = ∑ i ∈ z.support, DirectSum.lof (ZMod 2) ℤ A i (z i) :=
          (DirectSum.sum_support_of z).symm
        _ = _ := Finset.sum_subset hs (fun i hiS hiz => by
          have hi0 : z i = 0 := by
            simpa only [DFinsupp.mem_support_iff, not_not] using hiz
          rw [hi0, map_zero])

    have tensorCoaction_coassoc {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (hD : Mod2KunnethDiagonalCompatible H R K)
        (X : C) (n : ℤ) (x : mod2HomologyF2 H R n X) :
        cooperationTensorComultiply H R K (fun i => mod2HomologyF2 H R i X) n
          (mod2TensorCoaction H R K X n x) =
          cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X)
            (mod2TensorCoaction H R K X) n (mod2TensorCoaction H R K X n x) := by
      rw [tensorCoaction_apply, ← hD]
      change cooperationTensorMap H R _ (fun i => (K.comparison X i).toLinearMap) n
        (mod2TensorCoaction H R K (H.HF2 ⊗ X) n
          (Mod2Homology.pushforward H (adamsUnit H.unit X) n x)) = _
      rw [tensorCoaction_naturality, ← LinearMap.comp_apply, cooperationTensorMap_comp]
      rfl

    let rowProjection {R : Type} [CommRing R]  (A V : ℤ → Type)
        [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
        [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
        (q : V 0 →ₗ[R] R) (n : ℤ) : gradedTensor R A V n →ₗ[R] A n :=
      DirectSum.toModule R ℤ _ fun k =>
        if h : k = n then by
          subst k
          exact (TensorProduct.rid R (A n)).toLinearMap.comp
            ((q.comp (LinearEquiv.cast (R := R) (M := V) (sub_self n)).toLinearMap).lTensor (A n))
        else 0

    have rowProjection_lof_self {R : Type} [CommRing R] (A : ℤ → Type) (V : ℤ → Type) [(i : ℤ) → AddCommGroup (A i)] [(i : ℤ) → Module R (A i)] [(i : ℤ) → AddCommGroup (V i)] [(i : ℤ) → Module R (V i)] (q : V 0 →ₗ[R] R)  (n : ℤ) (a : A n) (x : V (n-n)) :
        rowProjection A V q n (DirectSum.lof R ℤ _ n (a ⊗ₜ[R] x)) =
          q ((LinearEquiv.cast (R := R) (M := V) (sub_self n)) x) • a := by
      simp [rowProjection]

    have rowProjection_lof_ne {R : Type} [CommRing R] (A : ℤ → Type) (V : ℤ → Type) [(i : ℤ) → AddCommGroup (A i)] [(i : ℤ) → Module R (A i)] [(i : ℤ) → AddCommGroup (V i)] [(i : ℤ) → Module R (V i)] (q : V 0 →ₗ[R] R)  (n k : ℤ) (hkn : k ≠ n) (a : A k) (x : V (n-k)) :
        rowProjection A V q n (DirectSum.lof R ℤ _ k (a ⊗ₜ[R] x)) = 0 := by
      simp [rowProjection, hkn]

    have cast_cast {R : Type} [CommRing R] (V : ℤ → Type) [(i : ℤ) → AddCommGroup (V i)] [(i : ℤ) → Module R (V i)]  (i j k : ℤ) (h : i = j) (h' : j = k) (x : V i) :
        (LinearEquiv.cast (R := R) (M := V) h')
          ((LinearEquiv.cast (R := R) (M := V) h) x) =
        (LinearEquiv.cast (R := R) (M := V) (h.trans h')) x := by
      subst j
      subst k
      rfl

    -- Evaluating the final tensor factor after reassociation is the same as
    -- evaluating it before reassociation. This is the matrix-coefficient step.

    have rowProjection_assoc {R : Type} [CommRing R] (A : ℤ → Type) (B : ℤ → Type) (V : ℤ → Type) [(i : ℤ) → AddCommGroup (A i)] [(i : ℤ) → Module R (A i)] [(i : ℤ) → AddCommGroup (B i)] [(i : ℤ) → Module R (B i)] [(i : ℤ) → AddCommGroup (V i)] [(i : ℤ) → Module R (V i)] (q : V 0 →ₗ[R] R)  (n : ℤ) :
        (gradedTensorMapRight A (rowProjection B V q) n).comp
            (gradedTensorAssoc A B V n) =
          rowProjection (gradedTensor R A B) V q n := by
      ext k j a b x i
      change (gradedTensorMapRight A (rowProjection B V q) n
        (gradedTensorAssoc A B V n
          (DirectSum.lof R ℤ _ k ((DirectSum.lof R ℤ _ j (a ⊗ₜ[R] b)) ⊗ₜ[R] x)))) i =
        (rowProjection (gradedTensor R A B) V q n
          (DirectSum.lof R ℤ _ k ((DirectSum.lof R ℤ _ j (a ⊗ₜ[R] b)) ⊗ₜ[R] x))) i
      apply congrArg (fun z : gradedTensor R A B n => z i)
      rw [gradedTensorAssoc_lof_tmul]
      simp only [gradedTensorMapRight, DirectSum.lmap_lof, LinearMap.lTensor_tmul]
      by_cases hkn : k = n
      · subst k
        rw [rowProjection_lof_self, rowProjection_lof_self]
        rw [cast_cast]
        simp only [TensorProduct.tmul_smul, map_smul]
      · rw [rowProjection_lof_ne _ _ _ _ _ (by omega), TensorProduct.tmul_zero, map_zero,
          rowProjection_lof_ne _ _ _ _ _ hkn]

    -- Evaluation commutes with every degree-preserving map on the first factor.

    have rowProjection_map {R : Type} [CommRing R] (A : ℤ → Type) (B : ℤ → Type) (V : ℤ → Type) [(i : ℤ) → AddCommGroup (A i)] [(i : ℤ) → Module R (A i)] [(i : ℤ) → AddCommGroup (B i)] [(i : ℤ) → Module R (B i)] [(i : ℤ) → AddCommGroup (V i)] [(i : ℤ) → Module R (V i)] (q : V 0 →ₗ[R] R)  (f : ∀ i, A i →ₗ[R] B i) (n : ℤ) :
        (rowProjection B V q n).comp (gradedTensorMap f V n) =
          (f n).comp (rowProjection A V q n) := by
      ext k a x
      change rowProjection B V q n
        (gradedTensorMap f V n (DirectSum.lof R ℤ _ k (a ⊗ₜ[R] x))) =
          f n (rowProjection A V q n (DirectSum.lof R ℤ _ k (a ⊗ₜ[R] x)))
      rw [gradedTensorMap_lof_tmul]
      by_cases hkn : k = n
      · subst k
        rw [rowProjection_lof_self, rowProjection_lof_self, map_smul]
      · rw [rowProjection_lof_ne _ _ _ _ _ hkn, rowProjection_lof_ne _ _ _ _ _ hkn,
          map_zero]

    let actualRow {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (X : C) (q : mod2HomologyF2 H R 0 X →ₗ[ZMod 2] ZMod 2) (n : ℤ) :
        mod2HomologyF2 H R n X →ₗ[ZMod 2] mod2HomologyF2 H R n H.HF2 :=
      (rowProjection (fun i => mod2HomologyF2 H R i H.HF2) (fun i => mod2HomologyF2 H R i X) q n).comp
        (mod2TensorCoaction H R K X n)

    have row_comultiply {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (q : V 0 →ₗ[ZMod 2] ZMod 2) (n : ℤ) (z : cooperationTensor H R V n) :
        cooperationTensorMap H R (cooperationTensor H R V)
          (rowProjection (fun i => mod2HomologyF2 H R i H.HF2) V q) n
          (cooperationTensorComultiply H R K V n z) =
        cooperationTensorDiagonal H R K n (rowProjection (fun i => mod2HomologyF2 H R i H.HF2) V q n z) := by
      change (gradedTensorMapRight (fun i => mod2HomologyF2 H R i H.HF2) (rowProjection (fun i => mod2HomologyF2 H R i H.HF2) V q) n)
        (gradedTensorAssoc (fun i => mod2HomologyF2 H R i H.HF2) (fun i => mod2HomologyF2 H R i H.HF2) V n
          (gradedTensorMap (cooperationTensorDiagonal H R K) V n z)) = _
      rw [← LinearMap.comp_apply, rowProjection_assoc]
      exact LinearMap.congr_fun
        (rowProjection_map (fun i => mod2HomologyF2 H R i H.HF2)
          (gradedTensor (ZMod 2) (fun i => mod2HomologyF2 H R i H.HF2)
            (fun i => mod2HomologyF2 H R i H.HF2)) V q
          (cooperationTensorDiagonal H R K) n) z

    -- This is the actual comodule law for the bottom row; it is derived from
    -- coassociativity, not assumed as a replacement for the spectrum's coaction.

    have actualRow_coaction {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (hD : Mod2KunnethDiagonalCompatible H R K)
        (X : C) (q : mod2HomologyF2 H R 0 X →ₗ[ZMod 2] ZMod 2)
        (n : ℤ) (x : mod2HomologyF2 H R n X) :
        cooperationTensorDiagonal H R K n (actualRow H R K X q n x) =
          cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X)
            (actualRow H R K X q) n (mod2TensorCoaction H R K X n x) := by
      have h := congrArg
        (cooperationTensorMap H R (cooperationTensor H R (fun i => mod2HomologyF2 H R i X))
          (rowProjection (fun i => mod2HomologyF2 H R i H.HF2) (fun i => mod2HomologyF2 H R i X) q) n)
        (tensorCoaction_coassoc H R K hD X n x)
      rw [row_comultiply] at h
      have hc := LinearMap.congr_fun
        (cooperationTensorMap_comp H R (fun i => mod2HomologyF2 H R i X)
          (mod2TensorCoaction H R K X)
          (rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
            (fun i => mod2HomologyF2 H R i X) q) n)
        (mod2TensorCoaction H R K X n x)
      exact h.trans hc

    have zeroTensor_unit_factor {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
        (z : mod2HomologyF2 H R 0 H.HF2 ⊗[ZMod 2] V) :
        letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
          fun i => mod2HomologyModule H R i H.HF2
        ∃ w : V, z = (cooperationUnit H : mod2HomologyF2 H R 0 H.HF2) ⊗ₜ[ZMod 2] w := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      let q := cooperationZeroEquiv H R B
      have hq : q.symm 1 = cooperationUnit H := by
        apply q.injective
        rw [q.apply_symm_apply]
        exact (cooperationZeroEquiv_unit H R B).symm
      obtain ⟨w, hw⟩ := tensor_rank_one q
        (TensorProduct.comm (ZMod 2) (mod2HomologyF2 H R 0 H.HF2) V z)
      refine ⟨w, ?_⟩
      apply (TensorProduct.comm (ZMod 2) (mod2HomologyF2 H R 0 H.HF2) V).injective
      rw [hw, hq, TensorProduct.comm_tmul]

    -- The degree-four expansion required by the three-cell η² cone.
    -- The two lower coordinates are the actual homology LES isomorphisms.

    have threeCell_coaction_expansion {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  (K : Mod2CooperationKunneth H R)
        (X : C)
        (hX : ∀ i, i ≠ 0 → i ≠ 2 → i ≠ 4 → Subsingleton (Mod2Homology H i X))
        (q0 : mod2HomologyF2 H R 0 X ≃ₗ[ZMod 2] ZMod 2)
        (q2 : mod2HomologyF2 H R 2 X ≃ₗ[ZMod 2] ZMod 2)
        (e4 : mod2HomologyF2 H R 4 X) :
        ∃ (c2 : mod2HomologyF2 H R 2 H.HF2) (c4 : mod2HomologyF2 H R 4 H.HF2),
          mod2TensorCoaction H R K X 4 e4 =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 4 e4 +
            DirectSum.lof (ZMod 2) ℤ _ 2 (c2 ⊗ₜ[ZMod 2] q2.symm 1) +
            DirectSum.lof (ZMod 2) ℤ _ 4 (c4 ⊗ₜ[ZMod 2] q0.symm 1) := by
      classical
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      let z := mod2TensorCoaction H R K X 4 e4
      obtain ⟨w, hw⟩ := zeroTensor_unit_factor H R B (z 0)
      obtain ⟨c2, hc2⟩ := tensor_rank_one q2 (z 2)
      obtain ⟨c4, hc4⟩ := tensor_rank_one q0 (z 4)
      have hd := directSum_supported_decomposition
        (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (4-i) X)
        {0, 2, 4} (fun i hi => by
          letI : Subsingleton (mod2HomologyF2 H R (4-i) X) := hX (4-i) (by simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega)
            (by simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega)
            (by simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega)
          infer_instance) z
      simp only [Finset.sum_insert (show (0 : ℤ) ∉ {2, 4} by decide),
        Finset.sum_insert (show (2 : ℤ) ∉ {4} by decide), Finset.sum_singleton] at hd
      rw [hw, hc2, hc4] at hd
      have he := congrArg (cooperationTensorAugmentation H R
        (fun i => mod2HomologyF2 H R i X) 4) hd
      change cooperationTensorAugmentation H R _ 4 z = _ at he
      rw [map_add, map_add,
        positiveTensor_augmentation_zero H R _ 4 2 (by decide),
        positiveTensor_augmentation_zero H R _ 4 4 (by decide), add_zero, add_zero] at he
      change cooperationTensorAugmentation H R _ 4 z =
        cooperationTensorAugmentation H R _ 4
          (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 4 w) at he
      rw [cooperationTensorUnit_augmentation] at he
      have he4 : e4 = w := by
        rw [← he]
        exact (tensorCoaction_counit H R K X 4 e4).symm
      refine ⟨c2, c4, ?_⟩
      have hu : cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 4 e4 =
          DirectSum.lof (ZMod 2) ℤ _ 0 (cooperationUnit H ⊗ₜ[ZMod 2] e4) := rfl
      rw [hu]
      simpa only [← he4, add_assoc] using hd

    have negative_cooperation_subsingleton {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  (n : ℤ) (hn : n < 0) :
        Subsingleton (mod2HomologyF2 H R n H.HF2) := by
      letI := mod2HomologyModule H R n H.HF2
      letI := mod2HF2HomotopyModule H R n
      letI := H.homotopy_vanishes n (ne_of_lt hn)
      letI : IsEmpty (PositiveMonomial n) :=
        ⟨fun d => (not_lt_of_ge (le_of_lt hn)) (positiveMonomial_degree_pos d)⟩
      have hs : Subsingleton (LinearMap.ker (cooperationCounitF2 H R n)) :=
        (B.basis n).repr.injective.subsingleton
      have hz (a : mod2HomologyF2 H R n H.HF2) : a = 0 := by
        have ha : cooperationCounitF2 H R n a = 0 := Subsingleton.elim _ _
        exact congrArg Subtype.val (hs.elim (⟨a, ha⟩ : LinearMap.ker (cooperationCounitF2 H R n)) 0)
      exact ⟨fun a b => (hz a).trans (hz b).symm⟩

    have fourCell_coaction_expansion {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  (K : Mod2CooperationKunneth H R)
        (X : C)
        (hX : ∀ i, i ≠ 0 → i ≠ 1 → i ≠ 3 → i ≠ 4 → Subsingleton (Mod2Homology H i X))
        (q0 : mod2HomologyF2 H R 0 X ≃ₗ[ZMod 2] ZMod 2)
        (q1 : mod2HomologyF2 H R 1 X ≃ₗ[ZMod 2] ZMod 2)
        (q3 : mod2HomologyF2 H R 3 X ≃ₗ[ZMod 2] ZMod 2)
        (e4 : mod2HomologyF2 H R 4 X) :
        ∃ (c1 : mod2HomologyF2 H R 1 H.HF2) (c3 : mod2HomologyF2 H R 3 H.HF2)
          (c4 : mod2HomologyF2 H R 4 H.HF2),
          mod2TensorCoaction H R K X 4 e4 =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 4 e4 +
            DirectSum.lof (ZMod 2) ℤ _ 1 (c1 ⊗ₜ[ZMod 2] q3.symm 1) +
            DirectSum.lof (ZMod 2) ℤ _ 3 (c3 ⊗ₜ[ZMod 2] q1.symm 1) +
            DirectSum.lof (ZMod 2) ℤ _ 4 (c4 ⊗ₜ[ZMod 2] q0.symm 1) := by
      classical
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      let z := mod2TensorCoaction H R K X 4 e4
      obtain ⟨w, hw⟩ := zeroTensor_unit_factor H R B (z 0)
      obtain ⟨c1, hc1⟩ := tensor_rank_one q3 (z 1)
      obtain ⟨c3, hc3⟩ := tensor_rank_one q1 (z 3)
      obtain ⟨c4, hc4⟩ := tensor_rank_one q0 (z 4)
      have hd := directSum_supported_decomposition
        (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (4-i) X)
        {0, 1, 3, 4} (fun i hi => by
          have his : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 3 ∧ i ≠ 4 := by simpa using hi
          letI : Subsingleton (mod2HomologyF2 H R (4-i) X) := hX (4-i) (by omega) (by omega) (by omega) (by omega)
          infer_instance) z
      simp only [Finset.sum_insert (show (0 : ℤ) ∉ {1, 3, 4} by decide),
        Finset.sum_insert (show (1 : ℤ) ∉ {3, 4} by decide),
        Finset.sum_insert (show (3 : ℤ) ∉ {4} by decide), Finset.sum_singleton] at hd
      rw [hw, hc1, hc3, hc4] at hd
      have he := congrArg (cooperationTensorAugmentation H R
        (fun i => mod2HomologyF2 H R i X) 4) hd
      rw [map_add, map_add, map_add,
        positiveTensor_augmentation_zero H R _ 4 1 (by decide),
        positiveTensor_augmentation_zero H R _ 4 3 (by decide),
        positiveTensor_augmentation_zero H R _ 4 4 (by decide), add_zero, add_zero, add_zero] at he
      change cooperationTensorAugmentation H R _ 4 z =
        cooperationTensorAugmentation H R _ 4
          (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 4 w) at he
      rw [cooperationTensorUnit_augmentation] at he
      have he4 : e4 = w := by
        rw [← he]
        exact (tensorCoaction_counit H R K X 4 e4).symm
      refine ⟨c1, c3, c4, ?_⟩
      have hu : cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 4 e4 =
          DirectSum.lof (ZMod 2) ℤ _ 0 (cooperationUnit H ⊗ₜ[ZMod 2] e4) := rfl
      rw [hu]
      simpa only [← he4, add_assoc] using hd

    let tensorTerm {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (n k : ℤ) (a : mod2HomologyF2 H R k H.HF2) (x : V (n-k)) :
        cooperationTensor H R V n :=
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      DirectSum.lof (ZMod 2) ℤ _ k (a ⊗ₜ[ZMod 2] x)

    have tensorMap_term {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V W : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 2) (W i)]
        (f : ∀ i, V i →ₗ[ZMod 2] W i) (n k : ℤ)
        (a : mod2HomologyF2 H R k H.HF2) (x : V (n-k)) :
        cooperationTensorMap H R V f n (tensorTerm H R V n k a x) =
          tensorTerm H R W n k a (f (n-k) x) := by
      simp [tensorTerm, cooperationTensorMap, gradedTensorMapRight]

    have rowProjection_term_self {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (q : V 0 →ₗ[ZMod 2] ZMod 2) (n : ℤ)
        (a : mod2HomologyF2 H R n H.HF2) (x : V (n-n)) :
        rowProjection (fun i => mod2HomologyF2 H R i H.HF2) V q n
          (tensorTerm H R V n n a x) =
          q ((LinearEquiv.cast (R := ZMod 2) (M := V) (sub_self n)) x) • a :=
      rowProjection_lof_self (fun i => mod2HomologyF2 H R i H.HF2) V q n a x

    have rowProjection_term_ne {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (q : V 0 →ₗ[ZMod 2] ZMod 2) (n k : ℤ) (hkn : k ≠ n)
        (a : mod2HomologyF2 H R k H.HF2) (x : V (n-k)) :
        rowProjection (fun i => mod2HomologyF2 H R i H.HF2) V q n
          (tensorTerm H R V n k a x) = 0 :=
      rowProjection_lof_ne (fun i => mod2HomologyF2 H R i H.HF2) V q n k hkn a x

    have rowProjection_unit_pos {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (q : V 0 →ₗ[ZMod 2] ZMod 2) (n : ℤ) (hn : n ≠ 0) (x : V n) :
        rowProjection (fun i => mod2HomologyF2 H R i H.HF2) V q n
          (cooperationTensorUnit H R V n x) = 0 :=
      rowProjection_lof_ne (fun i => mod2HomologyF2 H R i H.HF2) V q n 0 (Ne.symm hn) _ _

    -- Extracting the actual bottom-row matrix from a three-cell coaction yields
    -- precisely the degree-four reduced-diagonal obstruction used in §3.

    have threeCell_matrix {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (hD : Mod2KunnethDiagonalCompatible H R K)
        (X : C) (q : mod2HomologyF2 H R 0 X →ₗ[ZMod 2] ZMod 2)
        (e0 : mod2HomologyF2 H R 0 X) (hq : q e0 = 1)
        (e2 : mod2HomologyF2 H R 2 X) (e4 : mod2HomologyF2 H R 4 X)
        (u : mod2HomologyF2 H R 2 H.HF2) (a : mod2HomologyF2 H R 4 H.HF2)
        (h0 : mod2TensorCoaction H R K X 0 e0 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 0 e0)
        (h2 : mod2TensorCoaction H R K X 2 e2 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 2 e2 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 2 2 u e0)
        (h4 : mod2TensorCoaction H R K X 4 e4 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 4 e4 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 4 2 u e2 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 4 4 a e0) :
        cooperationTensorDiagonal H R K 4 a =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 4 a +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 2 u u +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 4 a (cooperationUnit H) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      have hr0 : actualRow H R K X q 0 e0 = cooperationUnit H := by
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 0 (mod2TensorCoaction H R K X 0 e0) = _
        rw [h0]
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 0
          (tensorTerm H R (fun i => mod2HomologyF2 H R i X) 0 0 (cooperationUnit H) e0) = _
        have hp := rowProjection_term_self H R (fun j => mod2HomologyF2 H R j X) q 0 (cooperationUnit H) e0
        change _ = q e0 • cooperationUnit H at hp
        exact hp.trans (by rw [hq, one_smul])
      have hr2 : actualRow H R K X q 2 e2 = u := by
        have hu := rowProjection_unit_pos H R (fun i => mod2HomologyF2 H R i X) q 2 (by decide) e2
        have hp := rowProjection_term_self H R (fun i => mod2HomologyF2 H R i X) q 2 u e0
        change _ = q e0 • u at hp
        rw [hq, one_smul] at hp
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2) (fun i => mod2HomologyF2 H R i X) q 2 (mod2TensorCoaction H R K X 2 e2) = _
        rw [h2, map_add]
        exact (congrArg₂ (· + ·) hu hp).trans (zero_add u)
      have hr4 : actualRow H R K X q 4 e4 = a := by
        have hu := rowProjection_unit_pos H R (fun i => mod2HomologyF2 H R i X) q 4 (by decide) e4
        have hm0 := rowProjection_term_ne H R (fun i => mod2HomologyF2 H R i X) q 4 2 (by decide) u e2
        have ht := rowProjection_term_self H R (fun i => mod2HomologyF2 H R i X) q 4 a e0
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 4
          (tensorTerm H R (fun i => mod2HomologyF2 H R i X) 4 4 a e0) = q e0 • a at ht
        rw [hq, one_smul] at ht
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 4 (mod2TensorCoaction H R K X 4 e4) = _
        rw [h4, map_add, map_add]
        exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu hm0) ht).trans (by simp only [zero_add])
      have hmap : cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 4
          (mod2TensorCoaction H R K X 4 e4) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 4 a +
            tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 2 u u +
            tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 4 a (cooperationUnit H) := by
        have hu := tensorUnit_naturality H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 4 e4
        have hu' := hu.trans (congrArg (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 4) hr4)
        have hm0 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 4 2 u e2
        change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 2 u (actualRow H R K X q 2 e2) at hm0
        have hm0' := hm0.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 2 u) hr2)
        have hm1 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 4 4 a e0
        change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 4 a (actualRow H R K X q 0 e0) at hm1
        have hm1' := hm1.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 4 a) hr0)
        rw [h4, map_add, map_add]
        exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu' hm0') hm1')
      have h := actualRow_coaction H R K hD X q 4 e4
      rw [hr4] at h
      exact h.trans hmap

    have threeCell_matrix_023 {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (hD : Mod2KunnethDiagonalCompatible H R K)
        (X : C) (q : mod2HomologyF2 H R 0 X →ₗ[ZMod 2] ZMod 2)
        (e0 : mod2HomologyF2 H R 0 X) (hq : q e0 = 1)
        (e2 : mod2HomologyF2 H R 2 X) (e4 : mod2HomologyF2 H R 3 X)
        (u : mod2HomologyF2 H R 2 H.HF2) (x1 : mod2HomologyF2 H R 1 H.HF2)
        (a : mod2HomologyF2 H R 3 H.HF2)
        (h0 : mod2TensorCoaction H R K X 0 e0 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 0 e0)
        (h2 : mod2TensorCoaction H R K X 2 e2 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 2 e2 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 2 2 u e0)
        (h4 : mod2TensorCoaction H R K X 3 e4 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 e4 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 3 1 x1 e2 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 3 3 a e0) :
        cooperationTensorDiagonal H R K 3 a =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3 a +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 1 x1 u +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a (cooperationUnit H) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      have hr0 : actualRow H R K X q 0 e0 = cooperationUnit H := by
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 0 (mod2TensorCoaction H R K X 0 e0) = _
        rw [h0]
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 0
          (tensorTerm H R (fun i => mod2HomologyF2 H R i X) 0 0 (cooperationUnit H) e0) = _
        have hp := rowProjection_term_self H R (fun j => mod2HomologyF2 H R j X) q 0 (cooperationUnit H) e0
        change _ = q e0 • cooperationUnit H at hp
        exact hp.trans (by rw [hq, one_smul])
      have hr2 : actualRow H R K X q 2 e2 = u := by
        have hu := rowProjection_unit_pos H R (fun i => mod2HomologyF2 H R i X) q 2 (by decide) e2
        have hp := rowProjection_term_self H R (fun i => mod2HomologyF2 H R i X) q 2 u e0
        change _ = q e0 • u at hp
        rw [hq, one_smul] at hp
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2) (fun i => mod2HomologyF2 H R i X) q 2 (mod2TensorCoaction H R K X 2 e2) = _
        rw [h2, map_add]
        exact (congrArg₂ (· + ·) hu hp).trans (zero_add u)
      have hr3 : actualRow H R K X q 3 e4 = a := by
        have hu := rowProjection_unit_pos H R (fun i => mod2HomologyF2 H R i X) q 3 (by decide) e4
        have hm0 := rowProjection_term_ne H R (fun i => mod2HomologyF2 H R i X) q 3 1 (by decide) x1 e2
        have ht := rowProjection_term_self H R (fun i => mod2HomologyF2 H R i X) q 3 a e0
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 3
          (tensorTerm H R (fun i => mod2HomologyF2 H R i X) 3 3 a e0) = q e0 • a at ht
        rw [hq, one_smul] at ht
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 3 (mod2TensorCoaction H R K X 3 e4) = _
        rw [h4, map_add, map_add]
        exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu hm0) ht).trans (by simp only [zero_add])
      have hmap : cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 3
          (mod2TensorCoaction H R K X 3 e4) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3 a +
            tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 1 x1 u +
            tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a (cooperationUnit H) := by
        have hu := tensorUnit_naturality H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 3 e4
        have hu' := hu.trans (congrArg (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3) hr3)
        have hm0 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 3 1 x1 e2
        change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 1 x1 (actualRow H R K X q 2 e2) at hm0
        have hm0' := hm0.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 1 x1) hr2)
        have hm1 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 3 3 a e0
        change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a (actualRow H R K X q 0 e0) at hm1
        have hm1' := hm1.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a) hr0)
        rw [h4, map_add, map_add]
        exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu' hm0') hm1')
      have h := actualRow_coaction H R K hD X q 3 e4
      rw [hr3] at h
      exact h.trans hmap

    have toda_homology_geometry {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (R : Mod2RingStructure H)
        (η : Sphere (C := C) 1 ⟶ SphereSpectrum)
        (hToda : Toda.Relation (0 : (Sphere (C := C) 1)⟦(1 : ℤ)⟧ ⟶ SphereSpectrum)
          (2 • 𝟙 (Sphere (C := C) 1)) η (2 • 𝟙 SphereSpectrum)) :
        ∃ (Q : C) (i : Sphere (C := C) 1 ⟶ Q)
          (p : Q ⟶ (Sphere (C := C) 1)⟦(1 : ℤ)⟧)
          (_ : Triangle.mk (2 • 𝟙 (Sphere (C := C) 1)) i p ∈ distTriang C)
          (b : Q ⟶ SphereSpectrum) (t : HasFunctorialCofiber.cofib b ⟶ SphereSpectrum),
          i ≫ b = η ∧ b ≫ (2 • 𝟙 SphereSpectrum) = 0 ∧
          HasFunctorialCofiber.cofibι b ≫ t = 2 • 𝟙 SphereSpectrum ∧
          (∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Mod2Homology H n Q)) ∧
          (∀ n, Mod2Homology.pushforward H b n = 0) ∧
          (∀ n, n ≠ 0 → n ≠ 2 → n ≠ 3 →
            Subsingleton (Mod2Homology H n (HasFunctorialCofiber.cofib b))) ∧
          (∀ n, Mod2Homology.pushforward H t n = 0) ∧
          (∀ n, n ≠ 0 → n ≠ 1 → n ≠ 3 → n ≠ 4 →
            Subsingleton (Mod2Homology H n (HasFunctorialCofiber.cofib t))) := by
      obtain ⟨Q, i, p, hT, b, t, hib, hb2, ht, hcompareη, hcompare2⟩ :=
        triple_cone_geometry (2 • 𝟙 (Sphere (C := C) 1)) η
          (2 • 𝟙 SphereSpectrum) hToda
      let TQ : HoCofiberSequence (C := C) :=
        ⟨Sphere 1, Sphere 1, Q, 2 • 𝟙 _, i, p, hT⟩
      have hQ (n : ℤ) (hn1 : n ≠ 1) (hn2 : n ≠ 2) :
          Subsingleton (Mod2Homology H n Q) :=
        homology_middle_subsingleton H TQ n
          (sphereHomologyShiftSubsingleton H n 1 hn1)
          (sphereHomologyShiftSubsingleton H (n-1) 1 (by omega))
      have hbzero (n : ℤ) : Mod2Homology.pushforward H b n = 0 := by
        apply pushforward_zero_of_disjoint_support H b n
        by_cases hn : n = 0
        · subst n
          exact Or.inl (hQ 0 (by decide) (by decide))
        · exact Or.inr (sphereHomologySubsingleton H n hn)
      let TX := HoCofiberSequence.ofMorphism b
      have hX (n : ℤ) (hn0 : n ≠ 0) (hn2 : n ≠ 2) (hn3 : n ≠ 3) :
          Subsingleton (Mod2Homology H n (HasFunctorialCofiber.cofib b)) :=
        homology_middle_subsingleton H TX n (sphereHomologySubsingleton H n hn0)
          (hQ (n-1) (by omega) (by omega))
      have htzero (n : ℤ) : Mod2Homology.pushforward H t n = 0 := by
        by_cases hn : n = 0
        · subst n
          exact pushforward_zero_of_surjective_precomposition H
            (HasFunctorialCofiber.cofibι b) t 0
            (bottomEquiv_of_homology_zero H R TX 0 (hbzero 0)
              (by exact hQ (-1) (by decide) (by decide))).surjective
            (by
              rw [ht]
              exact twice_map_zero H R (𝟙 SphereSpectrum) 0)
        · exact pushforward_zero_of_disjoint_support H t n
            (Or.inr (sphereHomologySubsingleton H n hn))
      let TE := HoCofiberSequence.ofMorphism t
      have hE (n : ℤ) (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hn3 : n ≠ 3) (hn4 : n ≠ 4) :
          Subsingleton (Mod2Homology H n (HasFunctorialCofiber.cofib t)) :=
        homology_middle_subsingleton H TE n (sphereHomologySubsingleton H n hn0)
          (hX (n-1) (by omega) (by omega) (by omega))
      exact ⟨Q, i, p, hT, b, t, hib, hb2, ht, hQ, hbzero, hX, htzero, hE⟩

    have threeCell_023_coaction_expansion {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  (K : Mod2CooperationKunneth H R)
        (X : C)
        (hX : ∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → Subsingleton (Mod2Homology H i X))
        (q0 : mod2HomologyF2 H R 0 X ≃ₗ[ZMod 2] ZMod 2)
        (q2 : mod2HomologyF2 H R 2 X ≃ₗ[ZMod 2] ZMod 2)
        (e4 : mod2HomologyF2 H R 3 X) :
        ∃ (c2 : mod2HomologyF2 H R 1 H.HF2) (c4 : mod2HomologyF2 H R 3 H.HF2),
          mod2TensorCoaction H R K X 3 e4 =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 e4 +
            DirectSum.lof (ZMod 2) ℤ _ 1 (c2 ⊗ₜ[ZMod 2] q2.symm 1) +
            DirectSum.lof (ZMod 2) ℤ _ 3 (c4 ⊗ₜ[ZMod 2] q0.symm 1) := by
      classical
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      let z := mod2TensorCoaction H R K X 3 e4
      obtain ⟨w, hw⟩ := zeroTensor_unit_factor H R B (z 0)
      obtain ⟨c2, hc2⟩ := tensor_rank_one q2 (z 1)
      obtain ⟨c4, hc4⟩ := tensor_rank_one q0 (z 3)
      have hd := directSum_supported_decomposition
        (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (3-i) X)
        {0, 1, 3} (fun i hi => by
          letI : Subsingleton (mod2HomologyF2 H R (3-i) X) := hX (3-i) (by simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega)
            (by simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega)
            (by simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega)
          infer_instance) z
      simp only [Finset.sum_insert (show (0 : ℤ) ∉ {1, 3} by decide),
        Finset.sum_insert (show (1 : ℤ) ∉ {3} by decide), Finset.sum_singleton] at hd
      rw [hw, hc2, hc4] at hd
      have he := congrArg (cooperationTensorAugmentation H R
        (fun i => mod2HomologyF2 H R i X) 3) hd
      change cooperationTensorAugmentation H R _ 3 z = _ at he
      rw [map_add, map_add,
        positiveTensor_augmentation_zero H R _ 3 1 (by decide),
        positiveTensor_augmentation_zero H R _ 3 3 (by decide), add_zero, add_zero] at he
      change cooperationTensorAugmentation H R _ 3 z =
        cooperationTensorAugmentation H R _ 3
          (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 w) at he
      rw [cooperationTensorUnit_augmentation] at he
      have he4 : e4 = w := by
        rw [← he]
        exact (tensorCoaction_counit H R K X 3 e4).symm
      refine ⟨c2, c4, ?_⟩
      have hu : cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 e4 =
          DirectSum.lof (ZMod 2) ℤ _ 0 (cooperationUnit H ⊗ₜ[ZMod 2] e4) := rfl
      rw [hu]
      simpa only [← he4, add_assoc] using hd

    have coaction_of_unit_image {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (hU : Mod2KunnethUnitCompatible H R K)
        (X : C) (n : ℤ) (a : HomotopyGroup n X) :
        mod2TensorCoaction H R K X n (a ≫ adamsUnit H.unit X) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) n
            (a ≫ adamsUnit H.unit X) := by
      rw [tensorCoaction_apply]
      have hu : mod2CoactionMap H X n (a ≫ adamsUnit H.unit X) =
          mod2OuterUnitMap H X n (a ≫ adamsUnit H.unit X) := by
        change (a ≫ adamsUnit H.unit X) ≫ H.HF2 ◁ adamsUnit H.unit X =
          (a ≫ adamsUnit H.unit X) ≫ adamsUnit H.unit (H.HF2 ⊗ X)
        rw [Category.assoc, mod2AdamsUnit_naturality, Category.assoc]
      rw [hu, hU]

    have transfer_unit {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  {X Y : C} (f : X ⟶ Y) (n : ℤ)
        (x : mod2HomologyF2 H R n X)
        (hx : mod2TensorCoaction H R K X n x =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) n x) :
        mod2TensorCoaction H R K Y n (Mod2Homology.pushforward H f n x) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i Y) n
            (Mod2Homology.pushforward H f n x) := by
      have hn := tensorCoaction_naturality H R K f n x
      have hu := tensorUnit_naturality H R (fun i => mod2HomologyF2 H R i X) (fun i => (mod2HomologyF2Map H R f i).hom) n x
      have hm := congrArg (cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X) (fun i => (mod2HomologyF2Map H R f i).hom) n) hx
      exact hn.trans (hm.trans hu)

    have transfer_twoTerm {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  {X Y : C} (f : X ⟶ Y) (n k : ℤ)
        (x : mod2HomologyF2 H R n X) (a : mod2HomologyF2 H R k H.HF2)
        (y : mod2HomologyF2 H R (n-k) X)
        (hx : mod2TensorCoaction H R K X n x =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) n x +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) n k a y) :
        mod2TensorCoaction H R K Y n (Mod2Homology.pushforward H f n x) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i Y) n
            (Mod2Homology.pushforward H f n x) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i Y) n k a
            (Mod2Homology.pushforward H f (n-k) y) := by
      have hn := tensorCoaction_naturality H R K f n x
      have hu := tensorUnit_naturality H R (fun i => mod2HomologyF2 H R i X) (fun i => (mod2HomologyF2Map H R f i).hom) n x
      have ht := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i Y) (fun i => (mod2HomologyF2Map H R f i).hom) n k a y
      have hm := congrArg (cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X) (fun i => (mod2HomologyF2Map H R f i).hom) n) hx
      rw [map_add] at hm
      exact hn.trans (hm.trans (congrArg₂ (· + ·) hu ht))

    have tensorLowerMap_unit {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V W : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 2) (W i)]
        (g : ∀ i, V i →ₗ[ZMod 2] W (i-1)) (n : ℤ) (x : V n) :
        cooperationTensorLowerMap H R V W g n (cooperationTensorUnit H R V n x) =
          cooperationTensorUnit H R W (n-1) (g n x) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      have hc (i j : ℤ) (h : i = j) (z : V i) :
          g j ((LinearEquiv.cast (R := ZMod 2) (M := V) h) z) =
            (LinearEquiv.cast (R := ZMod 2) (M := W) (congrArg (fun k => k - 1) h))
              (g i z) := by subst j; rfl
      have ht (i j k : ℤ) (h : i = j) (h' : j = k) (h'' : i = k) (z : W i) :
          (LinearEquiv.cast (R := ZMod 2) (M := W) h')
            ((LinearEquiv.cast (R := ZMod 2) (M := W) h) z) =
          (LinearEquiv.cast (R := ZMod 2) (M := W) h'') z := by subst j; subst k; rfl
      simp only [cooperationTensorUnit_apply, cooperationTensorLowerMap,
        gradedTensorLowerMap_lof_tmul]
      rw [hc, ht]

    have tensorLowerMap_term {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V W : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        [∀ i, AddCommGroup (W i)] [∀ i, Module (ZMod 2) (W i)]
        (g : ∀ i, V i →ₗ[ZMod 2] W (i-1)) (n k : ℤ)
        (a : mod2HomologyF2 H R k H.HF2) (x : V (n-k)) :
        cooperationTensorLowerMap H R V W g n (tensorTerm H R V n k a x) =
          tensorTerm H R W (n-1) k a
            ((LinearEquiv.cast (R := ZMod 2) (M := W)
              (show n-k-1=n-1-k by omega)) (g (n-k) x)) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      exact gradedTensorLowerMap_lof_tmul (Mod2Cooperations H) g n k a x

    have fourCell_bottom_matrix {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)  (hD : Mod2KunnethDiagonalCompatible H R K)
        (X : C) (q : mod2HomologyF2 H R 0 X →ₗ[ZMod 2] ZMod 2)
        (e0 : mod2HomologyF2 H R 0 X) (hq : q e0 = 1)
        (e1 : mod2HomologyF2 H R 1 X) (e3 : mod2HomologyF2 H R 3 X)
        (e4 : mod2HomologyF2 H R 4 X)
        (x : mod2HomologyF2 H R 1 H.HF2) (u : mod2HomologyF2 H R 2 H.HF2)
        (a b : mod2HomologyF2 H R 3 H.HF2) (c : mod2HomologyF2 H R 4 H.HF2)
        (h0 : mod2TensorCoaction H R K X 0 e0 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 0 e0)
        (h1 : mod2TensorCoaction H R K X 1 e1 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 1 e1 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 1 1 x e0)
        (h3 : mod2TensorCoaction H R K X 3 e3 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 e3 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 3 2 u e1 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 3 3 a e0)
        (h4 : mod2TensorCoaction H R K X 4 e4 =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 4 e4 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 4 1 x e3 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 4 3 b e1 +
          tensorTerm H R (fun i => mod2HomologyF2 H R i X) 4 4 c e0) :
        (cooperationTensorDiagonal H R K 3 a =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3 a +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 2 u x +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a (cooperationUnit H)) ∧
        (cooperationTensorDiagonal H R K 4 c =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 4 c +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 1 x a +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 3 b x +
          tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 4 c (cooperationUnit H)) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      have hr0 : actualRow H R K X q 0 e0 = cooperationUnit H := by
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 0 (mod2TensorCoaction H R K X 0 e0) = _
        rw [h0]
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 0
          (tensorTerm H R (fun i => mod2HomologyF2 H R i X) 0 0 (cooperationUnit H) e0) = _
        have hp := rowProjection_term_self H R (fun j => mod2HomologyF2 H R j X) q 0 (cooperationUnit H) e0
        change _ = q e0 • cooperationUnit H at hp
        exact hp.trans (by rw [hq, one_smul])
      have hr1 : actualRow H R K X q 1 e1 = x := by
        have hu := rowProjection_unit_pos H R (fun i => mod2HomologyF2 H R i X) q 1 (by decide) e1
        have hp := rowProjection_term_self H R (fun i => mod2HomologyF2 H R i X) q 1 x e0
        change _ = q e0 • x at hp
        rw [hq, one_smul] at hp
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2) (fun i => mod2HomologyF2 H R i X) q 1 (mod2TensorCoaction H R K X 1 e1) = _
        rw [h1, map_add]
        exact (congrArg₂ (· + ·) hu hp).trans (zero_add x)
      have hr3 : actualRow H R K X q 3 e3 = a := by
        have hu := rowProjection_unit_pos H R (fun i => mod2HomologyF2 H R i X) q 3 (by decide) e3
        have hm0 := rowProjection_term_ne H R (fun i => mod2HomologyF2 H R i X) q 3 2 (by decide) u e1
        have ht := rowProjection_term_self H R (fun i => mod2HomologyF2 H R i X) q 3 a e0
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 3
          (tensorTerm H R (fun i => mod2HomologyF2 H R i X) 3 3 a e0) = q e0 • a at ht
        rw [hq, one_smul] at ht
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 3 (mod2TensorCoaction H R K X 3 e3) = _
        rw [h3, map_add, map_add]
        exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu hm0) ht).trans (by simp only [zero_add])
      have hr4 : actualRow H R K X q 4 e4 = c := by
        have hu := rowProjection_unit_pos H R (fun i => mod2HomologyF2 H R i X) q 4 (by decide) e4
        have hm0 := rowProjection_term_ne H R (fun i => mod2HomologyF2 H R i X) q 4 1 (by decide) x e3
        have hm1 := rowProjection_term_ne H R (fun i => mod2HomologyF2 H R i X) q 4 3 (by decide) b e1
        have ht := rowProjection_term_self H R (fun i => mod2HomologyF2 H R i X) q 4 c e0
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 4
          (tensorTerm H R (fun i => mod2HomologyF2 H R i X) 4 4 c e0) = q e0 • c at ht
        rw [hq, one_smul] at ht
        change rowProjection (fun i => mod2HomologyF2 H R i H.HF2)
          (fun i => mod2HomologyF2 H R i X) q 4 (mod2TensorCoaction H R K X 4 e4) = _
        rw [h4, map_add, map_add, map_add]
        exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu hm0) hm1) ht).trans (by simp only [zero_add])
      constructor
      · have hmap : cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 3
            (mod2TensorCoaction H R K X 3 e3) =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3 a +
              tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 2 u x +
              tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a (cooperationUnit H) := by
          have hu := tensorUnit_naturality H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 3 e3
          have hu' := hu.trans (congrArg (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 3) hr3)
          have hm0 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 3 2 u e1
          change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 2 u (actualRow H R K X q 1 e1) at hm0
          have hm0' := hm0.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 2 u) hr1)
          have hm1 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 3 3 a e0
          change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a (actualRow H R K X q 0 e0) at hm1
          have hm1' := hm1.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 3 3 a) hr0)
          rw [h3, map_add, map_add]
          exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu' hm0') hm1')
        have h := actualRow_coaction H R K hD X q 3 e3
        rw [hr3] at h
        exact h.trans hmap
      · have hmap : cooperationTensorMap H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 4
            (mod2TensorCoaction H R K X 4 e4) =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 4 c +
              tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 1 x a +
              tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 3 b x +
              tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 4 c (cooperationUnit H) := by
          have hu := tensorUnit_naturality H R (fun i => mod2HomologyF2 H R i X) (actualRow H R K X q) 4 e4
          have hu' := hu.trans (congrArg (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 4) hr4)
          have hm0 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 4 1 x e3
          change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 1 x (actualRow H R K X q 3 e3) at hm0
          have hm0' := hm0.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 1 x) hr3)
          have hm1 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 4 3 b e1
          change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 3 b (actualRow H R K X q 1 e1) at hm1
          have hm1' := hm1.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 3 b) hr1)
          have hm2 := tensorMap_term H R (fun i => mod2HomologyF2 H R i X) (fun i => mod2HomologyF2 H R i H.HF2) (actualRow H R K X q) 4 4 c e0
          change _ = tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 4 c (actualRow H R K X q 0 e0) at hm2
          have hm2' := hm2.trans (congrArg (tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 4 c) hr0)
          rw [h4, map_add, map_add, map_add]
          exact (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu' hm0') hm1') hm2')
        have h := actualRow_coaction H R K hD X q 4 e4
        rw [hr4] at h
        exact h.trans hmap

    have tensorTerm_coefficient_injective {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
        (V : ℤ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (n k : ℤ) (x : V (n-k)) (q : V (n-k) →ₗ[ZMod 2] ZMod 2) (hq : q x = 1) :
        Function.Injective (fun a : mod2HomologyF2 H R k H.HF2 => tensorTerm H R V n k a x) := by
      intro a b h
      apply pureTensorCoefficient_injective x q hq
      have hh := congrArg (fun z : cooperationTensor H R V n => z k) h
      simpa only [tensorTerm, DirectSum.lof_apply] using hh

    have tensorTerm_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (n k : ℤ) (a : mod2HomologyF2 H R k H.HF2) :
        tensorTerm H R V n k a 0 = 0 := by
      simp only [tensorTerm, TensorProduct.tmul_zero, map_zero]

    have tensorTerm_component_zero {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (n i k : ℤ) (hik : i ≠ k) (a : mod2HomologyF2 H R k H.HF2) (x : V (n-k)) :
        (tensorTerm H R V n k a x) i = 0 := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      exact DirectSum.of_eq_of_ne
        (β := fun j => Mod2Cooperations H j ⊗[ZMod 2] V (n-j)) k i (a ⊗ₜ[ZMod 2] x) hik

    -- Equality of a two-term expansion identifies both coefficients, with the
    -- same normalized homology basis in each term.

    have tensorTerms_two_unique {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  (V : ℤ → Type)
        [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]
        (n i j : ℤ) (hij : i ≠ j)
        (xi : V (n-i)) (qi : V (n-i) →ₗ[ZMod 2] ZMod 2) (hqi : qi xi = 1)
        (xj : V (n-j)) (qj : V (n-j) →ₗ[ZMod 2] ZMod 2) (hqj : qj xj = 1)
        (ai bi : mod2HomologyF2 H R i H.HF2)
        (aj bj : mod2HomologyF2 H R j H.HF2)
        (h : tensorTerm H R V n i ai xi + tensorTerm H R V n j aj xj =
          tensorTerm H R V n i bi xi + tensorTerm H R V n j bj xj) : ai = bi ∧ aj = bj := by
      constructor
      · apply pureTensorCoefficient_injective xi qi hqi
        have hh := congrArg (fun z : cooperationTensor H R V n => z i) h
        change (tensorTerm H R V n i ai xi) i + (tensorTerm H R V n j aj xj) i =
          (tensorTerm H R V n i bi xi) i + (tensorTerm H R V n j bj xj) i at hh
        rw [tensorTerm_component_zero H R V n i j hij,
          tensorTerm_component_zero H R V n i j hij, add_zero, add_zero] at hh
        simpa only [tensorTerm, DirectSum.lof_apply] using hh
      · apply pureTensorCoefficient_injective xj qj hqj
        have hh := congrArg (fun z : cooperationTensor H R V n => z j) h
        change (tensorTerm H R V n i ai xi) j + (tensorTerm H R V n j aj xj) j =
          (tensorTerm H R V n i bi xi) j + (tensorTerm H R V n j bj xj) j at hh
        rw [tensorTerm_component_zero H R V n j i (Ne.symm hij),
          tensorTerm_component_zero H R V n j i (Ne.symm hij), zero_add, zero_add] at hh
        simpa only [tensorTerm, DirectSum.lof_apply] using hh

    have homologyBoundary_naturality {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T U : HoCofiberSequence (C := C))
        (a : T.X ⟶ U.X) (c : T.Z ⟶ U.Z)
        (hδ : T.h ≫ (shiftFunctor C (1 : ℤ)).map a = c ≫ U.h)
        (n : ℤ) (x : Mod2Homology H n T.Z) :
        mod2HomologyConnecting H U n (Mod2Homology.pushforward H c n x) =
          Mod2Homology.pushforward H a (n-1)
            (mod2HomologyConnecting H T n x) := by
      have hlast : (H.HF2 ◁ c) ≫ (U.map (tensorLeft H.HF2)).h =
          (T.map (tensorLeft H.HF2)).h ≫ (H.HF2 ◁ a)⟦(1 : ℤ)⟧' := by
        change (H.HF2 ◁ c) ≫ (H.HF2 ◁ U.h) ≫ _ =
          ((H.HF2 ◁ T.h) ≫ _) ≫ _
        rw [← Category.assoc, ← whiskerLeft_comp, ← hδ, whiskerLeft_comp, Category.assoc]
        have hn := ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.naturality a
        change (H.HF2 ◁ (shiftFunctor C (1 : ℤ)).map a) ≫
            ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app U.X =
          ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app T.X ≫
            (shiftFunctor C (1 : ℤ)).map (H.HF2 ◁ a) at hn
        simpa only [Category.assoc] using congrArg (fun f => (H.HF2 ◁ T.h) ≫ f) hn
      exact connectingHomomorphism_naturality (T.map (tensorLeft H.HF2))
        (U.map (tensorLeft H.HF2)) (H.HF2 ◁ a) (H.HF2 ◁ c) hlast n x

    have comparison_nonzero_of_boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T U : HoCofiberSequence (C := C))
        (a : T.X ⟶ U.X) (c : T.Z ⟶ U.Z)
        (hδ : T.h ≫ (shiftFunctor C (1 : ℤ)).map a = c ≫ U.h)
        (n : ℤ) (x : Mod2Homology H n T.Z) (hx : x ≠ 0)
        (hT : Function.Injective (mod2HomologyConnecting H T n))
        (ha : Function.Injective (Mod2Homology.pushforward H a (n-1))) :
        Mod2Homology.pushforward H c n x ≠ 0 := by
      intro hz
      have h := homologyBoundary_naturality H T U a c hδ n x
      rw [hz, map_zero] at h
      apply hx
      apply hT
      apply ha
      simpa only [map_zero] using h.symm

    -- Over F₂ every nonzero class in a rank-one group is its chosen basis.

    have coordinate_nonzero_unique   {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
        (q : V ≃ₗ[ZMod 2] ZMod 2) (x : V) (hx : x ≠ 0) : x = q.symm 1 := by
      apply q.injective
      rw [q.apply_symm_apply]
      have htwo : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      apply (htwo (q x)).resolve_left
      intro h
      apply hx
      apply q.injective
      simpa only [map_zero] using h

    have pushforward_comp_apply {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
        (n : ℤ) (x : Mod2Homology H n X) :
        Mod2Homology.pushforward H g n (Mod2Homology.pushforward H f n x) =
          Mod2Homology.pushforward H (f ≫ g) n x := by
      change (x ≫ H.HF2 ◁ f) ≫ H.HF2 ◁ g = x ≫ H.HF2 ◁ (f ≫ g)
      rw [whiskerLeft_comp, Category.assoc]

    have comparison_bottom_injective {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (T U : HoCofiberSequence (C := C))
        (b : T.Y ⟶ U.Y) (c : T.Z ⟶ U.Z) (hmid : T.g ≫ c = b ≫ U.g) (n : ℤ)
        (hT : Function.Surjective (Mod2Homology.pushforward H T.g n))
        (hb : Function.Injective (Mod2Homology.pushforward H b n))
        (hU : Function.Injective (Mod2Homology.pushforward H U.g n)) :
        Function.Injective (Mod2Homology.pushforward H c n) := by
      intro x y h
      obtain ⟨x', rfl⟩ := hT x
      obtain ⟨y', rfl⟩ := hT y
      rw [pushforward_comp_apply, pushforward_comp_apply, hmid,
        ← pushforward_comp_apply, ← pushforward_comp_apply] at h
      exact congrArg (Mod2Homology.pushforward H T.g n) (hb (hU h))

    -- A triangle comparison identifies both rank-one bases by nonzeroness.
    -- This is used for Cη→X and C₂→E; no preferred sign is assumed.

    have comparison_twoCell_transfer {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] (K : Mod2CooperationKunneth H R)
        (T U : HoCofiberSequence (C := C))
        (a : T.X ⟶ U.X) (b : T.Y ⟶ U.Y) (c : T.Z ⟶ U.Z)
        (hmid : T.g ≫ c = b ≫ U.g)
        (hlast : T.h ≫ (shiftFunctor C (1 : ℤ)).map a = c ≫ U.h)
        (d : ℤ) (qT0 : mod2HomologyF2 H R 0 T.Z ≃ₗ[ZMod 2] ZMod 2)
        (qTd : mod2HomologyF2 H R d T.Z ≃ₗ[ZMod 2] ZMod 2)
        (qU0 : mod2HomologyF2 H R 0 U.Z ≃ₗ[ZMod 2] ZMod 2)
        (qUd : mod2HomologyF2 H R d U.Z ≃ₗ[ZMod 2] ZMod 2)
        (u : mod2HomologyF2 H R d H.HF2)
        (hTg : Function.Surjective (Mod2Homology.pushforward H T.g 0))
        (hbg : Function.Injective (Mod2Homology.pushforward H b 0))
        (hUg : Function.Injective (Mod2Homology.pushforward H U.g 0))
        (hTd : Function.Injective (mod2HomologyConnecting H T d))
        (had : Function.Injective (Mod2Homology.pushforward H a (d-1)))
        (hψ : mod2TensorCoaction H R K T.Z d (qTd.symm 1) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i T.Z) d (qTd.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i T.Z) d d u
            ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i T.Z)
              (sub_self d).symm) (qT0.symm 1))) :
        mod2TensorCoaction H R K U.Z d (qUd.symm 1) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i U.Z) d (qUd.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i U.Z) d d u
            ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i U.Z)
              (sub_self d).symm) (qU0.symm 1)) := by
      have hn0 : qT0.symm 1 ≠ 0 := by
        intro h
        have hh := congrArg qT0 h
        exact one_ne_zero (by simpa only [qT0.apply_symm_apply, map_zero] using hh)
      have hnd : qTd.symm 1 ≠ 0 := by
        intro h
        have hh := congrArg qTd h
        exact one_ne_zero (by simpa only [qTd.apply_symm_apply, map_zero] using hh)
      have hc0 : Mod2Homology.pushforward H c 0 (qT0.symm 1) = qU0.symm 1 := by
        apply coordinate_nonzero_unique qU0
        intro hz
        apply hn0
        apply comparison_bottom_injective H T U b c hmid 0 hTg hbg hUg
        simpa only [map_zero] using hz
      have hcd : Mod2Homology.pushforward H c d (qTd.symm 1) = qUd.symm 1 :=
        coordinate_nonzero_unique qUd _
          (comparison_nonzero_of_boundary H T U a c hlast d _ hnd hTd had)
      have h := transfer_twoTerm H R K c d d (qTd.symm 1) u
        ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i T.Z)
          (sub_self d).symm) (qT0.symm 1)) hψ
      rw [hcd, homologyPushforward_cast, hc0] at h
      exact h

    have inducedMap_iso_bijective {C : Type 1} [StableHomotopyCategory.{1,0} C]  {X Y : C} (e : X ≅ Y) (n : ℤ) :
        Function.Bijective (inducedMap e.hom n) := by
      constructor
      · intro x y h
        exact (cancel_mono e.hom).mp h
      · intro y
        refine ⟨y ≫ e.inv, ?_⟩
        simp only [inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          Category.assoc, Iso.inv_hom_id, Category.comp_id]

    let desuspendEquiv {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [MonoidalPreadditive C] (R : Mod2RingStructure H)  (X : C) (n : ℤ) :
        mod2HomologyF2 H R n (X⟦(1 : ℤ)⟧) ≃ₗ[ZMod 2] mod2HomologyF2 H R (n - 1) X :=
      LinearEquiv.ofBijective (mod2HomologyDesuspendF2 H R X n)
        ((homotopyDesuspend_bijective (H.HF2 ⊗ X) n).comp
          (inducedMap_iso_bijective (((tensorLeft H.HF2).commShiftIso (1 : ℤ)).app X) n))

    have represented_desuspend_natTrans {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C]  (F G : C ⥤ C)
        [F.CommShift ℤ] [G.CommShift ℤ] (α : F ⟶ G) [α.CommShift ℤ]
        (X : C) (n : ℤ) (x : HomotopyGroup n (F.obj (X⟦(1 : ℤ)⟧))) :
        homotopyDesuspend (G.obj X) n
          ((x ≫ α.app (X⟦(1 : ℤ)⟧)) ≫ (G.commShiftIso (1 : ℤ)).hom.app X) =
          homotopyDesuspend (F.obj X) n (x ≫ (F.commShiftIso (1 : ℤ)).hom.app X) ≫
            α.app X := by
      rw [Category.assoc, ← NatTrans.shift_app_comm, ← Category.assoc,
        homotopyDesuspend_postcompose]

    have coaction_desuspend {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [MonoidalPreadditive C] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ]  (X : C) (n : ℤ) (x : Mod2Homology H n (X⟦(1 : ℤ)⟧)) :
        mod2DoubleHomologyDesuspend H X n (mod2CoactionMap H (X⟦(1 : ℤ)⟧) n x) =
          mod2CoactionMap H X (n - 1) (mod2HomologyDesuspend H X n x) := by
      let F := tensorLeft H.HF2
      let α : F ⟶ F ⋙ F := F.leftUnitor.inv ≫ Functor.whiskerRight (mod2UnitNatTrans H) F
      have h := represented_desuspend_natTrans F (F ⋙ F) α X n x
      change homotopyDesuspend (H.HF2 ⊗ (H.HF2 ⊗ X)) n
          (((x ≫ H.HF2 ◁ adamsUnit H.unit (X⟦(1 : ℤ)⟧)) ≫
            H.HF2 ◁ ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app X) ≫
              ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app (H.HF2 ⊗ X)) =
        homotopyDesuspend (H.HF2 ⊗ X) n
          (x ≫ ((tensorLeft H.HF2).commShiftIso (1 : ℤ)).hom.app X) ≫
            H.HF2 ◁ adamsUnit H.unit X
      simp [α, F, mod2UnitNatTrans, Functor.commShiftIso_comp_hom_app,
        Category.assoc] at h
      simp only [Category.assoc]
      convert h using 1 <;> rfl

    have tensorCoaction_desuspend {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [MonoidalPreadditive C] (R : Mod2RingStructure H) [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        (X : C) (n : ℤ) (x : Mod2Homology H n (X⟦(1 : ℤ)⟧)) :
        mod2TensorCoaction H R K X (n - 1) (mod2HomologyDesuspend H X n x) =
          cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i (X⟦(1 : ℤ)⟧))
            (fun i => mod2HomologyF2 H R i X) (mod2HomologyDesuspendF2 H R X) n
            (mod2TensorCoaction H R K (X⟦(1 : ℤ)⟧) n x) := by
      rw [tensorCoaction_apply, ← coaction_desuspend, hK]
      rfl

    have tensorDesuspend_injective {C : Type 1} [StableHomotopyCategory.{1,0} C] (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ] [MonoidalPreadditive C] (R : Mod2RingStructure H) [NatTrans.CommShift (mod2UnitNatTrans H) ℤ]  (X : C) (n : ℤ) :
        Function.Injective
          (cooperationTensorLowerMap H R (fun i => mod2HomologyF2 H R i (X⟦(1 : ℤ)⟧))
            (fun i => mod2HomologyF2 H R i X) (mod2HomologyDesuspendF2 H R X) n) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      dsimp only [cooperationTensorLowerMap, KIP126.Algebra.gradedTensorLowerMap]
      apply (DirectSum.lmap_injective _).mpr
      intro i
      exact (TensorProduct.congr (LinearEquiv.refl (ZMod 2) (Mod2Cooperations H i))
        ((desuspendEquiv H R X (n - i)).trans
          (LinearEquiv.cast (R := ZMod 2) (M := fun j => mod2HomologyF2 H R j X)
            (show n - i - 1 = n - 1 - i by omega)))).injective

    let shiftedConeIso {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)]  {A B Q : C} (α : A ⟶ B)
        (i : B⟦(1 : ℤ)⟧ ⟶ Q) (p : Q ⟶ (A⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)
        (hT : Triangle.mk (α⟦(1 : ℤ)⟧') i p ∈ distTriang C) :
        Q ≅ (HasFunctorialCofiber.cofib α)⟦(1 : ℤ)⟧ := by
      let T := Triangle.mk α (HasFunctorialCofiber.cofibι α) (HasFunctorialCofiber.cofibδ α)
      let eA : A⟦(1 : ℤ)⟧ ≅ A⟦(1 : ℤ)⟧ :=
        ⟨-𝟙 _, -𝟙 _, by simp, by simp⟩
      exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂
        (Triangle.mk (α⟦(1 : ℤ)⟧') i p) ((Triangle.shiftFunctor C (1 : ℤ)).obj T)
        hT (Triangle.shift_distinguished T (HasFunctorialCofiber.cofib_distinguished α) 1)
        eA (Iso.refl _) (by
          simp [T, eA, Triangle.shiftFunctor]
          exact (Category.id_comp _).symm))

    let isoHomologyEquiv {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)  {X Y : C} (e : X ≅ Y) (n : ℤ) :
        mod2HomologyF2 H R n X ≃ₗ[ZMod 2] mod2HomologyF2 H R n Y := {
      toFun := Mod2Homology.pushforward H e.hom n
      invFun := Mod2Homology.pushforward H e.inv n
      left_inv x := by
        change (x ≫ H.HF2 ◁ e.hom) ≫ H.HF2 ◁ e.inv = x
        rw [Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, Category.comp_id]
      right_inv x := by
        change (x ≫ H.HF2 ◁ e.inv) ≫ H.HF2 ◁ e.hom = x
        rw [Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id, Category.comp_id]
      map_add' := (mod2HomologyF2Map H R e.hom n).hom.map_add
      map_smul' := (mod2HomologyF2Map H R e.hom n).hom.map_smul }

    have cast_same   (V : ℤ → Type) [∀ i, AddCommGroup (V i)]
        [∀ i, Module (ZMod 2) (V i)] (i : ℤ) (h : i = i) (x : V i) :
        (LinearEquiv.cast (R := ZMod 2) (M := V) h) x = x := rfl

    let suspendClass {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ]  (X : C) (n : ℤ) (x : mod2HomologyF2 H R n X) :
        mod2HomologyF2 H R (n + 1) (X⟦(1 : ℤ)⟧) :=
      (desuspendEquiv H R X (n + 1)).symm
        ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i X)
          (by omega)) x)

    have nonzero_coordinate_one   {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
        (q : V ≃ₗ[ZMod 2] ZMod 2) (x : V) (hx : x ≠ 0) : q x = 1 := by
      have hn : q x ≠ 0 := fun h => hx (q.map_eq_zero_iff.mp h)
      have htwo (a : ZMod 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp
      exact (htwo _).resolve_left hn

    have nonzero_eq_basis   {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
        (q : V ≃ₗ[ZMod 2] ZMod 2) (x : V) (hx : x ≠ 0) : x = q.symm 1 := by
      apply q.injective
      rw [q.apply_symm_apply]
      exact nonzero_coordinate_one q x hx

    let shiftedCoordinate {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ]  {X Q : C} (e : Q ≅ X⟦(1 : ℤ)⟧)
        (n : ℤ) (q : mod2HomologyF2 H R n X ≃ₗ[ZMod 2] ZMod 2) :
        mod2HomologyF2 H R (n + 1) Q ≃ₗ[ZMod 2] ZMod 2 :=
      (((isoHomologyEquiv H R e (n + 1)).trans (desuspendEquiv H R X (n + 1))).trans
        (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i X)
          (by omega))).trans q

    have shiftedCoordinate_basis {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ]  {X Q : C} (e : Q ≅ X⟦(1 : ℤ)⟧)
        (n : ℤ) (q : mod2HomologyF2 H R n X ≃ₗ[ZMod 2] ZMod 2) :
        (shiftedCoordinate H R e n q).symm 1 =
          Mod2Homology.pushforward H e.inv (n + 1) (suspendClass H R X n (q.symm 1)) := by
      apply (shiftedCoordinate H R e n q).injective
      rw [LinearEquiv.apply_symm_apply]
      change 1 = q ((LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i X)
        (by omega)) ((desuspendEquiv H R X (n + 1))
          ((isoHomologyEquiv H R e (n + 1))
            ((isoHomologyEquiv H R e (n + 1)).symm (suspendClass H R X n (q.symm 1))))))
      rw [LinearEquiv.apply_symm_apply]
      simp only [suspendClass, LinearEquiv.apply_symm_apply]
      rw [cast_cast]
      simp only [cast_same, LinearEquiv.apply_symm_apply]

    have suspend_twoCell_coaction {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        (X : C) (d : ℤ) (hd : d = 1 ∨ d = 2)
        (e0 : mod2HomologyF2 H R 0 X) (ed : mod2HomologyF2 H R d X)
        (u : mod2HomologyF2 H R d H.HF2)
        (hψ : mod2TensorCoaction H R K X d ed =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) d ed +
          DirectSum.lof (ZMod 2) ℤ _ d (u ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i X)
              (sub_self d).symm) e0)) :
        mod2TensorCoaction H R K (X⟦(1 : ℤ)⟧) (d + 1) (suspendClass H R X d ed) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i (X⟦(1 : ℤ)⟧)) (d + 1)
            (suspendClass H R X d ed) +
          DirectSum.lof (ZMod 2) ℤ _ d (u ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i (X⟦(1 : ℤ)⟧))
              (by omega)) (suspendClass H R X 0 e0)) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      rcases hd with rfl | rfl
      · apply tensorDesuspend_injective H R X
        rw [← tensorCoaction_desuspend H R K hK, map_add, tensorLowerMap_unit]
        simp only [cooperationTensorLowerMap,
          KIP126.Algebra.gradedTensorLowerMap_lof_tmul]
        change mod2TensorCoaction H R K X 1
            ((desuspendEquiv H R X 2) ((desuspendEquiv H R X 2).symm ed)) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 1
            ((desuspendEquiv H R X 2) ((desuspendEquiv H R X 2).symm ed)) +
          DirectSum.lof (ZMod 2) ℤ
            (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (1 - i) X) 1
            (u ⊗ₜ[ZMod 2] (desuspendEquiv H R X 1) ((desuspendEquiv H R X 1).symm e0))
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact hψ
      · apply tensorDesuspend_injective H R X
        rw [← tensorCoaction_desuspend H R K hK, map_add, tensorLowerMap_unit]
        simp only [cooperationTensorLowerMap,
          KIP126.Algebra.gradedTensorLowerMap_lof_tmul]
        change mod2TensorCoaction H R K X 2
            ((desuspendEquiv H R X 3) ((desuspendEquiv H R X 3).symm ed)) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 2
            ((desuspendEquiv H R X 3) ((desuspendEquiv H R X 3).symm ed)) +
          DirectSum.lof (ZMod 2) ℤ
            (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (2 - i) X) 2
            (u ⊗ₜ[ZMod 2] (desuspendEquiv H R X 1) ((desuspendEquiv H R X 1).symm e0))
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact hψ

    -- Naturality transports the suspended formula through any spectrum isomorphism.

    have iso_suspended_twoCell_coaction {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        {X Q : C} (e : Q ≅ X⟦(1 : ℤ)⟧) (d : ℤ) (hd : d = 1 ∨ d = 2)
        (e0 : mod2HomologyF2 H R 0 X) (ed : mod2HomologyF2 H R d X)
        (u : mod2HomologyF2 H R d H.HF2)
        (hψ : mod2TensorCoaction H R K X d ed =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) d ed +
          DirectSum.lof (ZMod 2) ℤ _ d (u ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i X)
              (sub_self d).symm) e0)) :
        mod2TensorCoaction H R K Q (d + 1)
            (Mod2Homology.pushforward H e.inv (d + 1) (suspendClass H R X d ed)) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i Q) (d + 1)
            (Mod2Homology.pushforward H e.inv (d + 1) (suspendClass H R X d ed)) +
          DirectSum.lof (ZMod 2) ℤ _ d (u ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i Q)
              (by omega))
              (Mod2Homology.pushforward H e.inv 1 (suspendClass H R X 0 e0))) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      rw [tensorCoaction_naturality, suspend_twoCell_coaction H R K hK X d hd e0 ed u hψ,
        map_add, tensorUnit_naturality]
      congr 1
      simp [cooperationTensorMap, KIP126.Algebra.gradedTensorMapRight,
        homologyPushforward_cast]
      congr 2
      exact homologyPushforward_cast H R e.inv 1 (d + 1 - d)
        (by omega) (suspendClass H R X 0 e0)

    have shifted_coordinate_coaction {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        {X Q : C} (e : Q ≅ X⟦(1 : ℤ)⟧) (d : ℤ) (hd : d = 1 ∨ d = 2)
        (q0 : mod2HomologyF2 H R 0 X ≃ₗ[ZMod 2] ZMod 2)
        (qd : mod2HomologyF2 H R d X ≃ₗ[ZMod 2] ZMod 2)
        (u : mod2HomologyF2 H R d H.HF2)
        (hψ : mod2TensorCoaction H R K X d (qd.symm 1) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) d (qd.symm 1) +
          DirectSum.lof (ZMod 2) ℤ _ d (u ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i X)
              (sub_self d).symm) (q0.symm 1))) :
        mod2TensorCoaction H R K Q (d + 1) ((shiftedCoordinate H R e d qd).symm 1) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i Q) (d + 1)
            ((shiftedCoordinate H R e d qd).symm 1) +
          DirectSum.lof (ZMod 2) ℤ _ d (u ⊗ₜ[ZMod 2]
            (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i Q)
              (by omega)) ((shiftedCoordinate H R e 0 q0).symm 1)) := by
      rw [shiftedCoordinate_basis, shiftedCoordinate_basis]
      exact iso_suspended_twoCell_coaction H R K hK e d hd (q0.symm 1) (qd.symm 1) u hψ

    let zeroShiftConeIso {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)]  (f : (SphereSpectrum : C) ⟶ SphereSpectrum) :
        HasFunctorialCofiber.cofib ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ f) ≅
          HasFunctorialCofiber.cofib f := by
      let e : Sphere (C := C) 0 ≅ SphereSpectrum := (shiftFunctorZero C ℤ).app SphereSpectrum
      exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂
        (Triangle.mk (e.hom ≫ f) (HasFunctorialCofiber.cofibι (e.hom ≫ f))
          (HasFunctorialCofiber.cofibδ (e.hom ≫ f)))
        (Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f))
        (HasFunctorialCofiber.cofib_distinguished (e.hom ≫ f))
        (HasFunctorialCofiber.cofib_distinguished f) e (Iso.refl _) (by
          change (e.hom ≫ f) ≫ 𝟙 _ = e.hom ≫ f
          rw [Category.comp_id]))

    let twoCellOneTopCoordinate {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
        (f : Sphere (C := C) 0 ⟶ SphereSpectrum) (hf : H.HF2 ◁ f = 0) :
        mod2HomologyF2 H R 1 (HasFunctorialCofiber.cofib f) ≃ₗ[ZMod 2] ZMod 2 :=
      ((twoCell_top_equiv H R 1 (by decide) f hf).trans
        (isoHomologyEquiv H R ((shiftFunctorZero C ℤ).app SphereSpectrum) 0)).trans
          (sphereZeroCoordinate H R)

    have square_homology_geometry {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ]
        (η : Sphere (C := C) 1 ⟶ SphereSpectrum) (hη : η⟦(1 : ℤ)⟧' ≫ η = 0) :
        ∃ (b : HasFunctorialCofiber.cofib (η⟦(1 : ℤ)⟧') ⟶ SphereSpectrum)
          (c : HasFunctorialCofiber.cofib η ⟶ HasFunctorialCofiber.cofib b),
          HasFunctorialCofiber.cofibι (η⟦(1 : ℤ)⟧') ≫ b = η ∧
          HasFunctorialCofiber.cofibι η ≫ c = HasFunctorialCofiber.cofibι b ∧
          HasFunctorialCofiber.cofibδ η ≫
              (HasFunctorialCofiber.cofibι (η⟦(1 : ℤ)⟧'))⟦(1 : ℤ)⟧' =
            c ≫ HasFunctorialCofiber.cofibδ b ∧
          (∀ n, n ≠ 1 → n ≠ 3 →
            Subsingleton (Mod2Homology H n (HasFunctorialCofiber.cofib (η⟦(1 : ℤ)⟧')))) ∧
          (∀ n, Mod2Homology.pushforward H b n = 0) ∧
          (∀ n, n ≠ 0 → n ≠ 2 → n ≠ 4 →
            Subsingleton (Mod2Homology H n (HasFunctorialCofiber.cofib b))) := by
      obtain ⟨b, hb, c, hc, hδ⟩ := double_cone_geometry (η⟦(1 : ℤ)⟧') η hη
      let Q := HasFunctorialCofiber.cofib (η⟦(1 : ℤ)⟧')
      let e : Q ≅ (HasFunctorialCofiber.cofib η)⟦(1 : ℤ)⟧ :=
        shiftedConeIso η (HasFunctorialCofiber.cofibι (η⟦(1 : ℤ)⟧'))
          (HasFunctorialCofiber.cofibδ (η⟦(1 : ℤ)⟧'))
          (HasFunctorialCofiber.cofib_distinguished (η⟦(1 : ℤ)⟧'))
      have hQ (n : ℤ) (hn1 : n ≠ 1) (hn3 : n ≠ 3) :
          Subsingleton (Mod2Homology H n Q) := by
        letI : Subsingleton (mod2HomologyF2 H R (n - 1) (HasFunctorialCofiber.cofib η)) := by
          exact twoCell_otherDegrees H 2 η (n - 1) (by omega) (by omega)
        exact ((isoHomologyEquiv H R e n).trans
          (desuspendEquiv H R (HasFunctorialCofiber.cofib η) n)).injective.subsingleton
      have hbzero (n : ℤ) : Mod2Homology.pushforward H b n = 0 := by
        apply pushforward_zero_of_disjoint_support H b n
        by_cases hn : n = 0
        · subst n
          exact Or.inl (hQ 0 (by decide) (by decide))
        · exact Or.inr (sphereHomologySubsingleton H n hn)
      have hE (n : ℤ) (hn0 : n ≠ 0) (hn2 : n ≠ 2) (hn4 : n ≠ 4) :
          Subsingleton (Mod2Homology H n (HasFunctorialCofiber.cofib b)) :=
        homology_middle_subsingleton H (HoCofiberSequence.ofMorphism b) n
          (sphereHomologySubsingleton H n hn0) (hQ (n-1) (by omega) (by omega))
      exact ⟨b, c, hb, hc, hδ, hQ, hbzero, hE⟩

    have boundary_one_coefficient {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        (T : HoCofiberSequence (C := C)) (n k : ℤ)
        (zt : mod2HomologyF2 H R n T.Z)
        (zm : mod2HomologyF2 H R (n-k) T.Z)
        (zb : mod2HomologyF2 H R (n-n) T.Z)
        (xt : mod2HomologyF2 H R (n-1) T.X)
        (xm : mod2HomologyF2 H R (n-1-k) T.X)
        (q : mod2HomologyF2 H R (n-1-k) T.X →ₗ[ZMod 2] ZMod 2) (hqm : q xm = 1)
        (a c : mod2HomologyF2 H R k H.HF2) (b : mod2HomologyF2 H R n H.HF2)
        (hdt : boundaryF2 H R T n zt = xt)
        (hdm : (LinearEquiv.cast (R := ZMod 2) (M := fun i => mod2HomologyF2 H R i T.X)
          (show n-k-1=n-1-k by omega)) (boundaryF2 H R T (n-k) zm) = xm)
        (hdb : boundaryF2 H R T (n-n) zb = 0)
        (hX : mod2TensorCoaction H R K T.X (n-1) xt =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i T.X) (n-1) xt +
          tensorTerm H R (fun i => mod2HomologyF2 H R i T.X) (n-1) k a xm)
        (hZ : mod2TensorCoaction H R K T.Z n zt =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i T.Z) n zt +
          tensorTerm H R (fun i => mod2HomologyF2 H R i T.Z) n k c zm +
          tensorTerm H R (fun i => mod2HomologyF2 H R i T.Z) n n b zb) : c = a := by
      have hu := tensorLowerMap_unit H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n zt
      have hu' := hu.trans (congrArg (cooperationTensorUnit H R (fun d => mod2HomologyF2 H R d T.X) (n-1)) hdt)
      have hm := tensorLowerMap_term H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n k c zm
      have hm' := hm.trans (congrArg (tensorTerm H R (fun d => mod2HomologyF2 H R d T.X) (n-1) k c) hdm)
      have hb := tensorLowerMap_term H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n n b zb
      rw [hdb, map_zero] at hb
      have hb' := hb.trans (tensorTerm_zero H R (fun d => mod2HomologyF2 H R d T.X) (n-1) n b)
      have hmap := congrArg (cooperationTensorLowerMap H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n) hZ
      rw [map_add, map_add] at hmap
      have hmap' := hmap.trans (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu' hm') hb')
      have h := tensorCoaction_boundary H R K hK T n zt
      change mod2TensorCoaction H R K T.X (n-1) (boundaryF2 H R T n zt) = _ at h
      rw [hdt, hX] at h
      have he := h.trans (hmap'.trans (add_zero _))
      exact tensorTerm_coefficient_injective H R (fun d => mod2HomologyF2 H R d T.X)
        (n-1) k xm q hqm (add_left_cancel he).symm

    have boundary_two_coefficients {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (K : Mod2CooperationKunneth H R)  (hK : Mod2KunnethSuspensionCompatible H R K)
        (T : HoCofiberSequence (C := C)) (n i j : ℤ) (hij : i ≠ j)
        (zt : mod2HomologyF2 H R n T.Z)
        (zi : mod2HomologyF2 H R (n-i) T.Z) (zj : mod2HomologyF2 H R (n-j) T.Z)
        (zb : mod2HomologyF2 H R (n-n) T.Z)
        (xt : mod2HomologyF2 H R (n-1) T.X)
        (xi : mod2HomologyF2 H R (n-1-i) T.X) (xj : mod2HomologyF2 H R (n-1-j) T.X)
        (qi : mod2HomologyF2 H R (n-1-i) T.X →ₗ[ZMod 2] ZMod 2) (hqi : qi xi = 1)
        (qj : mod2HomologyF2 H R (n-1-j) T.X →ₗ[ZMod 2] ZMod 2) (hqj : qj xj = 1)
        (ai ci : mod2HomologyF2 H R i H.HF2) (aj cj : mod2HomologyF2 H R j H.HF2)
        (b : mod2HomologyF2 H R n H.HF2)
        (hdt : boundaryF2 H R T n zt = xt)
        (hdi : (LinearEquiv.cast (R := ZMod 2) (M := fun d => mod2HomologyF2 H R d T.X)
          (show n-i-1=n-1-i by omega)) (boundaryF2 H R T (n-i) zi) = xi)
        (hdj : (LinearEquiv.cast (R := ZMod 2) (M := fun d => mod2HomologyF2 H R d T.X)
          (show n-j-1=n-1-j by omega)) (boundaryF2 H R T (n-j) zj) = xj)
        (hdb : boundaryF2 H R T (n-n) zb = 0)
        (hX : mod2TensorCoaction H R K T.X (n-1) xt =
          cooperationTensorUnit H R (fun d => mod2HomologyF2 H R d T.X) (n-1) xt +
          tensorTerm H R (fun d => mod2HomologyF2 H R d T.X) (n-1) i ai xi +
          tensorTerm H R (fun d => mod2HomologyF2 H R d T.X) (n-1) j aj xj)
        (hZ : mod2TensorCoaction H R K T.Z n zt =
          cooperationTensorUnit H R (fun d => mod2HomologyF2 H R d T.Z) n zt +
          tensorTerm H R (fun d => mod2HomologyF2 H R d T.Z) n i ci zi +
          tensorTerm H R (fun d => mod2HomologyF2 H R d T.Z) n j cj zj +
          tensorTerm H R (fun d => mod2HomologyF2 H R d T.Z) n n b zb) : ci = ai ∧ cj = aj := by
      have hu := tensorLowerMap_unit H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n zt
      have hu' := hu.trans (congrArg (cooperationTensorUnit H R (fun d => mod2HomologyF2 H R d T.X) (n-1)) hdt)
      have hi := tensorLowerMap_term H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n i ci zi
      have hi' := hi.trans (congrArg (tensorTerm H R (fun d => mod2HomologyF2 H R d T.X) (n-1) i ci) hdi)
      have hj := tensorLowerMap_term H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n j cj zj
      have hj' := hj.trans (congrArg (tensorTerm H R (fun d => mod2HomologyF2 H R d T.X) (n-1) j cj) hdj)
      have hb := tensorLowerMap_term H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n n b zb
      rw [hdb, map_zero] at hb
      have hb' := hb.trans (tensorTerm_zero H R (fun d => mod2HomologyF2 H R d T.X) (n-1) n b)
      have hmap := congrArg (cooperationTensorLowerMap H R (fun d => mod2HomologyF2 H R d T.Z) (fun d => mod2HomologyF2 H R d T.X) (boundaryF2 H R T) n) hZ
      rw [map_add, map_add, map_add] at hmap
      have hmap' := hmap.trans
        (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) hu' hi') hj') hb')
      have h := tensorCoaction_boundary H R K hK T n zt
      change mod2TensorCoaction H R K T.X (n-1) (boundaryF2 H R T n zt) = _ at h
      rw [hdt, hX] at h
      have he := h.trans (hmap'.trans (add_zero _))
      rw [add_assoc, add_assoc] at he
      exact tensorTerms_two_unique H R (fun d => mod2HomologyF2 H R d T.X)
        (n-1) i j hij xi qi hqi xj qj hqj ci ai cj aj (add_left_cancel he).symm

    have square_zero_forces_coproduct {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (B : Mod2ReducedMilnorBasis H R) (K : Mod2CooperationKunneth H R)
        (hK : Mod2KunnethSuspensionCompatible H R K)
        (hU : Mod2KunnethUnitCompatible H R K)
        (hD : Mod2KunnethDiagonalCompatible H R K)
        (η : Sphere (C := C) 1 ⟶ SphereSpectrum)
        (qC0 : mod2HomologyF2 H R 0 (HasFunctorialCofiber.cofib η) ≃ₗ[ZMod 2] ZMod 2)
        (qC2 : mod2HomologyF2 H R 2 (HasFunctorialCofiber.cofib η) ≃ₗ[ZMod 2] ZMod 2)
        (u : mod2HomologyF2 H R 2 H.HF2)
        (hC2 : mod2TensorCoaction H R K (HasFunctorialCofiber.cofib η) 2 (qC2.symm 1) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η)) 2 (qC2.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η)) 2 2 u (qC0.symm 1))
        (hη : η⟦(1 : ℤ)⟧' ≫ η = 0) :
        ∃ a : mod2HomologyF2 H R 4 H.HF2,
          cooperationTensorDiagonal H R K 4 a =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i H.HF2) 4 a +
            tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 2 u u +
            tensorTerm H R (fun i => mod2HomologyF2 H R i H.HF2) 4 4 a (cooperationUnit H) := by
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      obtain ⟨b, c, hib, hc, hδ, hQ, hbzero, hE⟩ := square_homology_geometry H R η hη
      let Q := HasFunctorialCofiber.cofib (η⟦(1 : ℤ)⟧')
      let E := HasFunctorialCofiber.cofib b
      let TC := HoCofiberSequence.ofMorphism η
      let TQ := HoCofiberSequence.ofMorphism (η⟦(1 : ℤ)⟧')
      let TE := HoCofiberSequence.ofMorphism b
      let e : Q ≅ (HasFunctorialCofiber.cofib η)⟦(1 : ℤ)⟧ :=
        shiftedConeIso η (HasFunctorialCofiber.cofibι (η⟦(1 : ℤ)⟧'))
          (HasFunctorialCofiber.cofibδ (η⟦(1 : ℤ)⟧'))
          (HasFunctorialCofiber.cofib_distinguished (η⟦(1 : ℤ)⟧'))
      let qQ1 : mod2HomologyF2 H R 1 Q ≃ₗ[ZMod 2] ZMod 2 := shiftedCoordinate H R e 0 qC0
      let qQ3 : mod2HomologyF2 H R 3 Q ≃ₗ[ZMod 2] ZMod 2 := shiftedCoordinate H R e 2 qC2
      let eE0 := bottomEquiv_of_homology_zero H R TE 0 (hbzero 0)
        (by exact hQ (-1) (by decide) (by decide))
      let eE2 := boundaryEquiv_of_homology_zero H R TE 2 (hbzero 1)
        (sphereHomologySubsingleton H 2 (by decide))
      let eE4 := boundaryEquiv_of_homology_zero H R TE 4 (hbzero 3)
        (sphereHomologySubsingleton H 4 (by decide))
      let qE0 : mod2HomologyF2 H R 0 E ≃ₗ[ZMod 2] ZMod 2 := eE0.symm.trans (sphereZeroCoordinate H R)
      let qE2 : mod2HomologyF2 H R 2 E ≃ₗ[ZMod 2] ZMod 2 := eE2.trans qQ1
      let qE4 : mod2HomologyF2 H R 4 E ≃ₗ[ZMod 2] ZMod 2 := eE4.trans qQ3
      have hQ3 : mod2TensorCoaction H R K Q 3 (qQ3.symm 1) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i Q) 3 (qQ3.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i Q) 3 2 u (qQ1.symm 1) := by
        exact shifted_coordinate_coaction H R K hK e 2 (Or.inr rfl) qC0 qC2 u hC2
      have hiQ : Function.Injective (Mod2Homology.pushforward H TQ.g 1) := by
        apply bottom_injective_of_homology_zero H TQ 1
        apply pushforward_zero_of_disjoint_support H TQ.f 1
        apply Or.inl
        letI : Subsingleton (mod2HomologyF2 H R (1 - 1) (Sphere (C := C) 1)) := by
          exact sphereHomologyShiftSubsingleton H 0 1 (by decide)
        exact (desuspendEquiv H R (Sphere (C := C) 1) 1).injective.subsingleton
      have hE2 : mod2TensorCoaction H R K E 2 (qE2.symm 1) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i E) 2 (qE2.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i E) 2 2 u (qE0.symm 1) := by
        exact comparison_twoCell_transfer H R K TC TE TQ.g (𝟙 SphereSpectrum) c
          (by simpa only [TC, TE, HoCofiberSequence.ofMorphism, Category.id_comp] using hc) hδ 2 qC0 qC2 qE0 qE2 u
          (homology_bottom_surjective H TC 0
            (by exact sphereHomologyShiftSubsingleton H (-1) 1 (by decide)))
          (isoHomologyEquiv H R (Iso.refl SphereSpectrum) 0).injective
          eE0.injective (boundary_injective_of_target_zero H TC 2
            (sphereHomologySubsingleton H 2 (by decide))) hiQ hC2
      let eSphere : mod2HomologyF2 H R 0 SphereSpectrum :=
        (shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ adamsUnit H.unit SphereSpectrum
      have hE0basis : qE0.symm 1 = Mod2Homology.pushforward H TE.g 0 eSphere := by
        apply qE0.injective
        rw [LinearEquiv.apply_symm_apply]
        change 1 = sphereZeroCoordinate H R (eE0.symm (eE0 eSphere))
        rw [LinearEquiv.symm_apply_apply, sphereZeroCoordinate_unit]
      have hE0 : mod2TensorCoaction H R K E 0 (qE0.symm 1) =
          cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i E) 0 (qE0.symm 1) := by
        rw [hE0basis]
        exact transfer_unit H R K TE.g 0 eSphere
          (coaction_of_unit_image H R K hU SphereSpectrum 0 ((shiftFunctorZero C ℤ).hom.app SphereSpectrum))
      obtain ⟨c2, a, hE4⟩ := threeCell_coaction_expansion H R B K E hE qE0 qE2 (qE4.symm 1)
      have hb4 : boundaryF2 H R TE 4 (qE4.symm 1) = qQ3.symm 1 := by
        change eE4 (eE4.symm (qQ3.symm 1)) = _
        exact eE4.apply_symm_apply _
      have hb2 : boundaryF2 H R TE 2 (qE2.symm 1) = qQ1.symm 1 := by
        change eE2 (eE2.symm (qQ1.symm 1)) = _
        exact eE2.apply_symm_apply _
      have hb0 : boundaryF2 H R TE 0 (qE0.symm 1) = 0 :=
        (hQ (-1) (by decide) (by decide)).elim _ _
      change mod2TensorCoaction H R K E 4 (qE4.symm 1) =
        cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i E) 4 (qE4.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i E) 4 2 c2 (qE2.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i E) 4 4 a (qE0.symm 1) at hE4
      have hc2 : c2 = u := boundary_one_coefficient H R K hK
        TE 4 2 (qE4.symm 1) (qE2.symm 1) (qE0.symm 1)
        (qQ3.symm 1) (qQ1.symm 1) qQ1.toLinearMap (qQ1.apply_symm_apply 1)
        u c2 a hb4 (by exact hb2) hb0 hQ3 hE4
      rw [hc2] at hE4
      exact ⟨a, threeCell_matrix H R K hD E qE0.toLinearMap (qE0.symm 1)
        (qE0.apply_symm_apply 1) (qE2.symm 1) (qE4.symm 1) u a hE0 hE2 hE4⟩

    have fourCell_degree3_expansion {C : Type 1} [StableHomotopyCategory.{1,0} C] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) (B : Mod2ReducedMilnorBasis H R)  (K : Mod2CooperationKunneth H R)
        (X : C)
        (hX : ∀ i, i ≠ 0 → i ≠ 1 → i ≠ 3 → i ≠ 4 → Subsingleton (Mod2Homology H i X))
        (q0 : mod2HomologyF2 H R 0 X ≃ₗ[ZMod 2] ZMod 2)
        (q2 : mod2HomologyF2 H R 1 X ≃ₗ[ZMod 2] ZMod 2)
        (e4 : mod2HomologyF2 H R 3 X) :
        ∃ (c2 : mod2HomologyF2 H R 2 H.HF2) (c4 : mod2HomologyF2 H R 3 H.HF2),
          mod2TensorCoaction H R K X 3 e4 =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 e4 +
            DirectSum.lof (ZMod 2) ℤ _ 2 (c2 ⊗ₜ[ZMod 2] q2.symm 1) +
            DirectSum.lof (ZMod 2) ℤ _ 3 (c4 ⊗ₜ[ZMod 2] q0.symm 1) := by
      classical
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      let z := mod2TensorCoaction H R K X 3 e4
      obtain ⟨w, hw⟩ := zeroTensor_unit_factor H R B (z 0)
      obtain ⟨c2, hc2⟩ := tensor_rank_one q2 (z 2)
      obtain ⟨c4, hc4⟩ := tensor_rank_one q0 (z 3)
      have hd := directSum_supported_decomposition
        (fun i => Mod2Cooperations H i ⊗[ZMod 2] mod2HomologyF2 H R (3-i) X)
        {0, 2, 3} (fun i hi => by
          have his : i ≠ 0 ∧ i ≠ 2 ∧ i ≠ 3 := by simpa using hi
          by_cases hin : i = -1
          · subst i
            letI : Subsingleton (Mod2Cooperations H (-1)) :=
              negative_cooperation_subsingleton H R B (-1) (by decide)
            infer_instance
          · letI : Subsingleton (mod2HomologyF2 H R (3-i) X) :=
              hX (3-i) (by omega) (by omega) (by omega) (by omega)
            infer_instance) z
      simp only [Finset.sum_insert (show (0 : ℤ) ∉ {2, 3} by decide),
        Finset.sum_insert (show (2 : ℤ) ∉ {3} by decide), Finset.sum_singleton] at hd
      rw [hw, hc2, hc4] at hd
      have he := congrArg (cooperationTensorAugmentation H R
        (fun i => mod2HomologyF2 H R i X) 3) hd
      change cooperationTensorAugmentation H R _ 3 z = _ at he
      rw [map_add, map_add,
        positiveTensor_augmentation_zero H R _ 3 2 (by decide),
        positiveTensor_augmentation_zero H R _ 3 3 (by decide), add_zero, add_zero] at he
      change cooperationTensorAugmentation H R _ 3 z =
        cooperationTensorAugmentation H R _ 3
          (cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 w) at he
      rw [cooperationTensorUnit_augmentation] at he
      have he4 : e4 = w := by
        rw [← he]
        exact (tensorCoaction_counit H R K X 3 e4).symm
      refine ⟨c2, c4, ?_⟩
      have hu : cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i X) 3 e4 =
          DirectSum.lof (ZMod 2) ℤ _ 0 (cooperationUnit H ⊗ₜ[ZMod 2] e4) := rfl
      rw [hu]
      simpa only [← he4, add_assoc] using hd

    let coneBottomCoordinate {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  {Q : C} (b : Q ⟶ SphereSpectrum)
        (hb : Mod2Homology.pushforward H b 0 = 0)
        (hQ : Subsingleton (Mod2Homology H (-1) Q)) :
        mod2HomologyF2 H R 0 (HasFunctorialCofiber.cofib b) ≃ₗ[ZMod 2] ZMod 2 :=
      (bottomEquiv_of_homology_zero H R (HoCofiberSequence.ofMorphism b) 0 hb
        (by exact hQ)).symm.trans (sphereZeroCoordinate H R)

    let coneAboveCoordinate {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  {Q : C} (b : Q ⟶ SphereSpectrum)
        (n : ℤ) (hn : n ≠ 0)
        (hb : Mod2Homology.pushforward H b (n-1) = 0)
        (q : mod2HomologyF2 H R (n-1) Q ≃ₗ[ZMod 2] ZMod 2) :
        mod2HomologyF2 H R n (HasFunctorialCofiber.cofib b) ≃ₗ[ZMod 2] ZMod 2 :=
      (boundaryEquiv_of_homology_zero H R (HoCofiberSequence.ofMorphism b) n hb
        (sphereHomologySubsingleton H n hn)).trans q

    have coneAboveCoordinate_boundary {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  {Q : C} (b : Q ⟶ SphereSpectrum)
        (n : ℤ) (hn : n ≠ 0)
        (hb : Mod2Homology.pushforward H b (n-1) = 0)
        (q : mod2HomologyF2 H R (n-1) Q ≃ₗ[ZMod 2] ZMod 2) :
        boundaryF2 H R (HoCofiberSequence.ofMorphism b) n
          ((coneAboveCoordinate H R b n hn hb q).symm 1) = q.symm 1 := by
      change (boundaryEquiv_of_homology_zero H R (HoCofiberSequence.ofMorphism b) n hb
        (sphereHomologySubsingleton H n hn))
          ((boundaryEquiv_of_homology_zero H R (HoCofiberSequence.ofMorphism b) n hb
            (sphereHomologySubsingleton H n hn)).symm (q.symm 1)) = q.symm 1
      exact LinearEquiv.apply_symm_apply _ _

    have coneBottomCoordinate_generator {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  {Q : C} (b : Q ⟶ SphereSpectrum)
        (hb : Mod2Homology.pushforward H b 0 = 0)
        (hQ : Subsingleton (Mod2Homology H (-1) Q)) :
        (coneBottomCoordinate H R b hb hQ).symm 1 =
          Mod2Homology.pushforward H (HasFunctorialCofiber.cofibι b) 0
            ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ adamsUnit H.unit SphereSpectrum) := by
      apply (coneBottomCoordinate H R b hb hQ).injective
      rw [LinearEquiv.apply_symm_apply]
      change 1 = sphereZeroCoordinate H R
        ((bottomEquiv_of_homology_zero H R (HoCofiberSequence.ofMorphism b) 0 hb
          (by exact hQ)).symm
          ((bottomEquiv_of_homology_zero H R (HoCofiberSequence.ofMorphism b) 0 hb
            (by exact hQ)) _))
      rw [LinearEquiv.symm_apply_apply]
      exact (sphereZeroCoordinate_unit H R).symm

    have coneBottomCoordinate_coaction {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]  (K : Mod2CooperationKunneth H R)
        (hU : Mod2KunnethUnitCompatible H R K)
        {Q : C} (b : Q ⟶ SphereSpectrum)
        (hb : Mod2Homology.pushforward H b 0 = 0)
        (hQ : Subsingleton (Mod2Homology H (-1) Q)) :
        mod2TensorCoaction H R K (HasFunctorialCofiber.cofib b) 0
          ((coneBottomCoordinate H R b hb hQ).symm 1) =
        cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib b)) 0
          ((coneBottomCoordinate H R b hb hQ).symm 1) := by
      rw [coneBottomCoordinate_generator H R b hb hQ]
      exact transfer_unit H R K (HasFunctorialCofiber.cofibι b) 0 _
        (coaction_of_unit_image H R K hU SphereSpectrum 0
          ((shiftFunctorZero C ℤ).hom.app SphereSpectrum))

    have toda_matrix_exists {C : Type 1} [StableHomotopyCategory.{1,0} C] [HasFunctorialCofiber (C := C)] [MonoidalPreadditive C] (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H) [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated] [NatTrans.CommShift (mod2UnitNatTrans H) ℤ] (B : Mod2ReducedMilnorBasis H R) (K : Mod2CooperationKunneth H R)
        (hK : Mod2KunnethSuspensionCompatible H R K)
        (hD : Mod2KunnethDiagonalCompatible H R K)
        (hU : Mod2KunnethUnitCompatible H R K)
        (η : Sphere (C := C) 1 ⟶ SphereSpectrum)
        (x : mod2HomologyF2 H R 1 H.HF2) (u : mod2HomologyF2 H R 2 H.HF2)
        (q20 : mod2HomologyF2 H R 0 (HasFunctorialCofiber.cofib (2 • 𝟙 (SphereSpectrum : C))) ≃ₗ[ZMod 2] ZMod 2)
        (q21 : mod2HomologyF2 H R 1 (HasFunctorialCofiber.cofib (2 • 𝟙 (SphereSpectrum : C))) ≃ₗ[ZMod 2] ZMod 2)
        (qη0 : mod2HomologyF2 H R 0 (HasFunctorialCofiber.cofib η) ≃ₗ[ZMod 2] ZMod 2)
        (qη2 : mod2HomologyF2 H R 2 (HasFunctorialCofiber.cofib η) ≃ₗ[ZMod 2] ZMod 2)
        (hψ2 : mod2TensorCoaction H R K (HasFunctorialCofiber.cofib (2 • 𝟙 (SphereSpectrum : C))) 1 (q21.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n (HasFunctorialCofiber.cofib (2 • 𝟙 (SphereSpectrum : C)))) 1 (q21.symm 1) +
          tensorTerm H R (fun n => mod2HomologyF2 H R n (HasFunctorialCofiber.cofib (2 • 𝟙 (SphereSpectrum : C)))) 1 1 x (q20.symm 1))
        (hψη : mod2TensorCoaction H R K (HasFunctorialCofiber.cofib η) 2 (qη2.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n (HasFunctorialCofiber.cofib η)) 2 (qη2.symm 1) +
          tensorTerm H R (fun n => mod2HomologyF2 H R n (HasFunctorialCofiber.cofib η)) 2 2 u (qη0.symm 1))
        (hToda : Toda.Relation (0 : (Sphere (C := C) 1)⟦(1 : ℤ)⟧ ⟶ SphereSpectrum)
          (2 • 𝟙 (Sphere (C := C) 1)) η (2 • 𝟙 SphereSpectrum)) :
        ∃ (a b : mod2HomologyF2 H R 3 H.HF2) (c : mod2HomologyF2 H R 4 H.HF2),
          (cooperationTensorDiagonal H R K 3 a =
            cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n H.HF2) 3 a +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 3 2 u x +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 3 3 a (cooperationUnit H)) ∧
          (cooperationTensorDiagonal H R K 3 b =
            cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n H.HF2) 3 b +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 3 1 x u +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 3 3 b (cooperationUnit H)) ∧
          (cooperationTensorDiagonal H R K 4 c =
            cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n H.HF2) 4 c +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 4 1 x a +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 4 3 b x +
            tensorTerm H R (fun n => mod2HomologyF2 H R n H.HF2) 4 4 c (cooperationUnit H)) := by
      classical
      obtain ⟨Q, i, p, hT, b, t, hib, hb2, ht, hQ, hbzero, hX, htzero, hE⟩ :=
        toda_homology_geometry H R η hToda
      let TQ : HoCofiberSequence (C := C) :=
        ⟨Sphere 1, Sphere 1, Q, 2 • 𝟙 _, i, p, hT⟩
      let TX := HoCofiberSequence.ofMorphism b
      let TE := HoCofiberSequence.ofMorphism t
      let Tη := HoCofiberSequence.ofMorphism η
      let T2 := HoCofiberSequence.ofMorphism (2 • 𝟙 (SphereSpectrum : C))
      have hTshift : Triangle.mk ((2 • 𝟙 (SphereSpectrum : C))⟦(1 : ℤ)⟧') i p ∈ distTriang C := by
        have hmap : ((2 • 𝟙 (SphereSpectrum : C))⟦(1 : ℤ)⟧') = 2 • 𝟙 (Sphere (C := C) 1) := by
          calc
            _ = 2 • (shiftFunctor C (1 : ℤ)).map (𝟙 (SphereSpectrum : C)) := Functor.map_nsmul _
            _ = 2 • 𝟙 (Sphere (C := C) 1) :=
              congrArg (fun f : Sphere (C := C) 1 ⟶ Sphere (C := C) 1 => (2 : ℕ) • f)
                ((shiftFunctor C (1 : ℤ)).map_id SphereSpectrum)
        rw [hmap]
        exact hT
      let eQ := shiftedConeIso (2 • 𝟙 (SphereSpectrum : C)) i p hTshift
      let qQ1 : mod2HomologyF2 H R 1 Q ≃ₗ[ZMod 2] ZMod 2 :=
        shiftedCoordinate H R eQ 0 q20
      let qQ2 : mod2HomologyF2 H R 2 Q ≃ₗ[ZMod 2] ZMod 2 :=
        shiftedCoordinate H R eQ 1 q21
      have hψQ : mod2TensorCoaction H R K Q 2 (qQ2.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n Q) 2 (qQ2.symm 1) +
          tensorTerm H R (fun n => mod2HomologyF2 H R n Q) 2 1 x (qQ1.symm 1) := by
        exact shifted_coordinate_coaction H R K hK eQ 1 (Or.inl rfl) q20 q21 x hψ2
      let qX0 : mod2HomologyF2 H R 0 TX.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneBottomCoordinate H R b (hbzero 0) (hQ (-1) (by decide) (by decide))
      let qX2 : mod2HomologyF2 H R 2 TX.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneAboveCoordinate H R b 2 (by decide) (hbzero 1) qQ1
      let qX3 : mod2HomologyF2 H R 3 TX.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneAboveCoordinate H R b 3 (by decide) (hbzero 2) qQ2
      let qE0 : mod2HomologyF2 H R 0 TE.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneBottomCoordinate H R t (htzero 0) (hX (-1) (by decide) (by decide) (by decide))
      let qE1 : mod2HomologyF2 H R 1 TE.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneAboveCoordinate H R t 1 (by decide) (htzero 0) qX0
      let qE3 : mod2HomologyF2 H R 3 TE.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneAboveCoordinate H R t 3 (by decide) (htzero 2) qX2
      let qE4 : mod2HomologyF2 H R 4 TE.Z ≃ₗ[ZMod 2] ZMod 2 :=
        coneAboveCoordinate H R t 4 (by decide) (htzero 3) qX3
      have hid (n : ℤ) : Function.Injective
          (Mod2Homology.pushforward H (𝟙 (SphereSpectrum : C)) n) := by
        intro a b h
        change a ≫ H.HF2 ◁ 𝟙 _ = b ≫ H.HF2 ◁ 𝟙 _ at h
        simpa only [whiskerLeft_id, Category.comp_id] using h
      have hi1 : Function.Injective (Mod2Homology.pushforward H i 1) := by
        apply bottom_injective_of_homology_zero H TQ 1
        exact twice_map_zero H R (𝟙 (Sphere (C := C) 1)) 1
      obtain ⟨cη, hcη, hδη⟩ := compare_cones_of_factorization η b i hib
      have hψX2 : mod2TensorCoaction H R K TX.Z 2 (qX2.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n TX.Z) 2 (qX2.symm 1) +
          tensorTerm H R (fun n => mod2HomologyF2 H R n TX.Z) 2 2 u (qX0.symm 1) := by
        exact comparison_twoCell_transfer H R K Tη TX i (𝟙 SphereSpectrum) cη
          (by
            change HasFunctorialCofiber.cofibι η ≫ cη = 𝟙 SphereSpectrum ≫ HasFunctorialCofiber.cofibι b
            simpa only [Category.id_comp] using hcη) hδη 2 qη0 qη2 qX0 qX2 u
          (homology_bottom_surjective H Tη 0 (by
            change Subsingleton (Mod2Homology H (-1) (Sphere (C := C) 1))
            exact sphereHomologyShiftSubsingleton H (-1) 1 (by decide)))
          (hid 0) (bottom_injective_of_homology_zero H TX 0 (hbzero 0))
          (homology_connecting_injective H Tη 2 (sphereHomologySubsingleton H 2 (by decide)))
          hi1 hψη
      obtain ⟨c2, hc2, hδ2⟩ := compare_cones_of_factorization (2 • 𝟙 (SphereSpectrum : C)) t
        (HasFunctorialCofiber.cofibι b) ht
      have hψE1 : mod2TensorCoaction H R K TE.Z 1 (qE1.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n TE.Z) 1 (qE1.symm 1) +
          tensorTerm H R (fun n => mod2HomologyF2 H R n TE.Z) 1 1 x (qE0.symm 1) := by
        exact comparison_twoCell_transfer H R K T2 TE (HasFunctorialCofiber.cofibι b)
          (𝟙 SphereSpectrum) c2 (by
            change HasFunctorialCofiber.cofibι (2 • 𝟙 (SphereSpectrum : C)) ≫ c2 =
              𝟙 SphereSpectrum ≫ HasFunctorialCofiber.cofibι t
            simpa only [Category.id_comp] using hc2) hδ2
          1 q20 q21 qE0 qE1 x
          (homology_bottom_surjective H T2 0 (by
            change Subsingleton (Mod2Homology H (-1) (SphereSpectrum : C))
            exact sphereHomologySubsingleton H (-1) (by decide)))
          (hid 0) (bottom_injective_of_homology_zero H TE 0 (htzero 0))
          (homology_connecting_injective H T2 1 (sphereHomologySubsingleton H 1 (by decide)))
          (bottom_injective_of_homology_zero H TX 0 (hbzero 0)) hψ2
      have hδX2 : boundaryF2 H R TX 2 (qX2.symm 1) = qQ1.symm 1 :=
        coneAboveCoordinate_boundary H R b 2 (by decide) (hbzero 1) qQ1
      have hδX3 : boundaryF2 H R TX 3 (qX3.symm 1) = qQ2.symm 1 :=
        coneAboveCoordinate_boundary H R b 3 (by decide) (hbzero 2) qQ2
      have hδX0 : boundaryF2 H R TX 0 (qX0.symm 1) = 0 := by
        exact @Subsingleton.elim (mod2HomologyF2 H R (-1) Q)
          (hQ (-1) (by decide) (by decide)) _ _
      have hδE1 : boundaryF2 H R TE 1 (qE1.symm 1) = qX0.symm 1 :=
        coneAboveCoordinate_boundary H R t 1 (by decide) (htzero 0) qX0
      have hδE3 : boundaryF2 H R TE 3 (qE3.symm 1) = qX2.symm 1 :=
        coneAboveCoordinate_boundary H R t 3 (by decide) (htzero 2) qX2
      have hδE4 : boundaryF2 H R TE 4 (qE4.symm 1) = qX3.symm 1 :=
        coneAboveCoordinate_boundary H R t 4 (by decide) (htzero 3) qX3
      have hδE0 : boundaryF2 H R TE 0 (qE0.symm 1) = 0 := by
        exact @Subsingleton.elim (mod2HomologyF2 H R (-1) TX.Z)
          (hX (-1) (by decide) (by decide) (by decide)) _ _
      obtain ⟨cX1, b3, hψX3⟩ := threeCell_023_coaction_expansion H R B K TX.Z hX qX0 qX2 (qX3.symm 1)
      have hcX1 : cX1 = x := boundary_one_coefficient H R K hK TX 3 1
        (qX3.symm 1) (qX2.symm 1) (qX0.symm 1) (qQ2.symm 1) (qQ1.symm 1)
        qQ1.toLinearMap (qQ1.apply_symm_apply 1) x cX1 b3 hδX3 hδX2 hδX0 hψQ hψX3
      subst cX1
      obtain ⟨cE2, a3, hψE3⟩ := fourCell_degree3_expansion H R B K TE.Z hE qE0 qE1 (qE3.symm 1)
      have hcE2 : cE2 = u := boundary_one_coefficient H R K hK TE 3 2
        (qE3.symm 1) (qE1.symm 1) (qE0.symm 1) (qX2.symm 1) (qX0.symm 1)
        qX0.toLinearMap (qX0.apply_symm_apply 1) u cE2 a3 hδE3 hδE1 hδE0 hψX2 hψE3
      subst cE2
      obtain ⟨cE1, cE3, c4, hψE4⟩ := fourCell_coaction_expansion H R B K TE.Z hE qE0 qE1 qE3 (qE4.symm 1)
      obtain ⟨hcE1, hcE3⟩ := boundary_two_coefficients H R K hK TE 4 1 3 (by decide)
        (qE4.symm 1) (qE3.symm 1) (qE1.symm 1) (qE0.symm 1)
        (qX3.symm 1) (qX2.symm 1) (qX0.symm 1)
        qX2.toLinearMap (qX2.apply_symm_apply 1) qX0.toLinearMap (qX0.apply_symm_apply 1)
        x cE1 b3 cE3 c4 hδE4 hδE3 hδE1 hδE0 hψX3 hψE4
      subst cE1
      subst cE3
      have hψX0 : mod2TensorCoaction H R K TX.Z 0 (qX0.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n TX.Z) 0 (qX0.symm 1) :=
        coneBottomCoordinate_coaction H R K hU b (hbzero 0) (hQ (-1) (by decide) (by decide))
      have hψE0 : mod2TensorCoaction H R K TE.Z 0 (qE0.symm 1) =
          cooperationTensorUnit H R (fun n => mod2HomologyF2 H R n TE.Z) 0 (qE0.symm 1) :=
        coneBottomCoordinate_coaction H R K hU t (htzero 0) (hX (-1) (by decide) (by decide) (by decide))
      have hbdiag := threeCell_matrix_023 H R K hD TX.Z qX0.toLinearMap (qX0.symm 1)
        (qX0.apply_symm_apply 1) (qX2.symm 1) (qX3.symm 1) u x b3 hψX0 hψX2 hψX3
      obtain ⟨hadiag, hcdiag⟩ := fourCell_bottom_matrix H R K hD TE.Z qE0.toLinearMap
        (qE0.symm 1) (qE0.apply_symm_apply 1) (qE1.symm 1) (qE3.symm 1) (qE4.symm 1)
        x u a3 b3 c4 hψE0 hψE1 hψE3 hψE4
      exact ⟨a3, b3, c4, hadiag, hbdiag, hcdiag⟩

    open scoped TensorProduct DirectSum in
    have two_cell_coordinates :
        let R := KIP126.Def.standardHF2AdamsContext.cooperationStructure.ring
        let B := KIP126.Def.standardHF2AdamsContext.cooperationStructure.basis
        let K := KIP126.Def.standardHF2AdamsContext.cooperationStructure.kunneth
        let η := literature.sources.sourceComparisons.classicalSource.eta
        ∃ (x1 : mod2HomologyF2 H R 1 H.HF2) (u2 : mod2HomologyF2 H R 2 H.HF2)
          (q20 : mod2HomologyF2 H R 0
            (HasFunctorialCofiber.cofib ((2 : ℕ) • 𝟙 (SphereSpectrum : C))) ≃ₗ[ZMod 2] ZMod 2)
          (q21 : mod2HomologyF2 H R 1
            (HasFunctorialCofiber.cofib ((2 : ℕ) • 𝟙 (SphereSpectrum : C))) ≃ₗ[ZMod 2] ZMod 2)
          (qη0 : mod2HomologyF2 H R 0 (HasFunctorialCofiber.cofib η) ≃ₗ[ZMod 2] ZMod 2)
          (qη2 : mod2HomologyF2 H R 2 (HasFunctorialCofiber.cofib η) ≃ₗ[ZMod 2] ZMod 2),
          cooperationMilnorPolynomial H R B 1 x1 = MvPolynomial.X ((0 : Fin 1), 0) ∧
          cooperationMilnorPolynomial H R B 2 u2 = MvPolynomial.X ((0 : Fin 1), 0) ^ 2 ∧
          mod2TensorCoaction H R K
            (HasFunctorialCofiber.cofib ((2 : ℕ) • 𝟙 (SphereSpectrum : C))) 1 (q21.symm 1) =
            cooperationTensorUnit H R (fun i => mod2HomologyF2 H R i
              (HasFunctorialCofiber.cofib ((2 : ℕ) • 𝟙 (SphereSpectrum : C)))) 1 (q21.symm 1) +
            tensorTerm H R (fun i => mod2HomologyF2 H R i
              (HasFunctorialCofiber.cofib ((2 : ℕ) • 𝟙 (SphereSpectrum : C)))) 1 1 x1 (q20.symm 1) ∧
          mod2TensorCoaction H R K (HasFunctorialCofiber.cofib η) 2 (qη2.symm 1) =
            cooperationTensorUnit H R
              (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η)) 2 (qη2.symm 1) +
            tensorTerm H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η))
              2 2 u2 (qη0.symm 1) := by
      classical
      let R := KIP126.Def.standardHF2AdamsContext.cooperationStructure.ring
      let B := KIP126.Def.standardHF2AdamsContext.cooperationStructure.basis
      let K := KIP126.Def.standardHF2AdamsContext.cooperationStructure.kunneth
      let η := literature.sources.sourceComparisons.classicalSource.eta
      have h2 := two_filtration
      have hη := eta_filtration
      letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
        fun i => mod2HomologyModule H R i H.HF2
      letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
        fun i => mod2HF2HomotopyModule H R i
      have low_support (d : ℕ →₀ ℕ) (hd : slotWeight d ≤ 2) :
          d = Finsupp.single 0 (d 0) := by
        have hz (j : ℕ) (hj : 1 ≤ j) : d j = 0 := by
          by_contra hn
          have hw := Finsupp.le_weight_of_ne_zero'
            (fun j : ℕ => 2 ^ (j + 1) - 1) hn
          have hp : 2 ^ 2 ≤ 2 ^ (j + 1) :=
            Nat.pow_le_pow_right (by decide) (by omega)
          change 2 ^ (j + 1) - 1 ≤ slotWeight d at hw
          norm_num at hp
          omega
        ext j
        rcases j with _ | j
        · simp
        · simp [hz (j + 1) (by omega)]
      have low_weight (d : ℕ →₀ ℕ) (hd : slotWeight d ≤ 2) : slotWeight d = d 0 := by
        conv_lhs => rw [low_support d hd]
        simp [slotWeight, Finsupp.weight_single]
      let p1 : PositiveMonomial 1 :=
        ⟨Finsupp.single 0 1, by norm_num [slotWeight, Finsupp.weight_single], by simp⟩
      let p2 : PositiveMonomial 2 :=
        ⟨Finsupp.single 0 2, by norm_num [slotWeight, Finsupp.weight_single], by simp⟩
      have hp1 (q : PositiveMonomial 1) : q = p1 := by
        apply Subtype.ext
        have hw : slotWeight q.val = 1 := by exact_mod_cast q.property.1
        rw [low_support q.val (by omega), ← low_weight q.val (by omega), hw]
      have hp2 (q : PositiveMonomial 2) : q = p2 := by
        apply Subtype.ext
        have hw : slotWeight q.val = 2 := by exact_mod_cast q.property.1
        rw [low_support q.val (by omega), ← low_weight q.val (by omega), hw]
      have basis_polynomial (n : ℤ) (p : PositiveMonomial n) :
          cooperationMilnorPolynomial H R B n (B.basis n p).val =
            milnorMonomialPolynomial (⟨p.val, p.property.1⟩ : MilnorMonomial n) := by
        change Finsupp.linearCombination (ZMod 2) milnorMonomialPolynomial
          (cooperationMilnorEquiv H R B n (B.basis n p).val) = _
        erw [cooperationMilnorEquiv_reduced_basis H R B n p]
        simp only [Finsupp.linearCombination_single, one_smul]
      let x1 : mod2HomologyF2 H R 1 H.HF2 := (B.basis 1 p1).val
      let u2 : mod2HomologyF2 H R 2 H.HF2 := (B.basis 2 p2).val
      have hx : cooperationMilnorPolynomial H R B 1 x1 = MvPolynomial.X ((0 : Fin 1), 0) := by
        change cooperationMilnorPolynomial H R B 1 (B.basis 1 p1).val = _
        rw [basis_polynomial 1 p1]
        simp [milnorMonomialPolynomial, p1, Finsupp.mapDomain_single, MvPolynomial.X]
      have hu : cooperationMilnorPolynomial H R B 2 u2 = MvPolynomial.X ((0 : Fin 1), 0) ^ 2 := by
        change cooperationMilnorPolynomial H R B 2 (B.basis 2 p2).val = _
        rw [basis_polynomial 2 p2]
        simp [milnorMonomialPolynomial, p2, Finsupp.mapDomain_single,
          MvPolynomial.X_pow_eq_monomial]
      let f2 : (SphereSpectrum : C) ⟶ SphereSpectrum := (2 : ℕ) • 𝟙 _
      let α2 : Sphere (C := C) 0 ⟶ SphereSpectrum :=
        (shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ f2
      have hf2 : H.HF2 ◁ α2 = 0 := tensor_zero_of_first_filtration H R α2 h2.1
      have hfη : H.HF2 ◁ η = 0 := tensor_zero_of_first_filtration H R η hη.1
      obtain ⟨e21, q20old, he21, _, _, hψ2⟩ :=
        twoCell_actual_coaction H R B K 1 (by decide) p1 hp1 α2 h2.1 h2.2
          (low_basis_primitive 1 p1 1 (Or.inl rfl) rfl)
      obtain ⟨eη2, qη0, heη2, _, _, hψη⟩ :=
        twoCell_actual_coaction H R B K 2 (by decide) p2 hp2 η hη.1 hη.2
          (low_basis_primitive 2 p2 2 (Or.inr rfl) rfl)
      let q21old := twoCellOneTopCoordinate H R α2 hf2
      let qη2 : mod2HomologyF2 H R 2 (HasFunctorialCofiber.cofib η) ≃ₗ[ZMod 2] ZMod 2 :=
        ((twoCell_top_equiv H R 2 (by decide) η hfη).trans
          (desuspendEquiv H R (SphereSpectrum : C) 1)).trans (sphereZeroCoordinate H R)
      have he21' : e21 = q21old.symm 1 := nonzero_eq_basis q21old e21 he21
      have heη2' : eη2 = qη2.symm 1 := nonzero_eq_basis qη2 eη2 heη2
      have hψ2' : mod2TensorCoaction H R K (HasFunctorialCofiber.cofib α2) 1 (q21old.symm 1) =
          cooperationTensorUnit H R
            (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α2)) 1 (q21old.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α2))
            1 1 x1 (q20old.symm 1) := by
        rw [he21'] at hψ2
        change mod2TensorCoaction H R K (HasFunctorialCofiber.cofib α2) 1 (q21old.symm 1) =
          cooperationTensorUnit H R
            (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α2)) 1 (q21old.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib α2))
            1 1 x1 (q20old.symm 1) at hψ2
        exact hψ2
      have hψη' : mod2TensorCoaction H R K (HasFunctorialCofiber.cofib η) 2 (qη2.symm 1) =
          cooperationTensorUnit H R
            (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η)) 2 (qη2.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η))
            2 2 u2 (qη0.symm 1) := by
        rw [heη2'] at hψη
        change mod2TensorCoaction H R K (HasFunctorialCofiber.cofib η) 2 (qη2.symm 1) =
          cooperationTensorUnit H R
            (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η)) 2 (qη2.symm 1) +
          tensorTerm H R (fun i => mod2HomologyF2 H R i (HasFunctorialCofiber.cofib η))
            2 2 u2 (qη0.symm 1) at hψη
        exact hψη
      let e := zeroShiftConeIso f2
      let E0 := isoHomologyEquiv H R e 0
      let E1 := isoHomologyEquiv H R e 1
      let q20 := E0.symm.trans q20old
      let q21 := E1.symm.trans q21old
      have hc0 : Mod2Homology.pushforward H e.hom 0 (q20old.symm 1) = q20.symm 1 := by
        apply q20.injective
        change q20old (E0.symm (E0 (q20old.symm 1))) = q20 (q20.symm 1)
        rw [E0.symm_apply_apply, q20old.apply_symm_apply, q20.apply_symm_apply]
      have hc1 : Mod2Homology.pushforward H e.hom 1 (q21old.symm 1) = q21.symm 1 := by
        apply q21.injective
        change q21old (E1.symm (E1 (q21old.symm 1))) = q21 (q21.symm 1)
        rw [E1.symm_apply_apply, q21old.apply_symm_apply, q21.apply_symm_apply]
      refine ⟨x1, u2, q20, q21, qη0, qη2, hx, hu, ?_, hψη'⟩
      have ht := transfer_twoTerm H R K e.hom 1 1 (q21old.symm 1) x1 (q20old.symm 1) hψ2'
      erw [hc1, hc0] at ht
      exact ht

    open KIP126.Synthetic.SpectralSequence in
    have final_closure
        (hsmall1 : ∀ a b : HomotopyGroup (C := KIP126.Classical.Adams.standardFoundation.Spectrum)
            1 SphereSpectrum, a ≠ 0 → b ≠ 0 → a = b)
        (hsmall2 : ∀ a b : HomotopyGroup (C := KIP126.Classical.Adams.standardFoundation.Spectrum)
            2 SphereSpectrum, a ≠ 0 → b ≠ 0 → a = b)
        (hsquare : literature.sources.sourceComparisons.classicalSource.eta⟦(1 : ℤ)⟧' ≫
          literature.sources.sourceComparisons.classicalSource.eta ≠ 0)
        (htoda : ¬ Toda.Relation
          (0 : (Sphere (C := KIP126.Classical.Adams.standardFoundation.Spectrum) 1)⟦(1 : ℤ)⟧ ⟶
            SphereSpectrum)
          ((2 : ℕ) • 𝟙 (Sphere (C := KIP126.Classical.Adams.standardFoundation.Spectrum) 1))
          literature.sources.sourceComparisons.classicalSource.eta ((2 : ℕ) • 𝟙 SphereSpectrum))
        : adamsComparison.recovery.realization.map u =
          adamsComparison.recovery.realization.map (sphereProduct etaClass etaClass) := by
      have transport_map (F : Syn ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
          {X Y Z W : Syn} {x : X⟦(1 : ℤ)⟧ ⟶ W}
          {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
          (hx : Toda.Relation x f g h) :
          Toda.Relation ((F.commShiftIso (1 : ℤ)).inv.app X ≫ F.map x)
            (F.map f) (F.map g) (F.map h) := by
        obtain ⟨Q, i, p, hT, gbar, hg, hx⟩ := hx
        refine ⟨F.obj Q, F.map i, F.map p ≫ (F.commShiftIso (1 : ℤ)).hom.app X,
          F.map_distinguished (Triangle.mk f i p) hT, F.map gbar, ?_, ?_⟩
        · rw [← F.map_comp, hg]
        · simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
          rw [← F.map_comp, hx, F.map_comp]

      have transport_isos {X Y Z W X' Y' Z' W' : C}
          {x : X⟦(1 : ℤ)⟧ ⟶ W} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
          (hx : Toda.Relation x f g h)
          (a : X' ≅ X) (b : Y' ≅ Y) (c : Z' ≅ Z) (d : W' ≅ W) :
          Toda.Relation (a.hom⟦(1 : ℤ)⟧' ≫ x ≫ d.inv)
            (a.hom ≫ f ≫ b.inv) (b.hom ≫ g ≫ c.inv) (c.hom ≫ h ≫ d.inv) := by
        obtain ⟨Q, i, p, hT, gbar, hg, hx⟩ := hx
        refine ⟨Q, b.hom ≫ i, p ≫ a.inv⟦(1 : ℤ)⟧', ?_, gbar ≫ c.inv, ?_, ?_⟩
        · apply isomorphic_distinguished _ hT
          refine Triangle.isoMk _ _ a b (Iso.refl _) ?_ ?_ ?_
          · simp only [Triangle.mk, Category.assoc, Iso.inv_hom_id, Category.comp_id]
          · simp only [Triangle.mk, Iso.refl_hom, Category.comp_id]
          · simp only [Triangle.mk, Iso.refl_hom, Category.id_comp, Category.assoc,
              ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id]
            erw [(shiftFunctor C (1 : ℤ)).map_id X]
            exact Category.comp_id p
        · simpa only [Category.assoc] using congrArg (fun v => b.hom ≫ v ≫ c.inv) hg
        · simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
            Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]
          erw [(shiftFunctor C (1 : ℤ)).map_id X]
          simp only [Category.id_comp]
          simpa only [Category.assoc] using congrArg (fun v => v ≫ d.inv) hx

      have nonzero_transport_isos {X Y Z W X' Y' Z' W' : C}
          {x : X⟦(1 : ℤ)⟧ ⟶ W} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
          (hx : Toda.Relation x f g h)
          (a : X' ≅ X) (b : Y' ≅ Y) (c : Z' ≅ Z) (d : W' ≅ W)
          (hn : ¬ Toda.Relation (0 : X'⟦(1 : ℤ)⟧ ⟶ W')
            (a.hom ≫ f ≫ b.inv) (b.hom ≫ g ≫ c.inv) (c.hom ≫ h ≫ d.inv)) : x ≠ 0 := by
        intro hx0
        apply hn
        simpa only [hx0, comp_zero, zero_comp] using transport_isos hx a b c d

      have nonzero_two_maps
          (η : (SphereSpectrum : C)⟦(1 : ℤ)⟧ ⟶ SphereSpectrum)
          (hη : η ≠ 0) (hsquare : η⟦(1 : ℤ)⟧' ≫ η ≠ 0)
          (hsmall : ∀ a b : (SphereSpectrum : C)⟦(1 : ℤ)⟧ ⟶ SphereSpectrum,
            a ≠ 0 → b ≠ 0 → a = b)
          {A B E : C} (r : (SphereSpectrum : C)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ ≅ A)
          (s : (SphereSpectrum : C)⟦(1 : ℤ)⟧ ≅ B) (t : (SphereSpectrum : C) ≅ E)
          (a : A ⟶ B) (b : B ⟶ E) (ha : a ≠ 0) (hb : b ≠ 0) : a ≫ b ≠ 0 := by
        let a' := r.hom ≫ a ≫ s.inv
        let b' := s.hom ≫ b ≫ t.inv
        have ha' : a' ≠ 0 := by
          intro h
          apply ha
          apply (cancel_epi r.hom).mp
          apply (cancel_mono s.inv).mp
          simpa only [Category.assoc, comp_zero, zero_comp] using h
        have hb' : b' ≠ 0 := by
          intro h
          apply hb
          apply (cancel_epi s.hom).mp
          apply (cancel_mono t.inv).mp
          simpa only [Category.assoc, comp_zero, zero_comp] using h
        let a₀ := (shiftFunctor C (1 : ℤ)).preimage a'
        have ha₀ : a₀ ≠ 0 := by
          intro h
          apply ha'
          rw [← (shiftFunctor C (1 : ℤ)).map_preimage a']
          change (shiftFunctor C (1 : ℤ)).map a₀ = 0
          rw [h, Functor.map_zero]
        have hea : a' = η⟦(1 : ℤ)⟧' := by
          rw [← (shiftFunctor C (1 : ℤ)).map_preimage a']
          exact congrArg ((shiftFunctor C (1 : ℤ)).map) (hsmall a₀ η ha₀ hη)
        have heb : b' = η := hsmall b' η hb' hη
        intro hab
        apply hsquare
        rw [← hea, ← heb]
        change (r.hom ≫ a ≫ s.inv) ≫ s.hom ≫ b ≫ t.inv = 0
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← Category.assoc a b, hab, zero_comp, comp_zero]

      have normalized_toda_nonzero
          (η : (SphereSpectrum : C)⟦(1 : ℤ)⟧ ⟶ SphereSpectrum) (hη : η ≠ 0)
          (hsmall : ∀ a b : (SphereSpectrum : C)⟦(1 : ℤ)⟧ ⟶ SphereSpectrum,
            a ≠ 0 → b ≠ 0 → a = b)
          (htoda : ¬ Toda.Relation (0 : (SphereSpectrum : C)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ ⟶ SphereSpectrum)
            ((2 : ℕ) • 𝟙 ((SphereSpectrum : C)⟦(1 : ℤ)⟧)) η ((2 : ℕ) • 𝟙 SphereSpectrum))
          {X Y Z W : C} (v : X ≅ Y) (w : Z ≅ W)
          (jY : (SphereSpectrum : C)⟦(1 : ℤ)⟧ ≅ Y) (jW : (SphereSpectrum : C) ≅ W)
          {x : X⟦(1 : ℤ)⟧ ⟶ W} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
          (hf : f = (2 : ℕ) • v.hom) (hg : g ≠ 0) (hh : h = (2 : ℕ) • w.hom)
          (hx : Toda.Relation x f g h) : x ≠ 0 := by
        let jX := jY ≪≫ v.symm
        let jZ := jW ≪≫ w.symm
        have hf' : jX.hom ≫ f ≫ jY.inv = (2 : ℕ) • 𝟙 ((SphereSpectrum : C)⟦(1 : ℤ)⟧) := by
          simp only [jX, Iso.trans_hom, Iso.symm_hom, hf, Preadditive.comp_nsmul,
            Preadditive.nsmul_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
        have hh' : jZ.hom ≫ h ≫ jW.inv = (2 : ℕ) • 𝟙 (SphereSpectrum : C) := by
          simp only [jZ, Iso.trans_hom, Iso.symm_hom, hh, Preadditive.comp_nsmul,
            Preadditive.nsmul_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
        have hg' : jY.hom ≫ g ≫ jZ.inv = η := by
          apply hsmall _ η _ hη
          intro hzero
          apply hg
          apply (cancel_epi jY.hom).mp
          apply (cancel_mono jZ.inv).mp
          simpa only [Category.assoc, comp_zero, zero_comp] using hzero
        apply nonzero_transport_isos hx jX jY jZ jW
        rw [hf', hh', hg']
        exact htoda

      have realization_bundle : ∃ _B : ∀ m w : ℤ,
            SyntheticCategory.biShift (Syn := KIP126.Def.standardSyntheticContext.Syn) (m,w) ⋙
              adamsComparison.recovery.realization ≅ adamsComparison.recovery.realization ⋙
                shiftFunctor KIP126.Classical.Adams.standardFoundation.Spectrum m,
          (∀ n : ℕ, ∀ A : KIP126.Def.standardSyntheticContext.Syn,
            IsIso (adamsComparison.recovery.realization.map (lambdaPow n A))) ∧
          (∀ n : ℕ, ∀ A : KIP126.Def.standardSyntheticContext.Syn,
            IsIso (adamsComparison.recovery.realization.map (lambdaToPositivePow n A))) := by
        classical
        let Syn := KIP126.Def.standardSyntheticContext.Syn
        let D := adamsComparison
        let R := D.recovery.realization
        letI := D.realizationShift
        have map_lambda_iso (A : Syn) : IsIso (R.map (SyntheticCategory.lam.app A)) := by
          letI := D.recovery.localization.map_lambda_isIso A
          change IsIso (D.recovery.equivalence.functor.map
            (D.recovery.localization.reflector.map (SyntheticCategory.lam.app A)))
          infer_instance
        let T (w : ℤ) : Syn ⥤ Syn := SyntheticCategory.biShift (0,w)
        let F (w : ℤ) := T w ⋙ R
        let stepMap (w : ℤ) : T (w-1) ⟶ T w :=
          (biShiftAddIso (0,w) (0,-1) (0,w-1) (by ext <;> simp [sub_eq_add_neg])).inv ≫
            Functor.whiskerLeft (T w) SyntheticCategory.lam ≫
            (Functor.rightUnitor (T w)).hom
        let stepReal (w : ℤ) : F (w-1) ⟶ F w := Functor.whiskerRight (stepMap w) R
        have stepIso (w : ℤ) : IsIso (stepReal w) := by
          haveI (A : Syn) : IsIso ((stepReal w).app A) := by
            letI := map_lambda_iso ((T w).obj A)
            change IsIso (R.map ((biShiftAddIso (0,w) (0,-1) (0,w-1)
              (by ext <;> simp [sub_eq_add_neg])).inv.app A ≫
                SyntheticCategory.lam.app ((T w).obj A) ≫ 𝟙 ((T w).obj A)))
            erw [Category.comp_id, Functor.map_comp]
            infer_instance
          exact NatIso.isIso_of_isIso_app (stepReal w)
        let e (w : ℤ) : F (w-1) ≅ F w := by
          letI := stepIso w
          exact asIso (stepReal w)
        let z : F 0 ≅ R :=
          Functor.isoWhiskerRight SyntheticCategory.biShift_zero R ≪≫ Functor.leftUnitor R
        let succ (w : ℤ) (_ : 0 ≤ w) (q : F w ≅ R) : F (w+1) ≅ R :=
          (e (w+1)).symm ≪≫ eqToIso (congrArg F (by omega : w+1-1=w)) ≪≫ q
        let pred (w : ℤ) (_ : w ≤ 0) (q : F w ≅ R) : F (w-1) ≅ R := e w ≪≫ q
        let W (w : ℤ) : F w ≅ R := w.inductionOn' 0 z succ pred
        let B (m w : ℤ) : SyntheticCategory.biShift (m,w) ⋙ R ≅
            R ⋙ shiftFunctor KIP126.Classical.Adams.standardFoundation.Spectrum m :=
          Functor.isoWhiskerRight
              (biShiftAddIso (m,0) (0,w) (m,w) (by ext <;> simp)).symm R ≪≫
            Functor.associator (SyntheticCategory.biShift (m,0)) (SyntheticCategory.biShift (0,w)) R ≪≫
            Functor.isoWhiskerLeft (SyntheticCategory.biShift (m,0)) (W w) ≪≫
            Functor.isoWhiskerRight (SyntheticCategory.biShift_compat m) R ≪≫ R.commShiftIso m
        have map_shift_iso (p : ℤ × ℤ) {A A' : Syn} (f : A ⟶ A')
            (hf : IsIso (R.map f)) : IsIso (R.map ((SyntheticCategory.biShift p).map f)) := by
          letI := hf
          have hn := (B p.1 p.2).hom.naturality f
          change R.map ((SyntheticCategory.biShift p).map f) ≫ (B p.1 p.2).hom.app A' =
            (B p.1 p.2).hom.app A ≫ (R.map f)⟦p.1⟧' at hn
          have he : R.map ((SyntheticCategory.biShift p).map f) =
              (B p.1 p.2).hom.app A ≫ (R.map f)⟦p.1⟧' ≫ (B p.1 p.2).inv.app A' := by
            apply (cancel_mono ((B p.1 p.2).hom.app A')).mp
            simp only [Category.assoc, Iso.inv_hom_id_app]
            erw [Category.comp_id]
            exact hn
          rw [he]
          infer_instance
        have pow_iso (n : ℕ) (A : Syn) : IsIso (R.map (lambdaPow n A)) := by
          induction n with
          | zero =>
            change IsIso (R.map (SyntheticCategory.biShift_zero.hom.app A))
            infer_instance
          | succ n ih =>
            haveI : IsIso (R.map (lambdaPow n A)) := ih
            haveI : IsIso (R.map ((SyntheticCategory.biShift (Synthetic.Context.lambdaDegree n)).map
                (SyntheticCategory.lam.app A))) :=
              map_shift_iso (Synthetic.Context.lambdaDegree n) (SyntheticCategory.lam.app A) (map_lambda_iso A)
            rw [lambdaPow_add D.shiftCoherence 1 n (n+1) (by omega),
              lambdaPow_one D.shiftCoherence]
            simp only [Functor.map_comp]
            infer_instance
        refine ⟨B, pow_iso, ?_⟩
        intro n A
        letI := pow_iso n ((SyntheticCategory.biShift (0,(n : ℤ))).obj A)
        unfold lambdaToPositivePow
        simp only [Functor.map_comp]
        infer_instance

      -- §7.3.2: the comparison with classical η shows that the realization
      -- of the specified synthetic η is nonzero.
      have realization_eta_ne_zero (heta : literature.sources.sourceComparisons.classicalSource.eta ≠ 0) :
          adamsComparison.recovery.realization.map etaClass ≠ 0 := by
        let D := adamsComparison
        let R := D.recovery.realization
        obtain ⟨he, heq⟩ := literature.sources.sourceComparisons.hopfComparison.normalized_eta
        intro hz
        change R.map KIP126.Def.standardEta = 0 at hz
        have hnormalized : R.map
            (D.normalizedMap (.shift 1 .sphere) .sphere D.hopfAndDetector.etaMap).map = 0 := by
          rw [heq, Functor.map_comp, Functor.map_comp] at hz
          apply (cancel_epi (R.map (etaSourceIso D he).hom)).mp
          apply (cancel_mono (R.map D.nu.unitIso.hom)).mp
          simpa only [Category.assoc, comp_zero, zero_comp] using hz
        have hnu : R.map (D.nu.functor.map D.hopfAndDetector.etaMap) = 0 := by
          rw [← (D.normalizedMap (.shift 1 .sphere) .sphere D.hopfAndDetector.etaMap).factorization,
            Functor.map_comp, hnormalized, comp_zero]
        have hn := D.recovery.recovery_naturality D.hopfAndDetector.etaMap
        change R.map (D.nu.functor.map D.hopfAndDetector.etaMap) ≫
            D.recovery.nuRealizationIso.hom.app _ =
            D.recovery.nuRealizationIso.hom.app _ ≫ D.hopfAndDetector.etaMap at hn
        rw [hnu, zero_comp] at hn
        have heta0 : D.hopfAndDetector.etaMap = 0 := by
          apply (cancel_epi (D.recovery.nuRealizationIso.hom.app _)).mp
          simpa only [comp_zero] using hn.symm
        rw [literature.sources.sourceComparisons.hopfComparison.eta] at heta0
        exact heta heta0

      have realization_consequences
          (B : ∀ m w : ℤ,
            SyntheticCategory.biShift (Syn := KIP126.Def.standardSyntheticContext.Syn) (m,w) ⋙
              adamsComparison.recovery.realization ≅ adamsComparison.recovery.realization ⋙
                shiftFunctor KIP126.Classical.Adams.standardFoundation.Spectrum m)
          (hpow : ∀ n : ℕ, ∀ A : KIP126.Def.standardSyntheticContext.Syn,
            IsIso (adamsComparison.recovery.realization.map (lambdaPow n A))) :
          (∀ p : ℤ × ℤ, ∀ {A A' : KIP126.Def.standardSyntheticContext.Syn} (f : A ⟶ A'),
            adamsComparison.recovery.realization.map f ≠ 0 →
            adamsComparison.recovery.realization.map ((SyntheticCategory.biShift p).map f) ≠ 0) ∧
          Nonempty (∀ m w : ℤ, Sphere (C := KIP126.Classical.Adams.standardFoundation.Spectrum) m ≅
            adamsComparison.recovery.realization.obj (Smn (Syn := KIP126.Def.standardSyntheticContext.Syn) m w)) ∧
          (∃ v : adamsComparison.recovery.realization.obj
                (Smn (Syn := KIP126.Def.standardSyntheticContext.Syn) 0 1) ≅
              adamsComparison.recovery.realization.obj (S_0_0 : KIP126.Def.standardSyntheticContext.Syn),
            adamsComparison.recovery.realization.map literature.sources.sourceComparisons.todaSource.h0 =
              (2 : ℕ) • v.hom) ∧
          (∀ p : ℤ × ℤ, ∃ v :
              adamsComparison.recovery.realization.obj ((SyntheticCategory.biShift p).obj
                (Smn (Syn := KIP126.Def.standardSyntheticContext.Syn) 0 1)) ≅
              adamsComparison.recovery.realization.obj ((SyntheticCategory.biShift p).obj
                (S_0_0 : KIP126.Def.standardSyntheticContext.Syn)),
            adamsComparison.recovery.realization.map
                ((SyntheticCategory.biShift p).map literature.sources.sourceComparisons.todaSource.h0) =
              (2 : ℕ) • v.hom) := by
        classical
        let Syn := KIP126.Def.standardSyntheticContext.Syn
        let D := adamsComparison
        let R := D.recovery.realization
        letI := D.recovery.adjunction.isLeftAdjoint
        letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts R
        letI := Functor.additive_of_preservesBinaryBiproducts R
        have shift_nonzero (p : ℤ × ℤ) {A A' : Syn} (f : A ⟶ A')
            (hf : R.map f ≠ 0) : R.map ((SyntheticCategory.biShift p).map f) ≠ 0 := by
          intro hz
          have hn := (B p.1 p.2).hom.naturality f
          change R.map ((SyntheticCategory.biShift p).map f) ≫ (B p.1 p.2).hom.app A' =
            (B p.1 p.2).hom.app A ≫ (R.map f)⟦p.1⟧' at hn
          rw [hz, zero_comp] at hn
          have hs : (R.map f)⟦p.1⟧' = 0 := by
            apply (cancel_epi ((B p.1 p.2).hom.app A)).mp
            simpa only [comp_zero] using hn.symm
          apply hf
          apply (shiftFunctor KIP126.Def.standardHF2AdamsContext.stableContext.Spectrum p.1).map_injective
          simpa only [Functor.map_zero] using hs
        let j0 : (SphereSpectrum (C := KIP126.Classical.Adams.standardFoundation.Spectrum)) ≅
            R.obj (S_0_0 : Syn) :=
          D.recovery.nuRealizationIso.symm.app SphereSpectrum ≪≫ R.mapIso D.nu.unitIso
        let j (m w : ℤ) : Sphere (C := KIP126.Classical.Adams.standardFoundation.Spectrum) m ≅
            R.obj (Smn (Syn := Syn) m w) :=
          (shiftFunctor KIP126.Classical.Adams.standardFoundation.Spectrum m).mapIso j0 ≪≫
            ((B m w).app (S_0_0 : Syn)).symm
        have map_shift_iso (p : ℤ × ℤ) {A A' : Syn} (f : A ⟶ A')
            (hf : IsIso (R.map f)) : IsIso (R.map ((SyntheticCategory.biShift p).map f)) := by
          letI := hf
          have hn := (B p.1 p.2).hom.naturality f
          change R.map ((SyntheticCategory.biShift p).map f) ≫ (B p.1 p.2).hom.app A' =
            (B p.1 p.2).hom.app A ≫ (R.map f)⟦p.1⟧' at hn
          have he : R.map ((SyntheticCategory.biShift p).map f) =
              (B p.1 p.2).hom.app A ≫ (R.map f)⟦p.1⟧' ≫ (B p.1 p.2).inv.app A' := by
            apply (cancel_mono ((B p.1 p.2).hom.app A')).mp
            simp only [Category.assoc, Iso.inv_hom_id_app]
            erw [Category.comp_id]
            exact hn
          rw [he]
          infer_instance
        let h : BiHom 0 1 (S_0_0 : Syn) := literature.sources.sourceComparisons.todaSource.h0
        let a : Smn (Syn := Syn) 0 0 ⟶ Smn (Syn := Syn) 0 1 :=
          lambdaMultiply 1 (𝟙 (Smn (Syn := Syn) 0 1))
        let b : Smn (Syn := Syn) 0 0 ≅ (S_0_0 : Syn) :=
          SyntheticCategory.biShift_zero.app S_0_0
        have ha : IsIso (R.map a) := by
          letI := hpow 1 (Smn (Syn := Syn) 0 1)
          dsimp only [a, lambdaMultiply]
          simp only [Category.comp_id, Functor.map_comp]
          infer_instance
        have hab : a ≫ h = (2 : ℕ) • b.hom := by
          have hh := literature.theorems.toda_lambda_h0
          change lambdaMultiply 1 h = syntheticTwo at hh
          simpa only [a, b, lambdaMultiply, syntheticTwo, Category.assoc, BiHom,
            Nat.cast_one, sub_self, Iso.app_hom,
            Category.id_comp, Category.comp_id, Preadditive.comp_nsmul] using hh
        letI := ha
        let v : R.obj (Smn (Syn := Syn) 0 1) ≅ R.obj (S_0_0 : Syn) :=
          (asIso (R.map a)).symm ≪≫ R.mapIso b
        have hv : R.map h = (2 : ℕ) • v.hom := by
          apply (cancel_epi (R.map a)).mp
          have hh := congrArg R.map hab
          rw [Functor.map_comp, Functor.map_nsmul] at hh
          simpa only [v, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom,
            Preadditive.comp_nsmul, Category.assoc, IsIso.hom_inv_id_assoc] using hh
        refine ⟨shift_nonzero, ⟨j⟩, ⟨v, hv⟩, ?_⟩
        intro p
        letI := D.shiftAdditive p
        letI := map_shift_iso p a ha
        let vp : R.obj ((SyntheticCategory.biShift p).obj (Smn (Syn := Syn) 0 1)) ≅
            R.obj ((SyntheticCategory.biShift p).obj (S_0_0 : Syn)) :=
          (asIso (R.map ((SyntheticCategory.biShift p).map a))).symm ≪≫
            R.mapIso ((SyntheticCategory.biShift p).mapIso b)
        refine ⟨vp, ?_⟩
        apply (cancel_epi (R.map ((SyntheticCategory.biShift p).map a))).mp
        have hh := congrArg (fun q => R.map ((SyntheticCategory.biShift p).map q)) hab
        simp only [Functor.map_comp, Functor.map_nsmul] at hh
        simpa only [vp, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom,
          Preadditive.comp_nsmul, Category.assoc, IsIso.hom_inv_id_assoc] using hh

      have realized_comparison
          (hsmall1 : ∀ a b : HomotopyGroup (C := KIP126.Classical.Adams.standardFoundation.Spectrum)
              1 SphereSpectrum, a ≠ 0 → b ≠ 0 → a = b)
          (hsmall2 : ∀ a b : HomotopyGroup (C := KIP126.Classical.Adams.standardFoundation.Spectrum)
              2 SphereSpectrum, a ≠ 0 → b ≠ 0 → a = b)
          (hsquare : literature.sources.sourceComparisons.classicalSource.eta⟦(1 : ℤ)⟧' ≫
            literature.sources.sourceComparisons.classicalSource.eta ≠ 0)
          (htoda : ¬ Toda.Relation
            (0 : (Sphere (C := KIP126.Classical.Adams.standardFoundation.Spectrum) 1)⟦(1 : ℤ)⟧ ⟶
              SphereSpectrum)
            ((2 : ℕ) • 𝟙 (Sphere (C := KIP126.Classical.Adams.standardFoundation.Spectrum) 1))
            literature.sources.sourceComparisons.classicalSource.eta ((2 : ℕ) • 𝟙 SphereSpectrum))
          (u : BiHom 2 4 (S_0_0 : KIP126.Def.standardSyntheticContext.Syn))
          (hu : TripleToda literature.sources.sourceComparisons.todaSource.h0 etaClass
            literature.sources.sourceComparisons.todaSource.h0 u) :
          adamsComparison.recovery.realization.map u =
            adamsComparison.recovery.realization.map (sphereProduct etaClass etaClass) := by
        classical
        let C := KIP126.Classical.Adams.standardFoundation.Spectrum
        let Syn := KIP126.Def.standardSyntheticContext.Syn
        let D := adamsComparison
        let R := D.recovery.realization
        letI : R.CommShift ℤ := D.realizationShift
        letI : R.IsTriangulated := D.realizationExact
        letI := D.recovery.adjunction.isLeftAdjoint
        letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts R
        letI := Functor.additive_of_preservesBinaryBiproducts R
        let eta : HomotopyGroup (C := C) 1 SphereSpectrum := literature.sources.sourceComparisons.classicalSource.eta
        have heta : eta ≠ 0 := by
          intro hz
          apply hsquare
          change eta⟦(1 : ℤ)⟧' ≫ eta = 0
          rw [hz, Functor.map_zero, zero_comp]
        obtain ⟨B, hpow, _⟩ := realization_bundle
        obtain ⟨shift_nonzero, ⟨j⟩, ⟨w, hw⟩, shift_two⟩ := realization_consequences B hpow
        have he : R.map etaClass ≠ 0 := realization_eta_ne_zero heta
        let j0 : (SphereSpectrum : C) ≅ R.obj (S_0_0 : Syn) :=
          D.recovery.nuRealizationIso.symm.app SphereSpectrum ≪≫ R.mapIso D.nu.unitIso
        -- §7.3.3: two nonzero π₁ maps compose to the established nonzero η².
        have hprod : R.map (sphereProduct etaClass etaClass) ≠ 0 := by
          let i2 : (SphereSpectrum : C)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ ≅
              R.obj ((SyntheticCategory.biShift (1,2)).obj (Smn (Syn := Syn) 1 2)) :=
            ((shiftFunctorAdd' C 1 1 2 (by omega)).app SphereSpectrum).symm ≪≫
              j 2 4 ≪≫ R.mapIso
                ((SyntheticCategory.biShift_comp (1,2) (1,2)).app (S_0_0 : Syn)).symm
          have hc := nonzero_two_maps eta heta hsquare hsmall1 i2 (j 1 2) j0
            (R.map ((SyntheticCategory.biShift (1,2)).map etaClass)) (R.map etaClass)
            (shift_nonzero (1,2) etaClass he) he
          intro hz
          apply hc
          apply (cancel_epi (R.map
            ((SyntheticCategory.biShift_comp (1,2) (1,2)).inv.app (S_0_0 : Syn)))).mp
          simpa only [sphereProduct, Functor.map_comp, Category.assoc, comp_zero] using hz
        -- §7.3.4: normalize the outer Toda arrows by their actual invertible factors.
        let h : BiHom 0 1 (S_0_0 : Syn) := literature.sources.sourceComparisons.todaSource.h0
        let f := (SyntheticCategory.biShift (1,3)).map h
        let g := (SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app (S_0_0 : Syn) ≫
          (SyntheticCategory.biShift (0,1)).map etaClass
        let x := (tripleTodaSource 0 1 1 2 0 1).inv ≫ u
        have hx : Toda.Relation x f g h := hu
        have hg : R.map g ≠ 0 := by
          intro hz
          apply shift_nonzero (0,1) etaClass he
          apply (cancel_epi (R.map
            ((SyntheticCategory.biShift_comp (1,2) (0,1)).inv.app (S_0_0 : Syn)))).mp
          simpa only [g, Functor.map_comp, comp_zero] using hz
        obtain ⟨v, hv⟩ := shift_two (1,3)
        have hxR := transport_map R hx
        have hxn := normalized_toda_nonzero eta heta hsmall1 htoda v w (j 1 3) j0
          hv hg hw hxR
        have hun : R.map u ≠ 0 := by
          intro hz
          apply hxn
          simp only [x, Functor.map_comp, hz, comp_zero]
        -- §7.3.5: the specified Hom group injects into classical π₂ via sphere isos.
        let q (a : R.obj (Smn (Syn := Syn) 2 4) ⟶ R.obj (S_0_0 : Syn)) :
            HomotopyGroup (C := C) 2 SphereSpectrum := (j 2 4).hom ≫ a ≫ j0.inv
        have qinj : Function.Injective q := by
          intro a b hab
          apply (cancel_epi (j 2 4).hom).mp
          apply (cancel_mono j0.inv).mp
          simpa only [q, Category.assoc] using hab
        have qzero : q 0 = 0 := by simp only [q, comp_zero, zero_comp]
        apply qinj
        apply hsmall2
        · intro hz
          exact hun (qinj (hz.trans qzero.symm))
        · intro hz
          exact hprod (qinj (hz.trans qzero.symm))

      exact realized_comparison hsmall1 hsmall2 hsquare htoda u hu
    -- Apply the coaction obstructions to the fixed mod-two cooperation ring
    -- and the classical η class to establish η² and Toda nonvanishing.
    let Rlow := KIP126.Def.standardHF2AdamsContext.cooperationStructure.ring
    let Blow := KIP126.Def.standardHF2AdamsContext.cooperationStructure.basis
    let Klow := KIP126.Def.standardHF2AdamsContext.cooperationStructure.kunneth
    let ηlow := literature.sources.sourceComparisons.classicalSource.eta
    have hKlow := KIP126.Def.standardHF2AdamsContext.cooperationStructure.suspension
    have hUlow := KIP126.Def.standardHF2AdamsContext.cooperationStructure.unit
    have hDlow := KIP126.Def.standardHF2AdamsContext.cooperationStructure.diagonal
    obtain ⟨xlow, ulow, q20, q21, qη0, qη2, hxlow, hulow, hψ2, hψη⟩ :=
      two_cell_coordinates
    have eta_square_nonzero : ηlow⟦(1 : ℤ)⟧' ≫ ηlow ≠ 0 := by
      intro hz
      obtain ⟨a, ha⟩ := square_zero_forces_coproduct H Rlow Blow Klow hKlow hUlow hDlow
        ηlow qη0 qη2 ulow hψη hz
      apply low_cooperation_obstructions.1 ulow hulow a
      exact ha
    have classical_toda_nonzero : ¬ Toda.Relation
        (0 : (Sphere (C := C) 1)⟦(1 : ℤ)⟧ ⟶ SphereSpectrum)
        ((2 : ℕ) • 𝟙 (Sphere (C := C) 1)) ηlow ((2 : ℕ) • 𝟙 SphereSpectrum) := by
      intro ht
      obtain ⟨a, b, c, ha, hb, hc⟩ := toda_matrix_exists H Rlow Blow Klow
        hKlow hDlow hUlow ηlow xlow ulow q20 q21 qη0 qη2 hψ2 hψη ht
      apply low_cooperation_obstructions.2 xlow ulow hxlow hulow a b c ha hb
      change cooperationTensorDiagonal H Rlow Klow 4 c =
        cooperationTensorUnit H Rlow (fun n => mod2HomologyF2 H Rlow n H.HF2) 4 c +
          (tensorTerm H Rlow (fun n => mod2HomologyF2 H Rlow n H.HF2) 4 1 xlow a +
            tensorTerm H Rlow (fun n => mod2HomologyF2 H Rlow n H.HF2) 4 3 b xlow) +
          tensorTerm H Rlow (fun n => mod2HomologyF2 H Rlow n H.HF2) 4 4 c (cooperationUnit H)
      simpa only [add_assoc] using hc
    exact final_closure classical_smalls.1 classical_smalls.2 eta_square_nonzero classical_toda_nonzero
  have heq : u = sphereProduct etaClass etaClass := realization_injective hreal
  rw [heq] at hu
  exact hu

end KIP126.Main.AdamsSynthetic.Toda
