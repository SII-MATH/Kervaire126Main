module

public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Computation.LinCoordinates.Certificates.SphereAndCofiber.Stem125SixthPages
public import KIP126.Main.SectionSeven.TmfDetection
public import KIP126.Computation.LinCoordinates.Certificates.SphereAndCofiber.High125
public import KIP126.Computation.LinCoordinates.Certificates.SphereAndCofiber.Stem125Differentials
public import KIP126.Main.Literature.AdamsSynthetic.Theorems
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs

@[expose] public section

/-!
# The weight130 high-filtration argument of Proposition 7.8

LWX `prop:possible_h_6_sq` uses the actual group pi_(125,130) and its
lambda^10-divisible subgroup. It does not claim that all classical E5
components with AF>=15, AF!=25 vanish. The AF15 d5 source and AF18 d5
target in `Computation.SphereAndCofiber` are both nonzero on E5.

These are internal Main proof obligations on the same D and I. BHS gives
the synthetic E-infinity formulas, actual lambda maps and filtration
comparison. The finite C basis/differential reconstruction and the
independent vanishing line control the whole range; D.homotopySeparated
removes the infinitely filtered remainder. No selected survival, torsion
or exhaustion statement is added to Model, literature or C.
-/
namespace KIP126.Computation.SphereAndCofiber
open KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Literature.AdamsSynthetic
open KIP126.LinE2 KIP126.Computation.Near126
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  {D : AdamsComparison H M Syn} {L : SphereAdamsClasses H} {G : TmfDetectionClasses H}

attribute [local irreducible] KIP126.LinE2.homogeneousPart

private theorem permanentQuotient_zero_of_page_five_zero (s t b : ℤ) (hb : 4 ≤ b)
    (hpage : Subsingleton ((sequence D .sphere).Page 5 (s, t))) :
    Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
  set_option backward.isDefEq.respectTransparency false in
    let E := (sequence D .sphere).ssData (s, t)
    haveI : Subsingleton (E.page 3) := hpage
    have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
        PageRepresentatives.boundaries H SphereSpectrum 4 (s, t) := by
      rintro x ⟨z, hz⟩
      let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 3) (E.Z_anti le_top)) z
      have hzero : E.pageπ 3 zf = 0 := Subsingleton.elim _ _
      obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (E.B 3) (E.Z 3) (E.B_le_Z 3)) zf).mp hzero
      refine ⟨y, ?_⟩
      change PageRepresentatives.boundaryMap H SphereSpectrum 3 (s, t) y = x
      have hfactor : Subobject.ofLE (E.B 3) (E.Z 3) (E.B_le_Z 3) ≫
          PageRepresentatives.cycleMap H SphereSpectrum 3 (s, t) =
          PageRepresentatives.boundaryMap H SphereSpectrum 3 (s, t) := by
        dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, sequence, object]
        rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
      rw [← hfactor, CategoryTheory.comp_apply]
      apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 3 (s, t)) hy).trans
      exact (congrArg (fun f => f z)
        (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 3 ⊤ le_top)).trans hz
    have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
      rintro ⟨x⟩
      change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
      apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
      exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
    exact ⟨fun x y => (hall x).trans (hall y).symm⟩

/-- At weight130, finite E5 vanishing at AF26..64 and the classical tail
bound kill the entire actual F26. BHS quotients by the relevant incoming
boundaries (lambda exponent s-5>=21 in this range). The proof must pass
from all associated grades to the actual group using D.homotopySeparated;
neither the finite table cutoff nor graded convergence alone suffices. -/
theorem stem125_weight130_filtration26_zero
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (V : SphereVanishingLine H)
    (a : BiHom 125 130 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 26 a) : a = 0 := by
  apply D.sphereConvergence.eq_zero_of_eInfty_isZero_ge 26 125 130
    (D.homotopySeparated .sphere 125 130) ?_ a ha
  intro j hj
  set_option backward.isDefEq.respectTransparency false in
    have hpage : Subsingleton ((sequence D .sphere).Page 5 (j, 125 + j)) := by
      by_cases h64 : j ≤ 64
      · have h := stem125_e5_zero_finite I j.toNat (by omega) (by omega)
        simpa only [Int.toNat_of_nonneg (show 0 ≤ j by omega), add_comm] using h
      · simpa only [add_comm] using sphere_page_zero_stem125_tail (D := D) V 5 j (by omega) (by omega)
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1 + (125 + j) - 130) (j, 125 + j)) :=
      permanentQuotient_zero_of_page_five_zero (D := D) j (125 + j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j, 125 + j) 130 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j, 125 + j, 130)).eInfty) :=
      e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j, 125 + j, 130)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j, 125 + j, 130)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j, 125 + j, 130)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f, g]
      rw [← SpectralSequenceMorphism.eInftyMap_comp, ← Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0, CategoryTheory.Limits.comp_zero])

section
attribute [local irreducible] adamsTowerSSData adamsTowerInternalD
open CategoryTheory.Limits KIP126.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

-- In stem 125 and weight 130, filtrations 15 through 25 coincide.
set_option linter.unusedVariables false in
theorem stem125_weight130_filtration15_eq25
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (V : SphereVanishingLine H)
    (a : BiHom 125 130 (S_0_0 : Syn)) :
    FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a ↔
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 25 a := by
  apply D.sphereConvergence.filtrationAtLeast_iff_of_eInfty_isZero
    15 25 125 130 (by omega) ?_ a
  intro j hj h25
  -- Remaining obligation: the BHS weight130 quotient is zero throughout
  -- this interval, including the d5 source and target discussed above.
  classical

  have permanentQuotient_zero_of_page_six_zero (s t b : ℤ) (hb : 5 ≤ b)
      (hpage : Subsingleton ((sequence D .sphere).Page 6 (s, t))) :
      Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t)) := by
    set_option backward.isDefEq.respectTransparency false in
      let E := (sequence D .sphere).ssData (s, t)
      haveI : Subsingleton (E.page 4) := hpage
      have hcycles : PageRepresentatives.permanentCycles H SphereSpectrum (s, t) ≤
          PageRepresentatives.boundaries H SphereSpectrum 5 (s, t) := by
        rintro x ⟨z, hz⟩
        let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 4) (E.Z_anti le_top)) z
        have hzero : E.pageπ 4 zf = 0 := Subsingleton.elim _ _
        obtain ⟨y, hy⟩ := (cokernel_π_eq_zero_iff_mem_range
          (Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4)) zf).mp hzero
        refine ⟨y, ?_⟩
        change PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) y = x
        have hfactor : Subobject.ofLE (E.B 4) (E.Z 4) (E.B_le_Z 4) ≫
            PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t) =
            PageRepresentatives.boundaryMap H SphereSpectrum 4 (s, t) := by
          dsimp only [PageRepresentatives.cycleMap, PageRepresentatives.boundaryMap, E, sequence, object]
          rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
        rw [← hfactor, CategoryTheory.comp_apply]
        apply (congrArg (PageRepresentatives.cycleMap H SphereSpectrum 4 (s, t)) hy).trans
        exact (congrArg (fun f => f z)
          (PageRepresentatives.cycleMap_factor H SphereSpectrum (s, t) 4 ⊤ le_top)).trans hz
      have hall : ∀ x : PageRepresentatives.PermanentQuotient H SphereSpectrum b (s, t), x = 0 := by
        rintro ⟨x⟩
        change KIP126.Algebra.NestedQuotient.projection _ _ x = 0
        apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
        exact PageRepresentatives.boundaries_monotone H SphereSpectrum (s, t) hb (hcycles x.property)
      exact ⟨fun x y => (hall x).trans (hall y).symm⟩

  have hfinite : ∀ s : ℕ, 15 ≤ s → s ≤ 24 → Subsingleton ((sequence D .sphere).Page 6 (s,(s:ℤ)+125)) := by
    intro s hs hs'
    by_cases h : s ≤ 19
    · exact stem125_sixth_pages_15_19 I s hs h
    · exact stem125_sixth_pages_20_24 I s (by omega) hs'

  set_option backward.isDefEq.respectTransparency false in
    have hpage : Subsingleton ((sequence D .sphere).Page 6 (j,125+j)) := by
      have h := hfinite j.toNat (by omega) (by omega)
      simpa only [Int.toNat_of_nonneg (show 0≤j by omega),add_comm] using h
    haveI : Subsingleton (PageRepresentatives.PermanentQuotient H SphereSpectrum
        (1+(125+j)-130) (j,125+j)) :=
      permanentQuotient_zero_of_page_six_zero j (125+j) _ (by omega) hpage
    let e := BHS.eInfty.presentation.nuWindow SphereSpectrum (j,125+j) 130 (by omega)
    haveI : Subsingleton (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,125+j,130)).eInfty) := e.injective.subsingleton
    let hnu := ModuleCat.isZero_of_subsingleton
      (((D.family.nu D.nu SphereSpectrum).sequence.ssData (j,125+j,130)).eInfty)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (j,125+j,130)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (j,125+j,130)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f,g]
      rw [←SpectralSequenceMorphism.eInftyMap_comp,←Functor.map_comp,Iso.inv_hom_id,
        CategoryTheory.Functor.map_id,SpectralSequenceMorphism.eInftyMap_id]
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    exact hfg.symm.trans (by rw [hnu.eq_of_src f 0,CategoryTheory.Limits.comp_zero])
end

private theorem high125_nu_first_quotient (I : AdamsComputationTheorems D L G)
    (b : BiHom 125 150 (S_0_0 : Syn))
    (hb : D.sphereFirstQuotient 25 150 (quotientClass 1 b) =
      I.interpretation.sphere 25 150 highClass) :
    quotientClass 1 (b ≫ D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _) =
      firstLabel D .sphere 25 150 (G.high125 M) := by
  set_option backward.isDefEq.respectTransparency false in
    apply (D.firstQuotient SphereSpectrum 0 25 150).injective
    change (D.firstQuotient SphereSpectrum 0 25 150)
        (quotientClass 1 (b ≫ D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _)) =
      (D.firstQuotient SphereSpectrum 0 25 150)
        ((D.firstQuotient SphereSpectrum 0 25 150).symm (G.high125 M))
    rw [AddEquiv.apply_symm_apply, ← high125_label I, ← hb]
    change (D.firstQuotient SphereSpectrum 0 25 150) _ =
      (D.firstQuotient SphereSpectrum 0 25 150)
        (quotientClass 1 b ≫ XModLambdaN.map
          (D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _) 1)
    apply congrArg (D.firstQuotient SphereSpectrum 0 25 150)
    simp only [quotientClass, Category.assoc, XModLambdaN.incl_naturality,
      D.quotientFunctoriality.map_comp]

/-- The word lambda-free is expressed by every actual finite power, not
just nonvanishing at weight130. BHS lifetime applies to the permanent G
label and every chosen first-quotient lift; the same sphere/nu unit
comparison transports the result to b. -/
theorem high125_lift_lambda_powers_nonzero
    (I : AdamsComputationTheorems D L G) (R : RealizationDetectionData D)
    (hhigh : NonzeroSurvival (sequence D .sphere) (25,150) (G.high125 M))
    (b : BiHom 125 150 (S_0_0 : Syn))
    (hb : D.sphereFirstQuotient 25 150 (quotientClass 1 b) =
      I.interpretation.sphere 25 150 highClass) :
    ∀ k : ℕ, lambdaMultiply k b ≠ 0 := by
  set_option backward.isDefEq.respectTransparency false in
    let b₀ : BiHom 125 150 (nuZero D .sphere) :=
      b ≫ D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _
    have hb₀ := high125_nu_first_quotient I b hb
    obtain ⟨z, hz, hnz⟩ := hhigh
    have hpermanent : G.high125 M ∈ PageRepresentatives.permanentCycles
        H SphereSpectrum (25, 150) := ⟨z, hz⟩
    intro k
    let E := (sequence D .sphere).ssData (25, 150)
    let n : WithTop ℕ := ↑(((k : ℤ) + 2 - 2).toNat)
    let zf := (Subobject.ofLE (E.Z ⊤) (E.Z n) (E.Z_anti le_top)) z
    have hsurvives : SurvivesTo (sequence D .sphere) ((k : ℤ) + 2) (25, 150)
        (G.high125 M) := by
      have hrep : RepresentsOnPage (sequence D .sphere) ((k : ℤ) + 2) (25, 150)
          (G.high125 M) (E.pageπ n zf) := by
        refine ⟨by omega, ?_⟩
        change ∃ y : (Subobject.underlying.obj (E.Z n) : ModuleCat ℤ),
          (Subobject.ofLE (E.Z n) (E.Z 0) (E.Z_anti bot_le) ≫ E.pageπ 0) y = G.high125 M ∧
            E.pageπ n y = E.pageπ n zf
        refine ⟨zf, ?_, rfl⟩
        dsimp only [zf]
        rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
        exact hz
      refine ⟨E.pageπ n zf, hrep, ?_⟩
      intro hzero
      change E.pageπ n zf = 0 at hzero
      have hproj := E.infinity_projection_eq_of_page_projection_eq n z 0
        (by change E.pageπ n zf = _; simpa only [map_zero] using hzero)
      exact hnz (by simpa only [map_zero] using hproj)
    have hlife := R.detection.lifetime .sphere 25 150 (k + 1) (by omega)
      (G.high125 M) b₀ hpermanent (by simpa only [Nat.cast_add, Nat.cast_one,
        add_assoc, one_add_one_eq_two, sequence, object, ClassicalObject.obj] using hsurvives) hb₀
    change lambdaMultiply (k + 1 - 1) b₀ ≠ 0 at hlife
    have hk : k + 1 - 1 = k := by omega
    rw [hk] at hlife
    intro hzero
    apply hlife
    dsimp only [b₀]
    have h := congrArg (fun x => x ≫ D.nu.unitIso.inv ≫
      SyntheticCategory.biShift_zero.inv.app _) hzero
    simpa only [lambdaMultiply, Category.assoc, CategoryTheory.Limits.zero_comp] using h

/-- The two-element filtration subgroup used in Proposition 7.8.
The first-quotient comparison identifies the lift of G with the specified
E₂ class, and its λ²⁰ multiple spans F¹⁵. The nonzero permanence of G is
proved by `high125_nonzero_survival_of_computation`. -/
theorem high125_weight130_exhaustion
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (R : RealizationDetectionData D)
    (V : SphereVanishingLine H)
    (hhigh : NonzeroSurvival (sequence D .sphere) (25,150) (G.high125 M)) :
    ∃ b : BiHom 125 150 (S_0_0 : Syn),
      D.sphereFirstQuotient 25 150 (quotientClass 1 b) =
        I.interpretation.sphere 25 150 highClass ∧
      lambdaMultiply 20 b ≠ 0 ∧
      ∀ a : BiHom 125 130 (S_0_0 : Syn),
        FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a ↔
          a = 0 ∨ a = lambdaMultiply 20 b := by
  set_option backward.isDefEq.respectTransparency false in
    have hhigh' := hhigh
    obtain ⟨zg, hzg, _⟩ := hhigh'
    have hp : G.high125 M ∈ PageRepresentatives.permanentCycles H SphereSpectrum (25,150) :=
      ⟨zg, hzg⟩
    obtain ⟨b₀, hb₀⟩ := (BHS.permanent_lift .sphere 25 150 (G.high125 M)).mp hp
    let b : BiHom 125 150 (S_0_0 : Syn) :=
      b₀ ≫ SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom
    have hb : D.sphereFirstQuotient 25 150 (quotientClass 1 b) =
        I.interpretation.sphere 25 150 highClass := by
      rw [high125_label I]
      have heq : quotientClass 1 b ≫ XModLambdaN.map
          (D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _) 1 =
          quotientClass 1 b₀ := by
        have hc : b ≫ (D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _) = b₀ := by
          simp only [b, ClassicalObject.obj, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_app,
            Functor.id_obj]
          exact Category.comp_id b₀
        calc
          _ = quotientClass 1 (b ≫ (D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _)) := by
            dsimp only [quotientClass]
            rw [Category.assoc, ← XModLambdaN.incl_naturality, ← Category.assoc]
          _ = _ := congrArg (quotientClass 1) hc
      change (D.firstQuotient SphereSpectrum 0 25 150)
        (quotientClass 1 b ≫ XModLambdaN.map
          (D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _) 1) = _
      rw [heq, hb₀]
      exact (D.firstQuotient SphereSpectrum 0 25 150).apply_symm_apply (G.high125 M)
    have hn : lambdaMultiply 20 b ≠ 0 := high125_lift_lambda_powers_nonzero I R hhigh b hb 20
    let E := (sequence D .sphere).ssData (25, 150)
    let Z := PageRepresentatives.permanentCycles H SphereSpectrum (25, 150)
    let B := PageRepresentatives.boundaries H SphereSpectrum 21 (25, 150)
    let proj := KIP126.Algebra.NestedQuotient.projection Z B
    let pg : Z := ⟨G.high125 M, hp⟩
    obtain ⟨yg, hrep, _, hex⟩ := high125_component I
    obtain ⟨_, w, hw, hwy⟩ := hrep
    change (Subobject.underlying.obj (E.Z 3) : ModuleCat ℤ) at w
    rw [high125_label I] at hw
    change E.page 3 at yg
    change E.pageπ 3 w = yg at hwy
    change (Subobject.ofLE (E.Z 3) (E.Z 0) (E.Z_anti bot_le) ≫ E.pageπ 0) w = G.high125 M at hw
    have hboundary (y : (Subobject.underlying.obj (E.Z 3) : ModuleCat ℤ))
        (hy : E.pageπ 3 y = 0) :
        (Subobject.ofLE (E.Z 3) (E.Z 0) (E.Z_anti bot_le) ≫ E.pageπ 0) y ∈ B := by
      obtain ⟨v, hv⟩ := (cokernel_π_eq_zero_iff_mem_range
        (Subobject.ofLE (E.B 3) (E.Z 3) (E.B_le_Z 3)) y).mp hy
      apply PageRepresentatives.boundaries_monotone H SphereSpectrum (25, 150) (by decide : (4 : ℤ) ≤ 21)
      refine ⟨v, ?_⟩
      change (Subobject.ofLE (E.B 3) (E.Z 0) _ ≫ E.pageπ 0) v = _
      have hf : Subobject.ofLE (E.B 3) (E.Z 3) (E.B_le_Z 3) ≫
          Subobject.ofLE (E.Z 3) (E.Z 0) (E.Z_anti bot_le) =
          Subobject.ofLE (E.B 3) (E.Z 0) ((E.B_le_Z 3).trans (E.Z_anti bot_le)) := by
        rw [Subobject.ofLE_comp_ofLE]
      rw [← hf, Category.assoc]
      exact congrArg (fun q => (Subobject.ofLE (E.Z 3) (E.Z 0) (E.Z_anti bot_le) ≫ E.pageπ 0) q) hv
    have hq : ∀ x : KIP126.Algebra.NestedQuotient.Space Z B, x = 0 ∨ x = proj pg := by
      rintro ⟨x⟩
      obtain ⟨z, hz⟩ := x.property
      let zf := (Subobject.ofLE (E.Z ⊤) (E.Z 3) (E.Z_anti le_top)) z
      have hlabel : (Subobject.ofLE (E.Z 3) (E.Z 0) (E.Z_anti bot_le) ≫ E.pageπ 0) zf = x.val := by
        dsimp only [zf]
        rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
        exact hz
      change proj x = 0 ∨ proj x = proj pg
      obtain hx | hx := hex (E.pageπ 3 zf)
      · left
        apply (KIP126.Algebra.NestedQuotient.projection_eq_zero x).mpr
        exact hlabel ▸ hboundary zf hx
      · right
        apply sub_eq_zero.mp
        rw [← map_sub]
        apply (KIP126.Algebra.NestedQuotient.projection_eq_zero (x-pg)).mpr
        have hzero : E.pageπ 3 (zf - w) = 0 := by
          rw [map_sub, hx, hwy, sub_self]
        have hd := hboundary (zf - w) hzero
        change x.val - G.high125 M ∈ B
        simpa only [map_sub, hlabel, hw] using hd
    let enu := BHS.eInfty.presentation.nuWindow SphereSpectrum (25, 150) 130 (by decide)
    let f := (D.family.functor.map D.nu.unitIso.hom).eInftyMap (25, 150, 130)
    let g := (D.family.functor.map D.nu.unitIso.inv).eInftyMap (25, 150, 130)
    have hfg : g ≫ f = 𝟙 _ := by
      dsimp only [f, g]
      rw [← SpectralSequenceMorphism.eInftyMap_comp, ← Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, SpectralSequenceMorphism.eInftyMap_id]
    have hg : Function.Injective g := by
      intro x y hxy
      have h := congrArg f hxy
      simpa only [← CategoryTheory.comp_apply, hfg, ModuleCat.id_apply] using h
    let qmap := enu.toLinearMap.comp g.hom
    have hqi : Function.Injective qmap := enu.injective.comp hg
    have htwo (x y : ((D.family.sphere).sequence.ssData (25, 150, 130)).eInfty) :
        x = 0 ∨ y = 0 ∨ x = y := by
      obtain hx | hx := hq (qmap x)
      · exact Or.inl (hqi (by simpa only [map_zero] using hx))
      obtain hy | hy := hq (qmap y)
      · exact Or.inr (Or.inl (hqi (by simpa only [map_zero] using hy)))
      · exact Or.inr (Or.inr (hqi (hx.trans hy.symm)))
    let F := towerFiltration (nuCoefficientUnit H.unit D.nu) (S_0_0 : Syn)
    have hzero (x : (Subobject.underlying.obj (F.F 25 (125, 130)) : ModuleCat ℤ))
        (hx : F.toAssociatedGraded 25 (125, 130) x = 0) : (F.F 25 (125, 130)).arrow x = 0 := by
      have hmem := (subobject_cokernel_π_eq_zero_iff (F.F 26 (125, 130))
        (F.F 25 (125, 130)) (F.mono 25 (125, 130)) x).mp hx
      apply stem125_weight130_filtration26_zero I BHS V _
      simpa only [F, towerFiltration, OrderIso.apply_symm_apply, FiltrationAtLeast] using hmem
    have hgen : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 25 (lambdaMultiply 20 b) := by
      obtain ⟨_, _, a, ha, _⟩ := D.comparisonCompatible.homotopy_lambda 25 150 20 b
      change _ ∈ towerFiltrationSubmodule (nuCoefficientUnit H.unit D.nu) S_0_0 25 (125,130)
      have hmem : _ ∈ (ModuleCat.subobjectModule _)
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) S_0_0).F 25 (125,130)) := ⟨a, ha⟩
      simpa only [towerFiltration, OrderIso.apply_symm_apply] using hmem
    have hmember (a : BiHom 125 130 (S_0_0 : Syn))
        (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 25 a) :
        ∃ x : (Subobject.underlying.obj (F.F 25 (125, 130)) : ModuleCat ℤ),
          (F.F 25 (125, 130)).arrow x = a := by
      change a ∈ (ModuleCat.subobjectModule _) (F.F 25 (125,130))
      simpa only [F, towerFiltration, OrderIso.apply_symm_apply, FiltrationAtLeast] using ha
    obtain ⟨bg, hbg⟩ := hmember _ hgen
    refine ⟨b, hb, hn, fun a => ?_⟩
    constructor
    · intro ha
      obtain ⟨x, hx⟩ := hmember a ((stem125_weight130_filtration15_eq25 I BHS V a).mp ha)
      let e := D.sphereConvergence.identification (25,150,130)
      have hcases := htwo (e.inv (F.toAssociatedGraded 25 (125,130) x))
        (e.inv (F.toAssociatedGraded 25 (125,130) bg))
      rcases hcases with h | h | h
      · left
        rw [← hx]
        apply hzero
        exact e.toLinearEquiv.symm.map_eq_zero_iff.mp h
      · exact (hn (hbg ▸ hzero bg (e.toLinearEquiv.symm.map_eq_zero_iff.mp h))).elim
      · right
        apply sub_eq_zero.mp
        have h' : F.toAssociatedGraded 25 (125,130) (x-bg) = 0 := by
          rw [map_sub, e.toLinearEquiv.symm.injective h, sub_self]
        have h'' := hzero (x-bg) h'
        simpa only [map_sub, hx, hbg] using h''
    · rintro (rfl | rfl)
      · exact (towerFiltrationSubmodule _ _ _ _).zero_mem
      · exact (stem125_weight130_filtration15_eq25 I BHS V _).mpr hgen

/-- Every nonzero high-filtration class has the specified classical G
detector after the SAME realization. This is the input to the tmf
detection argument. The source sphere is transported to nu(S) by the
existing unit iso; no new realization or detected representative is chosen. -/
theorem high125_weight130_nonzero_classical_detection
    (I : AdamsComputationTheorems D L G) (BHS : SyntheticComparisonTheorems D) (R : RealizationDetectionData D)
    (V : SphereVanishingLine H)
    (hhigh : NonzeroSurvival (sequence D .sphere) (25,150) (G.high125 M))
    (a : BiHom 125 130 (S_0_0 : Syn))
    (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 15 a) (hne : a ≠ 0) :
    TowerDetection.Detects (D.classicalConvergence .sphere) (25,150)
      (G.high125 M) (realizeNu D R.coordinates .sphere (a ≫ D.nu.unitIso.inv)) := by
  set_option backward.isDefEq.respectTransparency false in
    obtain ⟨b, hb, _, hexhaust⟩ := high125_weight130_exhaustion I BHS R V hhigh
    obtain hzero | rfl := (hexhaust a).mp ha
    · exact (hne hzero).elim
    · let b₀ : BiHom 125 150 (nuZero D .sphere) :=
        b ≫ D.nu.unitIso.inv ≫ SyntheticCategory.biShift_zero.inv.app _
      have hd := R.detection.detection .sphere 25 150 (G.high125 M) b₀ hhigh
        (high125_nu_first_quotient I b hb)
      have hzero : realizeNuZero D R.coordinates .sphere b₀ =
          realizeNu D R.coordinates .sphere (b ≫ D.nu.unitIso.inv) := by
        simp only [realizeNuZero, b₀, ClassicalObject.obj, Category.assoc, Iso.inv_hom_id_app,
          Functor.id_obj, Category.comp_id]
      have hlambda : lambdaMultiply 20 b ≫ D.nu.unitIso.inv =
          lambdaMultiply 20 (𝟙 (Smn (Syn := Syn) 125 150)) ≫
            (b ≫ D.nu.unitIso.inv) := by
        simp only [lambdaMultiply, Category.assoc, Category.id_comp]
      have hreal : realizeNu D R.coordinates .sphere
          (lambdaMultiply 20 b ≫ D.nu.unitIso.inv) =
          realizeNu D R.coordinates .sphere (b ≫ D.nu.unitIso.inv) := by
        rw [hlambda]
        simp only [realizeNu, Functor.map_comp, ← Category.assoc, R.coordinates.lambda]
      rw [hreal]
      rw [hzero] at hd
      exact hd

end
end KIP126.Computation.SphereAndCofiber
