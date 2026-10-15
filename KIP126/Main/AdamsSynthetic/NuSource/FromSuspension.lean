module

public import KIP126.Def.AdamsSynthetic.ComparisonStatements
public import KIP126.Literature.Source
public import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
public import KIP126.Def.ClassicalAdams.TowerNaturality.Proofs
public import KIP126.Def.ClassicalAdams.MapFiltration.Proofs
public import KIP126.Def.ClassicalAdams.TowerResolution.Proofs
public import KIP126.Def.ClassicalAdams.TowerNaturality.Unit.Proofs
public import KIP126.Def.Synthetic.Context.Coherence.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Def.Synthetic.Localization.Recovery.Proofs
public import KIP126.Def.StableHomotopy.Context.Mapping.Data
public import KIP126.Def.SpectralSequence.Permanence.Proofs
public import KIP126.Def.SpectralSequence.Basic.Proofs
public import KIP126.Def.Comparison.ClassicalSynthetic.RealizationTower.Proofs
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Main.Computation.LinCoordinates.Model.Classes.Proofs
public import KIP126.Computation.LinCoordinates.Model.BasisCatalogue.Data
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-! The ν-cofiber source comparison from detection, finite coordinates, and the specified suspension square. -/

namespace KIP126.Main.AdamsSynthetic

section NuSourceProof
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Literature.AdamsSynthetic
open KIP126.LinE2 KIP126.Algebra KIP126.Comparison.ClassicalSynthetic
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C := Syn)]
    {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

private theorem nu_source_from_suspension_square
    (D : AdamsComparison H M Syn) (B : AlgebraRealizationComparison D) (van : E2WeightVanishing D)
    (eta : BiHom 1 2 (S_0_0 : Syn)) (CS : ClassicalHopfThetaClasses H)
    (CB : ClassicalHopfComparison D eta CS)
    (hdet : TowerDetection.Detects CS.convergence (1,4) (Sphere.Internal.hi H M 2) CS.nu)
    (hperm : NonzeroSurvival (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      (1,4) (Sphere.Internal.hi H M 2))
    (ring : Mod2RingStructure H)
    [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
    (hlift : KIP126.Synthetic.SyntheticTriangleLiftComparison H D.nu)
    (S : NuCofiberLifts D)
    (e : E2 H SphereSpectrum 1 4 ≃ₗ[ℤ] E2At 1 4)
    (coord : E2 H SphereSpectrum 1 4 ≃ₗ[ℤ] (BasisIndex 1 4 →₀ F2))
    (values : ∀ i : BasisIndex 1 4,
      (e (coord.symm (Finsupp.single i 1))).val = basisValue (basisRowAt 1 4 i))
    (rows : ∀ r ∈ basisRows, r.s=1 → r.t=4 → r.monomial="2,1")
    (hs : D.nu.functor.map ((shiftFunctor C (1:ℤ)).map D.hopfAndDetector.nuMap) ≫
        (D.nu.suspensionIso SphereSpectrum).hom =
      (D.nu.suspensionIso (Sphere (C:=C) 3)).hom ≫
        (SyntheticCategory.biShift (1,1)).map (D.nu.functor.map D.hopfAndDetector.nuMap)) :
    NuCofiberSourceResults D S := by
  classical
  have map_filtration_precompose {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
      (k : ℕ) (h : AdamsFiltrationAtLeast H g k) :
      AdamsFiltrationAtLeast H (f ≫ g) k := by
    obtain ⟨b,hb⟩ := h
    exact ⟨f ≫ b, by rw [Category.assoc,hb]⟩
  have map_filtration_postcompose {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
      (k : ℕ) (h : AdamsFiltrationAtLeast H f k) :
      AdamsFiltrationAtLeast H (f ≫ g) k := by
    obtain ⟨b,hb⟩ := h
    refine ⟨b ≫ adamsTowerInduced H.unit g k, ?_⟩
    rw [Category.assoc, adamsTowerInduced_map, ←Category.assoc,hb]
    rfl
  have realization_preserves_tower_factor
      (F : Syn ⥤ C) [F.Monoidal] [F.CommShift ℤ] [F.Additive]
      {HS : Syn} (unitS : S_0_0 ⟶ HS) (coefficient : F.obj HS ≅ H.HF2)
      (Y : Syn) (X : C) (base : F.obj Y ≅ X)
      (P : RealizationTower.Comparison F unitS H.unit coefficient Y X base)
      {A : Syn} (a : A ⟶ Y) (k : ℕ)
      (ha : ∃ b : A ⟶ adamsTower unitS Y k,
        b ≫ adamsTowerMap unitS Y 0 k (Nat.zero_le _) = a) :
      AdamsFiltrationAtLeast H (F.map a ≫ base.hom) k := by
    obtain ⟨b,hb⟩ := ha
    have ht := RealizationTower.towerMap_naturality P 0 k (Nat.zero_le _)
    rw [P.zero] at ht
    refine ⟨F.map b ≫ (P.tower k).hom, ?_⟩
    rw [Category.assoc, ←ht, ←Category.assoc, ←Functor.map_comp, hb]
  have nu_weight_five_filtration_two
      (D : AdamsComparison H M Syn) (van : E2WeightVanishing D)
      (a : BiHom 3 5 (nuZero D .sphere)) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 2 a := by
    have he (j : ℤ) (hj : 0 ≤ j) (hj2 : j < 2) :
        IsZero (((D.family.obj (nuZero D .sphere)).sequence.ssData (j,3+j,5)).eInfty) := by
      let sd := (D.family.obj (nuZero D .sphere)).sequence.ssData (j,3+j,5)
      have h0 : IsZero (sd.page 0) := by
        apply ModuleCat.isZero_iff_subsingleton.mpr
        exact van .sphere 0 j (3+j) 5 (by omega)
      have hb := sd.eq_of_page_isZero 0 h0
      apply sd.page_isZero_of_eq ⊤
      apply le_antisymm (sd.B_le_Z _)
      calc
        sd.Z ⊤ ≤ sd.Z 0 := sd.Z_anti (show (0 : WithTop ℕ) ≤ ⊤ from le_top)
        _ = sd.B 0 := hb.symm
        _ ≤ sd.B ⊤ := sd.B_mono le_top
    apply (D.convergence (.shift (0,0) (.nu .sphere))).filtrationAtLeast_iff_of_eInfty_isZero
      0 2 3 5 (by omega) he a |>.mp
    refine ⟨a, ?_⟩
    change a ≫ adamsTowerMap (nuCoefficientUnit H.unit D.nu) _ 0 0 _ = a
    rw [adamsTowerMap_self]
    exact Category.comp_id _
  have nu_weight_five_realization_filtration_two
      (D : AdamsComparison H M Syn) (B : AlgebraRealizationComparison D) (van : E2WeightVanishing D)
      (a : BiHom 3 5 (nuZero D .sphere)) :
      AdamsFiltrationAtLeast H (D.recovery.realization.map a) 2 := by
    letI := B.algebra.classicalSymmetric
    letI := B.algebra.syntheticSymmetric
    letI := B.algebra.realizationMonoidal.realization
    letI := B.realizationAdditive
    letI := D.realizationShift
    let R := D.recovery.realization
    let unit := nuCoefficientUnit H.unit D.nu
    let e : RealizationTower.nuWeightObject D .sphere 0 0 ≅ nuZero D .sphere :=
      SyntheticCategory.biShift_zero.app _
    let P := B.nuE2.tower .sphere 0 0
    let base := B.weights.doubleShift D.nu D.recovery
      (ClassicalObject.sphere.obj D.hopfAndDetector) 0 (-0)
    obtain ⟨b,hb⟩ := nu_weight_five_filtration_two D van a
    change b ≫ adamsTowerMap unit (nuZero D .sphere) 0 2 _ = a at hb
    have ha : ∃ b' : Smn (Syn := Syn) 3 5 ⟶
        adamsTower unit (RealizationTower.nuWeightObject D .sphere 0 0) 2,
        b' ≫ adamsTowerMap unit _ 0 2 (Nat.zero_le _) = a ≫ e.inv := by
      refine ⟨b ≫ adamsTowerInduced unit e.inv 2, ?_⟩
      rw [Category.assoc,adamsTowerInduced_map,←Category.assoc,hb]
      rfl
    have hf := realization_preserves_tower_factor R unit _ _ _ _ P (a ≫ e.inv) 2 ha
    change AdamsFiltrationAtLeast H (R.map (a ≫ e.inv) ≫ base.hom) 2 at hf
    have hh := map_filtration_postcompose _ (base.inv ≫ R.map e.hom) 2 hf
    have heq : (R.map (a ≫ e.inv) ≫ base.hom) ≫ (base.inv ≫ R.map e.hom) = R.map a := by
      rw [Category.assoc,base.hom_inv_id_assoc,←Functor.map_comp]
      simp only [Category.assoc,e.inv_hom_id,Category.comp_id]
    rw [heq] at hh
    exact hh
  have lambda_one_division_of_quotient_zero
      {X : Syn} (m w : ℤ) (z : BiHom m (w-1) X) (hz : quotientClass 1 z=0) :
      ∃ b : BiHom m w X, lambdaMultiply 1 b=z := by
    obtain ⟨a,ha⟩ := (vanishesModLambda_iff_factors 1 z).mp hz
    let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
    let e : F.obj (Smn m w : Syn) ≅ Smn m (w-1) :=
      (SyntheticCategory.biShift_comp (m,w) (0,-1)).app S_0_0 ≪≫
        eqToIso (by congr 1; simp [sub_eq_add_neg])
    let b := (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-1)).preimage (e.hom≫a)
    have hb : F.map b=e.hom≫a :=
      (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-1)).map_preimage _
    refine ⟨b,?_⟩
    have he : lambdaMultiply 1 b=e.inv≫lambdaPow 1 (Smn m w)≫b := by
      unfold lambdaMultiply
      change eqToHom (by congr 1; simp) ≫ (SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0 ≫
        lambdaPow 1 (Smn m w) ≫ b =
        (eqToHom (by congr 1; simp) ≫ (SyntheticCategory.biShift_comp (m,w) (0,-1)).inv.app S_0_0) ≫
        lambdaPow 1 (Smn m w) ≫ b
      exact (Category.assoc _ _ _).symm
    rw [he]
    rw [←lambdaPow_naturality 1 b]
    change e.inv≫F.map b≫lambdaPow 1 X=z
    rw [hb]
    simp only [Category.assoc,e.inv_hom_id_assoc]
    exact ha
  have sphere_weight_five_realization_filtration_two
      (D : AdamsComparison H M Syn) (B : AlgebraRealizationComparison D) (van : E2WeightVanishing D)
      (a : BiHom 3 5 (S_0_0 : Syn)) :
      AdamsFiltrationAtLeast H (D.recovery.realization.map a) 2 := by
    let R := D.recovery.realization
    let e : nuZero D .sphere ≅ (S_0_0 : Syn) :=
      SyntheticCategory.biShift_zero.app _ ≪≫ D.nu.unitIso
    have h := nu_weight_five_realization_filtration_two D B van (a ≫ e.inv)
    have hh := map_filtration_postcompose _ (R.map e.hom) 2 h
    have heq : R.map (a ≫ e.inv) ≫ R.map e.hom = R.map a := by
      rw [←Functor.map_comp]
      simp only [Category.assoc,e.inv_hom_id,Category.comp_id]
    rw [heq] at hh
    exact hh
  have sphere_quotient_zero_realization_filtration_two
      (D : AdamsComparison H M Syn) (B : AlgebraRealizationComparison D) (van : E2WeightVanishing D)
      (a : BiHom 3 4 (S_0_0 : Syn)) (ha : quotientClass 1 a = 0) :
      AdamsFiltrationAtLeast H (D.recovery.realization.map a) 2 := by
    obtain ⟨b,hb⟩ := lambda_one_division_of_quotient_zero 3 5 a ha
    have h := sphere_weight_five_realization_filtration_two D B van b
    rw [←hb]
    unfold lambdaMultiply
    simp only [Functor.map_comp, ←Category.assoc]
    exact map_filtration_precompose _ _ 2 h
  have normalized_nu_quotient_zero_forces_filtration_two
      (D : AdamsComparison H M Syn) (B : AlgebraRealizationComparison D) (van : E2WeightVanishing D)
      (S : NuCofiberLifts D) (he : normalizedExponent H D.hopfAndDetector.nuMap = 1)
      (hz : quotientClass 1 (sourceNormalizedNu D S he) = 0) :
      AdamsFiltrationAtLeast H D.hopfAndDetector.nuMap 2 := by
    let R := D.recovery.realization
    let e : (SyntheticCategory.biShift (0, (normalizedExponent H D.hopfAndDetector.nuMap : ℤ))).obj
        (D.nu.functor.obj (Sphere (C := C) 3)) ≅ Smn (Syn := Syn) 3 4 := by
      rw [he]
      exact (SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree D) ≪≫
        (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0
    have hf := sphere_quotient_zero_realization_filtration_two D B van
      (sourceNormalizedNu D S he) hz
    have hpre := map_filtration_precompose (R.map e.hom) _ 2 hf
    have hpost := map_filtration_postcompose _ (R.map D.nu.unitIso.inv) 2 hpre
    have hmap : AdamsFiltrationAtLeast H (R.map S.nuLift.map) 2 := by
      have heq : (R.map e.hom ≫ R.map (sourceNormalizedNu D S he)) ≫
          R.map D.nu.unitIso.inv = R.map S.nuLift.map := by
        rw [←Functor.map_comp,←Functor.map_comp]
        congr 1
        change (e.hom ≫ (e.inv ≫ S.nuLift.map ≫ D.nu.unitIso.hom)) ≫ D.nu.unitIso.inv = _
        simp only [Category.assoc,e.hom_inv_id_assoc,Iso.hom_inv_id,Category.comp_id]
      rw [heq] at hpost
      exact hpost
    have hfactor := map_filtration_precompose
      (R.map (lambdaToPositivePow (normalizedExponent H D.hopfAndDetector.nuMap)
        (D.nu.functor.obj (Sphere (C := C) 3)))) _ 2 hmap
    rw [←Functor.map_comp,S.nuLift.factorization] at hfactor
    have hrecover := map_filtration_postcompose _
      (D.recovery.nuRealizationIso.hom.app SphereSpectrum) 2 hfactor
    rw [D.recovery.recovery_naturality] at hrecover
    have hfinal := map_filtration_precompose
      (D.recovery.nuRealizationIso.inv.app (Sphere (C := C) 3)) _ 2 hrecover
    simpa only [Iso.inv_hom_id_app_assoc] using hfinal
  have detected_filtration_one_not_two {X : C}
      (c : TowerDetection.Convergence H.unit X) (t : ℤ)
      (x : (adamsTowerInternalSpectralSequence H.unit X).Page 2 (1,t))
      (hx : x ≠ 0) (a : HomotopyGroup (t-1) X)
      (hd : TowerDetection.Detects c (1,t) x a) :
      ¬ AdamsFiltrationAtLeast H a 2 := by
    intro htwo
    let E := adamsTowerInternalSpectralSequence H.unit X
    let sd := E.ssData (1,t)
    have hin (r : ℤ) (hr : 2 ≤ r) : E.d r ((1,t)-E.diffDeg r)=0 := by
      have hdeg : (1,t)-E.diffDeg r = ((1-r,t-r+1) : ℤ × ℤ) := by
        change (1,t)-(r,r-1)=_
        ext <;> dsimp; omega
      haveI : Subsingleton (E.Page r ((1,t)-E.diffDeg r)) := by
        rw [hdeg]
        exact adamsTowerInternal_page_subsingleton_of_negative H.unit X r
          (1-r) (t-r+1) (by omega)
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro b
      have hb : b=0 := Subsingleton.elim _ _
      simp only [hb,map_zero]
    have hB : sd.B ⊤ = sd.B 0 :=
      boundaries_top_eq_of_d_eq_zero E 2 (by rfl) (1,t) hin
    obtain ⟨z,hz,a',ha',hgr⟩ := hd
    let F := TowerDetection.filtration H.unit X
    have hm : a ∈ (ModuleCat.subobjectModule _) (F.F 2 (t-1)) := by
      have hm' : a ∈ TowerDetection.filtrationSubmodule H.unit X 2 (t-1) := htwo
      simpa only [F,TowerDetection.filtration,OrderIso.apply_symm_apply] using hm'
    have hgr0 : F.toAssociatedGraded 1 (t-1) a' = 0 := by
      apply (subobject_cokernel_π_eq_zero_iff (F.F 2 (t-1)) (F.F 1 (t-1))
        (F.mono 1 (t-1)) a').mpr
      rwa [ha']
    have hzero : sd.pageπ ⊤ z = 0 := by
      apply (c.identification (1,t)).toLinearEquiv.injective
      exact hgr.trans (hgr0.trans (map_zero _).symm)
    have hmem := (subobject_cokernel_π_eq_zero_iff (sd.B ⊤) (sd.Z ⊤)
      (sd.B_le_Z ⊤) z).mp hzero
    rw [hB] at hmem
    apply hx
    rw [←hz]
    apply (subobject_cokernel_π_eq_zero_iff (sd.B 0) (sd.Z 0) (sd.B_le_Z 0)
      ((Subobject.ofLE (sd.Z ⊤) (sd.Z 0) (sd.Z_anti le_top)) z)).mpr
    have heq := ConcreteCategory.congr_hom (Subobject.ofLE_arrow (sd.Z_anti (show (0 : WithTop ℕ) ≤ ⊤ from le_top))) z
    change (sd.Z 0).arrow ((Subobject.ofLE (sd.Z ⊤) (sd.Z 0) (sd.Z_anti le_top)) z) =
      (sd.Z ⊤).arrow z at heq
    rwa [heq]
  have nu_coordinates_nonzero_unique
   {A:Type v} [AddCommGroup A] [Module ℤ A]
   (e:A≃ₗ[ℤ] E2At 1 4) (coord:A≃ₗ[ℤ] (BasisIndex 1 4 →₀ F2))
   (values:∀i:BasisIndex 1 4,(e (coord.symm (Finsupp.single i 1))).val=basisValue (basisRowAt 1 4 i))
   (rows : ∀ (r : BasisRow), r ∈ basisRows → r.s = 1 → r.t = 4 → r.monomial = "2,1") :
   ∀f g:A,f≠0→g≠0→f=g := by
    classical
    have hi (i:BasisIndex 1 4) : (basisRowAt 1 4 i).monomial="2,1" := by
      have hm : basisRowAt 1 4 i ∈ basisRows.filter (fun r=>r.s==1 && r.t==4) := by
        change (basisRows.filter (fun r=>r.s==1 && r.t==4))[i.val] ∈ _
        exact List.getElem_mem i.isLt
      obtain ⟨hm,hd⟩:=List.mem_filter.mp hm
      have hd':(basisRowAt 1 4 i).s=1 ∧ (basisRowAt 1 4 i).t=4 := by simpa using hd
      exact rows _ hm hd'.1 hd'.2
    haveI : Subsingleton (BasisIndex 1 4) := ⟨by
      intro i j
      have hv : e (coord.symm (Finsupp.single i 1))=e (coord.symm (Finsupp.single j 1)) := by
        apply Subtype.ext
        rw [values,values]
        simp only [basisValue,hi i,hi j]
      have hs:Finsupp.single i (1:F2)=Finsupp.single j 1 := coord.symm.injective (e.injective hv)
      by_contra hij
      have hh:=congrArg (fun f:BasisIndex 1 4 →₀ F2=>f i) hs
      simp [hij] at hh⟩
    intro f g hf hg
    have hfn:coord f≠0 := by intro h; exact hf (coord.injective (h.trans (map_zero coord).symm))
    obtain ⟨i,hi⟩ : ∃ i, coord f i ≠ 0 := by
      by_contra h
      push Not at h
      exact hfn (Finsupp.ext h)
    have hc (a:A) (ha:a≠0) : coord a i=1 := by
      generalize h:coord a i=c
      fin_cases c
      · exfalso
        apply ha
        apply coord.injective
        ext j
        have hj:j=i:=Subsingleton.elim _ _
        subst j
        simpa using h
      · rfl
    apply coord.injective
    ext j
    have hj:j=i:=Subsingleton.elim _ _
    subst j
    rw [hc f hf,hc g hg]
  have nonzero_survival_label_ne_zero
      (E : KIP126.SpectralSequence (ModuleCat ℤ) (ℤ × ℤ)) (p : ℤ × ℤ)
      (x : E.Page 2 p) (h : NonzeroSurvival E p x) : x ≠ 0 := by
    obtain ⟨z,hz,hn⟩ := h
    intro hx
    apply hn
    have hh := (E.ssData p).infinity_projection_eq_of_page_projection_eq
      (↑(2-E.r₀).toNat) z 0 (hz.trans (hx.trans (map_zero _).symm))
    simpa only [map_zero] using hh
  have triangle_inverse_rotation_transport
      {A B E Z : Syn} (g : B ⟶ E) (h : E ⟶ Z) (d : Z ⟶ B⟦(1:ℤ)⟧)
      (hd : Triangle.mk g h d ∈ distTriang Syn) (j : Z ≅ A⟦(1:ℤ)⟧) :
      ∃ a : A ⟶ B,
        (shiftFunctor Syn (1:ℤ)).map a = -(j.inv ≫ d) ∧
        Triangle.mk a g (h ≫ j.hom) ∈ distTriang Syn := by
    let a := (shiftFunctor Syn (1:ℤ)).preimage (-(j.inv ≫ d))
    have ha : (shiftFunctor Syn (1:ℤ)).map a = -(j.inv ≫ d) :=
      (shiftFunctor Syn (1:ℤ)).map_preimage _
    refine ⟨a,ha,?_⟩
    apply (rotate_distinguished_triangle _).mpr
    apply isomorphic_distinguished _ hd
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) j.symm ?_ ?_ ?_
    · simp
    · simp
    · simp only [Triangle.rotate, Triangle.mk, Iso.refl_hom, CategoryTheory.Functor.map_id,
        Iso.symm_hom,Category.comp_id]
      exact congrArg Neg.neg ha |>.trans (neg_neg _)
  let nuPositiveLandingIso (N : NuFunctorData C Syn) (X : C) :
      N.functor.obj (X⟦(1:ℤ)⟧) ≅
        ((SyntheticCategory.biShift (0,1)).obj (N.functor.obj X))⟦(1:ℤ)⟧ :=
    N.suspensionIso X ≪≫
      (SyntheticCategory.biShift_comp (0,1) (1,0)).symm.app (N.functor.obj X) ≪≫
      (SyntheticCategory.biShift_compat (Syn:=Syn) 1).app _
  have boundaryLanding_natural_of_suspension_square
      (N : NuFunctorData C Syn) {X Y : C} (f : X ⟶ Y)
      (hs : N.functor.map ((shiftFunctor C (1:ℤ)).map f) ≫ (N.suspensionIso Y).hom =
        (N.suspensionIso X).hom ≫ (SyntheticCategory.biShift (1,1)).map (N.functor.map f)) :
      (SyntheticCategory.biShift (0,-1)).map (N.functor.map ((shiftFunctor C (1:ℤ)).map f)) ≫
        (N.boundaryLandingIso Y).hom =
        (N.boundaryLandingIso X).hom ≫ (shiftFunctor Syn (1:ℤ)).map (N.functor.map f) := by
    let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
    have h₁ := congrArg F.map hs
    have h₂ := (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.naturality (N.functor.map f)
    have h₃ := (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.naturality (N.functor.map f)
    change F.map (N.functor.map ((shiftFunctor C (1:ℤ)).map f)) ≫
        (F.map (N.suspensionIso Y).hom ≫
          (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (N.functor.obj Y) ≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app (N.functor.obj Y)) =
      (F.map (N.suspensionIso X).hom ≫
          (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (N.functor.obj X) ≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app (N.functor.obj X)) ≫ _
    simp only [Functor.map_comp] at h₁
    change F.map ((SyntheticCategory.biShift (1,1)).map (N.functor.map f)) ≫
        (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (N.functor.obj Y) =
        (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (N.functor.obj X) ≫
          (SyntheticCategory.biShift (1,0)).map (N.functor.map f) at h₂
    change (SyntheticCategory.biShift (1,0)).map (N.functor.map f) ≫ _ = _ at h₃
    calc
      _ = F.map (N.suspensionIso X).hom ≫
          F.map ((SyntheticCategory.biShift (1,1)).map (N.functor.map f)) ≫
          (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (N.functor.obj Y) ≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app (N.functor.obj Y) := by
        simpa only [Category.assoc] using congrArg (fun z => z ≫
          (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (N.functor.obj Y) ≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app (N.functor.obj Y)) h₁
      _ = _ := by rw [reassoc_of% h₂, h₃]; simp only [Category.assoc]
  have lambda_negative_self (coh : BiShiftCoherence Syn) (A : Syn) :
      SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,-1)).obj A) =
        (SyntheticCategory.biShift (0,-1)).map (SyntheticCategory.lam.app A) := by
    have h := coh.lambda_comm (0,-1) A
    simpa only [biShiftAddIso, Iso.trans_hom, NatTrans.comp_app,
      Iso.trans_inv, eqToIso.hom,eqToIso.inv,eqToHom_app,eqToHom_refl,
      Category.comp_id,Category.id_comp,Iso.hom_inv_id_app_assoc] using h
  have positive_lambda_shift_coherence
      (coh : BiShiftCoherence Syn) (A : Syn) :
      (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app A ≫
        (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A) =
      (SyntheticCategory.biShift (0,-1)).map
          ((SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A) ≫
        SyntheticCategory.lam.app
          ((SyntheticCategory.biShift (1,0)).obj ((SyntheticCategory.biShift (0,1)).obj A)) := by
    have ha := coh.associativity (0,1) (1,0) (0,-1) (1,1) (1,-1) (1,0)
      rfl rfl rfl rfl A
    have hb := coh.associativity (0,1) (0,-1) (1,0) (0,0) (1,-1) (1,0)
      rfl rfl rfl rfl A
    have hu := coh.left_unit (1,0) A
    have hc := coh.lambda_comm (1,0) ((SyntheticCategory.biShift (0,1)).obj A)
    simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,
      eqToHom_refl,Category.comp_id] at ha hb hu
    simp only [biShiftAddIso,Iso.trans_hom,Iso.trans_inv,
      eqToIso.hom,eqToIso.inv,eqToHom_refl,Category.comp_id,Category.id_comp] at hc
    have hL : lambdaToPositivePow 1 A = SyntheticCategory.biShift_zero.inv.app A ≫
        (SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app A ≫
        SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,1)).obj A) := by
      simp only [lambdaToPositivePow,lambdaPow_one coh,eqToHom_refl,Category.id_comp]
      rfl
    have haux : (SyntheticCategory.biShift_comp (0,1) (1,-1)).hom.app A ≫
        (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A) =
      (SyntheticCategory.biShift_comp (0,-1) (1,0)).inv.app
          ((SyntheticCategory.biShift (0,1)).obj A) ≫
        (SyntheticCategory.biShift (1,0)).map
          (SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,1)).obj A)) := by
      apply (cancel_epi ((SyntheticCategory.biShift_comp (0,-1) (1,0)).hom.app
        ((SyntheticCategory.biShift (0,1)).obj A))).1
      calc
        _ = ((SyntheticCategory.biShift (1,0)).map
            ((SyntheticCategory.biShift_comp (0,1) (0,-1)).hom.app A) ≫
            (SyntheticCategory.biShift_comp (0,0) (1,0)).hom.app A) ≫
              (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A) := by
          simpa only [Category.assoc] using congrArg
            (fun z => z ≫ (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A)) hb.symm
        _ = _ := by
          have hu' : (SyntheticCategory.biShift_comp (0,0) (1,0)).hom.app A =
              (SyntheticCategory.biShift (1,0)).map (SyntheticCategory.biShift_zero.hom.app A) := hu
          rw [hu',hL]
          simp only [Functor.map_comp,Category.assoc]
          simp only [←Functor.map_comp_assoc,Iso.hom_inv_id_app,
            Iso.hom_inv_id_app_assoc,Category.id_comp,CategoryTheory.Functor.map_id]
    apply (cancel_epi ((SyntheticCategory.biShift (0,-1)).map
      ((SyntheticCategory.biShift_comp (0,1) (1,0)).hom.app A))).1
    calc
      _ = ((SyntheticCategory.biShift_comp (1,0) (0,-1)).hom.app
          ((SyntheticCategory.biShift (0,1)).obj A) ≫
          (SyntheticCategory.biShift_comp (0,1) (1,-1)).hom.app A) ≫
          (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A) := by
        simpa only [Category.assoc] using congrArg
          (fun z => z ≫ (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A)) ha
      _ = SyntheticCategory.lam.app
          ((SyntheticCategory.biShift (1,0)).obj ((SyntheticCategory.biShift (0,1)).obj A)) := by
        rw [Category.assoc,haux]
        exact hc.symm
      _ = _ := by
        simp only [←Category.assoc,←Functor.map_comp,Iso.hom_inv_id_app,
          CategoryTheory.Functor.map_id,Category.id_comp]
  have positive_lambda_landing_square
      (coh : BiShiftCoherence Syn) (N : NuFunctorData C Syn) (X : C) :
      (N.boundaryLandingIso X).hom ≫
        (shiftFunctor Syn (1:ℤ)).map (lambdaToPositivePow 1 (N.functor.obj X)) =
      SyntheticCategory.lam.app (N.functor.obj (X⟦(1:ℤ)⟧)) ≫
        (nuPositiveLandingIso N X).hom := by
    let A := N.functor.obj X
    let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
    let P := (SyntheticCategory.biShift (Syn:=Syn) (0,1)).obj A
    have hp := positive_lambda_shift_coherence coh A
    have hc := (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.naturality
      (lambdaToPositivePow 1 A)
    have hn := SyntheticCategory.lam.naturality
      ((SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A)
    have hs := SyntheticCategory.lam.naturality (N.suspensionIso X).hom
    change (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A) ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app P =
      (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app A ≫
        (shiftFunctor Syn (1:ℤ)).map (lambdaToPositivePow 1 A) at hc
    change F.map ((SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A) ≫
        SyntheticCategory.lam.app ((SyntheticCategory.biShift (1,0)).obj P) =
      SyntheticCategory.lam.app ((SyntheticCategory.biShift (1,1)).obj A) ≫
        (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A at hn
    change F.map (N.suspensionIso X).hom ≫
        SyntheticCategory.lam.app ((SyntheticCategory.biShift (1,1)).obj A) =
      SyntheticCategory.lam.app (N.functor.obj (X⟦(1:ℤ)⟧)) ≫ (N.suspensionIso X).hom at hs
    change (F.map (N.suspensionIso X).hom ≫
        (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app A ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app A) ≫ _ =
      SyntheticCategory.lam.app (N.functor.obj (X⟦(1:ℤ)⟧)) ≫
        ((N.suspensionIso X).hom ≫
          (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A ≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app P)
    calc
      _ = F.map (N.suspensionIso X).hom ≫
          (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app A ≫
          (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A) ≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app P := by
        simpa only [Category.assoc] using congrArg (fun z =>
          F.map (N.suspensionIso X).hom ≫
          (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app A ≫ z) hc.symm
      _ = F.map (N.suspensionIso X).hom ≫
          F.map ((SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A) ≫
          SyntheticCategory.lam.app ((SyntheticCategory.biShift (1,0)).obj P) ≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app P := by
        simpa only [Category.assoc] using congrArg (fun z => F.map (N.suspensionIso X).hom ≫ z ≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app P) hp
      _ = _ := by
        rw [reassoc_of% hn]
        simpa only [Category.assoc] using congrArg (fun z => z ≫
          (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A ≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app P) hs
  have inverse_rotated_lift_factorization
      (coh : BiShiftCoherence Syn) (N : NuFunctorData C Syn)
      [(SyntheticCategory.biShift (Syn:=Syn) (0,-1)).Additive]
      {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1:ℤ)⟧)
      (S : KIP126.Synthetic.SyntheticTriangleLift N (Triangle.mk f g h).rotate)
      (hs : N.functor.map ((shiftFunctor C (1:ℤ)).map f) ≫ (N.suspensionIso Y).hom =
        (N.suspensionIso X).hom ≫ (SyntheticCategory.biShift (1,1)).map (N.functor.map f)) :
      ∃ a : (SyntheticCategory.biShift (0,1)).obj (N.functor.obj X) ⟶ N.functor.obj Y,
        lambdaToPositivePow 1 (N.functor.obj X) ≫ a = N.functor.map f ∧
        Triangle.mk a (N.functor.map g)
          (N.functor.map h ≫ (nuPositiveLandingIso N X).hom) ∈ distTriang Syn := by
    letI : N.functor.Additive := N.additive
    let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
    have hd : Triangle.mk (N.functor.map g) (N.functor.map h)
        (S.connecting ≫ (N.boundaryLandingIso Y).hom) ∈ distTriang Syn := S.distinguished
    obtain ⟨a,ha,htri⟩ := triangle_inverse_rotation_transport _ _ _ hd (nuPositiveLandingIso N X)
    refine ⟨a,?_,htri⟩
    have hδ : S.connecting ≫ SyntheticCategory.lam.app (N.functor.obj (Y⟦(1:ℤ)⟧)) =
        -(N.functor.map ((shiftFunctor C (1:ℤ)).map f)) := by
      have hh := S.factorization
      change S.connecting ≫ SyntheticCategory.lam.app (N.functor.obj (Y⟦(1:ℤ)⟧)) =
        N.functor.map (-((shiftFunctor C (1:ℤ)).map f)) at hh
      simpa only [Functor.map_neg] using hh
    have hlam : F.map (S.connecting ≫
        SyntheticCategory.lam.app (N.functor.obj (Y⟦(1:ℤ)⟧))) =
      SyntheticCategory.lam.app (N.functor.obj (X⟦(1:ℤ)⟧)) ≫ S.connecting := by
      rw [Functor.map_comp,←lambda_negative_self coh]
      exact SyntheticCategory.lam.naturality S.connecting
    apply (shiftFunctor Syn (1:ℤ)).map_injective
    rw [Functor.map_comp]
    apply (cancel_epi (N.boundaryLandingIso X).hom).1
    calc
      _ = SyntheticCategory.lam.app (N.functor.obj (X⟦(1:ℤ)⟧)) ≫
          (nuPositiveLandingIso N X).hom ≫ (shiftFunctor Syn (1:ℤ)).map a := by
        simpa only [Category.assoc] using congrArg
          (fun z => z ≫ (shiftFunctor Syn (1:ℤ)).map a)
          (positive_lambda_landing_square coh N X)
      _ = -(SyntheticCategory.lam.app (N.functor.obj (X⟦(1:ℤ)⟧)) ≫
          S.connecting ≫ (N.boundaryLandingIso Y).hom) := by
        rw [ha]
        simp only [Preadditive.comp_neg,Iso.hom_inv_id_assoc]
      _ = -(F.map (S.connecting ≫
          SyntheticCategory.lam.app (N.functor.obj (Y⟦(1:ℤ)⟧))) ≫
          (N.boundaryLandingIso Y).hom) := by
        rw [hlam]
        simp only [Category.assoc]
      _ = F.map (N.functor.map ((shiftFunctor C (1:ℤ)).map f)) ≫
          (N.boundaryLandingIso Y).hom := by
        rw [hδ,Functor.map_neg,Preadditive.neg_comp,neg_neg]
      _ = _ := boundaryLanding_natural_of_suspension_square N f hs
  let oneSourceIso (n : ℕ) (hn : n=1) (A : Syn) :
      (SyntheticCategory.biShift (0,(n:ℤ))).obj A ≅ (SyntheticCategory.biShift (0,1)).obj A := by
    subst n
    exact Iso.refl _
  let negativeZeroIso (k : ℕ) (hk : k=0) (X : Syn) :
      (SyntheticCategory.biShift (0,-(k:ℤ))).obj X ≅ X := by
    subst k
    exact SyntheticCategory.biShift_zero.app X
  have negative_lift_zero_factorization {X Y : Syn} (k : ℕ) (hk : k=0)
      (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj X ⟶ Y)
      (g : X ⟶ Y) (h : lambdaToPositivePow k X ≫ f = g) :
      negativeLift k f ≫ (negativeZeroIso k hk Y).hom = g := by
    subst k
    rw [←h]
    dsimp only [negativeLift,negativeZeroIso,lambdaToPositivePow,lambdaPow]
    simp only [eqToHom_refl,Category.id_comp,
      Iso.app_hom,Category.assoc]
    erw [SyntheticCategory.biShift_zero.hom.naturality]
    rfl
  let rawSourceConnecting (nf ng nh : ℕ)
      (he : (nf:ℤ)+(ng:ℤ)+(nh:ℤ)=1) {X X1 Z : Syn}
      (sx : X1 ≅ (SyntheticCategory.biShift (1,1)).obj X)
      (m : (SyntheticCategory.biShift (0,(nh:ℤ))).obj Z ⟶ X1) :
      (SyntheticCategory.biShift (0,-(ng:ℤ))).obj Z ⟶
        ((SyntheticCategory.biShift (0,(nf:ℤ))).obj X)⟦(1:ℤ)⟧ :=
    (SyntheticCategory.biShift (0,-(ng:ℤ))).map (negativeLift nh m) ≫
    (SyntheticCategory.biShift (0,-(ng:ℤ))).map
      ((SyntheticCategory.biShift (0,-(nh:ℤ))).map sx.hom) ≫
    (SyntheticCategory.biShift (0,-(ng:ℤ))).map
      ((SyntheticCategory.biShift_comp (1,1) (0,-(nh:ℤ))).hom.app X) ≫
    (SyntheticCategory.biShift_comp ((1,1)+(0,-(nh:ℤ))) (0,-(ng:ℤ))).hom.app X ≫
    eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj X)
      (show ((1,1)+(0,-(nh:ℤ)))+(0,-(ng:ℤ))=(0,(nf:ℤ))+(1,0) from by
        ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> omega)) ≫
    (SyntheticCategory.biShift_comp (0,(nf:ℤ)) (1,0)).inv.app X ≫
    (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app _
  have raw_connecting_zero_normalization
      (coh : BiShiftCoherence Syn) (nf ng nh : ℕ)
      (hf : nf=1) (hg : ng=0) (hh : nh=0) (he : (nf:ℤ)+(ng:ℤ)+(nh:ℤ)=1)
      {X X1 Z : Syn} (sx : X1 ≅ (SyntheticCategory.biShift (1,1)).obj X)
      (m : (SyntheticCategory.biShift (0,(nh:ℤ))).obj Z ⟶ X1)
      (h : Z ⟶ X1) (hfac : lambdaToPositivePow nh Z ≫ m=h) :
      rawSourceConnecting nf ng nh he sx m ≫
        (shiftFunctor Syn (1:ℤ)).map (oneSourceIso nf hf X).hom =
        (negativeZeroIso ng hg Z).hom ≫ h ≫ sx.hom ≫
          (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app X ≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app _ := by
    subst nf
    subst ng
    subst nh
    have hzero := negative_lift_zero_factorization 0 rfl m h hfac
    have hu := coh.right_unit (1,1) X
    simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hu
    change (SyntheticCategory.biShift_comp (1,1) (0,0)).hom.app X =
      SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (1,1)).obj X) at hu
    dsimp only [rawSourceConnecting,oneSourceIso,negativeZeroIso]
    simp only [eqToHom_refl,Iso.refl_hom,
      CategoryTheory.Functor.map_id,Category.comp_id,Category.id_comp]
    change (SyntheticCategory.biShift (0,0)).map (negativeLift 0 m) ≫
      (SyntheticCategory.biShift (0,0)).map ((SyntheticCategory.biShift (0,0)).map sx.hom) ≫
      (SyntheticCategory.biShift (0,0)).map ((SyntheticCategory.biShift_comp (1,1) (0,0)).hom.app X) ≫
      (SyntheticCategory.biShift_comp (1,1) (0,0)).hom.app X ≫ _ = _
    rw [hu]
    have hs := SyntheticCategory.biShift_zero.hom.naturality sx.hom
    have hz := SyntheticCategory.biShift_zero.hom.naturality (h ≫ sx.hom)
    have hcomp : negativeLift 0 m ≫ (SyntheticCategory.biShift (0,0)).map sx.hom ≫
        SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (1,1)).obj X) = h ≫ sx.hom := by
      rw [hs,←Category.assoc]
      exact congrArg (fun z=>z≫sx.hom) hzero
    calc
      _ = (SyntheticCategory.biShift (0,0)).map
          (negativeLift 0 m ≫ (SyntheticCategory.biShift (0,0)).map sx.hom ≫
            SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (1,1)).obj X)) ≫
          SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (1,1)).obj X) ≫
          (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app X ≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app _ := by
        simp only [Functor.map_comp,Category.assoc]
        rfl
      _ = _ := by
        rw [hcomp]
        simpa only [Functor.id_map,Iso.app_hom,Category.assoc] using congrArg (fun z=>z≫
          (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app X ≫
          (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app _) hz
  have source_connecting_zero_normalization
      (D : AdamsComparison H M Syn) (S : NuCofiberLifts D)
      (hf : normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.f=1)
      (hg : normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.g=0)
      (hh : normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.h=0)
      (he : (normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.f:ℤ) +
        normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.g +
        normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.h=1) :
      sourceNormalizedConnecting D S he ≫
        (shiftFunctor Syn (1:ℤ)).map
          (oneSourceIso (normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.f) hf
            (D.nu.functor.obj (D.hopfAndDetector.nuCofiberTriangle.X.obj D.hopfAndDetector))).hom =
      (negativeZeroIso (normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.g) hg
          (D.nu.functor.obj (D.hopfAndDetector.nuCofiberTriangle.Z.obj D.hopfAndDetector))).hom ≫
        D.nu.functor.map D.hopfAndDetector.nuCofiberTriangle.h ≫
        (nuPositiveLandingIso D.nu (D.hopfAndDetector.nuCofiberTriangle.X.obj D.hopfAndDetector)).hom := by
    exact raw_connecting_zero_normalization D.shiftCoherence _ _ _ hf hg hh he
      (D.nu.suspensionIso _) S.topLift.map _ S.topLift.factorization
  have lambda_injective_below_diagonal (D : AdamsComparison H M Syn)
      (m wt : ℤ) (hw : wt ≤ m + 1) :
      LambdaInjectiveAt m wt (S_0_0 : Syn) := by
    letI := D.shiftAdditive (0,-1)
    letI := (SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (0,-1)).faithful
    let U := (SyntheticCategory.biShift (0,-1)).obj (Smn (Syn := Syn) m wt)
    let T := XModLambdaN.cofiberTriangle (S_0_0 : Syn) 1
    let e₀ : U ≅ Smn (Syn := Syn) m (wt-1) :=
      (SyntheticCategory.biShift_comp (m,wt) (0,-1)).app S_0_0 ≪≫
        eqToIso (by congr 1; simp [sub_eq_add_neg])
    let e₁ : U⟦(1 : ℤ)⟧ ≅ Smn (Syn := Syn) (m+1) (wt-1) :=
      (shiftFunctor Syn (1 : ℤ)).mapIso e₀ ≪≫
        (SyntheticCategory.biShift_compat (Syn := Syn) 1).symm.app _ ≪≫
        (SyntheticCategory.biShift_comp (m,wt-1) (1,0)).app S_0_0 ≪≫
        eqToIso (by congr 1; simp)
    have hQ : ∀ q : U⟦(1 : ℤ)⟧ ⟶ T.obj₃, q = 0 := by
      intro q
      haveI : Subsingleton (PageRepresentatives.Ambient H SphereSpectrum (wt-m-2,wt-1)) :=
        adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum
          2 (wt-m-2) (wt-1) (by omega)
      have hz : ∀ a : BiHom (m+1) (wt-1) (XModLambdaN (S_0_0 : Syn) 1), a = 0 := by
        intro a
        have hp : wt - 1 - (wt-m-2) = m+1 := by omega
        have hsub : Subsingleton (BiHom (wt-1-(wt-m-2)) (wt-1)
            (XModLambdaN (S_0_0 : Syn) 1)) :=
          (D.sphereFirstQuotient (wt-m-2) (wt-1)).injective.subsingleton
        rw [hp] at hsub
        exact @Subsingleton.elim _ hsub a 0
      apply (cancel_epi e₁.inv).mp
      simpa only [comp_zero] using hz (e₁.inv ≫ q)
    intro a b hab
    have hpre : SyntheticCategory.lam.app (Smn (Syn := Syn) m wt) ≫ (a-b) = 0 := by
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
  have nu_source_lambda_injective (D : AdamsComparison H M Syn) :
      LambdaInjectiveAt 3 4 (S_0_0 : Syn) :=
    lambda_injective_below_diagonal D 3 4 (by omega)
  have positive_lift_unique_nu_degree (D : AdamsComparison H M Syn)
      {A B : Syn}
      (eA : (SyntheticCategory.biShift (0,1)).obj A ≅ Smn (Syn := Syn) 3 4)
      (eB : B ≅ (S_0_0 : Syn))
      (f g : (SyntheticCategory.biShift (0,1)).obj A ⟶ B)
      (h : lambdaToPositivePow 1 A ≫ f = lambdaToPositivePow 1 A ≫ g) : f = g := by
    have hlam : SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,1)).obj A) ≫ f =
        SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,1)).obj A) ≫ g := by
      dsimp only [lambdaToPositivePow] at h
      rw [lambdaPow_one D.shiftCoherence] at h
      simp only [Category.assoc, cancel_epi] at h
      exact h
    have hlamTransport : SyntheticCategory.lam.app (Smn (Syn := Syn) 3 4) ≫
          (eA.inv ≫ f ≫ eB.hom) =
        SyntheticCategory.lam.app (Smn (Syn := Syn) 3 4) ≫
          (eA.inv ≫ g ≫ eB.hom) := by
      have hn := SyntheticCategory.lam.naturality eA.inv
      dsimp only [Functor.id_map] at hn
      calc
        _ = (SyntheticCategory.biShift (0,-1)).map eA.inv ≫
            (SyntheticCategory.lam.app _ ≫ f) ≫ eB.hom := by simpa only [Category.assoc] using congrArg (fun z => z ≫ f ≫ eB.hom) hn.symm
        _ = (SyntheticCategory.biShift (0,-1)).map eA.inv ≫
            (SyntheticCategory.lam.app _ ≫ g) ≫ eB.hom := by rw [hlam]
        _ = _ := by simpa only [Category.assoc] using congrArg (fun z => z ≫ g ≫ eB.hom) hn
    have heq : eA.inv ≫ f ≫ eB.hom = eA.inv ≫ g ≫ eB.hom := by
      apply nu_source_lambda_injective D
      dsimp only [lambdaAction]
      simpa only [Category.assoc] using congrArg
        (fun z => eqToHom (by rfl) ≫
          (SyntheticCategory.biShift_comp (3,4) (0,-1)).inv.app (S_0_0 : Syn) ≫ z) hlamTransport
    exact (cancel_mono eB.hom).mp ((cancel_epi eA.inv).mp heq)
  have normalized_nu_lift_unique (D : AdamsComparison H M Syn)
      (he : normalizedExponent H D.hopfAndDetector.nuMap = 1)
      (S T : NormalizedSyntheticMap H D.nu D.hopfAndDetector.nuMap) : S.map = T.map := by
    let A := D.nu.functor.obj (Sphere (C := C) 3)
    let B := D.nu.functor.obj SphereSpectrum
    have h : lambdaToPositivePow (normalizedExponent H D.hopfAndDetector.nuMap) A ≫ S.map =
        lambdaToPositivePow (normalizedExponent H D.hopfAndDetector.nuMap) A ≫ T.map :=
      S.factorization.trans T.factorization.symm
    have aux (n : ℕ) (hn : n = 1)
        (f g : (SyntheticCategory.biShift (0,(n : ℤ))).obj A ⟶ B)
        (hh : lambdaToPositivePow n A ≫ f = lambdaToPositivePow n A ≫ g) : f = g := by
      subst n
      exact positive_lift_unique_nu_degree D
        ((SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree D) ≪≫
          (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0)
        D.nu.unitIso f g hh
    exact aux _ he S.map T.map h
  have source_triangle_of_rotation_and_square
      (D : AdamsComparison H M Syn) (S : NuCofiberLifts D)
      (hf : normalizedExponent H D.hopfAndDetector.nuMap=1)
      (hg : normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.g=0)
      (hh : normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.h=0)
      (R : KIP126.Synthetic.SyntheticTriangleLift D.nu
        (Triangle.mk D.hopfAndDetector.nuMap D.hopfAndDetector.nuCofiberTriangle.g
          D.hopfAndDetector.nuCofiberTriangle.h).rotate)
      (hs : D.nu.functor.map ((shiftFunctor C (1:ℤ)).map D.hopfAndDetector.nuMap) ≫
          (D.nu.suspensionIso SphereSpectrum).hom =
        (D.nu.suspensionIso (Sphere (C:=C) 3)).hom ≫
          (SyntheticCategory.biShift (1,1)).map (D.nu.functor.map D.hopfAndDetector.nuMap))
      (he : (normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.f:ℤ) +
        normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.g +
        normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.h=1) :
      sourceNormalizedTriangle D S he ∈ distTriang Syn := by
    letI := D.shiftAdditive (0,-1)
    obtain ⟨a,ha,htri⟩ := inverse_rotated_lift_factorization D.shiftCoherence D.nu
      D.hopfAndDetector.nuMap D.hopfAndDetector.nuCofiberTriangle.g D.hopfAndDetector.nuCofiberTriangle.h R hs
    let e := oneSourceIso (normalizedExponent H D.hopfAndDetector.nuMap) hf
      (D.nu.functor.obj (Sphere (C:=C) 3))
    have haf : lambdaToPositivePow (normalizedExponent H D.hopfAndDetector.nuMap)
        (D.nu.functor.obj (Sphere (C:=C) 3)) ≫ (e.hom ≫ a) = D.nu.functor.map D.hopfAndDetector.nuMap := by
      have aux (n : ℕ) (hn : n=1) : lambdaToPositivePow n (D.nu.functor.obj (Sphere (C:=C) 3)) ≫
          (oneSourceIso n hn (D.nu.functor.obj (Sphere (C:=C) 3))).hom ≫ a =
          D.nu.functor.map D.hopfAndDetector.nuMap := by
        subst n
        simpa only [oneSourceIso,Iso.refl_hom,Category.id_comp] using ha
      exact aux _ hf
    let U : NormalizedSyntheticMap H D.nu D.hopfAndDetector.nuMap := ⟨e.hom ≫ a,haf⟩
    have hnu : S.nuLift.map=e.hom ≫ a := normalized_nu_lift_unique D hf S.nuLift U
    have hb := negative_lift_zero_factorization _ hg S.bottomLift.map _ S.bottomLift.factorization
    have ht := source_connecting_zero_normalization D S hf hg hh he
    apply isomorphic_distinguished _ htri
    refine Triangle.isoMk _ _ e (Iso.refl _)
      (negativeZeroIso (normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.g) hg
        (D.nu.functor.obj (D.hopfAndDetector.nuCofiberTriangle.Z.obj D.hopfAndDetector))) ?_ ?_ ?_
    · change S.nuLift.map ≫ 𝟙 _ = e.hom ≫ a
      simpa only [Category.comp_id] using hnu
    · change negativeLift (normalizedExponent H D.hopfAndDetector.nuCofiberTriangle.g) S.bottomLift.map ≫ _ =
        𝟙 _ ≫ D.nu.functor.map D.hopfAndDetector.nuCofiberTriangle.g
      simpa only [Category.id_comp] using hb
    · exact ht
  have nu_exponent_from_classical_source
      (D : AdamsComparison H M Syn) (S : ClassicalHopfThetaClasses H)
      (eta : BiHom 1 2 (S_0_0 : Syn)) (B : ClassicalHopfComparison D eta S)
      (hnu : TowerDetection.Detects S.convergence (1,4)
        (Sphere.Internal.hi H M 2) S.nu) :
      normalizedExponent H D.hopfAndDetector.nuMap = 1 := by
    classical
    obtain ⟨z,hz,a,ha,hgr⟩ := hnu
    have hm : S.nu ∈ TowerDetection.filtrationSubmodule H.unit SphereSpectrum 1 3 := by
      have hh : S.nu ∈ (ModuleCat.subobjectModule _)
          ((TowerDetection.filtration H.unit SphereSpectrum).F 1 3) := ⟨a,ha⟩
      simpa only [TowerDetection.filtration, OrderIso.apply_symm_apply] using hh
    obtain ⟨f,hf⟩ := hm
    have hF : AdamsFiltrationAtLeast H S.nu 1 := ⟨f,hf⟩
    rw [← B.nu] at hF
    simp only [normalizedExponent, if_pos hF]
  have cofiber_cell_exponents_zero
      (R : Mod2RingStructure H)
      [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
      (f : Sphere (C := C) 3 ⟶ SphereSpectrum)
      (hF : AdamsFiltrationAtLeast H f 1) :
      normalizedExponent H (HasFunctorialCofiber.cofibι f) = 0 ∧
      normalizedExponent H (HasFunctorialCofiber.cofibδ f) = 0 := by
    have tensor_zero_of_positive_filtration
        (R : Mod2RingStructure H) [(tensorLeft H.HF2).PreservesZeroMorphisms]
        {X Y : C} (f : X ⟶ Y) (hF : AdamsFiltrationAtLeast H f 1) :
        H.HF2 ◁ f = 0 := by
      obtain ⟨l, hl⟩ := hF
      rw [← hl, whiskerLeft_comp, mod2_adamsTowerMap_eq_zero H R Y 0 1 (by decide),
        comp_zero]

    have mod2_object_not_isZero : ¬ IsZero H.HF2 := by
      intro hz
      have h : H.pi0Equiv.symm 1 = 0 := hz.eq_of_tgt _ _
      have h10 : (1 : ZMod 2) = 0 := by
        simpa only [AddEquiv.apply_symm_apply, map_zero] using congrArg H.pi0Equiv h
      exact one_ne_zero h10

    have mod2_sphere_not_isZero
        [(tensorLeft H.HF2).CommShift ℤ] (n : ℤ) :
        ¬ IsZero (H.HF2 ⊗ Sphere (C := C) n) := by
      intro hz
      let e : H.HF2 ⊗ Sphere (C := C) n ≅ (shiftFunctor C n).obj H.HF2 :=
        ((tensorLeft H.HF2).commShiftIso n).app SphereSpectrum ≪≫
          (shiftFunctor C n).mapIso (ρ_ H.HF2)
      have hs : IsZero ((shiftFunctor C n).obj H.HF2) := hz.of_iso e.symm
      have hi : 𝟙 H.HF2 = 0 := by
        apply (shiftFunctor C n).map_injective
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
        exact hs.eq_of_src _ _
      exact mod2_object_not_isZero ((IsZero.iff_id_eq_zero _).2 hi)

    classical
    let T := (HoCofiberSequence.ofMorphism f).map (tensorLeft H.HF2)
    have hf : T.f = 0 := tensor_zero_of_positive_filtration R f hF
    have hbottom : ¬ AdamsFiltrationAtLeast H (HasFunctorialCofiber.cofibι f) 1 := by
      intro hb
      have hg : T.g = 0 := tensor_zero_of_positive_filtration R _ hb
      have hz : IsZero (H.HF2 ⊗ SphereSpectrum) :=
        (Triangle.isZero₂_iff _ T.distinguished).2 ⟨hf,hg⟩
      exact mod2_object_not_isZero (hz.of_iso (ρ_ H.HF2).symm)
    have htop : ¬ AdamsFiltrationAtLeast H (HasFunctorialCofiber.cofibδ f) 1 := by
      intro ht
      have hh : T.h = 0 := by
        change (H.HF2 ◁ HasFunctorialCofiber.cofibδ f) ≫ _ = 0
        rw [tensor_zero_of_positive_filtration R _ ht, zero_comp]
      have hz : IsZero (H.HF2 ⊗ Sphere (C := C) 3) :=
        (Triangle.isZero₁_iff _ T.distinguished).2 ⟨hf,hh⟩
      exact mod2_sphere_not_isZero 3 hz
    simp only [normalizedExponent, if_neg hbottom, if_neg htop, and_self]
  have positive_filtration_of_tensor_zero
      {X Y : C} (f : X ⟶ Y) (hf : H.HF2 ◁ f = 0) :
      AdamsFiltrationAtLeast H f 1 := by
    have hu : f ≫ adamsUnit H.unit Y = 0 := by
      rw [adamsUnit_naturality, hf, comp_zero]
    obtain ⟨a,ha⟩ := (adamsResolutionTriangle H.unit Y 0).coyoneda_exact₂
      (adamsResolutionTriangle_distinguished H.unit Y 0) f hu
    change f = a ≫ adamsTowerStep H.unit Y 0 at ha
    refine ⟨a,?_⟩
    change a ≫ adamsTowerMap H.unit Y 0 1 (by decide) = f
    simpa only [adamsTowerMap,adamsTowerComposite,adamsResolutionTriangle,
      eqToHom_refl,Category.id_comp,Category.comp_id,Nat.add_zero] using ha.symm
  have rotated_cofiber_homology_short_exact
      [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
      {X Y : C} (f : X ⟶ Y) (hf : H.HF2 ◁ f = 0) :
      KIP126.Synthetic.HomologyShortExact H
        (Triangle.mk f (HasFunctorialCofiber.cofibι f)
          (HasFunctorialCofiber.cofibδ f)).rotate := by
    let U := (HoCofiberSequence.ofMorphism f).map (tensorLeft H.HF2)
    let T := Triangle.mk U.f U.g U.h
    have hT : T ∈ distTriang C := U.distinguished
    have hzero : T.mor₁ = 0 := hf
    haveI : Mono T.mor₂ := T.mono₂ hT hzero
    intro n
    refine ⟨?_,?_,?_⟩
    · intro a b hab
      exact (cancel_mono T.mor₂).1 hab
    · intro a
      change a ≫ (H.HF2 ◁ HasFunctorialCofiber.cofibδ f) = 0 ↔
        ∃ b, b ≫ (H.HF2 ◁ HasFunctorialCofiber.cofibι f) = a
      constructor
      · intro ha
        have hz : a ≫ T.mor₃ = 0 := by
          change a ≫ ((H.HF2 ◁ HasFunctorialCofiber.cofibδ f) ≫ _) = 0
          rw [←Category.assoc,ha,zero_comp]
        obtain ⟨b,hb⟩ := T.coyoneda_exact₃ hT a hz
        exact ⟨b,hb.symm⟩
      · rintro ⟨b,rfl⟩
        have hh := comp_distTriang_mor_zero₂₃ T hT
        change (H.HF2 ◁ HasFunctorialCofiber.cofibι f) ≫
          ((H.HF2 ◁ HasFunctorialCofiber.cofibδ f) ≫ _) = 0 at hh
        have hg : (H.HF2 ◁ HasFunctorialCofiber.cofibι f) ≫
            (H.HF2 ◁ HasFunctorialCofiber.cofibδ f) = 0 := by
          apply (cancel_mono (((tensorLeft H.HF2).commShiftIso (1:ℤ)).hom.app X)).1
          change (H.HF2 ◁ HasFunctorialCofiber.cofibι f) ≫
            ((H.HF2 ◁ HasFunctorialCofiber.cofibδ f) ≫
              (((tensorLeft H.HF2).commShiftIso (1:ℤ)).hom.app X)) = 0 at hh
          simpa only [Category.assoc,zero_comp] using hh
        rw [Category.assoc,hg,comp_zero]
    · intro a
      let e := (((tensorLeft H.HF2).commShiftIso (1:ℤ)).app X)
      obtain ⟨b,hb⟩ := T.coyoneda_exact₁ hT (a ≫ e.hom) (by
        rw [hzero,Functor.map_zero,comp_zero])
      refine ⟨b,?_⟩
      apply (cancel_mono e.hom).1
      change (b ≫ (H.HF2 ◁ HasFunctorialCofiber.cofibδ f)) ≫ e.hom = a ≫ e.hom
      change a ≫ e.hom = b ≫ ((H.HF2 ◁ HasFunctorialCofiber.cofibδ f) ≫ e.hom) at hb
      simpa only [Category.assoc] using hb.symm
  have rotated_cofiber_positive_filtration
      [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).Additive]
      {X Y : C} (f : X ⟶ Y) (hf : H.HF2 ◁ f = 0) :
      AdamsFiltrationAtLeast H
        (Triangle.mk f (HasFunctorialCofiber.cofibι f)
          (HasFunctorialCofiber.cofibδ f)).rotate.mor₃ 1 := by
    apply positive_filtration_of_tensor_zero
    change (tensorLeft H.HF2).map (-((shiftFunctor C (1:ℤ)).map f)) = 0
    rw [Functor.map_neg]
    apply neg_eq_zero.mpr
    apply (cancel_mono (((tensorLeft H.HF2).commShiftIso (1:ℤ)).hom.app Y)).1
    have hn := ((tensorLeft H.HF2).commShiftIso (1:ℤ)).hom.naturality f
    change (tensorLeft H.HF2).map ((shiftFunctor C (1:ℤ)).map f) ≫
        ((tensorLeft H.HF2).commShiftIso (1:ℤ)).hom.app Y =
      ((tensorLeft H.HF2).commShiftIso (1:ℤ)).hom.app X ≫
        (shiftFunctor C (1:ℤ)).map (H.HF2 ◁ f) at hn
    calc
      _ = _ := hn
      _ = _ := by rw [hf,Functor.map_zero,comp_zero,zero_comp]
  have actual_rotated_cofiber_lift
      (R : Mod2RingStructure H)
      [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
      (N : NuFunctorData C Syn)
      (hlift : KIP126.Synthetic.SyntheticTriangleLiftComparison H N)
      {X Y : C} (f : X ⟶ Y) (hF : AdamsFiltrationAtLeast H f 1) :
      ∃ S : KIP126.Synthetic.SyntheticTriangleLift N
        (Triangle.mk f (HasFunctorialCofiber.cofibι f)
          (HasFunctorialCofiber.cofibδ f)).rotate,
        S.FullLiftComparison N := by
    have hz : H.HF2 ◁ f = 0 := by
      obtain ⟨a,ha⟩ := hF
      rw [←ha,whiskerLeft_comp,mod2_adamsTowerMap_eq_zero H R Y 0 1 (by decide),
        comp_zero]
    exact hlift _ (rot_of_distTriang _ (HasFunctorialCofiber.cofib_distinguished f))
      (rotated_cofiber_positive_filtration f hz)
      (rotated_cofiber_homology_short_exact f hz)

  have hf := nu_exponent_from_classical_source D CS eta CB hdet
  have hF : AdamsFiltrationAtLeast H D.hopfAndDetector.nuMap 1 := by
    by_contra h
    simp only [normalizedExponent,if_neg h] at hf
    contradiction
  obtain ⟨hg,hh⟩ := cofiber_cell_exponents_zero ring D.hopfAndDetector.nuMap hF
  obtain ⟨R,hR⟩ := actual_rotated_cofiber_lift ring D.nu hlift D.hopfAndDetector.nuMap hF
  refine ⟨hf,hg,hh,?_,?_⟩
  · have hn := nonzero_survival_label_ne_zero _ _ _ hperm
    have haf := detected_filtration_one_not_two CS.convergence 4 _ hn _ hdet
    have haf' : ¬ AdamsFiltrationAtLeast H D.hopfAndDetector.nuMap 2 := by
      rw [CB.nu]
      exact haf
    have hq : quotientClass 1 (sourceNormalizedNu D S hf) ≠ 0 := by
      intro hz
      exact haf' (normalized_nu_quotient_zero_forces_filtration_two D B van S hf hz)
    have hl : D.sphereFirstQuotient 1 4 (quotientClass 1 (sourceNormalizedNu D S hf)) ≠ 0 := by
      intro hz
      exact hq ((D.sphereFirstQuotient 1 4).injective (hz.trans (map_zero _).symm))
    exact nu_coordinates_nonzero_unique e coord values rows _ _ hl hn
  · intro he
    exact source_triangle_of_rotation_and_square D S hf hg hh R hs he

end

end NuSourceProof

end KIP126.Main.AdamsSynthetic
