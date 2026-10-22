module

public import KIP126.AdamsSynthetic.Standard.Background
import KIP126.AdamsSynthetic.Standard.Filtration
public import KIP126.Literature.Delivery
import all KIP126.Literature.Delivery
import all KIP126.Literature.Classical
import all KIP126.Literature.ClassicalRange
import all KIP126.Literature.EInfinity
import all KIP126.Literature.Triangles
import all KIP126.Literature.May

/-! Fixed literature objects and directly callable source theorems.

Each admitted declaration below is a separate, tracked source or comparison
obligation. No result package is required from consumers. Generic definitions
and established proofs are reused internally. Mathematical range, projectivity,
completeness and detection conditions are retained in their original statements.
Sources remain those recorded in metadata/literature-sources.json; the fixed upstream
review is bbac1fc05843bdf2d56057e6114a38839e939378 (Apache-2.0).
-/

@[expose] section
set_option autoImplicit false
noncomputable section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (Spectrum SyntheticSpectrum model)

/-- Source or comparison proof remains to be supplied. -/
public theorem sphere_connected :
  IsConnected (SphereSpectrum (C := Spectrum)) (-1) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem connected_homology_vanishing :
  ∀ (X : Spectrum) (n : ℤ), IsConnected X n →
    ∀ i : ℤ, i ≤ n → Subsingleton (ModTwoHomology model.coefficients i X) := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def universal_coefficient :
  ∀ (n : ℤ) (X : Spectrum),
    ModTwoCohomology model n X ≃+ (ModTwoHomology model.coefficients (-n) X →+ ZMod 2) := by
  sorry

/-- The specified realization is additive by its actual adjunction.
The same argument occurs in Kervaire126 8cb35dad5,
Main/Solution/StageInput/Toda/Low.lean:254–258. -/
public theorem realization_additive :
  model.recovery.realization.Additive := by
  letI := model.recovery.adjunction.isLeftAdjoint
  letI := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
    model.recovery.realization
  exact Functor.additive_of_preservesBinaryBiproducts _

section RealizationConstruction
set_option backward.isDefEq.respectTransparency false

-- Baseline Literature/Standard.lean SHA-256:
-- 24a6452de81a4419bd0969d283df7b9004da848bd4e41c976e2bae20ba245777.
-- Adapted only from the actual adjunction proof in upstream
-- Kervaire126 8cb35dad5, Def/Synthetic/Localization/Proofs.lean:67--114.
private theorem reflector_lambda_iso (X : SyntheticSpectrum) :
    IsIso (model.recovery.localization.reflector.map (SyntheticCategory.lam.app X)) := by
  let L := model.recovery.localization
  have hl (Z : SyntheticSpectrum) (hZ : IsLambdaInvertible Z) :
      Function.Bijective (fun f : X ⟶ Z => SyntheticCategory.lam.app X ≫ f) := by
    letI : IsIso (SyntheticCategory.lam.app Z) := hZ
    let hS := SyntheticCategory.biShift_fullyFaithful (Syn := SyntheticSpectrum) (0,-1)
    have hn (f : X ⟶ Z) :
        (SyntheticCategory.biShift (0,-1)).map f ≫ SyntheticCategory.lam.app Z =
          SyntheticCategory.lam.app X ≫ f := by
      exact SyntheticCategory.lam.naturality f
    constructor
    · intro f g h
      apply hS.map_injective
      apply (cancel_mono (SyntheticCategory.lam.app Z)).mp
      rw [hn, hn]
      exact h
    · intro g
      obtain ⟨f, hf⟩ := hS.map_surjective (g ≫ inv (SyntheticCategory.lam.app Z))
      refine ⟨f, ?_⟩
      change SyntheticCategory.lam.app X ≫ f = g
      rw [← hn, hf]
      simp
  apply isIso_of_coyoneda_map_bijective
  intro Z
  change Function.Bijective (fun g : L.reflector.obj X ⟶ Z =>
    L.reflector.map (SyntheticCategory.lam.app X) ≫ g)
  have h : (fun g : L.reflector.obj X ⟶ Z =>
      L.reflector.map (SyntheticCategory.lam.app X) ≫ g) =
      (fun g => (L.adjunction.homEquiv _ Z).symm
        (SyntheticCategory.lam.app X ≫ (L.adjunction.homEquiv X Z) g)) := by
    funext g
    apply (L.adjunction.homEquiv _ Z).injective
    rw [Equiv.apply_symm_apply, L.adjunction.homEquiv_naturality_left]
    rfl
  rw [h]
  exact (L.adjunction.homEquiv _ Z).symm.bijective.comp
    ((hl Z.obj Z.property).comp (L.adjunction.homEquiv X Z).bijective)

private theorem realization_lambda_iso (X : SyntheticSpectrum) :
    IsIso (model.recovery.realization.map (SyntheticCategory.lam.app X)) := by
  letI := reflector_lambda_iso X
  change IsIso (model.recovery.equivalence.functor.map
    (model.recovery.localization.reflector.map (SyntheticCategory.lam.app X)))
  infer_instance

set_option backward.privateInPublic true in
private def realizationZeroBase :
    Sphere (C := Spectrum) 0 ≅ model.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) 0 0) :=
  (shiftFunctorZero Spectrum ℤ).app SphereSpectrum ≪≫
    model.recovery.nuRealizationIso.symm.app SphereSpectrum ≪≫
    model.recovery.realization.mapIso model.nu.unitIso ≪≫
    (model.recovery.realization.mapIso
      (SyntheticCategory.biShift_zero.app (S_0_0 : SyntheticSpectrum))).symm

set_option backward.privateInPublic true in
private def realizationBase (m : ℤ) :
    Sphere (C := Spectrum) m ≅ model.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m 0) := by
  by_cases hm : m = 0
  · subst m
    exact realizationZeroBase
  · let R := model.recovery.realization
    letI := model.exactness.realizationShift
    let j : (SphereSpectrum : Spectrum) ≅ R.obj (S_0_0 : SyntheticSpectrum) :=
      model.recovery.nuRealizationIso.symm.app SphereSpectrum ≪≫ R.mapIso model.nu.unitIso
    exact (shiftFunctor Spectrum m).mapIso j ≪≫
      ((R.commShiftIso m).app (S_0_0 : SyntheticSpectrum)).symm ≪≫
      (R.mapIso ((SyntheticCategory.biShift_compat m).app (S_0_0 : SyntheticSpectrum))).symm

set_option backward.privateInPublic true in
private def realizationStep (m w : ℤ) :
    model.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m (w-1)) ≅
      model.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m w) := by
  let f := lambdaMultiply 1 (𝟙 (Smn (Syn := SyntheticSpectrum) m w))
  haveI : IsIso (model.recovery.realization.map f) := by
    dsimp only [f, lambdaMultiply]
    rw [lambdaPow_one model.quotients.coherence]
    letI := realization_lambda_iso (Smn (Syn := SyntheticSpectrum) m w)
    simp only [Functor.map_comp]
    infer_instance
  exact asIso (model.recovery.realization.map f)

set_option backward.privateInPublic true in
@[irreducible] private def realizationSphere (m w : ℤ) :
    Sphere (C := Spectrum) m ≅ model.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m w) :=
  w.inductionOn' 0 (realizationBase m)
    (fun w _ e => e ≪≫
      eqToIso (congrArg (fun q => model.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m q))
        (by omega : w = w+1-1)) ≪≫ realizationStep m (w+1))
    (fun w _ e => e ≪≫ (realizationStep m w).symm)

private theorem realizationSphere_zero : realizationSphere 0 0 = realizationZeroBase := by
  rw [realizationSphere, Int.inductionOn'_self]
  simp [realizationBase]

private theorem realizationUnit :
    (realizationSphere 0 0).hom ≫ model.recovery.realization.map
        (SyntheticCategory.biShift_zero.hom.app (S_0_0 : SyntheticSpectrum)) =
      (shiftFunctorZero Spectrum ℤ).hom.app SphereSpectrum ≫
        model.recovery.nuRealizationIso.inv.app SphereSpectrum ≫
        model.recovery.realization.map model.nu.unitIso.hom := by
  rw [realizationSphere_zero]
  simp only [realizationZeroBase, Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]


end RealizationConstruction

set_option backward.privateInPublic true in
/-- The fixed mathematical object on the project background. -/
public def realization_sphere :
  ∀ m w : ℤ, Sphere (C := Spectrum) m ≅ model.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m w) := realizationSphere

set_option backward.proofsInPublic true in
set_option backward.privateInPublic true in
/-- The sphere coordinates use the specified nu-realization unit comparison. -/
public theorem realization_unit :
  (realization_sphere 0 0).hom ≫ model.recovery.realization.map
      (SyntheticCategory.biShift_zero.hom.app (S_0_0 : SyntheticSpectrum)) =
    (shiftFunctorZero Spectrum ℤ).hom.app SphereSpectrum ≫
      model.recovery.nuRealizationIso.inv.app SphereSpectrum ≫
      model.recovery.realization.map model.nu.unitIso.hom := by
  change (realizationSphere 0 0).hom ≫ _ = _
  exact realizationUnit

section RealizationLambdaConstruction
set_option backward.isDefEq.respectTransparency false

private theorem realizationSphere_succ (m w : ℤ) (hw : 0 ≤ w) :
    realizationSphere m (w+1) = realizationSphere m w ≪≫
      eqToIso (congrArg (fun q => model.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m q))
        (by omega : w = w+1-1)) ≪≫ realizationStep m (w+1) := by
  unfold realizationSphere
  rw [Int.inductionOn'_add_one hw]

private theorem realizationSphere_pred (m w : ℤ) (hw : w ≤ 0) :
    realizationSphere m (w-1) = realizationSphere m w ≪≫ (realizationStep m w).symm := by
  unfold realizationSphere
  rw [Int.inductionOn'_sub_one hw]

private theorem realizationSphere_succ_to (m v w : ℤ) (hv : 0 ≤ v) (hvw : v+1=w) :
    realizationSphere m w = realizationSphere m v ≪≫
      eqToIso (congrArg (fun q => model.recovery.realization.obj (Smn (Syn := SyntheticSpectrum) m q))
        (by omega : v = w-1)) ≪≫ realizationStep m w := by
  subst w
  exact realizationSphere_succ m v hv

private theorem realizationSphere_adjacent (m w : ℤ) :
    (realizationSphere m (w-1)).hom ≫ model.recovery.realization.map
      (lambdaMultiply 1 (𝟙 (Smn (Syn := SyntheticSpectrum) m w))) =
        (realizationSphere m w).hom := by
  change (realizationSphere m (w-1)).hom ≫ (realizationStep m w).hom = _
  by_cases hw : w ≤ 0
  · rw [realizationSphere_pred m w hw]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · have hs := realizationSphere_succ_to m (w-1) w (by omega) (by omega)
    rw [hs]
    simp only [Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.id_comp]


-- Pure coherence proof reconstructed from existing source; no Main import.
private theorem shift_assoc_inv (coh : BiShiftCoherence SyntheticSpectrum)
    (a b c ab bc total : ℤ × ℤ) (hab : a+b=ab) (hbc : b+c=bc)
    (habc : ab+c=total) (habc' : a+bc=total) (A : SyntheticSpectrum) :
    (biShiftAddIso ab c total habc).inv.app A ≫
      (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app A) =
    (biShiftAddIso a bc total habc').inv.app A ≫
      (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj A) := by
  classical
  have he : ((SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app A) ≪≫
      (biShiftAddIso ab c total habc).app A) =
    ((biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj A) ≪≫
      (biShiftAddIso a bc total habc').app A) :=
    Iso.ext (coh.associativity a b c ab bc total hab hbc habc habc' A)
  have hi := congrArg Iso.inv he
  exact hi


private def lambdaAt (m : ℤ) (n : ℕ) (w v : ℤ)
    (h : (m,w)+(0,-(n:ℤ))=(m,v))
    {X : SyntheticSpectrum} (a : BiHom m w X) : BiHom m v X :=
  (biShiftAddIso (m,w) (0,-(n:ℤ)) (m,v) h).inv.app S_0_0 ≫
    lambdaPow n (Smn m w) ≫ a

private theorem lambdaAt_heq (m : ℤ) (n : ℕ) (w v : ℤ)
    (h : (m,w)+(0,-(n:ℤ))=(m,v))
    {X : SyntheticSpectrum} (a : BiHom m w X) :
    HEq (lambdaAt m n w v h a) (lambdaMultiply n a) := by
  delta lambdaAt KIP126.Synthetic.Context.lambdaMultiply KIP126.Synthetic.Context.biShiftAddIso
  simp only [Iso.trans_inv,NatTrans.comp_app,eqToIso.inv,eqToHom_app,
    Category.assoc,eqToHom_comp_heq_iff,heq_eqToHom_comp_iff]
  rfl

private theorem multiply_heq {m w w' : ℤ} {X : SyntheticSpectrum} (n : ℕ)
    (h : w=w') {a : BiHom m w X} {b : BiHom m w' X} (hab : HEq a b) :
    HEq (lambdaMultiply n a) (lambdaMultiply n b) := by
  subst w'
  cases hab
  rfl

private theorem lambda_multiply_compose {m w : ℤ} {X : SyntheticSpectrum}
    (k n : ℕ) (a : BiHom m w X) :
    HEq (lambdaMultiply n (lambdaMultiply k a)) (lambdaMultiply (k+n) a) := by
  let v := w-(k:ℤ)
  let u := v-(n:ℤ)
  let hk : (m,w)+(0,-(k:ℤ))=(m,v) := by ext <;> dsimp [v] <;> omega
  let hn : (m,v)+(0,-(n:ℤ))=(m,u) := by ext <;> dsimp [u] <;> omega
  let hkn : (m,w)+(0,-((k+n:ℕ):ℤ))=(m,u) := by ext <;> (dsimp [u,v]; omega)
  have ha := shift_assoc_inv model.quotients.coherence (m,w) (0,-(k:ℤ)) (0,-(n:ℤ))
    (m,v) (0,-((k+n:ℕ):ℤ)) (m,u)
    hk (by ext <;> dsimp <;> omega) hn hkn (S_0_0 : SyntheticSpectrum)
  have heq : lambdaAt m n v u hn (lambdaAt m k w v hk a) =
      lambdaAt m (k+n) w u hkn a := by
    unfold lambdaAt
    have hnat₁ := congrArg (fun t => t ≫ (lambdaPow k (Smn m w) ≫ a))
      (lambdaPow_naturality n
        ((biShiftAddIso (m,w) (0,-(k:ℤ)) (m,v) hk).inv.app (S_0_0 : SyntheticSpectrum)))
    simp (config := { congrConsts := false }) only [Category.assoc] at hnat₁
    erw [← hnat₁]
    have hnat₂ := congrArg (fun t => t ≫ a)
      (lambdaPow_naturality n (lambdaPow k (Smn m w)))
    simp (config := { congrConsts := false }) only [Category.assoc] at hnat₂
    erw [← hnat₂]
    erw [←Category.assoc,ha]
    erw [lambdaPow_add model.quotients.coherence k n (k+n) rfl (Smn m w)]
    delta KIP126.Synthetic.Context.lambdaShiftAddIso KIP126.Synthetic.Context.lambdaDegree KIP126.Synthetic.Context.biShiftAddIso
    simp (config := { congrConsts := false }) only [Category.assoc]
    rfl
  have houter := lambdaAt_heq m n v u hn (lambdaAt m k w v hk a)
  have hinner := multiply_heq n (by rfl : v=w-(k:ℤ)) (lambdaAt_heq m k w v hk a)
  exact (houter.trans hinner).symm.trans ((heq_of_eq heq).trans (lambdaAt_heq m (k+n) _ _ hkn a))

private theorem realizationTransport {m w w' : ℤ} {X : SyntheticSpectrum}
    (hw : w = w') {a : BiHom m w X} {b : BiHom m w' X} (hab : HEq a b) :
    (realizationSphere m w).hom ≫ model.recovery.realization.map a =
      (realizationSphere m w').hom ≫ model.recovery.realization.map b := by
  subst w'
  cases hab
  rfl

private theorem realizationAdjacentMap {m w : ℤ} {X : SyntheticSpectrum} (a : BiHom m w X) :
    (realizationSphere m (w-1)).hom ≫ model.recovery.realization.map (lambdaMultiply 1 a) =
      (realizationSphere m w).hom ≫ model.recovery.realization.map a := by
  have hc : lambdaMultiply 1 a =
      lambdaMultiply 1 (𝟙 (Smn (Syn := SyntheticSpectrum) m w)) ≫ a := by
    delta KIP126.Synthetic.Context.lambdaMultiply
    simp only [Category.comp_id, Category.assoc]
  rw [hc, Functor.map_comp, ← Category.assoc, realizationSphere_adjacent]

private theorem lambdaMultiplyZero {m w : ℤ} {X : SyntheticSpectrum} (a : BiHom m w X) :
    HEq (lambdaMultiply 0 a) a := by
  let hz : (m,w)+(0,-((0:ℕ):ℤ))=(m,w) := by ext <;> simp
  have he : lambdaAt m 0 w w hz a = a := by
    unfold lambdaAt
    change (biShiftAddIso (m,w) 0 (m,w) (add_zero (m,w))).inv.app S_0_0 ≫
      SyntheticCategory.biShift_zero.hom.app (Smn (Syn := SyntheticSpectrum) m w) ≫ a = a
    erw [← model.quotients.coherence.right_unit (m,w) (S_0_0 : SyntheticSpectrum)]
    exact Iso.inv_hom_id_app_assoc (biShiftAddIso (m,w) 0 (m,w) (add_zero (m,w))) (S_0_0 : SyntheticSpectrum) a
  exact (lambdaAt_heq m 0 w w hz a).symm.trans (heq_of_eq he)

private theorem realizationLambdaMap {m w : ℤ} {X : SyntheticSpectrum}
    (a : BiHom m w X) (k : ℕ) :
    (realizationSphere m (w-k)).hom ≫ model.recovery.realization.map (lambdaMultiply k a) =
      (realizationSphere m w).hom ≫ model.recovery.realization.map a := by
  induction k with
  | zero =>
    exact realizationTransport (by omega : w-(0:ℕ)=w) (lambdaMultiplyZero a)
  | succ k ih =>
    have h := realizationTransport (by omega : w-(k:ℤ)-1=w-((k+1:ℕ):ℤ))
      (lambda_multiply_compose k 1 a)
    calc
      _ = (realizationSphere m (w-(k:ℤ)-1)).hom ≫
          model.recovery.realization.map (lambdaMultiply 1 (lambdaMultiply k a)) := h.symm
      _ = (realizationSphere m (w-(k:ℤ))).hom ≫
          model.recovery.realization.map (lambdaMultiply k a) := realizationAdjacentMap _
      _ = _ := ih

private theorem realizationLambda :
    ∀ (m w : ℤ) (k : ℕ),
      (realizationSphere m (w-k)).hom ≫ model.recovery.realization.map
        (lambdaMultiply k (𝟙 (Smn (Syn := SyntheticSpectrum) m w))) =
          (realizationSphere m w).hom := by
  intro m w k
  have h := realizationLambdaMap (𝟙 (Smn (Syn := SyntheticSpectrum) m w)) k
  erw [model.recovery.realization.map_id, Category.comp_id] at h
  exact h



end RealizationLambdaConstruction

set_option backward.proofsInPublic true in
set_option backward.privateInPublic true in
/-- Every realized lambda power agrees with the same sphere coordinates. -/
public theorem realization_lambda :
  ∀ (m w : ℤ) (k : ℕ),
    (realization_sphere m (w-k)).hom ≫
      model.recovery.realization.map (lambdaMultiply k (𝟙 (Smn (Syn := SyntheticSpectrum) m w))) =
        (realization_sphere m w).hom := by
  change ∀ (m w : ℤ) (k : ℕ), (realizationSphere m (w-k)).hom ≫ _ = (realizationSphere m w).hom
  exact realizationLambda

public def realizationData : RealizationCoordinates model where
  additive := realization_additive
  sphere := realization_sphere
  unit := realization_unit
  lambda := realization_lambda

public def realizeSphere := RealizationCoordinates.sphereMap model realizationData

/-- The fixed mathematical object on the project background. -/
public def tmf :
  Spectrum := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def tmfIso :
  tmf ≅ model.auxiliary.detector := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def tmf_algebra :
  MonObj tmf := by
  sorry

/-- The actual unit of the specified tmf algebra, as in a484b981
Def/AdamsSynthetic/ComparisonStatements.lean:709–710. -/
public def tmfUnit :
  SphereSpectrum ⟶ tmf := @MonObj.one _ _ _ tmf tmf_algebra

/-- Source or comparison proof remains to be supplied. -/
public theorem tmfUnit_agrees :
  tmfUnit ≫ tmfIso.hom = model.auxiliary.detectorUnit := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def g :
  model.classical.sphere.Page 2 (4,24) := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def deltaH1g :
  model.classical.sphere.Page 2 (9,54) := by
  sorry

private def tmfBindingData : TmfBindings model where
  source := tmf
  sourceIso := tmfIso
  sourceUnit := tmfUnit
  unit_agrees := tmfUnit_agrees
  g := g
  deltaH1g := deltaH1g

/-- Source or comparison proof remains to be supplied. -/
public theorem eta_detection :
  ClassicalDetects (model.classicalConvergence .sphere) (1,2)
    (model.standardClasses.standardHi 1) model.auxiliary.etaMap := by
  sorry

/-- Adapted from the actual filtration witness argument in a484b981,
Main/AdamsSynthetic/NuSource/FromSuspension.lean:805–821. -/
public theorem eta_exponent :
  normalizedExponent model.classicalTower model.auxiliary.etaMap = 1 := by
  classical
  obtain ⟨_, _, b, hb, _⟩ := eta_detection
  have hmem : model.auxiliary.etaMap ∈ ModuleCat.subobjectModule _
      ((model.classicalTower.tower SphereSpectrum).filtration.F 1 1) := by
    change ∃ b, ((model.classicalTower.tower SphereSpectrum).filtration.F 1 1).arrow.hom b = _
    exact ⟨b, hb⟩
  simp only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] at hmem
  obtain ⟨lift, hlift⟩ := hmem
  have hF : MapFiltrationAtLeast model.classicalTower model.auxiliary.etaMap 1 :=
    ⟨lift, hlift⟩
  change (if MapFiltrationAtLeast model.classicalTower model.auxiliary.etaMap 1 then 1 else 0) = 1
  exact if_pos hF

/-- Derived from the fixed objects and previously established operations. -/
public def eta :
  BiHom 1 2 (S_0_0 : SyntheticSpectrum) := (etaSourceIso model eta_exponent).hom ≫
    (model.normalizedMap (.shift 1 .sphere) .sphere model.auxiliary.etaMap).map ≫ model.nu.unitIso.hom

/-- Derived from the fixed objects and previously established operations. -/
public theorem eta_normalized :
  eta = (etaSourceIso model eta_exponent).hom ≫
    (model.normalizedMap (.shift 1 .sphere) .sphere model.auxiliary.etaMap).map ≫ model.nu.unitIso.hom := rfl

/-- The fixed mathematical object on the project background. -/
public def theta5 :
  HomotopyGroup (C := Spectrum) 62 SphereSpectrum := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem theta5_detection :
  ClassicalTheta5Detected model theta5 := by
  sorry

/-- The ordinary 62-stem has exponent two on its 2-primary subgroup.
Odd-primary summands are not covered by this source obligation. -/
public theorem stem62_exponent_two :
  ∀ a : HomotopyGroup (C := Spectrum) 62 SphereSpectrum,
    (∃ n : ℕ, (2 ^ n : ℕ) • a = 0) → a + a = 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem theta5_filtration_gap :
  ∀ a b, ClassicalTheta5Detected model a → ClassicalTheta5Detected model b →
    a-b ∈ (model.classicalTower.tower SphereSpectrum).filtrationSubmodule 6 62 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem nu_detection :
  ClassicalDetects (model.classicalConvergence .sphere) (1,4)
    (model.standardClasses.standardHi 2) model.auxiliary.nuMap := by
  sorry

section OneLinePermanenceConstruction
set_option backward.isDefEq.respectTransparency false

private theorem nonzeroSurvivalOfPermanentNoIncoming
    (p : ℤ × ℤ) (x : model.classical.sphere.Page 2 p)
    (hperm : IsPermanentCycle model.classical.sphere p x) (hx : x ≠ 0)
    (hin : ∀ r : ℤ, 2 ≤ r →
      model.classical.sphere.d r (p-model.classical.sphere.diffDeg r) = 0) :
    NonzeroSurvival model.classical.sphere p x := by
  let E := model.classical.sphere
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2-E.r₀).toNat
  obtain ⟨z,hz⟩ := hperm
  refine ⟨z,hz,?_⟩
  intro hz0
  have hB : D.B ⊤ = D.B n := boundaries_top_eq_of_d_eq_zero E 2
    (le_of_eq (model.classical.firstPage SphereSpectrum)) p hin
  have hb := (subobject_cokernel_π_eq_zero_iff (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) z).mp hz0
  apply hx
  rw [←hz]
  change D.pageπ n (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) z) = 0
  apply (subobject_cokernel_π_eq_zero_iff (D.B n) (D.Z n) (D.B_le_Z n) _).mpr
  change (Subobject.ofLE (D.Z ⊤) (D.Z n) (D.Z_anti le_top) ≫ (D.Z n).arrow) z ∈ _
  rw [Subobject.ofLE_arrow]
  rwa [←hB]

private theorem oneLineNoIncoming (t : ℤ) (r : ℤ) (hr : 2 ≤ r) :
    model.classical.sphere.d r (((1:ℤ),t)-model.classical.sphere.diffDeg r) = 0 := by
  let q := ((1:ℤ),t)-model.classical.sphere.diffDeg r
  have hs : q.1 < 0 := by
    dsimp only [q]
    rw [model.classical.differentialDegree]
    change 1-r < 0
    omega
  letI : Subsingleton (model.classical.sphere.Page r q) :=
    KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere r q.1 q.2 hs
  ext a
  have ha : a = 0 := Subsingleton.elim _ _
  simp only [ha, map_zero]


private theorem standardHiActualNonzero (i : ℕ) :
    model.standardClasses.standardHi i ≠ 0 := by
  change KIP126.AdamsSynthetic.Standard.standardHi i ≠ 0
  unfold KIP126.AdamsSynthetic.Standard.standardHi
  exact @Subtype.property
    (ActualE2At KIP126.AdamsSynthetic.Standard.classical (hiDegree i))
    (fun x => x ≠ 0) _

/-- The detected standard h₁ is nonzero, and every incoming source has negative filtration. -/
public theorem eta_permanent :
  NonzeroSurvival model.classical.sphere (1,2) (model.standardClasses.standardHi 1) := by
  have hperm : IsPermanentCycle model.classical.sphere (1,2)
      (model.standardClasses.standardHi 1) := by
    obtain ⟨z,hz,_,_,_⟩ := eta_detection
    exact ⟨z,hz⟩
  exact nonzeroSurvivalOfPermanentNoIncoming (1,2) _ hperm (standardHiActualNonzero 1) (oneLineNoIncoming 2)

/-- The detected standard h₂ is nonzero, and every incoming source has negative filtration. -/
public theorem nu_permanent :
  NonzeroSurvival model.classical.sphere (1,4) (model.standardClasses.standardHi 2) := by
  have hperm : IsPermanentCycle model.classical.sphere (1,4)
      (model.standardClasses.standardHi 2) := by
    obtain ⟨z,hz,_,_,_⟩ := nu_detection
    exact ⟨z,hz⟩
  exact nonzeroSurvivalOfPermanentNoIncoming (1,4) _ hperm (standardHiActualNonzero 2) (oneLineNoIncoming 4)

end OneLinePermanenceConstruction

/-- Source or comparison proof remains to be supplied. -/
public theorem eta_label :
  sphereFirstQuotient model 1 2 (quotientClass 1 eta) = model.standardClasses.standardHi 1 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem eta_realization :
  realizeSphere 1 2 eta = model.auxiliary.etaMap := by
  sorry

/-- The selected integral θ₅ has order two. Its independent proof is pending;
the ordinary 62-stem theorem only covers 2-primary elements. -/
public theorem theta5_order_two :
  theta5 + theta5 = 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem sphereVanishing :
  SphereVanishingLine model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem two_detection :
  ClassicalDetects (model.classicalConvergence .sphere) (1,1)
    (model.standardClasses.standardHi 0) (classicalTwo (C := Spectrum)) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem adamsOneLine_d2 :
  ∀ (j : ℕ), 4 ≤ j →
    HasNonzeroDifferential model.classical.sphere 2
      (1,((2^j : ℕ) : ℤ)) (3,1+((2^(j-1+1) : ℕ) : ℤ))
      (model.standardClasses.standardHi j) (oneLineTarget model j) := by
  sorry

section H5SquarePermanenceConstruction
set_option backward.isDefEq.respectTransparency false

private theorem h5SquareActualNonzero : model.standardClasses.standardHiSquare 5 ≠ 0 := by
  obtain ⟨hdeg,xr,yr,_,hy,_,hne⟩ := adamsOneLine_d2 6 (by decide)
  intro hz
  apply hne
  rw [←hy.eq_on_page_two]
  change model.sphereAlgebra.product (1,1) (2,64)
    (model.standardClasses.standardHi 0) (model.standardClasses.standardHiSquare 5) = 0
  rw [hz, map_zero]

private theorem h5SquareNoIncoming (r : ℤ) (hr : 2 ≤ r) :
    model.classical.sphere.d r (((2:ℤ),64)-model.classical.sphere.diffDeg r) = 0 := by
  by_cases h2 : r = 2
  · subst r
    have hq : ((2:ℤ),64)-model.classical.sphere.diffDeg 2 = (0,63) := by
      rw [model.classical.differentialDegree]
      decide
    rw [hq]
    letI := KIP126.AdamsSynthetic.Standard.sphere_page_filtration_zero 2 63 (by decide)
    ext a
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [ha, map_zero]
  · let q := ((2:ℤ),64)-model.classical.sphere.diffDeg r
    have hs : q.1 < 0 := by
      dsimp only [q]
      rw [model.classical.differentialDegree]
      change 2-r < 0
      omega
    letI : Subsingleton (model.classical.sphere.Page r q) :=
      KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere r q.1 q.2 hs
    ext a
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [ha, map_zero]

private theorem h5SquarePermanentCandidate :
    NonzeroSurvival model.classical.sphere (2,64)
      (model.standardClasses.standardHiSquare 5) := by
  have hperm : IsPermanentCycle model.classical.sphere (2,64)
      (model.standardClasses.standardHiSquare 5) := by
    obtain ⟨z,hz,_,_,_⟩ := theta5_detection
    exact ⟨z,hz⟩
  exact nonzeroSurvivalOfPermanentNoIncoming _ _ hperm h5SquareActualNonzero h5SquareNoIncoming

/-- The detected square is nonzero at infinity: the independent Adams d2 target
forces E2 nonvanishing, and every possible incoming source is zero. -/
public theorem h5Square_permanent :
  NonzeroSurvival model.classical.sphere (2,64)
    (model.standardClasses.standardHiSquare 5) := by
  exact h5SquarePermanentCandidate

end H5SquarePermanenceConstruction

/-- The specified tmf unit is definitionally the same algebra unit. -/
public theorem tmf_algebra_unit :
  tmf_algebra.one = tmfUnit := rfl

section TmfConvergenceTransport
set_option backward.isDefEq.respectTransparency false

/-- Transport the registered detector convergence along the same fixed tmf
comparison, retaining the actual tower lifts and their cofiber images. -/
public def tmf_convergence :
  ClassicalTowerConvergence model.classicalTower tmf := by
  let e : tmf ≅ model.auxiliary.detector := tmfIso
  let c : ClassicalTowerConvergence model.classicalTower model.auxiliary.detector :=
    model.classicalConvergence .detector
  have tmf_filtration_map {X Y : Spectrum} (f : X ⟶ Y) (s m : ℤ) (x : HomotopyGroup m X)
      (hx : x ∈ (model.classicalTower.tower X).filtrationSubmodule s m) :
      x ≫ f ∈ (model.classicalTower.tower Y).filtrationSubmodule s m := by
    obtain ⟨a, rfl⟩ := hx
    refine ⟨a ≫ (model.classicalTower.map f).stage s.toNat, ?_⟩
    change (a ≫ (model.classicalTower.map f).stage s.toNat) ≫ (model.classicalTower.tower Y).projection s =
      (a ≫ (model.classicalTower.tower X).projection s) ≫ f
    rw [Category.assoc, (model.classicalTower.map f).projection s, ← Category.assoc]

  have tmf_filtration_iso_mem {X Y : Spectrum} (e : X ≅ Y) (s m : ℤ)
      (x : AbstractAdamsTower.homotopy X m) :
      x ≫ e.hom ∈
          ModuleCat.subobjectModule _ ((model.classicalTower.tower Y).filtration.F s m) ↔
        x ∈ ModuleCat.subobjectModule _ ((model.classicalTower.tower X).filtration.F s m) := by
    simp (config := { congrConsts := false }) only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply]
    change x ≫ e.hom ∈ (model.classicalTower.tower Y).filtrationSubmodule s m ↔
      x ∈ (model.classicalTower.tower X).filtrationSubmodule s m
    constructor
    · intro hx
      simpa (config := { congrConsts := false }) only [Category.assoc, e.hom_inv_id, Category.comp_id] using
        tmf_filtration_map e.inv s m (x ≫ e.hom) hx
    · exact tmf_filtration_map e.hom s m x

  have tmf_quotient_iso {R : Type} [Ring R] {M N : ModuleCat.{0} R}
      (B Z : Subobject M) (B' Z' : Subobject N) (h : B ≤ Z) (h' : B' ≤ Z')
      (e : M ≃ₗ[R] N)
      (hB : ∀ x, e x ∈ (ModuleCat.subobjectModule N) B' ↔ x ∈ (ModuleCat.subobjectModule M) B)
      (hZ : ∀ x, e x ∈ (ModuleCat.subobjectModule N) Z' ↔ x ∈ (ModuleCat.subobjectModule M) Z) :
      ∃ q : cokernel (Subobject.ofLE B Z h) ≅ cokernel (Subobject.ofLE B' Z' h'),
        ∀ a : (Subobject.underlying.obj Z : ModuleCat R),
          ∃ b : (Subobject.underlying.obj Z' : ModuleCat R),
            Z'.arrow b = e (Z.arrow a) ∧
            q.hom (cokernel.π (Subobject.ofLE B Z h) a) =
              cokernel.π (Subobject.ofLE B' Z' h') b := by
    have restrict (S : Subobject M) (T : Subobject N)
        (he : ∀ x, e x ∈ (ModuleCat.subobjectModule N) T ↔ x ∈ (ModuleCat.subobjectModule M) S) :
        ∃ w : Subobject.underlying.obj S ≅ Subobject.underlying.obj T,
          ∀ a, T.arrow (w.hom a) = e (S.arrow a) := by
      let a := LinearEquiv.ofInjective S.arrow.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
      let b := LinearEquiv.ofInjective T.arrow.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
      have hm : ((ModuleCat.subobjectModule M) S).map e.toLinearMap =
          (ModuleCat.subobjectModule N) T := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact (he x).2 hx
        · intro hy
          refine ⟨e.symm y, (he (e.symm y)).1 ?_, e.apply_symm_apply y⟩
          simpa (config := { congrConsts := false }) only [e.apply_symm_apply] using hy
      let c := e.ofSubmodules ((ModuleCat.subobjectModule M) S) ((ModuleCat.subobjectModule N) T) hm
      refine ⟨((a.trans c).trans b.symm).toModuleIso, ?_⟩
      intro x
      exact congrArg Subtype.val (b.apply_symm_apply (c (a x)))
    obtain ⟨b, hb⟩ := restrict B B' hB
    obtain ⟨z, hz⟩ := restrict Z Z' hZ
    have comm : Subobject.ofLE B Z h ≫ z.hom = b.hom ≫ Subobject.ofLE B' Z' h' := by
      apply (cancel_mono Z'.arrow).1
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change Z'.arrow (z.hom (Subobject.ofLE B Z h x)) =
        Z'.arrow (Subobject.ofLE B' Z' h' (b.hom x))
      rw [hz]
      have hs := congrArg (fun f => f.hom x) (Subobject.ofLE_arrow h)
      have ht := congrArg (fun f => f.hom (b.hom x)) (Subobject.ofLE_arrow h')
      change Z.arrow (Subobject.ofLE B Z h x) = B.arrow x at hs
      change Z'.arrow (Subobject.ofLE B' Z' h' (b.hom x)) = B'.arrow (b.hom x) at ht
      rw [hs, ht, hb]
    let q := cokernel.mapIso (Subobject.ofLE B Z h) (Subobject.ofLE B' Z' h') b z comm
    refine ⟨q, fun a => ⟨z.hom a, hz a, ?_⟩⟩
    have hq : cokernel.π (Subobject.ofLE B Z h) ≫ q.hom =
        z.hom ≫ cokernel.π (Subobject.ofLE B' Z' h') := by
      simp (config := { congrConsts := false }) only [q, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]
    exact congrArg (fun f => f.hom a) hq
  let homotopyIso (m : ℤ) :
      AbstractAdamsTower.homotopy tmf m ≅ AbstractAdamsTower.homotopy model.auxiliary.detector m := {
    hom := ModuleCat.ofHom (inducedMap e.hom m).toIntLinearMap
    inv := ModuleCat.ofHom (inducedMap e.inv m).toIntLinearMap
    hom_inv_id := by
      ext a
      change (a ≫ e.hom) ≫ e.inv = a
      simp (config := { congrConsts := false }) only [Category.assoc, e.hom_inv_id, Category.comp_id]
    inv_hom_id := by
      ext a
      change (a ≫ e.inv) ≫ e.hom = a
      simp (config := { congrConsts := false }) only [Category.assoc, e.inv_hom_id, Category.comp_id] }
  let infinityIso (p : ℤ × ℤ) :
      ((model.classical.obj tmf).ssData p).eInfty ≅ ((model.classical.obj model.auxiliary.detector).ssData p).eInfty := {
    hom := (model.classical.map e.hom).eInftyMap p
    inv := (model.classical.map e.inv).eInftyMap p
    hom_inv_id := by
      rw [← SpectralSequenceMorphism.eInftyMap_comp, ← model.classical.map_comp, e.hom_inv_id,
        model.classical.map_id, SpectralSequenceMorphism.eInftyMap_id]
    inv_hom_id := by
      rw [← SpectralSequenceMorphism.eInftyMap_comp, ← model.classical.map_comp, e.inv_hom_id,
        model.classical.map_id, SpectralSequenceMorphism.eInftyMap_id] }
  have gr (s m : ℤ) :
      ∃ q : (model.classicalTower.tower tmf).filtration.associatedGraded s m ≅
        (model.classicalTower.tower model.auxiliary.detector).filtration.associatedGraded s m,
        ∀ b : (Subobject.underlying.obj ((model.classicalTower.tower tmf).filtration.F s m) : ModuleCat ℤ),
          ∃ b' : (Subobject.underlying.obj ((model.classicalTower.tower model.auxiliary.detector).filtration.F s m) : ModuleCat ℤ),
            ((model.classicalTower.tower model.auxiliary.detector).filtration.F s m).arrow b' =
              ((model.classicalTower.tower tmf).filtration.F s m).arrow b ≫ e.hom ∧
            q.hom ((model.classicalTower.tower tmf).filtration.toAssociatedGraded s m b) =
              (model.classicalTower.tower model.auxiliary.detector).filtration.toAssociatedGraded s m b' := by
    exact tmf_quotient_iso
      ((model.classicalTower.tower tmf).filtration.F (s+1) m) ((model.classicalTower.tower tmf).filtration.F s m)
      ((model.classicalTower.tower model.auxiliary.detector).filtration.F (s+1) m) ((model.classicalTower.tower model.auxiliary.detector).filtration.F s m)
      ((model.classicalTower.tower tmf).filtration.mono s m) ((model.classicalTower.tower model.auxiliary.detector).filtration.mono s m)
      (homotopyIso m).toLinearEquiv
      (tmf_filtration_iso_mem e (s+1) m) (tmf_filtration_iso_mem e s m)
  let q := fun s m => (gr s m).choose
  refine ⟨fun p => infinityIso p ≪≫ c.identification p ≪≫ (q p.1 (p.2-p.1)).symm, ?_⟩
  intro p a z hz b hb
  let z' := (model.classical.map e.hom).toSSDataMorphism.cycleMap p ⊤ z
  let a' := a ≫ (model.classicalTower.map e.hom).stage p.1.toNat
  obtain ⟨b', hb', hq⟩ := (gr p.1 (p.2-p.1)).choose_spec b
  have hz' : (model.classicalTower.sequence model.auxiliary.detector).infiniteRepresentativeE1 p z' =
      (model.classicalTower.tower model.auxiliary.detector).layerMap p a' := by
    have hc := congrArg (fun f => f.hom z)
      ((model.classical.map e.hom).toSSDataMorphism.cycleMap_arrow p ⊤)
    change (((model.classical.obj model.auxiliary.detector).ssData p).Z ⊤).arrow z' =
      (model.classical.map e.hom).φ p ((((model.classical.obj tmf).ssData p).Z ⊤).arrow z) at hc
    unfold TowerSequencePresentation.infiniteRepresentativeE1
    rw [hc, model.classicalTower.natural]
    change (model.classicalTower.sequence tmf).infiniteRepresentativeE1 p z ≫ (model.classicalTower.map e.hom).layer p.1 =
      (model.classicalTower.tower model.auxiliary.detector).layerMap p a'
    rw [hz]
    change (a ≫ HasFunctorialCofiber.cofibι _) ≫ (model.classicalTower.map e.hom).layer p.1 =
      (a ≫ (model.classicalTower.map e.hom).stage p.1.toNat) ≫ HasFunctorialCofiber.cofibι _
    dsimp only [TowerMap.layer]
    rw [Category.assoc, ← HasFunctorialCofiber.cofibMap_ι, ← Category.assoc]
  have hb'' : ((model.classicalTower.tower model.auxiliary.detector).filtration.F p.1 (p.2-p.1)).arrow b' =
      a' ≫ (model.classicalTower.tower model.auxiliary.detector).projection p.1 := by
    rw [hb', hb]
    change (a ≫ (model.classicalTower.tower tmf).projection p.1) ≫ e.hom =
      (a ≫ (model.classicalTower.map e.hom).stage p.1.toNat) ≫ (model.classicalTower.tower model.auxiliary.detector).projection p.1
    simpa (config := { congrConsts := false }) only [Category.assoc] using
      congrArg (fun f => a ≫ f) ((model.classicalTower.map e.hom).projection p.1).symm
  have hc := c.canonical p a' z' hz' b' hb''
  have hpage := congrArg (fun f => f.hom z)
    ((model.classical.map e.hom).toSSDataMorphism.pageπ_pageMap p ⊤)
  change (model.classical.map e.hom).eInftyMap p (((model.classical.obj tmf).ssData p).pageπ ⊤ z) =
    ((model.classical.obj model.auxiliary.detector).ssData p).pageπ ⊤ z' at hpage
  change (q p.1 (p.2-p.1)).inv
      ((c.identification p).hom
        ((model.classical.map e.hom).eInftyMap p (((model.classical.obj tmf).ssData p).pageπ ⊤ z))) = _
  rw [hpage, hc, ← hq]
  exact congrArg (fun f => f.hom ((model.classicalTower.tower tmf).filtration.toAssociatedGraded p.1 (p.2-p.1) b))
    (q p.1 (p.2-p.1)).hom_inv_id
end TmfConvergenceTransport

/-- The fixed mathematical object on the project background. -/
public def kappaBar :
  HomotopyGroup (C := Spectrum) 20 SphereSpectrum := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def wClass :
  HomotopyGroup (C := Spectrum) 45 SphereSpectrum := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def tmfV2Sixteen :
  (model.classical.obj tmf).Page 2 (16,112) := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def tmfBetaGFour :
  (model.classical.obj tmf).Page 2 (19,114) := by
  sorry

private def tmfSourceData : TmfSourceData model tmfBindingData where
  algebra := tmf_algebra
  algebra_unit := tmf_algebra_unit
  convergence := tmf_convergence
  kappaBar := kappaBar
  wClass := wClass
  v2Sixteen := tmfV2Sixteen
  betaGFour := tmfBetaGFour

public def high125 := classicalSphereProduct
  (classicalSphereProduct (classicalSphereProduct kappaBar kappaBar)
    (classicalSphereProduct kappaBar kappaBar)) wClass

/-- Source or comparison proof remains to be supplied. -/
public theorem tmf_connective :
  ∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n tmf) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem tmf_finiteModTwoType :
  ∀ n : ℤ, Finite (ModTwoHomology model.coefficients n tmf) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem g_nonzero :
  g ≠ 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem g_unique :
  ∀ x : model.classical.sphere.Page 2 (4,24), x ≠ 0 → x = g := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem deltaH1g_nonzero :
  deltaH1g ≠ 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem deltaH1g_unique :
  ∀ x : model.classical.sphere.Page 2 (9,54), x ≠ 0 → x = deltaH1g := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem tmf_vanishing62 :
  ∀ x : HomotopyGroup (C := Spectrum) 62 tmf, x = 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem tmf_low_filtration63 :
  ∀ s : ℤ, s ≤ 0 →
    Subsingleton ((model.classical.obj tmf).Page 2 (s,63+s)) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem kappaBar_detection :
  ClassicalDetects (model.classicalConvergence .sphere) (4,24) g kappaBar := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem w_detection :
  ClassicalDetects (model.classicalConvergence .sphere) (9,54) deltaH1g wClass := by
  sorry

/-- The specified image retains the non-odd-torsion content of the BMQ
2-local Hurewicz result. Its identification with the fixed source classes and
unit remains the same Literature proof responsibility. -/
public theorem tmf_high125_nonzero :
  ¬ IsOddTorsionMap (high125 ≫ tmfUnit) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem tmf_br21 :
  HasDifferential (model.classical.obj tmf) 3 (16,112) (19,114)
    tmfV2Sixteen tmfBetaGFour := by
  sorry

/-- Derived from the fixed objects and previously established operations. -/
public theorem detector_d3 :
  HasDifferential (model.classical.obj model.auxiliary.detector) 3 (16,112) (19,114)
    ((model.classical.map tmfIso.hom).pageMap 2 (16,112) tmfV2Sixteen)
    ((model.classical.map tmfIso.hom).pageMap 2 (19,114) tmfBetaGFour) := (model.classical.map tmfIso.hom).hasDifferential tmf_br21

/-- Constructed from the registered shift of the same tower, including every integer page.
Explicit equality transports keep proof auxiliaries private without changing exposure. -/
public def nuPage_weightShift :
  ∀ (X : ClassicalObject) (r s t w : ℤ),
    (model.family.nu model.nu (X.obj model.auxiliary)).Page r (s,t,w) ≅
      (model.family.obj ((SyntheticCategory.biShift (0,-1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))).Page r (s,t,w-1) := by
  intro X r s t w
  let two : ℤ := 2
  let F := model.family
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  let shiftedV := (SyntheticCategory.biShift (0,-1)).obj V
  let shift (page : ℤ) (hp : two ≤ page) :
      (F.obj V).Page page (s,t,w) ≅ (F.obj shiftedV).Page page (s,t,w-1) :=
    let q := t-s
    let q0 := q+0
    let a := q+s
    let b := q0+s
    let addS := fun z : ℤ => z+s
    let hq0 : q0=q := Int.add_zero q
    let hba : b=a := @congrArg ℤ ℤ q0 q addS hq0
    let hat : a=t := Int.sub_add_cancel t s
    let isoAt := fun aa bb : ℤ =>
      (F.obj V).Page page (s,aa,w) ≅ (F.obj shiftedV).Page page (s,bb,w-1)
    let raw : isoAt a b :=
      KIP126.AdamsSynthetic.Standard.shift_page (0,-1) (.nu X) page hp (q,w) s
    let same : isoAt a a := Eq.rec (motive := fun z _ => isoAt a z) raw hba
    Eq.rec (motive := fun z _ => isoAt z z) same hat
  by_cases hr : two ≤ r
  · exact shift r hr
  · let hlt : r < two := @Int.lt_of_not_ge two r hr
    let hle : r ≤ two := @Int.le_of_lt r two hlt
    let htwo : two ≤ two := Int.le_refl two
    let pageIso (Y : SyntheticSpectrum) (p : Tridegree) :
        (F.obj Y).Page r p ≅ (F.obj Y).Page two p :=
      let E := F.obj Y
      let c := E.sequence.r₀
      let hfirst : c=two := SyntheticAdamsFamily.firstPage F Y
      let nR := (r-c).toNat
      let nBase := (r-two).toNat
      let nTwo := (two-c).toNat
      let nZero : ℕ := 0
      let P : Prop := nBase=nZero
      let Q : Prop := r ≤ two
      let hiff : P ↔ Q := Int.toNat_sub_eq_zero_iff r two
      let hBase : P := @Iff.mpr P Q hiff hle
      let indexR := fun z : ℤ => (r-z).toNat
      let indexTwo := fun z : ℤ => (two-z).toNat
      let hR : nR=nBase := @congrArg ℤ ℕ c two indexR hfirst
      let hRZero : nR=nZero := @Eq.trans ℕ nR nBase nZero hR hBase
      let hTwo : nTwo=nZero := @congrArg ℤ ℕ c two indexTwo hfirst
      let A := ModuleCat.{0} ℤ
      let D := E.sequence.ssData p
      let pageN : ℕ → A := fun n => D.page (n : WithTop ℕ)
      let objR := pageN nR
      let objTwo := pageN nTwo
      let objZero := pageN nZero
      let hObjR : objR=objZero := @congrArg ℕ A nR nZero pageN hRZero
      let hObjTwo : objTwo=objZero := @congrArg ℕ A nTwo nZero pageN hTwo
      let hObjTwoSymm : objZero=objTwo := @Eq.symm A objTwo objZero hObjTwo
      let hObj : objR=objTwo := @Eq.trans A objR objZero objTwo hObjR hObjTwoSymm
      eqToIso hObj
    exact pageIso V (s,t,w) ≪≫ shift two htwo ≪≫ (pageIso shiftedV (s,t,w-1)).symm


/-- Source or comparison proof remains to be supplied. -/
public theorem nuPage_e2 :
  ∀ (X : ClassicalObject) (s t : ℤ) (k : ℕ)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)),
    HEq ((nuPage_weightShift X 2 s t (t-k)).hom (targetNuLabel model X s t k x))
      (model.comparison.nuE2 X (-1) s t k x) := by
  sorry

public def nuPageData : NuPageCoordinates model where
  weightShift := nuPage_weightShift
  e2 := nuPage_e2

public def pageLambda := NuPageCoordinates.lambda model nuPageData

section FirstPageComparisonConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private structure FromFirstMorphism
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    (E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι)
    extends SSDataMorphism ι E.ssData F.ssData where
  r₀_eq : E.r₀=F.r₀
  diffDeg_eq : E.diffDeg=F.diffDeg
  comm_d : ∀ (r : ℤ), E.r₀ ≤ r → ∀ p : ι,
    let g := toSSDataMorphism
    g.pageMapAt (E := E.toPreSS) (E' := F.toPreSS) r₀_eq r p ≫ F.d r p =
      E.d r p ≫ g.pageMapAt (E := E.toPreSS) (E' := F.toPreSS) r₀_eq r (p+E.diffDeg r) ≫
        eqToHom (by rw [diffDeg_eq])

private def FromFirstMorphism.pageMap
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι}
    (f : FromFirstMorphism E F) (r : ℤ) (p : ι) :=
  f.toSSDataMorphism.pageMapAt (E := E.toPreSS) (E' := F.toPreSS) f.r₀_eq r p

private theorem FromFirstMorphism.pageMap_comm_d
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι}
    (f : FromFirstMorphism E F) (r : ℤ) (hr : E.r₀ ≤ r) (p : ι) :
    f.pageMap r p ≫ F.d r p = E.d r p ≫ f.pageMap r (p+E.diffDeg r) ≫
      eqToHom (by rw [f.diffDeg_eq]) := f.comm_d r hr p

private def firstPageComparisonOfMorphism
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι}
    (f : SpectralSequenceMorphism E F) : FromFirstMorphism E F where
  toSSDataMorphism := f.toSSDataMorphism
  r₀_eq := f.r₀_eq
  diffDeg_eq := f.diffDeg_eq
  comm_d r _ p := f.pageMap_comm_d r p

private theorem finiteQuotientNextProjectionZero
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    (E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι)
    (r : ℤ) (hr : E.r₀ ≤ r) (p : ι)
    (z : (Subobject.underlying.obj ((E.ssData (p+E.diffDeg r)).Z
      ↑((r-E.r₀).toNat+1)) : ModuleCat.{0} ℤ)) :
    (E.ssData (p+E.diffDeg r)).pageπ ↑((r-E.r₀).toNat+1) z = 0 ↔
      (Subobject.ofLE _ _ ((E.ssData (p+E.diffDeg r)).Z_anti
        (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat)) ≫
          (E.ssData (p+E.diffDeg r)).pageπ ↑(r-E.r₀).toNat) z ∈
        LinearMap.range (E.d r p).hom := by
  let D := E.ssData (p+E.diffDeg r)
  let n := (r-E.r₀).toNat
  have hnm : (↑n : WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  let i := Subobject.ofLE (D.Z ↑(n+1)) (D.Z ↑n) (D.Z_anti hnm)
  let j := Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑n)
    ((D.B_le_Z _).trans (D.Z_anti hnm))
  rw [← subobjectModule_image, E.B_succ r p hr, subobjectModule_image]
  change D.pageπ ↑(n+1) z = 0 ↔ (i ≫ D.pageπ ↑n) z ∈ LinearMap.range (j ≫ D.pageπ ↑n).hom
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := (cokernel_π_eq_zero_iff_mem_range
      (Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _)) z).mp hz
    refine ⟨v, ?_⟩
    rw [← hv]
    change (j ≫ D.pageπ ↑n) v =
      ((Subobject.ofLE (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _)) ≫ i ≫ D.pageπ ↑n) v
    congr 2
    dsimp only [i,j]
    rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
  · rintro ⟨v, hv⟩
    apply (subobject_cokernel_π_eq_zero_iff (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _) z).mpr
    have hz : D.pageπ ↑n (i z-j v) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hv.symm
    have hb := (subobject_cokernel_π_eq_zero_iff (D.B ↑n) (D.Z ↑n) (D.B_le_Z _) _).mp hz
    have hb' := (ModuleCat.subobjectModule D.V).monotone (D.B_mono hnm) hb
    have hv' : (D.Z ↑n).arrow (j v) ∈ (ModuleCat.subobjectModule D.V) (D.B ↑(n+1)) := by
      change (j ≫ (D.Z ↑n).arrow) v ∈ _
      dsimp only [j]
      rw [Subobject.ofLE_arrow]
      exact ⟨v, rfl⟩
    have hh := ((ModuleCat.subobjectModule D.V) (D.B ↑(n+1))).add_mem hb' hv'
    rw [map_sub, sub_add_cancel] at hh
    change (i ≫ (D.Z ↑n).arrow) z ∈ _ at hh
    dsimp only [i] at hh
    rwa [Subobject.ofLE_arrow] at hh

private theorem finiteQuotientNextEqOfEarlierEq (D : SSData (ModuleCat.{0} ℤ))
    (n : ℕ) (a b : (Subobject.underlying.obj (D.Z ↑(n+1)) : ModuleCat.{0} ℤ))
    (h : (Subobject.ofLE _ _ (D.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
      D.pageπ ↑n) a = (Subobject.ofLE _ _ (D.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
      D.pageπ ↑n) b) : D.pageπ ↑(n+1) a = D.pageπ ↑(n+1) b := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (subobject_cokernel_π_eq_zero_iff (D.B ↑(n+1)) (D.Z ↑(n+1)) (D.B_le_Z _) _).mpr
  have hz : (Subobject.ofLE _ _ (D.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
      D.pageπ ↑n) (a-b) = 0 := by rw [map_sub, h, sub_self]
  have hb := (subobject_cokernel_π_eq_zero_iff (D.B ↑n) (D.Z ↑n) (D.B_le_Z _) _).mp hz
  have he := ConcreteCategory.congr_hom (Subobject.ofLE_arrow
    (D.Z_anti (show (↑n : WithTop ℕ) ≤ ↑(n+1) by exact_mod_cast Nat.le_succ n))) (a-b)
  change (D.Z ↑n).arrow _ = (D.Z ↑(n+1)).arrow (a-b) at he
  rw [he] at hb
  exact (ModuleCat.subobjectModule D.V).monotone
    (D.B_mono (by exact_mod_cast Nat.le_succ n)) hb

private theorem finiteQuotientSuccessorComparison
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι}
    (f : FromFirstMorphism E F) (r : ℤ) (hr : E.r₀ ≤ r) (q : ι) :
    (Function.Surjective (f.pageMap r q) →
      Function.Injective (f.pageMap r (q+E.diffDeg r)) →
      Function.Injective (f.pageMap (r+1) (q+E.diffDeg r))) ∧
    (Function.Surjective (f.pageMap r (q+E.diffDeg r)) →
      Function.Injective (f.pageMap r (q+E.diffDeg r+E.diffDeg r)) →
      Function.Surjective (f.pageMap (r+1) (q+E.diffDeg r))) := by
  have hfirst := f.r₀_eq
  have hdegree := f.diffDeg_eq
  rcases E with ⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩
  rcases F with ⟨⟨r₀',D',δ',d'⟩,dd',Zs',Bs'⟩
  dsimp at hfirst hdegree
  subst r₀'
  subst δ'
  change r₀ ≤ r at hr
  let E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι := ⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩
  let F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι := ⟨⟨r₀,D',δ,d'⟩,dd',Zs',Bs'⟩
  let p := q+δ r
  let g := f.toSSDataMorphism
  let n := (r-r₀).toNat
  have hs : (r+1-r₀).toNat = n+1 := by dsimp [n]; omega
  let down (T : SSData (ModuleCat.{0} ℤ)) :=
    Subobject.ofLE (T.Z ↑(n+1)) (T.Z ↑n)
      (T.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫ T.pageπ ↑n
  have naturalDown (z : (Subobject.underlying.obj ((D p).Z ↑(n+1)) : ModuleCat.{0} ℤ)) :
      (g.pageMap p ↑n) (down (D p) z) =
        down (D' p) (g.cycleMap p ↑(n+1) z) := by
    have h := g.cycleMap_ofLE_assoc p
      (show (↑n : WithTop ℕ) ≤ ↑(n+1) by exact_mod_cast Nat.le_succ n) ((D' p).pageπ ↑n)
    rw [← g.pageπ_pageMap] at h
    simpa only [down, ModuleCat.comp_apply] using (ConcreteCategory.congr_hom h z)
  have comm (q : ι) (x : (D q).page ↑n) :
      (g.pageMap (q+δ r) ↑n) (d r q x) = d' r q (g.pageMap q ↑n x) := by
    have h := f.pageMap_comm_d r hr q
    simpa only [FromFirstMorphism.pageMap, SSDataMorphism.pageMapAt, eqToHom_refl,
      Category.comp_id, ModuleCat.comp_apply, E, F, g, n] using
        (ConcreteCategory.congr_hom h x).symm
  constructor
  · intro hin hmid
    change Function.Surjective (g.pageMap q ↑n) at hin
    change Function.Injective (g.pageMap p ↑n) at hmid
    change Function.Injective (g.pageMap p ↑(r+1-r₀).toNat)
    rw [hs]
    intro a b hab
    apply sub_eq_zero.mp
    have ha : g.pageMap p ↑(n+1) (a-b) = 0 := by rw [map_sub, hab, sub_self]
    haveI : Epi ((D p).pageπ ↑(n+1)) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective ((D p).pageπ ↑(n+1))).mp inferInstance (a-b)
    rw [← hz] at ha ⊢
    have hzmap : (D' p).pageπ ↑(n+1) (g.cycleMap p ↑(n+1) z) = 0 := by
      simpa only [ModuleCat.comp_apply] using
        (ConcreteCategory.congr_hom (g.pageπ_pageMap p ↑(n+1)) z).symm.trans ha
    have hzin := (finiteQuotientNextProjectionZero F r hr q (g.cycleMap p ↑(n+1) z)).mp hzmap
    change down (D' p) (g.cycleMap p ↑(n+1) z) ∈ LinearMap.range
      (d' r q).hom at hzin
    obtain ⟨b,hb⟩ := hzin
    obtain ⟨c,rfl⟩ := hin b
    have hc := comm q c
    have he : down (D p) z = d r q c := by
      apply hmid
      rw [naturalDown, hc, hb]
    apply (finiteQuotientNextProjectionZero E r hr q z).mpr
    change down (D p) z ∈ LinearMap.range (d r q).hom
    exact ⟨c,he.symm⟩
  · intro hmid hout
    change Function.Surjective (g.pageMap p ↑n) at hmid
    change Function.Injective (g.pageMap (p+δ r) ↑n) at hout
    change Function.Surjective (g.pageMap p ↑(r+1-r₀).toNat)
    rw [hs]
    intro a
    haveI : Epi ((D' p).pageπ ↑(n+1)) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z',rfl⟩ := (ModuleCat.epi_iff_surjective ((D' p).pageπ ↑(n+1))).mp inferInstance a
    obtain ⟨x,hx⟩ := hmid (down (D' p) z')
    have hx0 : d r p x = 0 := by
      apply hout
      rw [map_zero, comm, hx]
      change down (D' p) z' ∈ LinearMap.ker (d' r p).hom
      rw [← subobjectModule_kernel, Zs' r p hr, subobjectModule_image]
      exact ⟨z',rfl⟩
    have hxmem : x ∈ ModuleCat.subobjectModule _ (kernelSubobject (d r p)) := by
      rw [subobjectModule_kernel]
      exact hx0
    rw [Zs r p hr, subobjectModule_image] at hxmem
    obtain ⟨z,hz⟩ := hxmem
    refine ⟨(D p).pageπ ↑(n+1) z, ?_⟩
    have hp := ConcreteCategory.congr_hom (g.pageπ_pageMap p ↑(n+1)) z
    simp only [ModuleCat.comp_apply] at hp
    refine hp.trans (finiteQuotientNextEqOfEarlierEq (D' p) n _ z' ?_)
    change down (D' p) (g.cycleMap p ↑(n+1) z) = down (D' p) z'
    rw [← naturalDown, hz, hx]

end FirstPageComparisonConstruction

universe absorbComparisonU absorbComparisonV absorbComparisonI

set_option backward.isDefEq.respectTransparency false in
/-- Finite representative preservation extends to the intersection of cycles
and the union of boundaries. The ambient maps remain exactly the given maps. -/
private def dataMorphismOfFinite
    {C : Type absorbComparisonU} [Category.{absorbComparisonV} C] [Abelian C]
    {ι : Type absorbComparisonI} [AddCommGroup ι] [DecidableEq ι]
    (D D' : ι → SSData C) (φ : ∀ i, (D i).V ⟶ (D' i).V)
    (hZ : ∀ i (n : ℕ), ∃ (lift : Subobject.underlying.obj ((D i).Z n) ⟶
        Subobject.underlying.obj ((D' i).Z n)),
      lift ≫ ((D' i).Z n).arrow = ((D i).Z n).arrow ≫ φ i)
    (hB : ∀ i (n : ℕ), ∃ (lift : Subobject.underlying.obj ((D i).B n) ⟶
        Subobject.underlying.obj ((D' i).B n)),
      lift ≫ ((D' i).B n).arrow = ((D i).B n).arrow ≫ φ i) :
    SSDataMorphism ι D D' where
  φ := φ
  preserves_Z i r := by
    cases r using WithTop.recTopCoe with
    | coe n => exact hZ i n
    | top =>
      let f := ((D i).Z ⊤).arrow ≫ φ i
      have hI : imageSubobject f ≤ (D' i).Z ⊤ := by
        apply (D' i).Z_top_greatest
        intro n
        apply imageSubobject_le f
          (Subobject.ofLE ((D i).Z ⊤) ((D i).Z n) ((D i).Z_anti le_top) ≫
            (hZ i n).choose)
        rw [Category.assoc, (hZ i n).choose_spec, ← Category.assoc,
          Subobject.ofLE_arrow]
      refine ⟨factorThruImageSubobject f ≫
        Subobject.ofLE (imageSubobject f) ((D' i).Z ⊤) hI, ?_⟩
      rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
  preserves_B i r := by
    cases r using WithTop.recTopCoe with
    | coe n => exact hB i n
    | top =>
      let Q := (Subobject.pullback (φ i)).obj ((D' i).B ⊤)
      have hQ : (D i).B ⊤ ≤ Q := by
        apply (D i).B_top_least
        intro n
        apply Subobject.le_of_factors
        apply (pullback_factors_iff (φ i) ((D' i).B ⊤) (((D i).B n).arrow)).mpr
        rw [Subobject.factors_iff]
        have hn : (D' i).B n ≤ (D' i).B ⊤ := (D' i).B_mono le_top
        refine ⟨(hB i n).choose ≫
          Subobject.ofLE ((D' i).B n) ((D' i).B ⊤) hn, ?_⟩
        calc
          ((hB i n).choose ≫ Subobject.ofLE ((D' i).B n) ((D' i).B ⊤) hn) ≫
              ((D' i).B ⊤).arrow =
            (hB i n).choose ≫
              (Subobject.ofLE ((D' i).B n) ((D' i).B ⊤) hn ≫ ((D' i).B ⊤).arrow) :=
            Category.assoc _ _ _
          _ = (hB i n).choose ≫ ((D' i).B n).arrow :=
            congrArg (fun q => (hB i n).choose ≫ q) (Subobject.ofLE_arrow hn)
          _ = ((D i).B n).arrow ≫ φ i := (hB i n).choose_spec
      refine ⟨Subobject.ofLE ((D i).B ⊤) Q hQ ≫
        Subobject.pullbackπ (φ i) ((D' i).B ⊤), ?_⟩
      rw [Category.assoc, (Subobject.isPullback (φ i) ((D' i).B ⊤)).w,
        ← Category.assoc, Subobject.ofLE_arrow]

set_option backward.isDefEq.respectTransparency false in
private theorem dataMorphismOfFinite_ambient
    {C : Type absorbComparisonU} [Category.{absorbComparisonV} C] [Abelian C]
    {ι : Type absorbComparisonI} [AddCommGroup ι] [DecidableEq ι]
    (D D' : ι → SSData C) (φ : ∀ i, (D i).V ⟶ (D' i).V)
    (hZ : ∀ i (n : ℕ), ∃ (lift : Subobject.underlying.obj ((D i).Z n) ⟶
        Subobject.underlying.obj ((D' i).Z n)),
      lift ≫ ((D' i).Z n).arrow = ((D i).Z n).arrow ≫ φ i)
    (hB : ∀ i (n : ℕ), ∃ (lift : Subobject.underlying.obj ((D i).B n) ⟶
        Subobject.underlying.obj ((D' i).B n)),
      lift ≫ ((D' i).B n).arrow = ((D i).B n).arrow ≫ φ i) (i : ι) :
    (dataMorphismOfFinite D D' φ hZ hB).φ i = φ i := rfl


/-- The fixed mathematical object on the project background. -/
public def inversion_data :
  ∀ X : ClassicalObject,
    SSDataMorphism Tridegree
      (model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData
      (fun i => (model.classical.obj (X.obj model.auxiliary)).ssData (i.1,i.2.1)) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem inversion_e2 :
  ∀ (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)),
    comparisonPageMap model X (inversion_data X) 2 s t w (nuWeightLabel model X s t w hw x) = x := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem inversion_differential :
  ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ),
    let map := fun s t => comparisonPageMap model X (inversion_data X) r s t w
    syntheticDifferential model X r s t w ≫ map (s+r) (t+r-1) =
      map s t ≫ classicalDifferential model X r s t := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem inversion_lambda :
  ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ),
    let map := fun w => comparisonPageMap model X (inversion_data X) r s t w
    pageLambda X r s t w ≫ map (w-1) = map w := by
  sorry

public def inversionData : LambdaInversionComparison model nuPageData where
  data := inversion_data
  e2 := inversion_e2
  differential := inversion_differential
  lambda := inversion_lambda

section FreeInversionConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem freeDifferentialTransport
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    (E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι)
    (r : ℤ) {p q : ι} (h : p=q) :
    eqToHom (congrArg (E.Page r) h) ≫ E.d r q =
      E.d r p ≫ eqToHom (congrArg (E.Page r) (congrArg (fun p => p+E.diffDeg r) h)) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private def freeInflate
    {ι κ : Type} [AddCommGroup ι] [DecidableEq ι] [AddCommGroup κ] [DecidableEq κ]
    (E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) κ)
    (τ : ι →+ κ) (δ : ℤ → ι) (hδ : ∀ r, τ (δ r) = E.diffDeg r) :
    KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι where
  r₀ := E.r₀
  ssData p := E.ssData (τ p)
  diffDeg := δ
  d r p := E.d r (τ p) ≫ eqToHom (congrArg (E.Page r)
    (by rw [map_add, hδ]))
  d_comp_d r p := by
    have h := freeDifferentialTransport E r
      (p := τ p+E.diffDeg r) (q := τ (p+δ r)) (by rw [map_add,hδ])
    simp only [← Category.assoc]
    rw [Category.assoc (E.d r (τ p)), h]
    simp only [← Category.assoc, E.d_comp_d, zero_comp]
  Z_succ r p hr := by
    dsimp only
    rw [← E.Z_succ r (τ p) hr]
    apply (ModuleCat.subobjectModule _).injective
    simp only [subobjectModule_kernel]
    ext x
    change (E.d r (τ p) ≫ eqToHom _) x = 0 ↔ E.d r (τ p) x = 0
    rw [ModuleCat.comp_apply]
    exact (ModuleCat.mono_iff_injective (eqToHom _)).mp inferInstance |>.eq_iff' (by simp)
  B_succ r p hr := by
    dsimp only
    have aux (q : κ) (h : τ p+E.diffDeg r=q) :
        imageSubobject (E.d r (τ p) ≫ eqToHom (congrArg (E.Page r) h)) =
          imageSubobject (Subobject.ofLE ((E.ssData q).B ↑((r-E.r₀).toNat+1))
            ((E.ssData q).Z ↑(r-E.r₀).toNat)
            (((E.ssData q).B_le_Z _).trans ((E.ssData q).Z_anti
              (by exact_mod_cast Nat.le_succ (r-E.r₀).toNat))) ≫
                (E.ssData q).pageπ ↑(r-E.r₀).toNat) := by
      cases h
      simpa only [eqToHom_refl, Category.comp_id] using E.B_succ r (τ p) hr
    exact aux _ (by rw [map_add,hδ])

private def freeForgetWeight : Tridegree →+ (ℤ × ℤ) where
  toFun i := (i.1,i.2.1)
  map_zero' := rfl
  map_add' _ _ := rfl

private def freeClassicalInflation (X : ClassicalObject) :=
  freeInflate (model.classical.obj (X.obj model.auxiliary)) freeForgetWeight syntheticAdamsRawShift
    (fun r => (model.classical.differentialDegree _ r).symm)

private theorem freeNormalizePageMap
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData (ModuleCat.{0} ℤ)} (g : SSDataMorphism ι D D')
    (a b c : ℤ) (ha : a=c) (hb : b=c) (r : ℤ) (p : ι) :
    eqToHom (congrArg (fun z => (D p).page ↑(r-z).toNat) ha) ≫
      g.pageMap p ↑(r-c).toNat ≫
        eqToHom (congrArg (fun z => (D' p).page ↑(r-z).toNat) hb.symm) =
      g.pageMap p ↑(r-a).toNat ≫
        eqToHom (congrArg (fun z => (D' p).page ↑(r-z).toNat) (ha.trans hb.symm)) := by
  cases ha
  cases hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private def freeInversionRawMap (X : ClassicalObject) (r s t w : ℤ) :=
  (inversion_data X).pageMapAt
    (E := (model.family.nu model.nu (X.obj model.auxiliary)).sequence.toPreSS)
    (E' := (freeClassicalInflation X).toPreSS)
    ((model.family.nu model.nu (X.obj model.auxiliary)).firstPage.trans
      (model.classical.firstPage _).symm) r (s,t,w)

private theorem freeInversionRawMap_eq (X : ClassicalObject) (r s t w : ℤ) :
    freeInversionRawMap X r s t w = comparisonPageMap model X (inversion_data X) r s t w := by
  dsimp only [freeInversionRawMap, comparisonPageMap, SSDataMorphism.pageMapAt]
  exact (freeNormalizePageMap (inversion_data X) _ _ 2
    (model.family.nu model.nu (X.obj model.auxiliary)).firstPage
    (model.classical.firstPage _) r (s,t,w)).symm

private theorem freeDegreeMapNatural
    {ι : Type} {A B : ι → ModuleCat.{0} ℤ}
    (m : ∀ i, A i ⟶ B i) {p q : ι} (h : p=q) :
    eqToHom (congrArg A h) ≫ m q = m p ≫ eqToHom (congrArg B h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem freeLocalDifferentialSquare
    {ι : Type} [AddCommGroup ι] [DecidableEq ι]
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) ι}
    (r : ℤ) (p q : ι) (hδ : E.diffDeg r=F.diffDeg r)
    (m : ∀ i, E.Page r i ⟶ F.Page r i)
    (hs : p+E.diffDeg r=q) (ht : p+F.diffDeg r=q)
    (h : (E.d r p ≫ eqToHom (congrArg (E.Page r) hs)) ≫ m q =
      m p ≫ (F.d r p ≫ eqToHom (congrArg (F.Page r) ht))) :
    m p ≫ F.d r p = E.d r p ≫ m (p+E.diffDeg r) ≫
      eqToHom (congrArg (F.Page r) (congrArg (fun d => p+d) hδ)) := by
  apply (cancel_mono (eqToHom (congrArg (F.Page r) ht))).mp
  simp only [Category.assoc, eqToHom_trans]
  have hn := freeDegreeMapNatural m hs
  rw [Category.assoc, hn] at h
  simpa only [Category.assoc] using h.symm

private def freeInversionMorphism (X : ClassicalObject) :
    FromFirstMorphism
      (model.family.nu model.nu (X.obj model.auxiliary)).sequence (freeClassicalInflation X) where
  toSSDataMorphism := inversion_data X
  r₀_eq := (model.family.nu model.nu (X.obj model.auxiliary)).firstPage.trans
    (model.classical.firstPage _).symm
  diffDeg_eq := funext (model.family.nu model.nu (X.obj model.auxiliary)).differentialDegree
  comm_d r hr p := by
    rcases p with ⟨s,t,w⟩
    have hr2 : 2 ≤ r := by
      simpa only [(model.family.nu model.nu (X.obj model.auxiliary)).firstPage] using hr
    let E := (model.family.nu model.nu (X.obj model.auxiliary)).sequence
    let F := freeClassicalInflation X
    let m := fun i : Tridegree => freeInversionRawMap X r i.1 i.2.1 i.2.2
    change m (s,t,w) ≫ F.d r (s,t,w) =
      E.d r (s,t,w) ≫ m ((s,t,w)+E.diffDeg r) ≫ _
    apply freeLocalDifferentialSquare (E := E) (F := F) r (s,t,w) (s+r,t+r-1,w)
      ((model.family.nu model.nu (X.obj model.auxiliary)).differentialDegree r) m
      (by rw [(model.family.nu model.nu (X.obj model.auxiliary)).differentialDegree];
          ext <;> simp only [syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add] <;> omega)
      (by change (s,t,w)+syntheticAdamsRawShift r = _;
          ext <;> simp only [syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add] <;> omega)
    change (E.d r (s,t,w) ≫ _) ≫ freeInversionRawMap X r (s+r) (t+r-1) w =
      freeInversionRawMap X r s t w ≫ (F.d r (s,t,w) ≫ _)
    rw [freeInversionRawMap_eq, freeInversionRawMap_eq]
    have h := inversion_differential X r hr2 s t w
    dsimp only at h
    delta KIP126.Literature.syntheticDifferential KIP126.Literature.classicalDifferential at h
    delta SyntheticAdamsSS.d at h
    simpa only [E, F, freeClassicalInflation, freeInflate, freeForgetWeight,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, Category.assoc, eqToHom_trans] using h

private theorem freeInversionMorphism_pageMap (X : ClassicalObject) (r s t w : ℤ) :
    (freeInversionMorphism X).pageMap r (s,t,w) =
      comparisonPageMap model X (inversion_data X) r s t w := by
  change freeInversionRawMap X r s t w = _
  exact freeInversionRawMap_eq X r s t w

private def freeRawPageIso
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Tridegree}
    (e : E ≅ F) (r : ℤ) (p : Tridegree) : E.Page r p ≅ F.Page r p where
  hom := e.hom.pageMap r p
  inv := e.inv.pageMap r p
  hom_inv_id := by
    rw [← SpectralSequenceMorphism.pageMap_comp, e.hom_inv_id,
      SpectralSequenceMorphism.pageMap_id]
  inv_hom_id := by
    rw [← SpectralSequenceMorphism.pageMap_comp, e.inv_hom_id,
      SpectralSequenceMorphism.pageMap_id]

private theorem freeNuWeightLabelBijective (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t) :
    Function.Bijective (nuWeightLabel model X s t w hw) := by
  let zeroIso := SyntheticCategory.biShift_zero.app
    (model.nu.functor.obj (X.obj model.auxiliary))
  let zeroPage := freeRawPageIso (model.family.functor.mapIso zeroIso) 2
    (s,t,t-(t-w).toNat)
  have hzero : Function.Bijective zeroPage.hom := ConcreteCategory.bijective_of_isIso _
  change Function.Bijective (fun x => nuWeightLabel model X s t w hw x)
  dsimp only [nuWeightLabel, regradeE2, targetNuLabel]
  apply Function.Bijective.comp
  · exact ConcreteCategory.bijective_of_isIso _
  · apply Function.Bijective.comp
    · exact hzero
    · change Function.Bijective
        ((fun z : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj
            (model.nu.functor.obj (X.obj model.auxiliary)))).E₂
              (s,t,t+0-(t-w).toNat) =>
          Eq.mp (by simp only [add_zero]) z) ∘
            (model.comparison.nuE2 X 0 s t (t-w).toNat))
      exact (Equiv.cast _).bijective.comp
        (model.comparison.nuE2 X 0 s t (t-w).toNat).bijective

private theorem freeInversionMorphism_e2_bijective (X : ClassicalObject) (s t w : ℤ)
    (hw : w ≤ t) : Function.Bijective ((freeInversionMorphism X).pageMap 2 (s,t,w)) := by
  rw [freeInversionMorphism_pageMap]
  have hlabel := freeNuWeightLabelBijective X s t w hw
  constructor
  · intro a b hab
    obtain ⟨x,rfl⟩ := hlabel.2 a
    obtain ⟨y,rfl⟩ := hlabel.2 b
    apply congrArg (nuWeightLabel model X s t w hw)
    exact (inversion_e2 X s t w hw x).symm.trans (hab.trans (inversion_e2 X s t w hw y))
  · intro x
    exact ⟨nuWeightLabel model X s t w hw x, inversion_e2 X s t w hw x⟩

-- Preserve this proved witness under its private name in the exposed constructor.
set_option backward.privateInPublic true in
private theorem freeInversionIsIso (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (hfree : r-2 ≤ t-w) :
    IsIso (comparisonPageMap model X (inversion_data X) r s t w) := by
  let E := (model.family.nu model.nu (X.obj model.auxiliary)).sequence
  let f := freeInversionMorphism X
  have first : E.r₀ = 2 := (model.family.nu model.nu (X.obj model.auxiliary)).firstPage
  have degree (r : ℤ) : E.diffDeg r = syntheticAdamsRawShift r :=
    (model.family.nu model.nu (X.obj model.auxiliary)).differentialDegree r
  have comparison (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) :
      (Function.Surjective (f.pageMap r (s-r,t-r+1,w)) →
        Function.Injective (f.pageMap r (s,t,w)) →
        Function.Injective (f.pageMap (r+1) (s,t,w))) ∧
      (Function.Surjective (f.pageMap r (s,t,w)) →
        Function.Injective (f.pageMap r (s+r,t+r-1,w)) →
        Function.Surjective (f.pageMap (r+1) (s,t,w))) := by
    let q : Tridegree := (s-r,t-r+1,w)
    have hcenter : q+E.diffDeg r = (s,t,w) := by
      rw [degree]
      ext <;> simp only [q, syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add] <;> omega
    have hout : (s,t,w)+E.diffDeg r = (s+r,t+r-1,w) := by
      rw [degree]
      ext <;> simp only [syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add] <;> omega
    let P (p p' : Tridegree) : Prop :=
      (Function.Surjective (f.pageMap r q) →
        Function.Injective (f.pageMap r p) → Function.Injective (f.pageMap (r+1) p)) ∧
      (Function.Surjective (f.pageMap r p) →
        Function.Injective (f.pageMap r p') → Function.Surjective (f.pageMap (r+1) p))
    have h : P (q+E.diffDeg r) (q+E.diffDeg r+E.diffDeg r) :=
      finiteQuotientSuccessorComparison f r (by rw [first]; exact hr) q
    have h' : P (s,t,w) ((s,t,w)+E.diffDeg r) :=
      Eq.mp (congrArg (fun p => P p (p+E.diffDeg r)) hcenter) h
    exact Eq.mp (congrArg (P (s,t,w)) hout) h'
  have pages (k : ℕ) :
      (∀ s t w : ℤ, (k : ℤ) ≤ t-w → Function.Injective (f.pageMap (k+2) (s,t,w))) ∧
      (∀ s t w : ℤ, 0 ≤ t-w → Function.Surjective (f.pageMap (k+2) (s,t,w))) := by
    induction k with
    | zero =>
      constructor
      · intro s t w hnonneg
        change Function.Injective (f.pageMap 2 (s,t,w))
        exact (freeInversionMorphism_e2_bijective X s t w (by omega)).1
      · intro s t w hnonneg
        change Function.Surjective (f.pageMap 2 (s,t,w))
        exact (freeInversionMorphism_e2_bijective X s t w (by omega)).2
    | succ k ih =>
      have hr : (2 : ℤ) ≤ (k : ℤ)+2 := by omega
      constructor
      · intro s t w hfree
        have hin := ih.2 (s-(k+2)) (t-(k+2)+1) w (by omega)
        have hmid := ih.1 s t w (by omega)
        have h := (comparison ((k : ℤ)+2) hr s t w).1 hin hmid
        have hpage : ((Nat.succ k : ℕ) : ℤ)+2 = (k : ℤ)+2+1 := by omega
        exact Eq.mp (congrArg (fun r : ℤ => Function.Injective (f.pageMap r (s,t,w))) hpage.symm) h
      · intro s t w hnonneg
        have hmid := ih.2 s t w hnonneg
        have hout := ih.1 (s+(k+2)) (t+(k+2)-1) w (by omega)
        have h := (comparison ((k : ℤ)+2) hr s t w).2 hmid hout
        have hpage : ((Nat.succ k : ℕ) : ℤ)+2 = (k : ℤ)+2+1 := by omega
        exact Eq.mp (congrArg (fun r : ℤ => Function.Surjective (f.pageMap r (s,t,w))) hpage.symm) h
  let k := (r-2).toNat
  have hk : (k : ℤ)+2 = r := by dsimp [k]; rw [Int.toNat_of_nonneg (by omega)]; omega
  have hbij : Function.Bijective (f.pageMap r (s,t,w)) := by
    rw [← hk]
    exact ⟨(pages k).1 s t w (by omega), (pages k).2 s t w (by omega)⟩
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  rw [← freeInversionMorphism_pageMap X r s t w]
  exact hbij

-- Keep the IsIso witness private and preserve the frozen public/generated exports.
set_option backward.proofsInPublic true in
set_option backward.privateInPublic true in
/-- The fixed inversion map is an isomorphism throughout the free range,
by the joint injectivity/surjectivity comparison induction. -/
public def free_component :
  ∀ (X : ClassicalObject) (r : ℤ) (_hr : 2 ≤ r)
    (s t w : ℤ) (_h : r-2 ≤ t-w),
    (model.family.nu model.nu (X.obj model.auxiliary)).Page r (s,t,w) ≅
      (model.classical.obj (X.obj model.auxiliary)).Page r (s,t) := by
  intro X r hr s t w h
  letI : IsIso (comparisonPageMap model X (inversion_data X) r s t w) := by
    exact freeInversionIsIso X r hr s t w h
  exact asIso (comparisonPageMap model X (inversion_data X) r s t w)

/-- Compatibility is inherited from the same fixed inversion comparison. -/
public theorem free_e2 :
  ∀ (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)),
    (free_component X 2 (by omega) s t w (by omega)).hom (nuWeightLabel model X s t w hw x) = x := by
  intro X s t w hw x
  exact inversion_e2 X s t w hw x

/-- Compatibility is inherited from the same fixed inversion comparison. -/
public theorem free_lambda :
  ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
      (s t w : ℤ) (h : r-2 ≤ t-w),
    pageLambda X r s t w ≫ (free_component X r hr s t (w-1) (by omega)).hom =
      (free_component X r hr s t w h).hom := by
  intro X r hr s t w h
  exact inversion_lambda X r hr s t w

/-- Compatibility is inherited from the same fixed inversion comparison. -/
public theorem free_differential :
  ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
      (s t w : ℤ) (h : r-2 ≤ t-w),
    syntheticDifferential model X r s t w ≫
        (free_component X r hr (s+r) (t+r-1) w (by omega)).hom =
      (free_component X r hr s t w h).hom ≫ classicalDifferential model X r s t := by
  intro X r hr s t w h
  exact inversion_differential X r hr s t w

public def freeData : FreeLambdaPages model nuPageData where
  component := free_component
  e2 := free_e2
  lambda := free_lambda
  differential := free_differential

public def classicalLift := FreeLambdaPages.classicalLift model freeData

public abbrev classicalLift_differential := FreeLambdaPages.classicalLift_differential model freeData

public abbrev classicalLift_lambda := FreeLambdaPages.classicalLift_lambda model freeData

/-- The constructed free comparison uses precisely this inversion map. -/
public theorem free_inversion :
  ∀ (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
    (s t w : ℤ) (h : r-2 ≤ t-w),
    (free_component X r hr s t w h).hom = comparisonPageMap model X (inversion_data X) r s t w := by
  intro X r hr s t w h
  rfl

end FreeInversionConstruction

/-- The fixed mathematical object on the project background. -/
public def finite_quotient_component :
  ∀ (X : ClassicalObject) (n : ℕ) (hn : 0 < n),
  ∀ s t w : ℤ,
    (model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) n).Page 2 (s,t,w) ≅
      quotientE2Component model X n s t w := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem finite_quotient_component_retained :
  ∀ (X : ClassicalObject) (n : ℕ) (hn : 0 < n),
  ∀ (s t w : ℤ) (h : 0 ≤ t-w ∧ t-w < n)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)),
    HEq (((finite_quotient_component X n hn) s t w).hom
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) n).pageMap
        2 (s,t,w) (nuWeightLabel model X s t w (by omega) x))) x := by
  sorry

private def retainedLabelPageIso
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Tridegree}
    (e : E ≅ F) (r : ℤ) (p : Tridegree) : E.Page r p ≅ F.Page r p where
  hom := e.hom.pageMap r p
  inv := e.inv.pageMap r p
  hom_inv_id := by
    rw [← SpectralSequenceMorphism.pageMap_comp, e.hom_inv_id,
      SpectralSequenceMorphism.pageMap_id]
  inv_hom_id := by
    rw [← SpectralSequenceMorphism.pageMap_comp, e.inv_hom_id,
      SpectralSequenceMorphism.pageMap_id]

private theorem projection_isIso_of_retained_labels
    {A B Q R : ModuleCat.{0} ℤ} (e : Q ≅ R) (f : A ⟶ Q)
    (label : B → A) (hlabel : Function.Bijective label)
    (hR : R = B) (hret : ∀ x : B, HEq (e.hom (f (label x))) x) :
    IsIso f := by
  subst R
  have hret' (x : B) : e.hom (f (label x)) = x := eq_of_heq (hret x)
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso _
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := hlabel.surjective a
    obtain ⟨y, rfl⟩ := hlabel.surjective b
    apply congrArg label
    have hcxy := congrArg e.hom hab
    simpa only [hret'] using hcxy
  · intro b
    refine ⟨label (e.hom b), ?_⟩
    apply he.injective
    exact hret' (e.hom b)

private theorem finiteQuotientRetainedImpl :
  ∀ (X : ClassicalObject) (n : ℕ) (hn : 0 < n),
  ∀ (s t w : ℤ), 0 ≤ t-w ∧ t-w < n →
    IsIso ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) n).pageMap 2 (s,t,w)) := by
  intro X n hn s t w hstrip
  have hw : w ≤ t := by omega
  let zeroIso := SyntheticCategory.biShift_zero.app
    (model.nu.functor.obj (X.obj model.auxiliary))
  let zeroPage := retainedLabelPageIso (model.family.functor.mapIso zeroIso) 2
    (s,t,t-(t-w).toNat)
  have hzero : Function.Bijective zeroPage.hom :=
    ConcreteCategory.bijective_of_isIso _
  have hlabel : Function.Bijective (nuWeightLabel model X s t w hw) := by
    change Function.Bijective (fun x => nuWeightLabel model X s t w hw x)
    dsimp only [nuWeightLabel, regradeE2, targetNuLabel]
    apply Function.Bijective.comp
    · exact ConcreteCategory.bijective_of_isIso _
    · apply Function.Bijective.comp
      · exact hzero
      · change Function.Bijective
          ((fun z : (model.family.obj ((SyntheticCategory.biShift (0,0)).obj
              (model.nu.functor.obj (X.obj model.auxiliary)))).E₂
                (s,t,t+0-(t-w).toNat) =>
            Eq.mp (by simp only [add_zero]) z) ∘
              (model.comparison.nuE2 X 0 s t (t-w).toNat))
        exact (Equiv.cast _).bijective.comp
          (model.comparison.nuE2 X 0 s t (t-w).toNat).bijective
  apply projection_isIso_of_retained_labels (finite_quotient_component X n hn s t w)
    ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) n).pageMap
      2 (s,t,w)) (nuWeightLabel model X s t w hw) hlabel
    (by
      change (if 0 ≤ t-w ∧ t-w < n then
        (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t) else ModuleCat.of ℤ PUnit) = _
      exact if_pos hstrip)
  intro x
  exact finite_quotient_component_retained X n hn s t w hstrip x


/-- The actual retained quotient projection is an isomorphism by its component label square. -/
public theorem finite_quotient_retained :
  ∀ (X : ClassicalObject) (n : ℕ) (hn : 0 < n),
  ∀ (s t w : ℤ), 0 ≤ t-w ∧ t-w < n →
    IsIso ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) n).pageMap 2 (s,t,w)) := finiteQuotientRetainedImpl

/-- The zero E₂ components remain zero on every later page by monotonicity
of the same cycle and boundary subobjects. -/
public theorem finite_quotient_vanishing :
  ∀ (X : ClassicalObject) (n : ℕ), 0 < n →
    ∀ (r : ℤ), 2 ≤ r → ∀ (s t w : ℤ), (t-w < 0 ∨ (n : ℤ) ≤ t-w) →
      IsZero ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) n).Page r (s,t,w)) := by
  intro X n hn r hr s t w hout
  let E := (model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) n).sequence
  let D := E.ssData (s,t,w)
  have hstrip : ¬ (0 ≤ t-w ∧ t-w < n) := by omega
  have hzero2 : IsZero (E.Page 2 (s,t,w)) := by
    apply (finite_quotient_component X n hn s t w).isZero_iff.mpr
    change IsZero (if 0 ≤ t-w ∧ t-w < n then
      (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t) else ModuleCat.of ℤ PUnit)
    rw [if_neg hstrip]
    exact ModuleCat.isZero_of_subsingleton _
  have hfirst : E.r₀ = 2 :=
    (model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) n).firstPage
  have hzero0 : IsZero (D.page (↑(0 : ℕ))) := by
    simpa only [D, Page, hfirst, sub_self, Int.toNat_zero] using hzero2
  have hBZ : D.B (↑(0 : ℕ)) = D.Z (↑(0 : ℕ)) :=
    D.eq_of_page_isZero _ hzero0
  change IsZero (D.page ↑(r-E.r₀).toNat)
  apply D.page_isZero_of_eq
  apply le_antisymm (D.B_le_Z _)
  calc
    D.Z ↑(r-E.r₀).toNat ≤ D.Z (↑(0 : ℕ)) := D.Z_anti (by exact bot_le)
    _ = D.B (↑(0 : ℕ)) := hBZ.symm
    _ ≤ D.B ↑(r-E.r₀).toNat := D.B_mono (by exact bot_le)


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The retained E₂ strip propagates by a joint induction: the whole strip
remains injective, while the stated safe substrip remains surjective. -/
public theorem finite_quotient_safe :
  ∀ (X : ClassicalObject) (n : ℕ) (hn : 0 < n),
  ∀ (r s t w : ℤ), 2 ≤ r → 0 ≤ t-w → t-w+r-2 < n →
    IsIso ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) n).pageMap r (s,t,w)) := by
  intro X n hn
  let E := (model.family.nu model.nu (X.obj model.auxiliary)).sequence
  let F := (model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) n).sequence
  let f : E ⟶ F := model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) n
  have first : E.r₀ = 2 := (model.family.nu model.nu (X.obj model.auxiliary)).firstPage
  have degree (r : ℤ) : E.diffDeg r = syntheticAdamsRawShift r :=
    (model.family.nu model.nu (X.obj model.auxiliary)).differentialDegree r
  have comparison (r : ℤ) (hr : 2 ≤ r) (s t w : ℤ) :
      (Function.Surjective (f.pageMap r (s-r,t-r+1,w)) →
        Function.Injective (f.pageMap r (s,t,w)) →
        Function.Injective (f.pageMap (r+1) (s,t,w))) ∧
      (Function.Surjective (f.pageMap r (s,t,w)) →
        Function.Injective (f.pageMap r (s+r,t+r-1,w)) →
        Function.Surjective (f.pageMap (r+1) (s,t,w))) := by
    let q : Tridegree := (s-r,t-r+1,w)
    have hcenter : q+E.diffDeg r = (s,t,w) := by
      rw [degree]
      ext <;> simp only [q, syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add] <;> omega
    have hout : (s,t,w)+E.diffDeg r = (s+r,t+r-1,w) := by
      rw [degree]
      ext <;> simp only [syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add] <;> omega
    let P (p p' : Tridegree) : Prop :=
      (Function.Surjective (f.pageMap r q) →
        Function.Injective (f.pageMap r p) → Function.Injective (f.pageMap (r+1) p)) ∧
      (Function.Surjective (f.pageMap r p) →
        Function.Injective (f.pageMap r p') → Function.Surjective (f.pageMap (r+1) p))
    have h : P (q+E.diffDeg r) (q+E.diffDeg r+E.diffDeg r) :=
      finiteQuotientSuccessorComparison (firstPageComparisonOfMorphism f) r (by rw [first]; exact hr) q
    have h' : P (s,t,w) ((s,t,w)+E.diffDeg r) :=
      Eq.mp (congrArg (fun p => P p (p+E.diffDeg r)) hcenter) h
    exact Eq.mp (congrArg (P (s,t,w)) hout) h'
  have pages (k : ℕ) :
      (∀ s t w : ℤ, 0 ≤ t-w → t-w < n →
        Function.Injective (f.pageMap (k+2) (s,t,w))) ∧
      (∀ s t w : ℤ, 0 ≤ t-w → t-w+(k+2)-2 < n →
        Function.Surjective (f.pageMap (k+2) (s,t,w))) := by
    induction k with
    | zero =>
      constructor
      · intro s t w hnonneg hlt
        change Function.Injective (f.pageMap 2 (s,t,w))
        haveI : IsIso (f.pageMap 2 (s,t,w)) := finite_quotient_retained X n hn s t w ⟨hnonneg,hlt⟩
        exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance |>.1
      · intro s t w hnonneg hlt
        change Function.Surjective (f.pageMap 2 (s,t,w))
        haveI : IsIso (f.pageMap 2 (s,t,w)) := finite_quotient_retained X n hn s t w ⟨hnonneg,by omega⟩
        exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance |>.2
    | succ k ih =>
      have hr : (2 : ℤ) ≤ (k : ℤ)+2 := by omega
      constructor
      · intro s t w hnonneg hlt
        have hin : Function.Surjective (f.pageMap (k+2) (s-(k+2),t-(k+2)+1,w)) := by
          by_cases hsource : 0 ≤ (t-((k : ℤ)+2)+1)-w
          · exact ih.2 _ _ _ hsource (by omega)
          · have hz := finite_quotient_vanishing X n hn ((k : ℤ)+2) hr
              (s-(k+2)) (t-(k+2)+1) w (Or.inl (by omega))
            haveI := hz.epi (f.pageMap (k+2) (s-(k+2),t-(k+2)+1,w))
            exact (ModuleCat.epi_iff_surjective _).mp inferInstance
        have h := (comparison ((k : ℤ)+2) hr s t w).1 hin (ih.1 _ _ _ hnonneg hlt)
        have hpage : ((Nat.succ k : ℕ) : ℤ)+2 = (k : ℤ)+2+1 := by omega
        exact Eq.mp (congrArg (fun r : ℤ => Function.Injective (f.pageMap r (s,t,w))) hpage.symm) h
      · intro s t w hnonneg hlt
        have hmid := ih.2 s t w hnonneg (by push_cast at hlt; omega)
        have hout := ih.1 (s+(k+2)) (t+(k+2)-1) w (by omega) (by push_cast at hlt; omega)
        have h := (comparison ((k : ℤ)+2) hr s t w).2 hmid hout
        have hpage : ((Nat.succ k : ℕ) : ℤ)+2 = (k : ℤ)+2+1 := by omega
        exact Eq.mp (congrArg (fun r : ℤ => Function.Surjective (f.pageMap r (s,t,w))) hpage.symm) h
  intro r s t w hr hnonneg hlt
  let k := (r-2).toNat
  have hk : (k : ℤ)+2 = r := by dsimp [k]; rw [Int.toNat_of_nonneg (by omega)]; omega
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  rw [← hk]
  exact ⟨(pages k).1 s t w hnonneg (by omega), (pages k).2 s t w hnonneg (by omega)⟩

/-- Source or comparison proof remains to be supplied. -/
public theorem degeneration :
  ∀ (X : ClassicalObject) (N : ℤ),
    DegeneratesAt (model.classical.obj (X.obj model.auxiliary)) N →
    DegeneratesAt (model.family.nu model.nu (X.obj model.auxiliary)).sequence N := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem above_diagonal :
  ∀ (X : ClassicalObject) (r : ℤ), 2 ≤ r →
    ∀ (s t w : ℤ), t < w → IsZero ((model.family.nu model.nu (X.obj model.auxiliary)).Page r (s,t,w)) := by
  sorry

/-- Derived from the fixed objects and previously established operations. -/
public def finite_quotient :
  ∀ (X : ClassicalObject) (n : ℕ), 0 < n → NuModLambdaPageData model X n := fun X n hn => { component := finite_quotient_component X n hn, component_retained := finite_quotient_component_retained X n hn, retained := finite_quotient_retained X n hn, safe := finite_quotient_safe X n hn }

/-- The fixed mathematical object on the project background. -/
public def eInfinity_nu :
  ∀ (X : ClassicalObject) (p : Bidegree) (w : ℤ),
    ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      nuEInftyModel model X p w := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def eInfinity_finite :
  ∀ (X : ClassicalObject) (q : ℕ) (_hq : 0 < q) (p : Bidegree) (w : ℤ),
    ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData (p.1,p.2,w)).eInfty ≃+
      finiteEInftyModel model X q p w := by
  sorry

public def infinityPresentationData : EInfinityPresentation model where
  nu := eInfinity_nu
  finite := eInfinity_finite

/-- Derived from the fixed objects and previously established operations. -/
public def infinityShift_comparison :
  ∀ k : ℕ, SyntheticESSShiftComparison model (0,-(k:ℤ)) := fun k => KIP126.AdamsSynthetic.Standard.essShift (0,-(k:ℤ))

/- Naturality descends from the same actual filtered homotopy maps and
convergence identifications. The source ambient quotient argument is adapted
to the fixed filtered-piece shift; no E∞ presentation is assumed. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityMapReindex {ι : Type} {A B : ι → ModuleCat.{0} ℤ}
    (φ : ∀ i, A i ⟶ B i) {i j : ι} (h : i=j) :
    φ i ≫ eqToHom (congrArg B h) = eqToHom (congrArg A h) ≫ φ j := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityTransportedSquare
    {A B A' B' A₀ B₀ A₀' B₀' : ModuleCat.{0} ℤ}
    (iA : A₀=A) (iB : B₀=B) (jA : A'=A₀') (jB : B'=B₀')
    (eA : A ≅ A') (eB : B ≅ B')
    (f : A ⟶ B) (f' : A' ⟶ B') (g : A₀ ⟶ B₀) (g' : A₀' ⟶ B₀')
    (h : f ≫ eB.hom = eA.hom ≫ f')
    (hin : g ≫ eqToHom iB = eqToHom iA ≫ f)
    (hout : f' ≫ eqToHom jB = eqToHom jA ≫ g') :
    g ≫ (eqToHom iB ≫ eB.hom ≫ eqToHom jB) =
      (eqToHom iA ≫ eA.hom ≫ eqToHom jA) ≫ g' := by
  calc
    _ = (g ≫ eqToHom iB) ≫ eB.hom ≫ eqToHom jB := by
      simp only [Category.assoc]
    _ = (eqToHom iA ≫ f) ≫ eB.hom ≫ eqToHom jB := by rw [hin]
    _ = eqToHom iA ≫ (f ≫ eB.hom) ≫ eqToHom jB := by
      simp only [Category.assoc]
    _ = eqToHom iA ≫ (eA.hom ≫ f') ≫ eqToHom jB := by rw [h]
    _ = eqToHom iA ≫ eA.hom ≫ (f' ≫ eqToHom jB) := by
      simp only [Category.assoc]
    _ = _ := by rw [hout]; simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityGradedTransportComm
    {A B A' B' : (ℤ × ℤ) → ModuleCat.{0} ℤ}
    {F : Filtration A} {G : Filtration B} {F' : Filtration A'} {G' : Filtration B'}
    {f : FilteredMorphism F G} {f' : FilteredMorphism F' G'}
    {p q : ℤ × ℤ} (e : FilteredMapTransport f f' p q) (s : ℤ) :
    f.inducedGrMap s p ≫ (e.target.gradedIso s).hom =
      (e.source.gradedIso s).hom ≫ f'.inducedGrMap s q := by
  have level_comm : (f.compat s p).choose ≫ (e.target.level s).hom =
      (e.source.level s).hom ≫ (f'.compat s q).choose := by
    apply (cancel_mono (G'.F s q).arrow).mp
    simp only [Category.assoc]
    rw [e.target.level_arrow, (f'.compat s q).choose_spec]
    rw [← Category.assoc, (f.compat s p).choose_spec, Category.assoc,
      ← e.map_comm]
    simpa only [Category.assoc] using congrArg (fun a => a ≫ f'.map q)
      (e.source.level_arrow s).symm
  haveI : Epi (F.toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
  apply (cancel_epi (F.toAssociatedGraded s p)).mp
  rw [← Category.assoc, f.quotient_naturality, Category.assoc,
    e.target.projection_comm, ← Category.assoc, level_comm]
  rw [Category.assoc, ← f'.quotient_naturality, ← Category.assoc,
    ← e.source.projection_comm]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityTowerGradedNatural
    {Syn : Type 1} [SyntheticCategory.{1,0} Syn]
    [HasFunctorialCofiber (C := Syn)]
    {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
    {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
    (cx : SyntheticTowerConvergence P X) (cy : SyntheticTowerConvergence P Y)
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s : ℤ) :
    (F.map g).eInftyMap (s,p.1+s,p.2) ≫ (towerGradedIso cy p s).hom =
      (towerGradedIso cx p s).hom ≫ M.filteredMap.inducedGrMap s p := by
  let i : Tridegree := (s,p.1+s,p.2)
  let q : ℤ × ℤ := (p.1+s-s,p.2)
  have hp : q=p := Prod.ext (add_sub_cancel_right p.1 s) rfl
  have h := (M.infinity_action_graded i).symm
  change (F.map g).eInftyMap i ≫
      ((cy.identification i).hom ≫
        eqToHom (congrArg (fun q => cy.filtration.associatedGraded s q) hp)) =
    ((cx.identification i).hom ≫
        eqToHom (congrArg (fun q => cx.filtration.associatedGraded s q) hp)) ≫
      M.filteredMap.inducedGrMap s p
  rw [← Category.assoc, h, Category.assoc,
    infinityMapReindex (fun q => M.filteredMap.inducedGrMap s q) hp]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityTowerNatural
    {C : Type 1} [StableHomotopyCategory.{1,0} C]
    [HasFunctorialCofiber (C := C)]
    {Syn : Type 1} [SyntheticCategory.{1,0} Syn]
    [HasFunctorialCofiber (C := Syn)]
    (D : Model C Syn) (δ : ℤ × ℤ) (S : SyntheticESSShiftComparison D δ)
    (X Y : SyntheticObject)
    (f : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary)
    (p : ℤ × ℤ) (s : ℤ) :
    (D.family.map f).eInftyMap (s,p.1+s,p.2) ≫
        (towerInfinityIso (D.convergence Y) (D.convergence (.shift δ Y))
          (S.filtered Y p) s).hom =
      (towerInfinityIso (D.convergence X) (D.convergence (.shift δ X))
          (S.filtered X p) s).hom ≫
        (D.family.map ((SyntheticCategory.biShift δ).map f)).eInftyMap
          (s,(p+δ).1+s,(p+δ).2) := by
  let M := D.convergentMap X Y f
  let M' := D.convergentMap (.shift δ X) (.shift δ Y)
    ((SyntheticCategory.biShift δ).map f)
  have h := infinityGradedTransportComm (S.transport X Y f p) s
  change M.filteredMap.inducedGrMap s p ≫ ((S.filtered Y p).gradedIso s).hom =
    ((S.filtered X p).gradedIso s).hom ≫ M'.filteredMap.inducedGrMap s (p+δ) at h
  have hM' : M'.filteredMap.inducedGrMap s (p+δ) =
      (towerGradedIso (D.convergence (.shift δ X)) (p+δ) s).inv ≫
        (D.family.map ((SyntheticCategory.biShift δ).map f)).eInftyMap
          (s,(p+δ).1+s,(p+δ).2) ≫
        (towerGradedIso (D.convergence (.shift δ Y)) (p+δ) s).hom := by
    calc
      _ = (towerGradedIso (D.convergence (.shift δ X)) (p+δ) s).inv ≫
          ((towerGradedIso (D.convergence (.shift δ X)) (p+δ) s).hom ≫
            M'.filteredMap.inducedGrMap s (p+δ)) := by
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = _ := by
        rw [← infinityTowerGradedNatural (D.convergence (.shift δ X))
          (D.convergence (.shift δ Y)) M' (p+δ) s]
  apply (cancel_mono (towerGradedIso (D.convergence (.shift δ Y)) (p+δ) s).hom).mp
  simp only [towerInfinityIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, infinityTowerGradedNatural (D.convergence X) (D.convergence Y) M]
  rw [Category.assoc, h, hM']

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityShiftNatural
    {C : Type 1} [StableHomotopyCategory.{1,0} C]
    [HasFunctorialCofiber (C := C)]
    {Syn : Type 1} [SyntheticCategory.{1,0} Syn]
    [HasFunctorialCofiber (C := Syn)]
    (D : Model C Syn) (K : ∀ k : ℕ, SyntheticESSShiftComparison D (0,-(k:ℤ)))
    (X Y : SyntheticObject) (f : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary)
    (k : ℕ) (p : ℤ × ℤ) (w : ℤ) :
    (D.family.map f).eInftyMap (p.1,p.2,w) ≫ (infinityShift D K Y k p w).hom =
      (infinityShift D K X k p w).hom ≫
        (D.family.map ((SyntheticCategory.biShift (0,-(k:ℤ))).map f)).eInftyMap
          (p.1,p.2,w-k) := by
  let a : Tridegree := (p.1,p.2,w)
  let b : Tridegree := (p.1,(p.2-p.1)+p.1,w)
  let c : Tridegree :=
    (p.1,((p.2-p.1,w)+(0,-(k:ℤ))).1+p.1,((p.2-p.1,w)+(0,-(k:ℤ))).2)
  let d : Tridegree := (p.1,p.2,w-k)
  have hab : a=b := Prod.ext rfl (Prod.ext (sub_add_cancel p.2 p.1).symm rfl)
  have hcd : c=d := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · change (p.2-p.1)+0+p.1=p.2
        omega
      · change w+(-(k:ℤ))=w-k
        omega
  have hin := infinityMapReindex (fun i => (D.family.map f).eInftyMap i) hab
  have hout := infinityMapReindex
    (fun i => (D.family.map ((SyntheticCategory.biShift (0,-(k:ℤ))).map f)).eInftyMap i) hcd
  have h := infinityTowerNatural D (0,-(k:ℤ)) (K k) X Y f (p.2-p.1,w) p.1
  change (D.family.map f).eInftyMap a ≫
      (eqToHom (congrArg (fun i =>
          ((D.family.obj (Y.obj D.nu D.auxiliary)).sequence.ssData i).eInfty) hab) ≫
        (towerInfinityIso (D.convergence Y) (D.convergence (.shift (0,-(k:ℤ)) Y))
          ((K k).filtered Y (p.2-p.1,w)) p.1).hom ≫
        eqToHom (congrArg (fun i =>
          ((D.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) Y).obj D.nu D.auxiliary)).sequence.ssData i).eInfty) hcd)) =
    (eqToHom (congrArg (fun i =>
          ((D.family.obj (X.obj D.nu D.auxiliary)).sequence.ssData i).eInfty) hab) ≫
        (towerInfinityIso (D.convergence X) (D.convergence (.shift (0,-(k:ℤ)) X))
          ((K k).filtered X (p.2-p.1,w)) p.1).hom ≫
        eqToHom (congrArg (fun i =>
          ((D.family.obj ((SyntheticObject.shift (0,-(k:ℤ)) X).obj D.nu D.auxiliary)).sequence.ssData i).eInfty) hcd)) ≫
      (D.family.map ((SyntheticCategory.biShift (0,-(k:ℤ))).map f)).eInftyMap d
  exact infinityTransportedSquare _ _ _ _ _ _ _ _ _ _ h hin hout

/-- Source or comparison proof remains to be supplied. -/
public theorem infinityShift_natural :
  ∀ (X Y : SyntheticObject) (f : X.obj model.nu model.auxiliary ⟶ Y.obj model.nu model.auxiliary)
    (k : ℕ) (p : Bidegree) (w : ℤ),
    (model.family.map f).eInftyMap (p.1,p.2,w) ≫ (infinityShift model infinityShift_comparison Y k p w).hom =
      (infinityShift model infinityShift_comparison X k p w).hom ≫
        (model.family.map ((SyntheticCategory.biShift (0,-(k:ℤ))).map f)).eInftyMap (p.1,p.2,w-k) := by
  exact infinityShiftNatural model infinityShift_comparison

public def infinityShiftData : InfinityShiftCoordinates model where
  comparison := infinityShift_comparison
  natural := infinityShift_natural

public def infinityLambda := InfinityShiftCoordinates.lambdaMap model infinityShiftData

public def infinityFiniteLambda := InfinityShiftCoordinates.finiteLambdaMap model infinityShiftData

public def infinityWeightMap := InfinityShiftCoordinates.weightMap model infinityShiftData

public def infinityNuWindow := EInfinityPresentation.nuWindow model infinityPresentationData

public def infinityFiniteWindow := EInfinityPresentation.finiteWindow model infinityPresentationData

public def infinityNuLinear := EInfinityPresentation.nuLinear model infinityPresentationData

public def infinityFiniteLinear := EInfinityPresentation.finiteLinear model infinityPresentationData

/-- Source or comparison proof remains to be supplied. -/
public theorem eInfinity_nu_labels :
  ∀ (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (z : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w) (nuWeightLabel model X s t w hw x) z ↔
      ∃ hx : x ∈ permanentCycles model X (s,t),
        infinityNuWindow X (s,t) w hw z = subquotientClass (permanentCycles model X (s,t)) (boundaries model X (1+t-w) (s,t)) ⟨x,hx⟩ := by
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
private theorem lambdaNuWeightMap_eq
    (X : KIP126.Kervaire.Route.ClassicalObject) (k : ℕ) (s t w : ℤ)
    (hk : k ≠ 0) (hw : w ≤ t) :
    KIP126.AdamsSynthetic.Standard.weight_map X s t (w-k) w (by omega) hw =
      infinityLambda (.nu X) k (s,t) w := by
  have hnat : (w-(w-(k:ℤ))).toNat = k := by omega
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let δ (j : ℕ) : ℤ × ℤ := (0,-(j:ℤ))
  let p : ℤ × ℤ := (t-s,w)
  let φ (j : ℕ) (hj : w-(j:ℤ) = w-(k:ℤ)) :
      ((model.family.obj A).sequence.ssData (s,t,w)).eInfty ⟶
        ((model.family.obj A).sequence.ssData (s,t,w-k)).eInfty :=
    (eqToIso (congrArg (fun q => ((model.family.obj A).sequence.ssData q).eInfty)
        (show (s,t,w) = (s,p.1+s,p.2) by dsimp only [p]; ext <;> simp (config := { congrConsts := false }))) ≪≫
      towerInfinityIso (model.convergence (.nu X))
        (model.convergence (.shift (δ j) (.nu X)))
        (KIP126.AdamsSynthetic.Standard.shift_filtered (δ j) (.nu X) p) s ≪≫
      eqToIso (congrArg (fun q =>
        ((model.family.obj ((SyntheticCategory.biShift (δ j)).obj A)).sequence.ssData q).eInfty)
        (show (s,(p+δ j).1+s,(p+δ j).2) = (s,t,w-k) by
          dsimp only [p, δ, Prod.fst_add, Prod.snd_add]
          ext <;> simp (config := { congrConsts := false }) only [add_zero, sub_add_cancel]
          omega))).hom ≫
      (model.family.map (lambdaPow j A)).eInftyMap (s,t,w-k)
  have hφ : ∀ (j : ℕ) (hjk : j=k) (hj : w-(j:ℤ) = w-(k:ℤ)),
      φ j hj = φ k rfl := by
    intro j hjk hj
    subst j
    rfl
  have hlambda : infinityLambda (.nu X) k (s,t) w = φ k rfl := by
    exact dif_neg hk
  exact (hφ (w-(w-(k:ℤ))).toNat hnat (by omega)).trans hlambda.symm


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- The same permanent E₂ representative is preserved by the actual λ weight map. -/
public theorem eInfinity_lambda_nu :
  ∀ (X : ClassicalObject) (k : ℕ) (p : Bidegree) (w : ℤ) (hw : w ≤ p.2)
      (x : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty),
    infinityNuWindow X p (w-k) (by omega) (infinityLambda (.nu X) k p w x) =
      permanentQuotientMap model X (by omega) p (infinityNuWindow X p w hw x) := by
  intro X k p w hw z
  rcases p with ⟨s,t⟩
  by_cases hk : k = 0
  · subst k
    dsimp only [infinityLambda, InfinityShiftCoordinates.lambdaMap]
    simp (config := { congrConsts := false }) only [dite_true]
    have htransport : ∀ (v : ℤ) (h : w = v) (hv : v ≤ t)
        (he : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w)).eInfty =
          ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,v)).eInfty),
        HEq (infinityNuWindow X (s,t) v hv ((eqToHom he) z))
          (infinityNuWindow X (s,t) w hw z) := by
      intro v h hv he
      subst v
      rfl
    have hquot : ∀ (v : ℤ) (h : v = w) (hb : 1+t-w ≤ 1+t-v),
        HEq (permanentQuotientMap model X hb (s,t) (infinityNuWindow X (s,t) w hw z))
          (infinityNuWindow X (s,t) w hw z) := by
      intro v h hb
      subst v
      obtain ⟨a, ha⟩ := Quotient.mk_surjective (infinityNuWindow X (s,t) w hw z)
      rw [← ha]
      rfl
    apply eq_of_heq
    exact (htransport (w-((0:ℕ):ℤ)) (by omega) (by omega) _).trans
      (hquot (w-((0:ℕ):ℤ)) (by omega) _).symm
  · obtain ⟨a, ha⟩ := Quotient.mk_surjective (infinityNuWindow X (s,t) w hw z)
    have hrep := (eInfinity_nu_labels X s t w hw a.val z).mpr ⟨a.property, ha.symm⟩
    have hrep' := KIP126.AdamsSynthetic.Standard.weight_representative
      X s t (w-k) w (by omega) hw a.val z hrep
    rw [lambdaNuWeightMap_eq X k s t w hk hw] at hrep'
    obtain ⟨hperm, hleft⟩ :=
      (eInfinity_nu_labels X s t (w-k) (by omega) a.val _).mp hrep'
    calc
      _ = subquotientClass (permanentCycles model X (s,t))
            (boundaries model X (1+t-(w-k)) (s,t)) ⟨a.val,hperm⟩ := hleft
      _ = permanentQuotientMap model X (by omega) (s,t)
            (subquotientClass (permanentCycles model X (s,t))
              (boundaries model X (1+t-w) (s,t)) a) := rfl
      _ = _ := congrArg (permanentQuotientMap model X (by omega) (s,t)) ha

/-- Source or comparison proof remains to be supplied. -/
public theorem eInfinity_lambda_finite :
  ∀ (X : ClassicalObject) (q k : ℕ) (hkq : k < q)
      (p : Bidegree) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < (q-k : ℕ))
      (x : ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)).sequence.ssData (p.1,p.2,w)).eInfty),
    infinityFiniteWindow X q (by omega) p (w-k) (by constructor <;> omega)
        (infinityFiniteLambda X q k hkq p w x) =
      quotientMap model X (by omega) (by omega) p
        (infinityFiniteWindow X (q-k) (by omega) p w hw x) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem eInfinity_finite_labels :
  ∀ (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < q)
      (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (z : ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData (s,t,w)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) x)) z ↔
      ∃ hx : x ∈ cycles model X (q-t+w) (s,t),
        infinityFiniteWindow X q hq (s,t) w hw z = subquotientClass (cycles model X (q-t+w) (s,t)) (boundaries model X (1+t-w) (s,t)) ⟨x,hx⟩ := by
  sorry

private theorem rhoNuLabelSurjective (X : ClassicalObject) (s t w : ℤ) (hw : w ≤ t) :
    Function.Surjective (nuWeightLabel model X s t w hw) := by
  intro a
  let F := free_component X 2 (by omega) s t w (by omega)
  refine ⟨F.hom a, ?_⟩
  apply (ModuleCat.mono_iff_injective F.hom).mp inferInstance
  exact free_e2 X s t w hw (F.hom a)

private theorem rhoInfinityRepresentativeExists (A : SyntheticAdamsSS.{0})
    (i : Tridegree) (e : (A.sequence.ssData i).eInfty) :
    ∃ x : A.Page 2 i, HasInfinityRepresentative A 2 i x e := by
  let D := A.sequence.ssData i
  haveI : Epi (D.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (D.pageπ ⊤)).mp inferInstance e
  exact ⟨(Subobject.ofLE _ _ (D.Z_anti le_top) ≫
    D.pageπ (↑(2-A.sequence.r₀).toNat : WithTop ℕ)) z, by omega, z, rfl, hz⟩

-- The actual SSData morphism sends one common infinite cycle to another.
-- Adapted from Background.infinity_rep_morphism, without importing its private declaration.
private theorem rhoInfinityRepresentativeMorphism
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) Tridegree}
    (f : E ⟶ E') (i : Tridegree) {x : E.Page 2 i} {e : (E.ssData i).eInfty}
    (h : ∃ z : (Subobject.underlying.obj ((E.ssData i).Z ⊤) : ModuleCat ℤ),
      (Subobject.ofLE _ _ ((E.ssData i).Z_anti le_top) ≫
        (E.ssData i).pageπ (↑(2-E.r₀).toNat : WithTop ℕ)) z = x ∧
      (E.ssData i).pageπ ⊤ z = e) :
    ∃ z : (Subobject.underlying.obj ((E'.ssData i).Z ⊤) : ModuleCat ℤ),
      (Subobject.ofLE _ _ ((E'.ssData i).Z_anti le_top) ≫
        (E'.ssData i).pageπ (↑(2-E'.r₀).toNat : WithTop ℕ)) z = f.pageMap 2 i x ∧
      (E'.ssData i).pageπ ⊤ z = f.eInftyMap i e := by
  have hstart := f.r₀_eq
  rcases E with ⟨⟨r₀,D,δ,d⟩,dd,Zs,Bs⟩
  rcases E' with ⟨⟨r₀',D',δ',d'⟩,dd',Zs',Bs'⟩
  dsimp at hstart
  subst r₀'
  obtain ⟨z,hz,he⟩ := h
  let n : WithTop ℕ := ↑(2-r₀).toNat
  refine ⟨f.toSSDataMorphism.cycleMap i ⊤ z, ?_, ?_⟩
  · have hs := f.toSSDataMorphism.cycleMap_ofLE_assoc i
      (r := n) (s := ⊤) le_top ((D' i).pageπ n)
    have hp := f.toSSDataMorphism.pageπ_pageMap i n
    have hq : (Subobject.ofLE ((D i).Z ⊤) ((D i).Z n) ((D i).Z_anti le_top) ≫
        (D i).pageπ n) ≫ f.toSSDataMorphism.pageMap i n =
        f.toSSDataMorphism.cycleMap i ⊤ ≫
          Subobject.ofLE ((D' i).Z ⊤) ((D' i).Z n) ((D' i).Z_anti le_top) ≫ (D' i).pageπ n := by
      rw [Category.assoc,hp]
      exact hs
    change ((Subobject.ofLE _ _ _ ≫ (D' i).pageπ n)
      (f.toSSDataMorphism.cycleMap i ⊤ z)) =
      ((f.toSSDataMorphism.pageMap i n ≫ eqToHom _) x)
    simpa only [ModuleCat.comp_apply, hz, eqToHom_refl, Category.comp_id, n]
      using (ConcreteCategory.congr_hom hq z).symm
  · have hp := f.toSSDataMorphism.pageπ_pageMap i ⊤
    change (D' i).pageπ ⊤ (f.toSSDataMorphism.cycleMap i ⊤ z) =
      f.toSSDataMorphism.pageMap i ⊤ e
    simpa only [ModuleCat.comp_apply, he] using
      (ConcreteCategory.congr_hom hp z).symm

private theorem rhoInfinityRepresentativeMap {X Y : SyntheticSpectrum}
    (g : X ⟶ Y) (i : Tridegree) {x : (model.family.obj X).Page 2 i}
    {e : ((model.family.obj X).sequence.ssData i).eInfty}
    (h : HasInfinityRepresentative (model.family.obj X) 2 i x e) :
    HasInfinityRepresentative (model.family.obj Y) 2 i
      (model.family.pageMap g 2 i x) ((model.family.map g).eInftyMap i e) := by
  obtain ⟨hr,z,hz,he⟩ := h
  obtain ⟨z',hz',he'⟩ := rhoInfinityRepresentativeMorphism (model.family.map g) i ⟨z,hz,he⟩
  exact ⟨hr,z',hz',he'⟩

private theorem rhoFiniteLabelSurjective (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < q) :
    Function.Surjective (fun x =>
      (model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap
        2 (s,t,w) (nuWeightLabel model X s t w (by omega) x)) := by
  haveI := finite_quotient_retained X q hq s t w hw
  exact ((ModuleCat.epi_iff_surjective _).mp inferInstance).comp
    (rhoNuLabelSurjective X s t w (by omega))

private theorem rhoFiniteLabelMap (X : ClassicalObject) (i j : ℕ) (hij : i ≤ j)
    (s t w : ℤ) (a : (model.family.nu model.nu (X.obj model.auxiliary)).Page 2 (s,t,w)) :
    model.family.pageMap
        ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho i j hij)
        2 (s,t,w)
        ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) j).pageMap
          2 (s,t,w) a) =
      (model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) i).pageMap
        2 (s,t,w) a := by
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  let rho := (model.quotients.tower V).rho i j hij
  change (((model.family.map (XModLambdaN.incl V j)).pageMap 2 (s,t,w)) ≫
    (model.family.map rho).pageMap 2 (s,t,w)) a = _
  rw [← SpectralSequenceMorphism.pageMap_comp, ← model.family.map_comp,
    (model.quotients.tower V).rho_quotient hij]
  rfl

/-- Restriction preserves the common infinite representative and its quotient class. -/
public theorem eInfinity_rho_finite :
  ∀ (X : ClassicalObject) (i j : ℕ) (hi : 0 < i) (hij : i ≤ j)
      (p : Bidegree) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < i)
      (x : ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) j).sequence.ssData (p.1,p.2,w)).eInfty),
    infinityFiniteWindow X i hi p w hw
        ((model.family.map ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho i j hij)).eInftyMap (p.1,p.2,w) x) =
      quotientMap model X (by omega) le_rfl p
        (infinityFiniteWindow X j (by omega) p w (by constructor <;> omega) x) := by
  intro X i j hi hij p w hw z
  rcases p with ⟨s,t⟩
  have hj : 0 < j := by omega
  have hwj : 0 ≤ t-w ∧ t-w < j := by constructor <;> omega
  obtain ⟨a,ha⟩ := rhoInfinityRepresentativeExists
    (model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) j) (s,t,w) z
  obtain ⟨x,hx⟩ := rhoFiniteLabelSurjective X j hj s t w hwj a
  rw [← hx] at ha
  obtain ⟨hxj,hfinitej⟩ := (eInfinity_finite_labels X j hj s t w hwj x z).mp ha
  have hmap := rhoInfinityRepresentativeMap
    ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho i j hij) (s,t,w) ha
  have hmap' : HasInfinityRepresentative
      (model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) i) 2 (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) i).pageMap
        2 (s,t,w) (nuWeightLabel model X s t w (by omega) x))
      ((model.family.map
        ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho i j hij)).eInftyMap
        (s,t,w) z) := by
    have heq := rhoFiniteLabelMap X i j hij s t w (nuWeightLabel model X s t w (by omega) x)
    exact Eq.mp (congrArg (fun a => HasInfinityRepresentative
      (model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) i) 2 (s,t,w) a
      ((model.family.map
        ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho i j hij)).eInftyMap
        (s,t,w) z)) heq) hmap
  obtain ⟨hxi,hfinitei⟩ := (eInfinity_finite_labels X i hi s t w hw x _).mp hmap'
  calc
    _ = subquotientClass (KIP126.Literature.cycles model X (i-t+w) (s,t))
        (KIP126.Literature.boundaries model X (1+t-w) (s,t)) ⟨x,hxi⟩ := hfinitei
    _ = KIP126.Literature.quotientMap model X (by omega) le_rfl (s,t)
        (subquotientClass (KIP126.Literature.cycles model X (j-t+w) (s,t))
          (KIP126.Literature.boundaries model X (1+t-w) (s,t)) ⟨x,hxj⟩) := rfl
    _ = _ := congrArg (KIP126.Literature.quotientMap model X (by omega) le_rfl (s,t)) hfinitej.symm

/-- Projection from nu preserves the common infinite representative and its quotient class. -/
public theorem eInfinity_rho_nu :
  ∀ (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (p : Bidegree) (w : ℤ) (hw : 0 ≤ p.2-w ∧ p.2-w < q)
      (x : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (p.1,p.2,w)).eInfty),
    infinityFiniteWindow X q hq p w hw
        ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).eInftyMap (p.1,p.2,w) x) =
      permanentToFinite model X (q-p.2+w) (1+p.2-w) p
        (infinityNuWindow X p w (by omega) x) := by
  intro X q hq p w hw z
  rcases p with ⟨s,t⟩
  obtain ⟨a,ha⟩ := rhoInfinityRepresentativeExists (model.family.nu model.nu (X.obj model.auxiliary)) (s,t,w) z
  obtain ⟨x,hx⟩ := rhoNuLabelSurjective X s t w (by omega) a
  rw [← hx] at ha
  obtain ⟨hxperm,hnu⟩ := (eInfinity_nu_labels X s t w (by omega) x z).mp ha
  have hmap := rhoInfinityRepresentativeMap
    (XModLambdaN.incl (model.nu.functor.obj (X.obj model.auxiliary)) q) (s,t,w) ha
  obtain ⟨hxcycle,hfinite⟩ := (eInfinity_finite_labels X q hq s t w hw x _).mp hmap
  calc
    _ = subquotientClass (KIP126.Literature.cycles model X (q-t+w) (s,t))
        (KIP126.Literature.boundaries model X (1+t-w) (s,t)) ⟨x,hxcycle⟩ := hfinite
    _ = permanentToFinite model X (q-t+w) (1+t-w) (s,t)
        (subquotientClass (KIP126.Literature.permanentCycles model X (s,t))
          (KIP126.Literature.boundaries model X (1+t-w) (s,t)) ⟨x,hxperm⟩) := rfl
    _ = _ := congrArg (permanentToFinite model X (q-t+w) (1+t-w) (s,t)) hnu.symm

private def infinityCompatibilityData : EInfinityCompatibility model infinityPresentationData infinityShiftData where
  lambda_nu := eInfinity_lambda_nu
  lambda_finite := eInfinity_lambda_finite
  rho_finite := eInfinity_rho_finite
  rho_nu := eInfinity_rho_nu
  nu_labels := eInfinity_nu_labels
  finite_labels := eInfinity_finite_labels

public abbrev infinityLambda_zero := InfinityShiftCoordinates.lambdaMap_zero model infinityShiftData

public abbrev infinityFiniteLambda_zero := InfinityShiftCoordinates.finiteLambdaMap_zero model infinityShiftData

/-- Derived from the fixed objects and previously established operations. -/
public theorem infinityLambda_epi :
  ∀ (X : ClassicalObject) (k : ℕ) (p : Bidegree) (w : ℤ), w ≤ p.2 →
    Epi (infinityLambda (.nu X) k p w) := EInfinityCompatibility.lambda_epi model infinityCompatibilityData

/-- Derived from the fixed objects and previously established operations. -/
public theorem infinityWeightMap_epi :
  ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂), w₂ ≤ t →
    Epi (infinityWeightMap X s t w₁ w₂ hw) := EInfinityCompatibility.weight_epi model infinityCompatibilityData

set_option backward.isDefEq.respectTransparency false in
private theorem lambdaRegradedWindowClass
    (X : ClassicalObject) (s t w₁ w₂ : ℤ) (k : ℕ)
    (h : w₂-k = w₁)
    (transport :
      ((model.family.obj ((SyntheticObject.nu X).obj model.nu model.auxiliary)).sequence.ssData
        (s,t,w₂-k)).eInfty =
      ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w₁)).eInfty)
    (ht : w₂ ≤ t) (x : KIP126.Literature.permanentCycles model X (s,t))
    (z : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w₂)).eInfty)
    (hz : infinityNuWindow X (s,t) w₂ ht z =
      subquotientClass (KIP126.Literature.permanentCycles model X (s,t))
        (KIP126.Literature.boundaries model X (1+t-w₂) (s,t)) x) :
    infinityNuWindow X (s,t) w₁ (by omega)
      ((InfinityShiftCoordinates.lambdaMap model infinityShiftData (.nu X) k (s,t) w₂ ≫
        eqToHom transport) z) =
      subquotientClass (KIP126.Literature.permanentCycles model X (s,t))
        (KIP126.Literature.boundaries model X (1+t-w₁) (s,t)) x := by
  subst w₁
  let f := InfinityShiftCoordinates.lambdaMap model infinityShiftData (.nu X) k (s,t) w₂
  have hcast : eqToHom transport =
      𝟙 (((model.family.obj ((SyntheticObject.nu X).obj model.nu model.auxiliary)).sequence.ssData
        ((s,t).1,(s,t).2,w₂-k)).eInfty) := by
    rfl
  have hmap : f ≫ eqToHom transport = f :=
    (congrArg (fun q => f ≫ q) hcast).trans (Category.comp_id f)
  calc
    _ = infinityNuWindow X (s,t) (w₂-k) (by omega)
        (infinityLambda (.nu X) k (s,t) w₂ z) :=
      congrArg (fun (g :
        ((model.family.obj ((SyntheticObject.nu X).obj model.nu model.auxiliary)).sequence.ssData
          ((s,t).1,(s,t).2,w₂)).eInfty ⟶
        ((model.family.obj ((SyntheticObject.nu X).obj model.nu model.auxiliary)).sequence.ssData
          ((s,t).1,(s,t).2,w₂-k)).eInfty) =>
        infinityNuWindow X (s,t) (w₂-k) (by omega) (g z)) hmap
    _ = permanentQuotientMap model X (by omega) (s,t)
        (infinityNuWindow X (s,t) w₂ ht z) :=
      eInfinity_lambda_nu X k (s,t) w₂ ht z
    _ = permanentQuotientMap model X (by omega) (s,t)
        (subquotientClass (KIP126.Literature.permanentCycles model X (s,t))
          (KIP126.Literature.boundaries model X (1+t-w₂) (s,t)) x) :=
      congrArg (permanentQuotientMap model X (by omega) (s,t)) hz
    _ = _ := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem weightWindowClass
    (X : ClassicalObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t)
    (x : KIP126.Literature.permanentCycles model X (s,t))
    (z : ((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w₂)).eInfty)
    (hz : infinityNuWindow X (s,t) w₂ ht z =
      subquotientClass (KIP126.Literature.permanentCycles model X (s,t))
        (KIP126.Literature.boundaries model X (1+t-w₂) (s,t)) x) :
    infinityNuWindow X (s,t) w₁ (hw.trans ht)
      (infinityWeightMap X s t w₁ w₂ hw z) =
      subquotientClass (KIP126.Literature.permanentCycles model X (s,t))
        (KIP126.Literature.boundaries model X (1+t-w₁) (s,t)) x := by
  unfold infinityWeightMap InfinityShiftCoordinates.weightMap
  exact lambdaRegradedWindowClass X s t w₁ w₂ (w₂-w₁).toNat (by omega) _ ht x z hz

set_option backward.isDefEq.respectTransparency false in
private theorem weightsLambdaImpl :
  ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    KIP126.AdamsSynthetic.Standard.weight_map X s t w₁ w₂ hw ht =
      infinityWeightMap X s t w₁ w₂ hw := by
  intro X s t w₁ w₂ hw ht
  ext z
  obtain ⟨x, hx⟩ := Quotient.mk_surjective (infinityNuWindow X (s,t) w₂ ht z)
  have hz : infinityNuWindow X (s,t) w₂ ht z =
      subquotientClass (KIP126.Literature.permanentCycles model X (s,t))
        (KIP126.Literature.boundaries model X (1+t-w₂) (s,t)) x := hx.symm
  have hrep := (eInfinity_nu_labels X s t w₂ ht x.val z).mpr ⟨x.property, hz⟩
  have hweight := KIP126.AdamsSynthetic.Standard.weight_representative
    X s t w₁ w₂ hw ht x.val z hrep
  obtain ⟨hpermanent, hleft⟩ :=
    (eInfinity_nu_labels X s t w₁ (hw.trans ht) x.val _).mp hweight
  apply (infinityNuWindow X (s,t) w₁ (hw.trans ht)).injective
  exact hleft.trans (weightWindowClass X s t w₁ w₂ hw ht x z hz).symm

/-- The registered weight operation equals the actual lambda weight map:
both send the same permanent E₂ representative to its larger boundary quotient. -/
public theorem weights_lambda :
  ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    KIP126.AdamsSynthetic.Standard.weight_map X s t w₁ w₂ hw ht =
      infinityWeightMap X s t w₁ w₂ hw := weightsLambdaImpl

/-- Derived from the fixed objects and previously established operations. -/
public theorem weight_epi :
  ∀ (X : ClassicalObject) (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    Epi (KIP126.AdamsSynthetic.Standard.weight_map X s t w₁ w₂ hw ht) := by
  intro X s t w₁ w₂ hw ht
  rw [weights_lambda]
  exact infinityWeightMap_epi X s t w₁ w₂ hw ht

/-- Source or comparison proof remains to be supplied. -/
public theorem unshifted :
  ∀ T : TriangleData model.auxiliary,
    normalizedExponent model.classicalTower T.f +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1 →
    ∃ (f : model.nu.functor.obj (T.X.obj model.auxiliary) ⟶ model.nu.functor.obj (T.Y.obj model.auxiliary))
      (g : model.nu.functor.obj (T.Y.obj model.auxiliary) ⟶ model.nu.functor.obj (T.Z.obj model.auxiliary))
      (h : model.nu.functor.obj (T.Z.obj model.auxiliary) ⟶
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).obj (model.nu.functor.obj (T.X.obj model.auxiliary))),
      Triangle.mk f g h ∈ distTriang SyntheticSpectrum := by
  sorry

/-- The fixed mathematical object on the project background. -/
public def normalized_cofiber :
  ∀ T : TriangleData model.auxiliary, NormalizedCofiberComparison model T := by
  sorry

public def normalizedCofiberTriangle (T : TriangleData model.auxiliary) :=
  NormalizedCofiberComparison.triangle model (normalized_cofiber T)

public abbrev normalizedCofiberTriangle_distinguished (T : TriangleData model.auxiliary) :=
  NormalizedCofiberComparison.distinguished model (normalized_cofiber T)

/-- Adapted from the actual filtration witness argument in a484b981,
Main/AdamsSynthetic/NuSource/FromSuspension.lean:805–821. -/
public theorem nuCofiber_nu_exponent :
  normalizedExponent model.classicalTower model.auxiliary.nuMap = 1 := by
  classical
  obtain ⟨_, _, b, hb, _⟩ := nu_detection
  have hmem : model.auxiliary.nuMap ∈ ModuleCat.subobjectModule _
      ((model.classicalTower.tower SphereSpectrum).filtration.F 1 3) := by
    change ∃ b, ((model.classicalTower.tower SphereSpectrum).filtration.F 1 3).arrow.hom b = _
    exact ⟨b, hb⟩
  simp only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] at hmem
  obtain ⟨lift, hlift⟩ := hmem
  have hF : MapFiltrationAtLeast model.classicalTower model.auxiliary.nuMap 1 :=
    ⟨lift, hlift⟩
  change (if MapFiltrationAtLeast model.classicalTower model.auxiliary.nuMap 1 then 1 else 0) = 1
  exact if_pos hF

section
set_option backward.isDefEq.respectTransparency false

/- a48 FromSuspension:822–875.  The old ring-dependent strict tensor-zero
argument is replaced by the current fixed factorization-filtration theorem,
which gives exactly the vanishing on represented HF₂ homology needed here. -/
private theorem nuFactorizationZeroOnHomology {X Y : Spectrum} {n : ℕ}
    {f : X ⟶ Y} (h : AdamsMapFactorization model.coefficients n f) :
    ZeroOnModTwoHomology model.coefficients f := by
  cases h with
  | single f hf => exact hf
  | prepend f g hf hg =>
      intro i x
      change x ≫ (model.coefficients.object ◁ (f ≫ g)) = 0
      rw [whiskerLeft_comp, ← Category.assoc]
      change modTwoHomologyMap model.coefficients f i x ≫ _ = 0
      rw [hf i x, zero_comp]

private theorem nuPositiveFiltrationZeroOnRightHomology {X Y : Spectrum}
    (f : X ⟶ Y) (hf : MapFiltrationAtLeast model.classicalTower f 1)
    (i : ℤ) (x : HomotopyGroup i (X ⊗ model.coefficients.object)) :
    x ≫ (f ▷ model.coefficients.object) = 0 := by
  letI := KIP126.AdamsSynthetic.Standard.closedBackground.symmetric
  have hF : FactorizationFiltration model.coefficients f 1 :=
    (KIP126.AdamsSynthetic.Standard.factorization_filtration_iff f 1).mpr hf
  have hz := nuFactorizationZeroOnHomology (hF 1 (by decide) (by decide))
  apply (cancel_mono (β_ Y model.coefficients.object).hom).mp
  rw [Category.assoc, BraidedCategory.braiding_naturality_left,
    ← Category.assoc]
  change modTwoHomologyMap model.coefficients f i
    (x ≫ (β_ X model.coefficients.object).hom) = _
  rw [hz, zero_comp]

private theorem nuCoefficientUnitNonzero : model.coefficients.unit ≠ 0 := by
  intro h
  have h0 : model.coefficients.pi0Equiv.symm 1 = 0 := by
    dsimp only [ModTwoCoefficients.unit] at h
    have hh := congrArg
      (fun z => (shiftFunctorZero Spectrum ℤ).hom.app SphereSpectrum ≫ z) h
    simpa (config := { congrConsts := false }) only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp,
      comp_zero] using hh
  have h10 : (1 : ZMod 2) = 0 := by
    simpa (config := { congrConsts := false }) only [AddEquiv.apply_symm_apply, map_zero] using
      congrArg model.coefficients.pi0Equiv h0
  exact one_ne_zero h10

private theorem nuCofiberCellExponents :
    normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g = 0 ∧
    normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h = 0 := by
  let B := KIP126.AdamsSynthetic.Standard.closedBackground
  let H := model.coefficients.object
  let F := tensorRight H
  letI := B.tensorShift H
  letI := B.tensorExact H
  let T := F.mapTriangle.obj
    (Triangle.mk model.auxiliary.nuMap
      (HasFunctorialCofiber.cofibι model.auxiliary.nuMap)
      (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap))
  have hT : T ∈ distTriang Spectrum :=
    F.map_distinguished _ (HasFunctorialCofiber.cofib_distinguished _)
  have hF : MapFiltrationAtLeast model.classicalTower model.auxiliary.nuMap 1 := by
    classical
    have h := nuCofiber_nu_exponent
    change (if MapFiltrationAtLeast model.classicalTower model.auxiliary.nuMap 1
      then 1 else 0) = 1 at h
    by_contra hn
    simp (config := { congrConsts := false }) only [if_neg hn] at h
    contradiction
  have hf (i : ℤ) (x : HomotopyGroup i T.obj₁) : x ≫ T.mor₁ = 0 :=
    nuPositiveFiltrationZeroOnRightHomology _ hF i x
  have hbottom : ¬ MapFiltrationAtLeast model.classicalTower
      model.auxiliary.nuRouteTriangle.g 1 := by
    intro hg
    let a : HomotopyGroup 0 T.obj₂ :=
      model.coefficients.pi0Equiv.symm 1 ≫ (λ_ H).inv
    have ha : a ≠ 0 := by
      intro hz
      have h0 : model.coefficients.pi0Equiv.symm 1 = 0 := by
        have hh := congrArg (fun z => z ≫ (λ_ H).hom) hz
        simpa (config := { congrConsts := false }) only [a, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          zero_comp] using hh
      have h10 : (1 : ZMod 2) = 0 := by
        simpa (config := { congrConsts := false }) only [AddEquiv.apply_symm_apply, map_zero] using
          congrArg model.coefficients.pi0Equiv h0
      exact one_ne_zero h10
    have hag : a ≫ T.mor₂ = 0 :=
      nuPositiveFiltrationZeroOnRightHomology _ hg 0 a
    obtain ⟨b, hb⟩ := T.coyoneda_exact₂ hT a hag
    exact ha (hb.trans (hf 0 b))
  have htop : ¬ MapFiltrationAtLeast model.classicalTower
      model.auxiliary.nuRouteTriangle.h 1 := by
    intro hh
    let a₃ : HomotopyGroup 3 T.obj₁ :=
      (shiftFunctor Spectrum (3 : ℤ)).map model.coefficients.unit ≫
        (B.sphereTensorShift 3 H).inv
    have ha₃ : a₃ ≠ 0 := by
      intro hz
      have hu : (shiftFunctor Spectrum (3 : ℤ)).map model.coefficients.unit = 0 := by
        have h := congrArg (fun z => z ≫ (B.sphereTensorShift 3 H).hom) hz
        simpa (config := { congrConsts := false }) only [a₃, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          zero_comp] using h
      apply nuCoefficientUnitNonzero
      apply (shiftFunctor Spectrum (3 : ℤ)).map_injective
      rw [Functor.map_zero]
      exact hu
    let a₄ : HomotopyGroup 4 (T.obj₁⟦(1 : ℤ)⟧) :=
      (shiftFunctorAdd' Spectrum (3 : ℤ) 1 4 (by norm_num)).hom.app SphereSpectrum ≫
        (shiftFunctor Spectrum (1 : ℤ)).map a₃
    have ha₄ : a₄ ≠ 0 := by
      intro hz
      have h : (shiftFunctor Spectrum (1 : ℤ)).map a₃ = 0 := by
        apply (cancel_epi
          ((shiftFunctorAdd' Spectrum (3 : ℤ) 1 4 (by norm_num)).hom.app SphereSpectrum)).mp
        simpa (config := { congrConsts := false }) only [a₄, comp_zero] using hz
      apply ha₃
      apply (shiftFunctor Spectrum (1 : ℤ)).map_injective
      rw [Functor.map_zero]
      exact h
    have haf : a₄ ≫ (shiftFunctor Spectrum (1 : ℤ)).map T.mor₁ = 0 := by
      dsimp only [a₄]
      rw [Category.assoc, ← Functor.map_comp, hf 3 a₃,
        Functor.map_zero, comp_zero]
    obtain ⟨b, hb⟩ := T.coyoneda_exact₁ hT a₄ haf
    have hbh : b ≫ T.mor₃ = 0 := by
      change b ≫ ((model.auxiliary.nuRouteTriangle.h ▷ H) ≫ _) = 0
      rw [← Category.assoc]
      have hz := nuPositiveFiltrationZeroOnRightHomology
        model.auxiliary.nuRouteTriangle.h hh 4 b
      change b ≫ (model.auxiliary.nuRouteTriangle.h ▷ H) = 0 at hz
      rw [hz, zero_comp]
    exact ha₄ (hb.trans hbh)
  classical
  dsimp only [normalizedExponent]
  simp (config := { congrConsts := false }) only [if_neg hbottom, if_neg htop, and_self]

end

/-- Adapted from a48 FromSuspension:822–875 using the fixed homology-factorization
comparison and exact tensor structure of this same Adams model. -/
public theorem nuCofiber_bottom_exponent :
  normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g = 0 :=
  nuCofiberCellExponents.1

/-- The top cell has filtration exponent zero by the same actual Cν triangle. -/
public theorem nuCofiber_top_exponent :
  normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h = 0 :=
  nuCofiberCellExponents.2

/-- Source or comparison proof remains to be supplied. -/
public theorem nuCofiber_normalized_label :
  sphereFirstQuotient model 1 4 (quotientClass 1 (normalizedNu model nuCofiber_nu_exponent)) =
    model.standardClasses.standardHi 2 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem nuCofiber_triangle :
  ∀ he :
      (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.f : ℤ) +
        normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g +
        normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h = 1,
    NormalizedTriangleCompatible model model.auxiliary.nuRouteTriangle he := by
  sorry

private def nuCofiberData : NuCofiberApplicability model where
  nu_exponent := nuCofiber_nu_exponent
  bottom_exponent := nuCofiber_bottom_exponent
  top_exponent := nuCofiber_top_exponent
  normalized_label := nuCofiber_normalized_label
  triangle := nuCofiber_triangle

/-- Derived from the fixed objects and previously established operations. -/
public theorem nuCofiber_exponent_sum :
  (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.f : ℤ) +
    normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g +
    normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h = 1 := NuCofiberApplicability.exponent_sum model nuCofiberData

/-- Derived from the fixed objects and previously established operations. -/
public theorem nuCofiber_distinguished :
  normalizedTriangle model model.auxiliary.nuRouteTriangle nuCofiber_exponent_sum ∈ distTriang SyntheticSpectrum := nuCofiber_triangle _

/-- Source or comparison proof remains to be supplied. -/
public theorem nu_cofiber :
  NuCofiberCriterion model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem lift :
  SyntheticLiftComparison model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem triangle_lift :
  SyntheticTriangleLiftComparison model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bhs_finite_lift :
  FiniteLiftCriterion model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bhs_bockstein :
  BocksteinDifferential model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bhs_differentials :
  DifferentialRigidity model := by
  sorry

public def realizeNu := realizeNuZero model realizationData

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_permanent_lift :
  ∀ X : ClassicalObject, PermanentLiftAt model X := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_filtration_lambda :
  ∀ X : ClassicalObject, FiltrationLambdaAt model X := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_realization_lifetime :
  ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (a : BiHom (t-s) t (nuZero model X)),
    ClassicalPermanentCycle model X (s,t) x →
    SurvivesTo (model.classical.obj (X.obj model.auxiliary)) (r+1) (s,t) x →
    quotientClass 1 a = firstLabel model X s t x → lambdaMultiply (r-1) a ≠ 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_realization_detection :
  ∀ (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) t (nuZero model X)),
    NonzeroSurvival (model.classical.obj (X.obj model.auxiliary)) (s,t) x →
    quotientClass 1 a = firstLabel model X s t x →
    ClassicalDetects (model.classicalConvergence X) (s,t) x (realizeNu X a) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_realization_prescribed_lift :
  ∀ (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (a : HomotopyGroup (t-s) (X.obj model.auxiliary)),
    NonzeroSurvival (model.classical.obj (X.obj model.auxiliary)) (s,t) x →
    ClassicalDetects (model.classicalConvergence X) (s,t) x a →
    ∃ b : BiHom (t-s) t (nuZero model X), quotientClass 1 b = firstLabel model X s t x ∧
      realizeNu X b = a := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_realization_boundary_lift :
  ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ y : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t),
    ClassicalPermanentCycle model X (s,t) y →
    HitOnPage (model.classical.obj (X.obj model.auxiliary)) r (s,t) y →
    ∃ a : BiHom (t-s) t (nuZero model X), quotientClass 1 a = firstLabel model X s t y ∧
      lambdaMultiply (r-1) a = 0 := by
  sorry

/-- Specialization of the registered selected-object comparison; the same object
and all source applicability hypotheses are retained. The selected comparison
remains a separate construction obligation. -/
public theorem bhs_permanent_lift :
  ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ Spectrum),
    BHSObjectApplicability model products (X.obj model.auxiliary) → PermanentLiftAt model X := by
  intro X _ _
  exact selected_permanent_lift X

/-- Specialization of the registered selected-object comparison; the same object
and all source applicability hypotheses are retained. The selected comparison
remains a separate construction obligation. -/
public theorem bhs_filtration_lambda :
  ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ Spectrum),
    BHSObjectApplicability model products (X.obj model.auxiliary) → FiltrationLambdaAt model X := by
  intro X _ _
  exact selected_filtration_lambda X



/-- Source or comparison proof remains to be supplied. -/
public theorem selected_realization_kernel :
  RealizationKernel model := by
  sorry


/-- Specialization of the registered selected-object comparison; the same object
and all source applicability hypotheses are retained. The selected comparison
remains a separate construction obligation. -/
public theorem bhs_realization_lifetime :
  ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ Spectrum),
    BHSObjectApplicability model products (X.obj model.auxiliary) →
    ∀ (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (a : BiHom (t-s) t (nuZero model X)),
    ClassicalPermanentCycle model X (s,t) x →
    SurvivesTo (model.classical.obj (X.obj model.auxiliary)) (r+1) (s,t) x →
    quotientClass 1 a = firstLabel model X s t x → lambdaMultiply (r-1) a ≠ 0 := by
  intro X _ _
  exact selected_realization_lifetime X

/-- Specialization of the registered selected-object comparison; the same object
and all source applicability hypotheses are retained. The selected comparison
remains a separate construction obligation. -/
public theorem bhs_realization_detection :
  ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ Spectrum),
    BHSObjectApplicability model products (X.obj model.auxiliary) →
    ∀ (s t : ℤ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (a : BiHom (t-s) t (nuZero model X)),
    NonzeroSurvival (model.classical.obj (X.obj model.auxiliary)) (s,t) x →
    quotientClass 1 a = firstLabel model X s t x →
    ClassicalDetects (model.classicalConvergence X) (s,t) x (realizeNu X a) := by
  intro X _ _
  exact selected_realization_detection X

/-- Specialization of the registered selected-object comparison; the same object
and all source applicability hypotheses are retained. The selected comparison
remains a separate construction obligation. -/
public theorem bhs_realization_prescribed_lift :
  ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ Spectrum),
    BHSObjectApplicability model products (X.obj model.auxiliary) →
    ∀ (s t : ℤ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (a : HomotopyGroup (t-s) (X.obj model.auxiliary)),
    NonzeroSurvival (model.classical.obj (X.obj model.auxiliary)) (s,t) x →
    ClassicalDetects (model.classicalConvergence X) (s,t) x a →
    ∃ b : BiHom (t-s) t (nuZero model X), quotientClass 1 b = firstLabel model X s t x ∧
      realizeNu X b = a := by
  intro X _ _
  exact selected_realization_prescribed_lift X

/-- Specialization of the registered selected-object comparison; the same object
and all source applicability hypotheses are retained. The selected comparison
remains a separate construction obligation. -/
public theorem bhs_realization_boundary_lift :
  ∀ (X : ClassicalObject) (products : HasProductsOfShape ℕ Spectrum),
    BHSObjectApplicability model products (X.obj model.auxiliary) →
    ∀ (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ y : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t),
    ClassicalPermanentCycle model X (s,t) y →
    HitOnPage (model.classical.obj (X.obj model.auxiliary)) r (s,t) y →
    ∃ a : BiHom (t-s) t (nuZero model X), quotientClass 1 a = firstLabel model X s t y ∧
      lambdaMultiply (r-1) a = 0 := by
  intro X _ _
  exact selected_realization_boundary_lift X




set_option backward.isDefEq.respectTransparency false in
private theorem absorbedTheta5Lift :
  ∃ a : BiHom 62 64 (S_0_0 : SyntheticSpectrum),
    KIP126.Literature.Theta5Detected model a ∧ realizeSphere 62 64 a = theta5 := by
  obtain ⟨b, hb, hr⟩ := selected_realization_prescribed_lift .sphere 2 64
    (model.standardClasses.standardHiSquare 5) theta5
    h5Square_permanent theta5_detection
  change BiHom 62 64 (KIP126.Literature.nuZero model .sphere) at b
  change (realization_sphere 62 64).hom ≫ model.recovery.realization.map b ≫
      model.recovery.realization.map (SyntheticCategory.biShift_zero.hom.app _) ≫
      model.recovery.nuRealizationIso.hom.app SphereSpectrum = theta5 at hr
  let e : KIP126.Literature.nuZero model .sphere ≅ (S_0_0 : SyntheticSpectrum) :=
    SyntheticCategory.biShift_zero.app _ ≪≫ model.nu.unitIso
  let a : BiHom 62 64 (S_0_0 : SyntheticSpectrum) := b ≫ e.hom
  have hq : quotientClass 1 a ≫ XModLambdaN.map e.inv 1 = quotientClass 1 b := by
    dsimp only [a, quotientClass]
    simp (config := { congrConsts := false }) only [Category.assoc]
    rw [← XModLambdaN.incl_naturality]
    simp (config := { congrConsts := false }) only [Category.assoc, Iso.hom_inv_id_assoc]
  refine ⟨a, ?_, ?_⟩
  · change (model.firstQuotient .sphere 0 2 64)
      (quotientClass 1 a ≫ XModLambdaN.map e.inv 1) = _
    rw [hq]
    have hb' : quotientClass 1 b =
        (model.firstQuotient .sphere 0 2 64).symm
          (model.standardClasses.standardHiSquare 5) := hb
    rw [hb']
    exact (model.firstQuotient .sphere 0 2 64).apply_symm_apply _
  · have hu : model.recovery.realization.map e.hom ≫
        model.recovery.realization.map model.nu.unitIso.inv =
        model.recovery.realization.map
          (SyntheticCategory.biShift_zero.hom.app
            (model.nu.functor.obj SphereSpectrum)) := by
      have hu0 : e.hom ≫ model.nu.unitIso.inv =
          SyntheticCategory.biShift_zero.hom.app
            (model.nu.functor.obj SphereSpectrum) :=
        (Category.assoc
          (SyntheticCategory.biShift_zero.hom.app
            (model.nu.functor.obj SphereSpectrum))
          model.nu.unitIso.hom model.nu.unitIso.inv).trans
          ((congrArg (fun k =>
              SyntheticCategory.biShift_zero.hom.app
                (model.nu.functor.obj SphereSpectrum) ≫ k)
            model.nu.unitIso.hom_inv_id).trans (Category.comp_id _))
      exact (model.recovery.realization.map_comp e.hom model.nu.unitIso.inv).symm.trans
        (congrArg (fun f => model.recovery.realization.map f) hu0)
    change (realization_sphere 62 64).hom ≫
      model.recovery.realization.map (b ≫ e.hom) ≫
      model.recovery.realization.map model.nu.unitIso.inv ≫
      model.recovery.nuRealizationIso.hom.app SphereSpectrum = theta5
    calc
      _ = (realization_sphere 62 64).hom ≫ model.recovery.realization.map b ≫
          (model.recovery.realization.map e.hom ≫
            model.recovery.realization.map model.nu.unitIso.inv) ≫
          model.recovery.nuRealizationIso.hom.app SphereSpectrum := by
        rw [Functor.map_comp]
        simp (config := { congrConsts := false }) only [Category.assoc]
      _ = _ := by rw [hu]; exact hr

/-- The prescribed realization lift, transported by the specified ν-unit isomorphism.
The same classical θ₅ and the same prescribed witness are retained. -/
public theorem theta5_lift :
  ∃ a : BiHom 62 64 (S_0_0 : SyntheticSpectrum),
    Theta5Detected model a ∧ realizeSphere 62 64 a = theta5 := absorbedTheta5Lift

/-- Derived from the fixed objects and previously established operations. -/
public theorem theta5_detected_exists :
  ∃ a : BiHom 62 64 (S_0_0 : SyntheticSpectrum), Theta5Detected model a := by
  obtain ⟨a, ha, _⟩ := theta5_lift
  exact ⟨a, ha⟩


/-- The fixed mathematical object on the project background. -/
public def bxTheta5 :
  BiHom 62 64 (S_0_0 : SyntheticSpectrum) := by
  sorry

/-- Derived from the fixed objects and previously established operations. -/
public theorem bx_eta_label :
  sphereFirstQuotient model 1 2 (quotientClass 1 eta) = model.standardClasses.standardHi 1 := eta_label

/-- Source or comparison proof remains to be supplied. -/
public theorem bx_theta_label :
  Theta5Detected model bxTheta5 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bx_order_two :
  bxTheta5 + bxTheta5 = 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bx_finite :
  ∀ r : ℕ, 1 ≤ r →
    (SurvivesTo model.classical.sphere ((r : ℤ)+3) (2,128)
      model.standardClasses.standardH6Square ↔ quotientClass r (etaThetaSquare eta bxTheta5) = 0) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bx_total_boundary :
  deltaH6Square model = lambdaEtaThetaSquare eta bxTheta5 := by
  sorry

section BxUntruncatedConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem sphereLiftIff (x : model.classical.sphere.Page 2 (2,128)) :
    ClassicalPermanentCycle model .sphere (2,128) x ↔
      ∃ a : BiHom 126 128 (S_0_0 : SyntheticSpectrum),
        sphereFirstQuotient model 2 128 (quotientClass 1 a) = x := by
  let e : nuZero model .sphere ≅ (S_0_0 : SyntheticSpectrum) :=
    SyntheticCategory.biShift_zero.app _ ≪≫ model.nu.unitIso
  constructor
  · intro hx
    obtain ⟨b,hb⟩ := (selected_permanent_lift .sphere 2 128 x).mp hx
    let a := b ≫ e.hom
    have hq : quotientClass 1 a ≫ XModLambdaN.map e.inv 1 = quotientClass 1 b := by
      dsimp only [a, quotientClass]
      simp only [Category.assoc]
      rw [← XModLambdaN.incl_naturality]
      simp only [Iso.hom_inv_id_assoc]
    refine ⟨a, ?_⟩
    change (model.firstQuotient .sphere 0 2 128)
      (quotientClass 1 a ≫ XModLambdaN.map e.inv 1) = x
    rw [hq, hb]
    exact (model.firstQuotient .sphere 0 2 128).apply_symm_apply x
  · rintro ⟨a,ha⟩
    apply (selected_permanent_lift .sphere 2 128 x).mpr
    refine ⟨a ≫ e.inv, ?_⟩
    have hq : quotientClass 1 (a ≫ e.inv) =
        quotientClass 1 a ≫ XModLambdaN.map e.inv 1 := by
      dsimp only [quotientClass]
      rw [Category.assoc, XModLambdaN.incl_naturality]
      simp only [Category.assoc]
    rw [hq]
    apply (model.firstQuotient .sphere 0 2 128).injective
    change (model.firstQuotient .sphere 0 2 128)
        (quotientClass 1 a ≫ XModLambdaN.map e.inv 1) =
      (model.firstQuotient .sphere 0 2 128)
        ((model.firstQuotient .sphere 0 2 128).symm x)
    rw [LinearEquiv.apply_symm_apply]
    exact ha

private theorem h6SquareNonzero : model.standardClasses.standardH6Square ≠ 0 := by
  obtain ⟨hdeg,xr,yr,_,hy,_,hne⟩ := adamsOneLine_d2 7 (by decide)
  intro hz
  apply hne
  rw [←hy.eq_on_page_two]
  change model.sphereAlgebra.product (1,1) (2,128)
    (model.standardClasses.standardHi 0) model.standardClasses.standardH6Square = 0
  rw [hz, map_zero]

private theorem h6SquareNoIncoming (r : ℤ) (hr : 2 ≤ r) :
    model.classical.sphere.d r (((2:ℤ),128)-model.classical.sphere.diffDeg r) = 0 := by
  by_cases h2 : r = 2
  · subst r
    have hq : ((2:ℤ),128)-model.classical.sphere.diffDeg 2 = (0,127) := by
      rw [model.classical.differentialDegree]
      decide
    rw [hq]
    letI := KIP126.AdamsSynthetic.Standard.sphere_page_filtration_zero 2 127 (by decide)
    ext a
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [ha, map_zero]
  · let q := ((2:ℤ),128)-model.classical.sphere.diffDeg r
    have hs : q.1 < 0 := by
      dsimp only [q]
      rw [model.classical.differentialDegree]
      change 2-r < 0
      omega
    letI : Subsingleton (model.classical.sphere.Page r q) :=
      KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere r q.1 q.2 hs
    ext a
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [ha, map_zero]

private theorem permanentIffSurvival :
    ClassicalPermanentCycle model .sphere (2,128) model.standardClasses.standardH6Square ↔
      model.H6SquarePermanent := by
  constructor
  · intro h
    exact KIP126.Literature.Standard.nonzeroSurvivalOfPermanentNoIncoming _ _ h
      h6SquareNonzero h6SquareNoIncoming
  · rintro ⟨z,hz,_⟩
    exact ⟨z,hz⟩

private theorem boundaryLiftIff :
    deltaH6Square model = 0 ↔
      ∃ a : BiHom 126 128 (S_0_0 : SyntheticSpectrum),
        sphereFirstQuotient model 2 128 (quotientClass 1 a) = model.standardClasses.standardH6Square := by
  let x := (sphereFirstQuotient model 2 128).symm model.standardClasses.standardH6Square
  have hboundary : deltaH6Square model = 0 ↔ x ≫ XModLambdaN.proj (S_0_0 : SyntheticSpectrum) 1 = 0 := by
    change (susp_invariance 125 129 1 (-1) (S_0_0 : SyntheticSpectrum)).symm
        (x ≫ sphereTotalBoundary) = 0 ↔ _
    have hz : (susp_invariance 125 129 1 (-1) (S_0_0 : SyntheticSpectrum)) 0 = 0 := by
      letI := model.exactness.shiftAdditive (1,-1)
      change (SyntheticCategory.biShift_comp (125,129) (1,-1)).inv.app
          (S_0_0 : SyntheticSpectrum) ≫
        (SyntheticCategory.biShift (1,-1)).map
          (0 : BiHom 125 129 (S_0_0 : SyntheticSpectrum)) ≫ 𝟙 _ = 0
      erw [Functor.map_zero, Category.comp_id, comp_zero]
    rw [Equiv.symm_apply_eq, hz]
    dsimp only [sphereTotalBoundary]
    constructor
    · intro h
      apply (cancel_mono ((SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).inv.app
        ((SyntheticCategory.biShift (0,-1)).obj S_0_0))).mp
      apply (cancel_mono ((SyntheticCategory.biShift_comp (0,-1) (1,0)).hom.app
        (S_0_0 : SyntheticSpectrum))).mp
      simpa only [Category.assoc, zero_comp] using h
    · intro h
      simp only [← Category.assoc, h, zero_comp]
  rw [hboundary]
  constructor
  · intro hx
    let T := XModLambdaN.cofiberTriangle (S_0_0 : SyntheticSpectrum) 1
    obtain ⟨a,ha⟩ := T.coyoneda_exact₃ (XModLambdaN.cofiberTriangle_distinguished _ _) x hx
    refine ⟨a, ?_⟩
    change x = a ≫ XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 1 at ha
    change sphereFirstQuotient model 2 128
      (a ≫ XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 1) = _
    rw [←ha]
    exact (sphereFirstQuotient model 2 128).apply_symm_apply _
  · rintro ⟨a,ha⟩
    have hx : quotientClass 1 a = x := by
      apply (sphereFirstQuotient model 2 128).injective
      rw [ha]
      exact ((sphereFirstQuotient model 2 128).apply_symm_apply _).symm
    rw [←hx]
    dsimp only [quotientClass]
    rw [Category.assoc, XModLambdaN.incl_comp_proj, comp_zero]

/-- The first λ-cofiber exact sequence identifies the total boundary obstruction
with a permanent lift. Nonzero survival follows from the independent one-line
differential and the absence of incoming classes. -/
public theorem bx_untruncated :
    model.H6SquarePermanent ↔ lambdaEtaThetaSquare eta bxTheta5 = 0 := by
  rw [←bx_total_boundary]
  exact permanentIffSurvival.symm.trans ((sphereLiftIff _).trans boundaryLiftIff.symm)

end BxUntruncatedConstruction

/-- The fixed mathematical object on the project background. -/
@[implicit_reducible] public def may_leftShift :
  ∀ X : SyntheticSpectrum, (tensorLeft X).CommShift ℤ := by
  sorry

/-- The fixed mathematical object on the project background. -/
@[implicit_reducible] public def may_rightShift :
  ∀ X : SyntheticSpectrum, (tensorRight X).CommShift ℤ := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem may_leftExact :
  ∀ X : SyntheticSpectrum, letI := may_leftShift X; (tensorLeft X).IsTriangulated := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem may_rightExact :
  ∀ X : SyntheticSpectrum, letI := may_rightShift X; (tensorRight X).IsTriangulated := by
  sorry

public def mayData : Route.MayContext SyntheticSpectrum where
  leftShift := may_leftShift
  rightShift := may_rightShift
  leftExact := may_leftExact
  rightExact := may_rightExact

/-- Source or comparison proof remains to be supplied. -/
public theorem may_pushpull :
  ∀ T U : HoCofiberSequence (C := SyntheticSpectrum), Nonempty (Route.MayPushpullData SyntheticSpectrum mayData T U) := by
  sorry

/-- Derived from the fixed objects and previously established operations. -/
public theorem may_signed_boundary :
  Route.MayContext.SignedBoundary SyntheticSpectrum mayData := Route.may_signed_boundary_of_source mayData may_pushpull

/-- Derived from the fixed objects and previously established operations. -/
public def closedTensor :
  ClosedSymmetricTensorTriangulated Spectrum := KIP126.AdamsSynthetic.Standard.closedBackground

/-- Derived from the fixed objects and previously established operations. -/
public def finiteMappingObject :
  MappingObject (fun X : Spectrum => X = SphereSpectrum) → MappingObject (IsFiniteSpectrum (C := Spectrum)) := fun X => ⟨X.val, by rw [X.property]; exact IsFiniteSpectrum.sphere⟩

/-- Derived from the fixed objects and previously established operations. -/
public def mapping :
  MappingSpectrumSystem closedTensor model.classicalTower (fun X : Spectrum => X = SphereSpectrum) := {
    convergence := fun X Y hX hY =>
      KIP126.AdamsSynthetic.Standard.mappingConvergence X Y
        (by rw [hX]; exact IsFiniteSpectrum.sphere) (by rw [hY]; exact IsFiniteSpectrum.sphere) }

/-- Derived from the fixed objects and previously established operations. -/
public def mappingComposition :
  MappingComposition mapping := {
    pairing := fun X Y Z => KIP126.AdamsSynthetic.Standard.mapping_pairing
      (finiteMappingObject X) (finiteMappingObject Y) (finiteMappingObject Z)
    parity := fun X Y Z => KIP126.AdamsSynthetic.Standard.mapping_parity
      (finiteMappingObject X) (finiteMappingObject Y) (finiteMappingObject Z)
    abutment_compatible := fun X Y Z => KIP126.AdamsSynthetic.Standard.mapping_abutment_compatible
      (finiteMappingObject X) (finiteMappingObject Y) (finiteMappingObject Z)
    page_associative := fun W X Y Z => KIP126.AdamsSynthetic.Standard.mapping_page_associative
      (finiteMappingObject W) (finiteMappingObject X) (finiteMappingObject Y) (finiteMappingObject Z)
    identity := fun X => KIP126.AdamsSynthetic.Standard.mapping_identity (finiteMappingObject X)
    identity_actual := fun X => KIP126.AdamsSynthetic.Standard.mapping_identity_actual (finiteMappingObject X)
    page_left_unital := fun X Y => KIP126.AdamsSynthetic.Standard.mapping_page_left_unital
      (finiteMappingObject X) (finiteMappingObject Y)
    page_right_unital := fun X Y => KIP126.AdamsSynthetic.Standard.mapping_page_right_unital
      (finiteMappingObject X) (finiteMappingObject Y) }

/-- Derived from the fixed objects and previously established operations. -/
public theorem mappingSphereCompatibility :
  MappingSphereCompatibility mappingComposition model.sphereAlgebra rfl := ⟨KIP126.AdamsSynthetic.Standard.mapping_sphere_product, KIP126.AdamsSynthetic.Standard.mapping_sphere_unit⟩

/-- Source or comparison proof remains to be supplied. -/
public theorem moss_weak_convergence :
  ∀ X Y : MappingObject (fun X : Spectrum => X = SphereSpectrum), Moss.WeakConvergence (P := model.classicalTower) (B := closedTensor) X Y := by
  sorry

set_option backward.isDefEq.respectTransparency false in
private def mossPieceCast {A : ℤ → ModuleCat.{0} ℤ} (F : Filtration A)
    {p q : ℤ × ℤ} (h : p = q) :
    FiltrationPiece F p.1 p.2 ⟶ FiltrationPiece F q.1 q.2 :=
  eqToHom (congrArg (fun k : ℤ × ℤ => FiltrationPiece F k.1 k.2) h)

set_option backward.isDefEq.respectTransparency false in
private theorem mossPieceCast_arrow {A : ℤ → ModuleCat.{0} ℤ} (F : Filtration A)
    {p q : ℤ × ℤ} (h : p = q) (f : FiltrationPiece F p.1 p.2) :
    (F.F q.1 q.2).arrow (mossPieceCast F h f) =
      (eqToHom (congrArg (fun k : ℤ × ℤ => A k.2) h)) ((F.F p.1 p.2).arrow f) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem mossGradedLiftOfTransport {A : ℤ → ModuleCat.{0} ℤ} (F : Filtration A)
    {p q : ℤ × ℤ} (h : p = q) (x : F.associatedGraded q.1 q.2)
    (f : FiltrationPiece F p.1 p.2)
    (hx : F.transportGraded h.symm x = F.toAssociatedGraded p.1 p.2 f) :
    x = F.toAssociatedGraded q.1 q.2 (mossPieceCast F h f) := by
  cases h
  simpa only [Filtration.transportGraded_self, mossPieceCast, eqToHom_refl,
    ModuleCat.id_apply] using hx

set_option backward.isDefEq.respectTransparency false in
private theorem mossMappingDegreeCast (X Y : Spectrum) {m n : ℤ} (h : m = n)
    (x : HomotopyGroup m (mappingSpectrum closedTensor X Y)) :
    mappingHomotopyEquiv closedTensor n X Y
      ((eqToHom (congrArg (fun k => AbstractAdamsTower.homotopy
        (mappingSpectrum closedTensor X Y) k) h)) x) =
      eqToHom (congrArg (fun k => X⟦k⟧) h.symm) ≫
        mappingHomotopyEquiv closedTensor m X Y x := by
  cases h
  simp only [eqToHom_refl, ModuleCat.id_apply, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem mossDetectionImpl : Moss.DetectionCompatible mapping mappingComposition := by
  intro X Y Z r hr i j a b α β hα hβ
  rcases hα with ⟨eα, ⟨zα, hza, hzeα⟩, fα, hfa, hgα⟩
  rcases hβ with ⟨eβ, ⟨zβ, hzb, hzeβ⟩, fβ, hfb, hgβ⟩
  subst eα
  subst eβ
  let P := mappingComposition.pairing X Y Z
  let z := P.cyclePairAtInfinity i j zα zβ
  refine ⟨_, ⟨z, ?_, rfl⟩, ?_⟩
  · have hp := P.finitePagePair_compatible r i j
      (by
        change (model.classical.obj (mappingSpectrum closedTensor X.val Y.val)).r₀ ≤ r
        rw [model.classical.firstPage]
        exact hr)
      (by
        change (model.classical.obj (mappingSpectrum closedTensor Y.val Z.val)).r₀ ≤ r
        rw [model.classical.firstPage]
        exact hr)
      (by
        change (model.classical.obj (mappingSpectrum closedTensor X.val Z.val)).r₀ ≤ r
        rw [model.classical.firstPage]
        exact hr) zα zβ
    change infinityToPage (mapping.hom X Y).underlying.E r i zα = a at hza
    change infinityToPage (mapping.hom Y Z).underlying.E r j zβ = b at hzb
    rw [hza, hzb] at hp
    exact hp.symm
  · let F := (mapping.hom X Z).underlying.F
    have h : (i.1+j.1, Moss.stem i+Moss.stem j) = ((i+j).1, Moss.stem (i+j)) :=
      P.reindex_compatible i j
    let f : FiltrationPiece F (i.1+j.1) (Moss.stem i+Moss.stem j) :=
      P.filteredAbutmentPair i.1 j.1 (Moss.stem i) (Moss.stem j) fα fβ
    refine ⟨mossPieceCast F h f, ?_, ?_⟩
    · refine (mossPieceCast_arrow F h f).trans ?_
      have hf : (F.F (i.1+j.1) (Moss.stem i+Moss.stem j)).arrow f =
          P.abutmentPair (Moss.stem i) (Moss.stem j) α β :=
        (P.filteredAbutmentPair_compatible i.1 j.1
          (Moss.stem i) (Moss.stem j) fα fβ).trans
          (congrArg₂ (fun u v => P.abutmentPair (Moss.stem i) (Moss.stem j) u v) hfa hfb)
      refine (congrArg (fun x =>
        (eqToHom (congrArg (fun k : ℤ × ℤ => (mapping.hom X Z).underlying.A k.2) h)) x) hf).trans ?_
      apply (mappingHomotopyEquiv closedTensor (Moss.stem (i+j)) X.val Z.val).injective
      have hc := mossMappingDegreeCast X.val Z.val (congrArg Prod.snd h)
        (P.abutmentPair (Moss.stem i) (Moss.stem j) α β)
      refine hc.trans ?_
      have hcompat := mappingComposition.abutment_compatible X Y Z
        (Moss.stem i) (Moss.stem j) α β
      refine (congrArg (fun c =>
        eqToHom (congrArg (fun k => X.val⟦k⟧) (congrArg Prod.snd h).symm) ≫ c) hcompat).trans ?_
      delta Moss.abutmentComposition Moss.shiftMap Moss.abutmentMap
      simp (config := { congrConsts := false }) only [Equiv.apply_symm_apply, Category.assoc]
    · apply mossGradedLiftOfTransport F h _ f
      have hp := P.eInfty_compatible i j
        ((((mapping.hom X Y).underlying.E).ssData i).pageπ ⊤ zα)
        ((((mapping.hom Y Z).underlying.E).ssData j).pageπ ⊤ zβ)
      rw [← P.eInftyPair_induced] at hp
      change F.transportGraded h.symm
          (((mapping.convergence X.val Z.val X.property Z.property).identification (i+j)).hom
            (((Moss.sequence mapping X Z).ssData (i+j)).pageπ ⊤ z)) =
          P.associatedGradedPair i.1 j.1 (Moss.stem i) (Moss.stem j)
            (((mapping.convergence X.val Y.val X.property Y.property).identification i).hom
              (((Moss.sequence mapping X Y).ssData i).pageπ ⊤ zα))
            (((mapping.convergence Y.val Z.val Y.property Z.property).identification j).hom
              (((Moss.sequence mapping Y Z).ssData j).pageπ ⊤ zβ)) at hp
      rw [hgα, hgβ] at hp
      exact hp.trans (P.associatedGradedPair_induced i.1 j.1
        (Moss.stem i) (Moss.stem j) fα fβ)


/-- The same common infinite-cycle product and filtered abutment product
supply multiplicative detection; the abutment is the actual stable composite. -/
public theorem moss_detection :
  Moss.DetectionCompatible mapping mappingComposition := mossDetectionImpl

/-- Source or comparison proof remains to be supplied. -/
public theorem moss_indeterminacy :
  ∀ (r : ℤ) (hr : 3 ≤ r) (W X Y Z : MappingObject (fun X : Spectrum => X = SphereSpectrum)) (i j k : ℤ × ℤ)
    (a : (Moss.sequence mapping W X).Page r i) (b : (Moss.sequence mapping X Y).Page r j)
    (c : (Moss.sequence mapping Y Z).Page r k)
    (x₀ x : (Moss.sequence mapping W Z).Page r (Moss.PageMassey.degree r i j k)),
    Moss.PageMassey.Relation mapping mappingComposition r hr x₀ a b c →
      (Moss.PageMassey.Relation mapping mappingComposition r hr x a b c ↔
        Moss.PageMassey.Indeterminacy mapping mappingComposition r (j := j) a c (x-x₀)) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem moss_convergence :
  ∀ W X Y Z : MappingObject (fun X : Spectrum => X = SphereSpectrum),
    Moss.StatementAt mapping mappingComposition W X Y Z := by
  sorry

/-- Derived from the fixed objects and previously established operations. -/
public theorem moss_at :
  ∀ W X Y Z : MappingObject (fun X : Spectrum => X = SphereSpectrum),
    Moss.StatementAt mapping mappingComposition W X Y Z := moss_convergence

/-- The fixed mathematical object on the project background. -/
public def syntheticH0 :
  BiHom 0 1 (S_0_0 : SyntheticSpectrum) := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem toda_h0_label :
  KIP126.AdamsSynthetic.sphereFirstQuotient model.nu model.quotients.functoriality model.firstQuotient
    1 1 (quotientClass 1 syntheticH0) = model.standardClasses.standardHi 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem toda_lambda_h0 :
  lambdaMultiply 1 syntheticH0 = Route.syntheticTwo := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem toda_h0_eta :
  sphereProduct syntheticH0 eta = 0 := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem toda_low_indeterminacy :
  ∀ a : BiHom 2 3 (S_0_0 : SyntheticSpectrum), sphereProduct syntheticH0 a = 0 := by
  sorry

public abbrev IsConnected := KIP126.Literature.IsConnected (C := Spectrum)

public abbrev ModTwoCohomology := KIP126.Literature.ModTwoCohomology model

public abbrev sphereFirstQuotient := KIP126.Literature.sphereFirstQuotient model

public abbrev h6FirstQuotient := KIP126.Literature.h6FirstQuotient model

public abbrev h6FirstQuotient_label := KIP126.Literature.h6FirstQuotient_label model

public abbrev Theta5Detected := KIP126.Literature.Theta5Detected model

public abbrev ClassicalTheta5Detected := KIP126.Literature.ClassicalTheta5Detected model

public abbrev ClassicalPermanentCycle := KIP126.Literature.ClassicalPermanentCycle model

public abbrev BHSObjectApplicability := KIP126.Literature.BHSObjectApplicability model

public abbrev FiniteLiftCriterion := KIP126.Literature.FiniteLiftCriterion model

public abbrev PermanentLiftAt := KIP126.Literature.PermanentLiftAt model

public abbrev FiltrationLambdaAt := KIP126.Literature.FiltrationLambdaAt model

public abbrev LambdaDivisible := KIP126.Literature.LambdaDivisible model

public abbrev nuZero := KIP126.Literature.nuZero model

public abbrev firstLabel := KIP126.Literature.firstLabel model

public abbrev bocksteinArrow := KIP126.Literature.bocksteinArrow model

public abbrev bocksteinLabel := KIP126.Literature.bocksteinLabel model

public abbrev oneLineTarget := KIP126.Literature.oneLineTarget model

public abbrev classicalTwo := KIP126.Literature.classicalTwo (C := Spectrum)

public abbrev classicalSphereProduct := @KIP126.Literature.classicalSphereProduct Spectrum inferInstance

public abbrev etaThetaSquare := KIP126.Literature.etaThetaSquare eta

public abbrev lambdaEtaThetaSquare := KIP126.Literature.lambdaEtaThetaSquare eta

public abbrev deltaH6Square := KIP126.Literature.deltaH6Square model

public abbrev classicalDifferential := KIP126.Literature.classicalDifferential model

public abbrev syntheticDifferential := KIP126.Literature.syntheticDifferential model

public abbrev cycles := KIP126.Literature.cycles model

public abbrev boundaries := KIP126.Literature.boundaries model

public abbrev permanentCycles := KIP126.Literature.permanentCycles model

public abbrev CycleQuotient := KIP126.Literature.CycleQuotient model

public abbrev PermanentQuotient := KIP126.Literature.PermanentQuotient model

public abbrev quotientMap := @KIP126.Literature.quotientMap Spectrum inferInstance inferInstance SyntheticSpectrum inferInstance inferInstance model

public abbrev NuCofiberCriterion := KIP126.Literature.NuCofiberCriterion model

public abbrev SyntheticLiftComparison := KIP126.Literature.SyntheticLiftComparison model

public abbrev SyntheticTriangleLiftComparison := KIP126.Literature.SyntheticTriangleLiftComparison model

public abbrev NormalizedTriangleCompatible := KIP126.Literature.NormalizedTriangleCompatible model

public abbrev normalizedTriangle := KIP126.Literature.normalizedTriangle model

public abbrev normalizedNu := KIP126.Literature.normalizedNu model

public abbrev MossStatementAt := Moss.StatementAt mapping mappingComposition

public abbrev MossRelation := @Moss.PageMassey.Relation

public abbrev MossIndeterminacy := @Moss.PageMassey.Indeterminacy

public abbrev TripleToda := @Route.TripleToda

public abbrev TodaRelation := @KIP126.StableHomotopy.Toda.Relation

public abbrev toda_composable := @KIP126.StableHomotopy.Toda.composable

public abbrev toda_exists_relation := @KIP126.StableHomotopy.Toda.exists_relation

public abbrev toda_relation_iff_indeterminacy := @KIP126.StableHomotopy.Toda.relation_iff_indeterminacy

public abbrev toda_juggling := @KIP126.StableHomotopy.Toda.juggling

public abbrev toda_precompose := @KIP126.StableHomotopy.Toda.precompose

public abbrev toda_postcompose := @KIP126.StableHomotopy.Toda.postcompose

public abbrev toda_absorb_first := @KIP126.StableHomotopy.Toda.absorb_first

public abbrev toda_absorb_last := @KIP126.StableHomotopy.Toda.absorb_last

public abbrev toda_shuffle_iff := @KIP126.StableHomotopy.Toda.shuffle_iff

public abbrev toda_suspension_iff := @KIP126.StableHomotopy.Toda.suspension_iff

public abbrev toda_map := @KIP126.StableHomotopy.Toda.map

public abbrev toda_tensor_right := @KIP126.StableHomotopy.Toda.tensor_right

public abbrev toda_tensor_left := @KIP126.StableHomotopy.Toda.tensor_left

end KIP126.Literature.Standard
end
