module

public import KIP126.AdamsSynthetic.Standard.Background
import KIP126.AdamsSynthetic.Standard.Filtration
import KIP126.AdamsSynthetic.Standard.ClassicalSupport
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
public theorem triangle_lift :
  SyntheticTriangleLiftComparison model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem selected_realization_kernel :
  RealizationKernel model := by
  sorry

/- The rotation and suspension-square argument is adapted from the real
NuSource proofs in donor c60fbbbb93ee1f225e69bb8b93d06b4f842d031d.
The fixed triangle-lift and realization-kernel inputs remain explicit above. -/
section NuCofiberMigrationScope
namespace NuCofiberMigration
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard (Spectrum SyntheticSpectrum model)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C := Syn)]
private theorem triangle_inverse_rotation_transport
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
private def nuPositiveLandingIso (N : NuFunctorData C Syn) (X : C) :
    N.functor.obj (X⟦(1:ℤ)⟧) ≅
      ((SyntheticCategory.biShift (0,1)).obj (N.functor.obj X))⟦(1:ℤ)⟧ :=
  N.suspensionIso X ≪≫
    (SyntheticCategory.biShift_comp (0,1) (1,0)).symm.app (N.functor.obj X) ≪≫
    (SyntheticCategory.biShift_compat (Syn:=Syn) 1).app _
private theorem boundaryLanding_natural_of_suspension_square
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
private theorem lambda_negative_self (coh : BiShiftCoherence Syn) (A : Syn) :
    SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,-1)).obj A) =
      (SyntheticCategory.biShift (0,-1)).map (SyntheticCategory.lam.app A) := by
  have h := coh.lambda_comm (0,-1) A
  simpa only [biShiftAddIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.trans_inv, eqToIso.hom,eqToIso.inv,eqToHom_app,eqToHom_refl,
    Category.comp_id,Category.id_comp,Iso.hom_inv_id_app_assoc] using h
private theorem positive_lambda_shift_coherence
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
    delta lambdaToPositivePow
    simp only [lambdaPow_one coh,eqToHom_refl,Category.id_comp]
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
private theorem positive_lambda_landing_square
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
private theorem inverse_rotated_lift_factorization
    (D : Model C Syn) (coh : BiShiftCoherence Syn)
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-1)).Additive]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1:ℤ)⟧)
    (S : SyntheticTriangleLift D (Triangle.mk f g h).rotate)
    (hs : D.nu.functor.map ((shiftFunctor C (1:ℤ)).map f) ≫ (D.nu.suspensionIso Y).hom =
      (D.nu.suspensionIso X).hom ≫ (SyntheticCategory.biShift (1,1)).map (D.nu.functor.map f)) :
    ∃ a : (SyntheticCategory.biShift (0,1)).obj (D.nu.functor.obj X) ⟶ D.nu.functor.obj Y,
      lambdaToPositivePow 1 (D.nu.functor.obj X) ≫ a = D.nu.functor.map f ∧
      Triangle.mk a (D.nu.functor.map g)
        (D.nu.functor.map h ≫ (nuPositiveLandingIso D.nu X).hom) ∈ distTriang Syn := by
  letI : D.nu.functor.Additive := D.nu.additive
  let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
  have hd : Triangle.mk (D.nu.functor.map g) (D.nu.functor.map h)
      (S.connecting ≫ (D.nu.boundaryLandingIso Y).hom) ∈ distTriang Syn := S.distinguished
  obtain ⟨a,ha,htri⟩ := triangle_inverse_rotation_transport _ _ _ hd (nuPositiveLandingIso D.nu X)
  refine ⟨a,?_,htri⟩
  have hδ : S.connecting ≫ SyntheticCategory.lam.app (D.nu.functor.obj (Y⟦(1:ℤ)⟧)) =
      -(D.nu.functor.map ((shiftFunctor C (1:ℤ)).map f)) := by
    have hh := S.factorization
    change S.connecting ≫ SyntheticCategory.lam.app (D.nu.functor.obj (Y⟦(1:ℤ)⟧)) =
      D.nu.functor.map (-((shiftFunctor C (1:ℤ)).map f)) at hh
    simpa only [Functor.map_neg] using hh
  have hlam : F.map (S.connecting ≫
      SyntheticCategory.lam.app (D.nu.functor.obj (Y⟦(1:ℤ)⟧))) =
    SyntheticCategory.lam.app (D.nu.functor.obj (X⟦(1:ℤ)⟧)) ≫ S.connecting := by
    rw [Functor.map_comp,←lambda_negative_self coh]
    exact SyntheticCategory.lam.naturality S.connecting
  apply (shiftFunctor Syn (1:ℤ)).map_injective
  rw [Functor.map_comp]
  apply (cancel_epi (D.nu.boundaryLandingIso X).hom).1
  calc
    _ = SyntheticCategory.lam.app (D.nu.functor.obj (X⟦(1:ℤ)⟧)) ≫
        (nuPositiveLandingIso D.nu X).hom ≫ (shiftFunctor Syn (1:ℤ)).map a := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (shiftFunctor Syn (1:ℤ)).map a)
        (positive_lambda_landing_square coh D.nu X)
    _ = -(SyntheticCategory.lam.app (D.nu.functor.obj (X⟦(1:ℤ)⟧)) ≫
        S.connecting ≫ (D.nu.boundaryLandingIso Y).hom) := by
      rw [ha]
      simp only [Preadditive.comp_neg,Iso.hom_inv_id_assoc]
    _ = -(F.map (S.connecting ≫
        SyntheticCategory.lam.app (D.nu.functor.obj (Y⟦(1:ℤ)⟧))) ≫
        (D.nu.boundaryLandingIso Y).hom) := by
      rw [hlam]
      simp only [Category.assoc]
    _ = F.map (D.nu.functor.map ((shiftFunctor C (1:ℤ)).map f)) ≫
        (D.nu.boundaryLandingIso Y).hom := by
      rw [hδ,Functor.map_neg,Preadditive.neg_comp,neg_neg]
    _ = _ := boundaryLanding_natural_of_suspension_square D.nu f hs
private def oneSourceIso (n : ℕ) (hn : n=1) (A : Syn) :
    (SyntheticCategory.biShift (0,(n:ℤ))).obj A ≅ (SyntheticCategory.biShift (0,1)).obj A := by
  subst n
  exact Iso.refl _
private def negativeZeroIso (k : ℕ) (hk : k=0) (X : Syn) :
    (SyntheticCategory.biShift (0,-(k:ℤ))).obj X ≅ X := by
  subst k
  exact SyntheticCategory.biShift_zero.app X
private theorem negative_lift_zero_factorization {X Y : Syn} (k : ℕ) (hk : k=0)
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
private def rawSourceConnecting (nf ng nh : ℕ)
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
private theorem raw_connecting_zero_normalization
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

private theorem source_connecting_zero_normalization

    (hf : normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.f=1)
    (hg : normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g=0)
    (hh : normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h=0)
    (he : (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.f:ℤ) +
      normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g +
      normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h=1) :
    normalizedConnecting model model.auxiliary.nuRouteTriangle he ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (oneSourceIso (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.f) hf
          (model.nu.functor.obj (model.auxiliary.nuRouteTriangle.X.obj model.auxiliary))).hom =
    (negativeZeroIso (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g) hg
        (model.nu.functor.obj (model.auxiliary.nuRouteTriangle.Z.obj model.auxiliary))).hom ≫
      model.nu.functor.map model.auxiliary.nuRouteTriangle.h ≫
      (nuPositiveLandingIso model.nu (model.auxiliary.nuRouteTriangle.X.obj model.auxiliary)).hom := by
  exact raw_connecting_zero_normalization model.quotients.coherence _ _ _ hf hg hh he
    (model.nu.suspensionIso _) (model.normalizedMap .nuCofiber (.shift 1 (.shift 3 .sphere)) model.auxiliary.nuRouteTriangle.h).map _ (model.normalizedMap .nuCofiber (.shift 1 (.shift 3 .sphere)) model.auxiliary.nuRouteTriangle.h).factorization
private theorem lambda_injective_below_diagonal
    (m wt : ℤ) (hw : wt ≤ m + 1) :
    LambdaInjectiveAt m wt (S_0_0 : SyntheticSpectrum) := by
  letI := model.exactness.shiftAdditive (0,-1)
  letI := (SyntheticCategory.biShift_fullyFaithful (Syn := SyntheticSpectrum) (0,-1)).faithful
  let U := (SyntheticCategory.biShift (0,-1)).obj (Smn (Syn := SyntheticSpectrum) m wt)
  let T := XModLambdaN.cofiberTriangle (S_0_0 : SyntheticSpectrum) 1
  let e₀ : U ≅ Smn (Syn := SyntheticSpectrum) m (wt-1) :=
    (SyntheticCategory.biShift_comp (m,wt) (0,-1)).app S_0_0 ≪≫
      eqToIso (by congr 1; simp [sub_eq_add_neg])
  let e₁ : U⟦(1 : ℤ)⟧ ≅ Smn (Syn := SyntheticSpectrum) (m+1) (wt-1) :=
    (shiftFunctor SyntheticSpectrum (1 : ℤ)).mapIso e₀ ≪≫
      (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift_comp (m,wt-1) (1,0)).app S_0_0 ≪≫
      eqToIso (by congr 1; simp)
  have hQ : ∀ q : U⟦(1 : ℤ)⟧ ⟶ T.obj₃, q = 0 := by
    intro q
    haveI : Subsingleton (model.classical.sphere.Page 2 (wt-m-2,wt-1)) :=
      KIP126.AdamsSynthetic.Standard.classical_page_negative .sphere
        2 (wt-m-2) (wt-1) (by omega)
    have hz : ∀ a : BiHom (m+1) (wt-1) (XModLambdaN (S_0_0 : SyntheticSpectrum) 1), a = 0 := by
      intro a
      have hp : wt - 1 - (wt-m-2) = m+1 := by omega
      have hsub : Subsingleton (BiHom (wt-1-(wt-m-2)) (wt-1)
          (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)) :=
        (KIP126.Literature.sphereFirstQuotient model (wt-m-2) (wt-1)).injective.subsingleton
      rw [hp] at hsub
      exact @Subsingleton.elim _ hsub a 0
    apply (cancel_epi e₁.inv).mp
    simpa only [comp_zero] using hz (e₁.inv ≫ q)
  intro a b hab
  have hpre : SyntheticCategory.lam.app (Smn (Syn := SyntheticSpectrum) m wt) ≫ (a-b) = 0 := by
    rw [Preadditive.comp_sub]
    apply sub_eq_zero.mpr
    simpa only [lambdaAction, Category.assoc, cancel_epi] using hab
  have hf : (SyntheticCategory.biShift (0,-1)).map (a-b) ≫ T.mor₁ = 0 := by
    change (SyntheticCategory.biShift (0,-1)).map (a-b) ≫ lambdaPow 1 S_0_0 = 0
    rw [lambdaPow_one model.quotients.coherence]
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
    apply (shiftFunctor SyntheticSpectrum (1 : ℤ)).map_injective
    simpa only [Functor.map_zero] using hz
  apply sub_eq_zero.mp
  apply (SyntheticCategory.biShift (0,-1)).map_injective
  simpa only [Functor.map_zero] using hz'
private theorem nu_source_lambda_injective  :
    LambdaInjectiveAt 3 4 (S_0_0 : SyntheticSpectrum) :=
  lambda_injective_below_diagonal 3 4 (by omega)
private theorem positive_lift_unique_nu_degree
    {A B : SyntheticSpectrum}
    (eA : (SyntheticCategory.biShift (0,1)).obj A ≅ Smn (Syn := SyntheticSpectrum) 3 4)
    (eB : B ≅ (S_0_0 : SyntheticSpectrum))
    (f g : (SyntheticCategory.biShift (0,1)).obj A ⟶ B)
    (h : lambdaToPositivePow 1 A ≫ f = lambdaToPositivePow 1 A ≫ g) : f = g := by
  have hlam : SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,1)).obj A) ≫ f =
      SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,1)).obj A) ≫ g := by
    dsimp only [lambdaToPositivePow] at h
    rw [lambdaPow_one model.quotients.coherence] at h
    simp only [Category.assoc, cancel_epi] at h
    exact h
  have hlamTransport : SyntheticCategory.lam.app (Smn (Syn := SyntheticSpectrum) 3 4) ≫
        (eA.inv ≫ f ≫ eB.hom) =
      SyntheticCategory.lam.app (Smn (Syn := SyntheticSpectrum) 3 4) ≫
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
    apply nu_source_lambda_injective
    dsimp only [lambdaAction]
    simpa only [Category.assoc] using congrArg
      (fun z => eqToHom (by rfl) ≫
        (SyntheticCategory.biShift_comp (3,4) (0,-1)).inv.app (S_0_0 : SyntheticSpectrum) ≫ z) hlamTransport
  exact (cancel_mono eB.hom).mp ((cancel_epi eA.inv).mp heq)
private theorem normalized_nu_lift_unique
    (he : normalizedExponent model.classicalTower model.auxiliary.nuMap = 1)
    (S T : NormalizedSyntheticMap model.classicalTower model.nu model.auxiliary.nuMap) : S.map = T.map := by
  let A := model.nu.functor.obj (Sphere (C := Spectrum) 3)
  let B := model.nu.functor.obj SphereSpectrum
  have h : lambdaToPositivePow (normalizedExponent model.classicalTower model.auxiliary.nuMap) A ≫ S.map =
      lambdaToPositivePow (normalizedExponent model.classicalTower model.auxiliary.nuMap) A ≫ T.map :=
    S.factorization.trans T.factorization.symm
  have aux (n : ℕ) (hn : n = 1)
      (f g : (SyntheticCategory.biShift (0,(n : ℤ))).obj A ⟶ B)
      (hh : lambdaToPositivePow n A ≫ f = lambdaToPositivePow n A ≫ g) : f = g := by
    subst n
    exact positive_lift_unique_nu_degree
      ((SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree model) ≪≫
        (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0)
      model.nu.unitIso f g hh
  exact aux _ he S.map T.map h
private theorem source_triangle_of_rotation_and_square

    (hf : normalizedExponent model.classicalTower model.auxiliary.nuMap=1)
    (hg : normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g=0)
    (hh : normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h=0)
    (R : SyntheticTriangleLift model
      (Triangle.mk model.auxiliary.nuMap model.auxiliary.nuRouteTriangle.g
        model.auxiliary.nuRouteTriangle.h).rotate)
    (hs : model.nu.functor.map ((shiftFunctor Spectrum (1:ℤ)).map model.auxiliary.nuMap) ≫
        (model.nu.suspensionIso SphereSpectrum).hom =
      (model.nu.suspensionIso (Sphere (C:=Spectrum) 3)).hom ≫
        (SyntheticCategory.biShift (1,1)).map (model.nu.functor.map model.auxiliary.nuMap))
    (he : (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.f:ℤ) +
      normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g +
      normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h=1) :
    KIP126.Literature.normalizedTriangle model model.auxiliary.nuRouteTriangle he ∈ distTriang SyntheticSpectrum := by
  letI := model.exactness.shiftAdditive (0,-1)
  obtain ⟨a,ha,htri⟩ := inverse_rotated_lift_factorization model model.quotients.coherence
    model.auxiliary.nuMap model.auxiliary.nuRouteTriangle.g model.auxiliary.nuRouteTriangle.h R hs
  let e := oneSourceIso (normalizedExponent model.classicalTower model.auxiliary.nuMap) hf
    (model.nu.functor.obj (Sphere (C:=Spectrum) 3))
  have haf : lambdaToPositivePow (normalizedExponent model.classicalTower model.auxiliary.nuMap)
      (model.nu.functor.obj (Sphere (C:=Spectrum) 3)) ≫ (e.hom ≫ a) = model.nu.functor.map model.auxiliary.nuMap := by
    have aux (n : ℕ) (hn : n=1) : lambdaToPositivePow n (model.nu.functor.obj (Sphere (C:=Spectrum) 3)) ≫
        (oneSourceIso n hn (model.nu.functor.obj (Sphere (C:=Spectrum) 3))).hom ≫ a =
        model.nu.functor.map model.auxiliary.nuMap := by
      subst n
      simpa only [oneSourceIso,Iso.refl_hom,Category.id_comp] using ha
    exact aux _ hf
  let U : NormalizedSyntheticMap model.classicalTower model.nu model.auxiliary.nuMap := ⟨e.hom ≫ a,haf⟩
  have hnu : (model.normalizedMap (.shift 3 .sphere) .sphere model.auxiliary.nuMap).map=e.hom ≫ a := normalized_nu_lift_unique hf (model.normalizedMap (.shift 3 .sphere) .sphere model.auxiliary.nuMap) U
  have hb := negative_lift_zero_factorization _ hg (model.normalizedMap .sphere .nuCofiber model.auxiliary.nuRouteTriangle.g).map _ (model.normalizedMap .sphere .nuCofiber model.auxiliary.nuRouteTriangle.g).factorization
  have ht := source_connecting_zero_normalization hf hg hh he
  apply isomorphic_distinguished _ htri
  refine Triangle.isoMk _ _ e (Iso.refl _)
    (negativeZeroIso (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g) hg
      (model.nu.functor.obj (model.auxiliary.nuRouteTriangle.Z.obj model.auxiliary))) ?_ ?_ ?_
  · change (model.normalizedMap (.shift 3 .sphere) .sphere model.auxiliary.nuMap).map ≫ 𝟙 _ = e.hom ≫ a
    simpa only [Category.comp_id] using hnu
  · change negativeLift (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g) (model.normalizedMap .sphere .nuCofiber model.auxiliary.nuRouteTriangle.g).map ≫ _ =
      𝟙 _ ≫ model.nu.functor.map model.auxiliary.nuRouteTriangle.g
    dsimp only [AuxiliaryData.nuRouteTriangle] at hb ⊢
    simpa only [Category.id_comp] using hb
  · exact ht

section TensorSupport
local instance tensorSymmetric : SymmetricCategory Spectrum :=
  KIP126.AdamsSynthetic.Standard.closedBackground.symmetric
local instance rightTensorShift (X : Spectrum) : (tensorRight X).CommShift ℤ :=
  KIP126.AdamsSynthetic.Standard.closedBackground.tensorShift X
local instance rightTensorExact (X : Spectrum) : (tensorRight X).IsTriangulated :=
  KIP126.AdamsSynthetic.Standard.closedBackground.tensorExact X
local instance leftTensorShift (X : Spectrum) : (tensorLeft X).CommShift ℤ :=
  Functor.CommShift.ofIso (BraidedCategory.tensorLeftIsoTensorRight X).symm ℤ
local instance leftTensorShiftCompatibility (X : Spectrum) :
    NatTrans.CommShift (BraidedCategory.tensorLeftIsoTensorRight X).symm.hom ℤ :=
  Functor.CommShift.ofIso_compatibility (BraidedCategory.tensorLeftIsoTensorRight X).symm ℤ
local instance leftTensorExact (X : Spectrum) : (tensorLeft X).IsTriangulated :=
  Functor.isTriangulated_of_iso (BraidedCategory.tensorLeftIsoTensorRight X).symm

private theorem shifted_zero_homology {X Y : Spectrum} (f : X ⟶ Y)
    (hf : ZeroOnModTwoHomology model.coefficients f) :
    ZeroOnModTwoHomology model.coefficients ((shiftFunctor Spectrum (1:ℤ)).map f) := by
  let F := tensorLeft model.coefficients.object
  let S := shiftFunctor Spectrum (1:ℤ)
  intro n a
  let e : Sphere (C:=Spectrum) n ≅ S.obj (Sphere (n-1)) :=
    (shiftFunctorAdd' Spectrum (n-1) 1 n (by omega)).app SphereSpectrum
  let b : HomotopyGroup (n-1) (F.obj X) :=
    S.preimage (e.inv ≫ a ≫ (F.commShiftIso (1:ℤ)).hom.app X)
  have hb : S.map b = e.inv ≫ a ≫ (F.commShiftIso (1:ℤ)).hom.app X :=
    S.map_preimage _
  have hz := congrArg S.map (hf (n-1) b)
  change S.map (b ≫ F.map f) = S.map 0 at hz
  rw [Functor.map_comp, hb, Functor.map_zero] at hz
  apply (cancel_mono ((F.commShiftIso (1:ℤ)).hom.app Y)).mp
  apply (cancel_epi e.inv).mp
  change e.inv ≫ ((a ≫ F.map (S.map f)) ≫ (F.commShiftIso (1:ℤ)).hom.app Y) = _
  have hn := (F.commShiftIso (1:ℤ)).hom.naturality f
  change F.map (S.map f) ≫ (F.commShiftIso (1:ℤ)).hom.app Y =
    (F.commShiftIso (1:ℤ)).hom.app X ≫ S.map (F.map f) at hn
  simp only [Category.assoc]
  rw [hn]
  simpa only [Category.assoc, comp_zero, zero_comp] using hz

private theorem positive_filtration_of_homology_zero {X Y : Spectrum}
    (f : X ⟶ Y) (hf : ZeroOnModTwoHomology model.coefficients f) :
    MapFiltrationAtLeast model.classicalTower f 1 := by
  apply (KIP126.AdamsSynthetic.Standard.factorization_filtration_iff f 1).mp
  intro n hn hn1
  have he : n=1 := by omega
  subst n
  exact AdamsMapFactorization.single f hf

private theorem rotated_cofiber_homology_short_exact {X Y : Spectrum}
    (f : X ⟶ Y) (hf : ZeroOnModTwoHomology model.coefficients f) :
    HomologyShortExact model.coefficients
      (Triangle.mk f (HasFunctorialCofiber.cofibι f)
        (HasFunctorialCofiber.cofibδ f)).rotate := by
  let F := tensorLeft model.coefficients.object
  let T := F.mapTriangle.obj (Triangle.mk f (HasFunctorialCofiber.cofibι f)
    (HasFunctorialCofiber.cofibδ f))
  have hT : T ∈ distTriang Spectrum :=
    F.map_distinguished _ (HasFunctorialCofiber.cofib_distinguished f)
  intro n
  refine ⟨?_,?_,?_⟩
  · intro a b hab
    have hzero : (a-b) ≫ T.mor₂ = 0 := by
      rw [Preadditive.sub_comp]
      exact sub_eq_zero.mpr hab
    obtain ⟨c,hc⟩ := T.coyoneda_exact₂ hT (a-b) hzero
    apply sub_eq_zero.mp
    exact hc.trans (hf n c)
  · intro a
    change a ≫ (model.coefficients.object ◁ HasFunctorialCofiber.cofibδ f) = 0 ↔
      ∃ b, b ≫ (model.coefficients.object ◁ HasFunctorialCofiber.cofibι f) = a
    constructor
    · intro ha
      have hz : a ≫ T.mor₃ = 0 := by
        change a ≫ ((model.coefficients.object ◁ HasFunctorialCofiber.cofibδ f) ≫ _) = 0
        rw [←Category.assoc,ha,zero_comp]
      obtain ⟨b,hb⟩ := T.coyoneda_exact₃ hT a hz
      exact ⟨b,hb.symm⟩
    · rintro ⟨b,rfl⟩
      have hh := comp_distTriang_mor_zero₂₃ T hT
      have hg : (model.coefficients.object ◁ HasFunctorialCofiber.cofibι f) ≫
          (model.coefficients.object ◁ HasFunctorialCofiber.cofibδ f) = 0 := by
        apply (cancel_mono ((F.commShiftIso (1:ℤ)).hom.app X)).mp
        change (model.coefficients.object ◁ HasFunctorialCofiber.cofibι f) ≫
          ((model.coefficients.object ◁ HasFunctorialCofiber.cofibδ f) ≫ _) = 0 at hh
        simpa only [T, Functor.mapTriangle_obj, Triangle.mk, Category.assoc, zero_comp] using hh
      rw [Category.assoc,hg,comp_zero]
  · intro a
    let e := (F.commShiftIso (1:ℤ)).app X
    have hz : (a ≫ e.hom) ≫ T.mor₁⟦(1:ℤ)⟧' = 0 := by
      have hshift := shifted_zero_homology f hf n a
      change a ≫ F.map ((shiftFunctor Spectrum (1:ℤ)).map f) = 0 at hshift
      have hn := (F.commShiftIso (1:ℤ)).hom.naturality f
      change F.map ((shiftFunctor Spectrum (1:ℤ)).map f) ≫ (F.commShiftIso (1:ℤ)).hom.app Y =
        e.hom ≫ (shiftFunctor Spectrum (1:ℤ)).map (F.map f) at hn
      change (a ≫ e.hom) ≫ (shiftFunctor Spectrum (1:ℤ)).map (F.map f) = 0
      rw [Category.assoc, ← hn, ← Category.assoc, hshift, zero_comp]
    obtain ⟨b,hb⟩ := T.coyoneda_exact₁ hT (a ≫ e.hom) hz
    refine ⟨b,?_⟩
    apply (cancel_mono e.hom).mp
    change (b ≫ (model.coefficients.object ◁ HasFunctorialCofiber.cofibδ f)) ≫ e.hom = a ≫ e.hom
    change a ≫ e.hom = b ≫ ((model.coefficients.object ◁ HasFunctorialCofiber.cofibδ f) ≫ e.hom) at hb
    simpa only [Category.assoc] using hb.symm

private theorem actual_rotated_cofiber_lift {X Y : Spectrum}
    (f : X ⟶ Y) (hf : ZeroOnModTwoHomology model.coefficients f) :
    ∃ R : SyntheticTriangleLift model
      (Triangle.mk f (HasFunctorialCofiber.cofibι f)
        (HasFunctorialCofiber.cofibδ f)).rotate, R.FullLiftComparison model := by
  have hz : ZeroOnModTwoHomology model.coefficients
      (-(shiftFunctor Spectrum (1:ℤ)).map f) := by
    intro n a
    change a ≫ (tensorLeft model.coefficients.object).map (-(shiftFunctor Spectrum (1:ℤ)).map f) = 0
    have hshift : a ≫ (tensorLeft model.coefficients.object).map ((shiftFunctor Spectrum (1:ℤ)).map f) = 0 :=
      shifted_zero_homology f hf n a
    rw [Functor.map_neg, Preadditive.comp_neg, hshift, neg_zero]
  exact triangle_lift _ (rot_of_distTriang _ (HasFunctorialCofiber.cofib_distinguished f))
    (positive_filtration_of_homology_zero _ hz)
    (rotated_cofiber_homology_short_exact f hf)


private theorem triangle_of_suspension_square
    (hs : model.nu.functor.map ((shiftFunctor Spectrum (1:ℤ)).map model.auxiliary.nuMap) ≫
        (model.nu.suspensionIso SphereSpectrum).hom =
      (model.nu.suspensionIso (Sphere (C:=Spectrum) 3)).hom ≫
        (SyntheticCategory.biShift (1,1)).map (model.nu.functor.map model.auxiliary.nuMap)) :
    ∀ he : (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.f:ℤ) +
      normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g +
      normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h=1,
      KIP126.Literature.NormalizedTriangleCompatible model model.auxiliary.nuRouteTriangle he := by
  have hF : MapFiltrationAtLeast model.classicalTower model.auxiliary.nuMap 1 := by
    classical
    have he := nuCofiber_nu_exponent
    change (if MapFiltrationAtLeast model.classicalTower model.auxiliary.nuMap 1 then 1 else 0)=1 at he
    by_contra hn
    simp only [if_neg hn] at he
    contradiction
  have hzero : ZeroOnModTwoHomology model.coefficients model.auxiliary.nuMap := by
    have hfac := (KIP126.AdamsSynthetic.Standard.factorization_filtration_iff model.auxiliary.nuMap 1).mpr hF
    exact nuFactorizationZeroOnHomology (hfac 1 (by decide) (by decide))
  obtain ⟨R,_⟩ := actual_rotated_cofiber_lift model.auxiliary.nuMap hzero
  intro he
  exact source_triangle_of_rotation_and_square nuCofiber_nu_exponent
    nuCofiber_bottom_exponent nuCofiber_top_exponent R hs he


-- ν suspension naturality, adapted from c60fbbb NuSource/Suspension.
private theorem nu_suspension_square_candidate :
    model.nu.functor.map ((shiftFunctor Spectrum (1:ℤ)).map model.auxiliary.nuMap) ≫
        (model.nu.suspensionIso SphereSpectrum).hom =
      (model.nu.suspensionIso (Sphere (C:=Spectrum) 3)).hom ≫
        (SyntheticCategory.biShift (1,1)).map (model.nu.functor.map model.auxiliary.nuMap) := by
  have tensorRight_fullyFaithful_of_inverse (A Z : Spectrum)
      (e : A ⊗ Z ≅ 𝟙_ Spectrum) : (tensorRight A).Full ∧ (tensorRight A).Faithful := by
    have compIso (P Q : Spectrum) (e : P ⊗ Q ≅ 𝟙_ Spectrum) :
        tensorRight P ⋙ tensorRight Q ≅ 𝟭 Spectrum := by
      refine NatIso.ofComponents (fun X =>
        (α_ X P Q) ≪≫ (tensorLeft X).mapIso e ≪≫ (ρ_ X)) ?_
      intro X Y f
      change (f ▷ P ▷ Q) ≫ ((α_ Y P Q).hom ≫ (Y ◁ e.hom) ≫ (ρ_ Y).hom) =
        ((α_ X P Q).hom ≫ (X ◁ e.hom) ≫ (ρ_ X).hom) ≫ f
      simp only [Category.assoc]
      rw [associator_naturality_left_assoc]
      rw [← whisker_exchange_assoc]
      rw [rightUnitor_naturality]
    let i := compIso A Z e
    let j := compIso Z A ((β_ Z A) ≪≫ e)
    letI : (tensorRight Z).Faithful := Functor.Faithful.of_comp_iso j
    exact ⟨Functor.Full.of_comp_faithful_iso i, Functor.Faithful.of_comp_iso i⟩

  have sphere_tensorRight_fullyFaithful (n : ℤ)
      [(tensorRight (Sphere (C := Spectrum) (-n))).CommShift ℤ] :
      (tensorRight (Sphere (C := Spectrum) n)).Full ∧
        (tensorRight (Sphere (C := Spectrum) n)).Faithful := by
    let e : (Sphere (C := Spectrum) n) ⊗ Sphere (-n) ≅ 𝟙_ Spectrum :=
      ((tensorRight (Sphere (C := Spectrum) (-n))).commShiftIso n).app (𝟙_ Spectrum) ≪≫
        (shiftFunctor Spectrum n).mapIso (λ_ (Sphere (C := Spectrum) (-n))) ≪≫
        (shiftFunctorCompIsoId Spectrum (-n) n (by omega)).app (𝟙_ Spectrum)
    exact tensorRight_fullyFaithful_of_inverse _ _ e

  have scalar_end_cancellation
      (A B Z : Spectrum) [(tensorRight A).Full] [(tensorRight Z).Faithful]
      (e : B ⊗ Z ≅ A) (f : A ⟶ B) (κ : A ⟶ A)
      (hκ : ((f ▷ Z) ≫ e.hom) ≫ κ = (f ▷ Z) ≫ e.hom) :
      κ ≫ f = f := by
    let scalar (c : 𝟙_ Spectrum ⟶ 𝟙_ Spectrum) (X : Spectrum) : X ⟶ X :=
      (λ_ X).inv ≫ (c ▷ X) ≫ (λ_ X).hom
    have scalar_natural (c : 𝟙_ Spectrum ⟶ 𝟙_ Spectrum) {X Y : Spectrum} (g : X ⟶ Y) :
        scalar c X ≫ g = g ≫ scalar c Y := by
      dsimp [scalar]
      simp only [Category.assoc]
      rw [← leftUnitor_naturality, ← whisker_exchange_assoc,
        leftUnitor_inv_naturality_assoc]
    have scalar_tensor (c : 𝟙_ Spectrum ⟶ 𝟙_ Spectrum) (X Y : Spectrum) :
        scalar c (X ⊗ Y) = (scalar c X) ▷ Y := by
      dsimp [scalar]
      simp only [leftUnitor_tensor_inv, leftUnitor_tensor_hom,
        whiskerRight_tensor, comp_whiskerRight, Category.assoc,
        Iso.hom_inv_id_assoc]
    obtain ⟨c, hc⟩ := (tensorRight A).map_surjective
      ((λ_ A).hom ≫ κ ≫ (λ_ A).inv)
    change c ▷ A = (λ_ A).hom ≫ κ ≫ (λ_ A).inv at hc
    have hscalar : scalar c A = κ := by
      dsimp [scalar]
      rw [hc]
      simp
    have hwhisker : (f ▷ Z) ≫ (scalar c B ▷ Z) = f ▷ Z := by
      apply (cancel_mono e.hom).mp
      rw [← scalar_tensor]
      rw [Category.assoc, scalar_natural, hscalar]
      simpa only [Category.assoc] using hκ
    have hright : f ≫ scalar c B = f := by
      apply (tensorRight Z).map_injective
      change (f ≫ scalar c B) ▷ Z = f ▷ Z
      rw [comp_whiskerRight]
      exact hwhisker
    rw [← hscalar, scalar_natural, hright]

  have lambda_powers_injective_of_lower_weights
      (coh : BiShiftCoherence SyntheticSpectrum) (m wt : ℤ) (X : SyntheticSpectrum)
      (h : ∀ wt' : ℤ, wt' ≤ wt → LambdaInjectiveAt m wt' X) :
      ∀ k : ℕ, Function.Injective (fun a : BiHom m wt X => lambdaMultiply k a) := by
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
    delta lambdaMultiply at hab
    have hc := (cancel_epi (eqToHom (by congr 1; simp))).mp hab
    exact (cancel_epi ((SyntheticCategory.biShift_comp (m,wt) (0,-(k : ℤ))).inv.app S_0_0)).mp
      (by simpa only [Category.assoc] using hc)

  have low_realization_zero_iff
       {m wt : ℤ} (hw : wt ≤ m+1)
      (a : BiHom m wt (S_0_0 : SyntheticSpectrum)) : model.recovery.realization.map a = 0 ↔ a = 0 := by
    letI := model.recovery.adjunction.isLeftAdjoint
    letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts model.recovery.realization
    letI := Functor.additive_of_preservesBinaryBiproducts model.recovery.realization
    constructor
    · intro ha
      obtain ⟨k,hk⟩ := (selected_realization_kernel .sphere m wt a).mp ha
      have hi := lambda_powers_injective_of_lower_weights model.quotients.coherence m wt
        (S_0_0 : SyntheticSpectrum) (fun wt' h => lambda_injective_below_diagonal m wt' (by omega))
      apply hi k
      delta lambdaMultiply at hk ⊢
      simpa only [comp_zero] using hk
    · rintro rfl
      exact model.recovery.realization.map_zero _ _

  have third_arrow_unique_of_no_return
      {A B E : Spectrum} (f : A ⟶ B) (g : B ⟶ E) (h h' : E ⟶ A⟦(1:ℤ)⟧)
      (hT : Triangle.mk f g h ∈ distTriang Spectrum)
      (hT' : Triangle.mk f g h' ∈ distTriang Spectrum)
      (hzero : ∀ z : A⟦(1:ℤ)⟧ ⟶ E, z = 0) : h = h' := by
    obtain ⟨c,hc,hc'⟩ := complete_distinguished_triangle_morphism
      (Triangle.mk f g h) (Triangle.mk f g h') hT hT' (𝟙 A) (𝟙 B) (by
        change f ≫ 𝟙 B = 𝟙 A ≫ f
        exact (Category.comp_id f).trans (Category.id_comp f).symm)
    change E ⟶ E at c
    change g ≫ c = 𝟙 B ≫ g at hc
    change h ≫ (shiftFunctor Spectrum (1:ℤ)).map (𝟙 A) = c ≫ h' at hc'
    have hz : g ≫ (c - 𝟙 E) = 0 := by
      simpa only [Triangle.mk_mor₂, Preadditive.comp_sub, Category.id_comp,
        Category.comp_id, sub_eq_zero] using hc
    obtain ⟨z,hz'⟩ := (Triangle.mk f g h).yoneda_exact₃ hT (c-𝟙 E) hz
    have he : c = 𝟙 E := by
      apply sub_eq_zero.mp
      rw [hz', hzero z, comp_zero]
    rw [(shiftFunctor Spectrum (1:ℤ)).map_id A, Category.comp_id, he, Category.id_comp] at hc'
    exact hc'

  have realized_triangle_lift_third
      (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
      (L : SyntheticTriangleLift model T)
      (hzero : ∀ z : T.obj₁⟦(1:ℤ)⟧ ⟶ T.obj₃, z = 0) :
      letI := model.exactness.realizationShift
      model.recovery.nuRealizationIso.inv.app T.obj₃ ≫
        model.recovery.realization.map (L.connecting ≫ (model.nu.boundaryLandingIso T.obj₁).hom) ≫
        (model.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
        (shiftFunctor Spectrum (1:ℤ)).map (model.recovery.nuRealizationIso.hom.app T.obj₁) = T.mor₃ := by
    letI := model.exactness.realizationShift
    letI := model.exactness.realizationExact
    let F := model.recovery.realization
    let e := model.recovery.nuRealizationIso
    let U := Triangle.mk (model.nu.functor.map T.mor₁) (model.nu.functor.map T.mor₂)
      (L.connecting ≫ (model.nu.boundaryLandingIso T.obj₁).hom)
    let d := e.inv.app T.obj₃ ≫ F.map U.mor₃ ≫
      (F.commShiftIso (1:ℤ)).hom.app U.obj₁ ≫
      (shiftFunctor Spectrum (1:ℤ)).map (e.hom.app T.obj₁)
    have hU : U ∈ distTriang SyntheticSpectrum := L.distinguished
    have hi : F.mapTriangle.obj U ≅ Triangle.mk T.mor₁ T.mor₂ d := by
      refine Triangle.isoMk _ _ (e.app T.obj₁) (e.app T.obj₂) (e.app T.obj₃) ?_ ?_ ?_
      · exact model.recovery.nuRealizationIso.hom.naturality T.mor₁
      · exact model.recovery.nuRealizationIso.hom.naturality T.mor₂
      · change (F.map U.mor₃ ≫ (F.commShiftIso (1:ℤ)).hom.app U.obj₁) ≫
          (shiftFunctor Spectrum (1:ℤ)).map (e.hom.app T.obj₁) = e.hom.app T.obj₃ ≫ d
        dsimp only [d]
        simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    have hd : Triangle.mk T.mor₁ T.mor₂ d ∈ distTriang Spectrum :=
      isomorphic_distinguished _ (F.map_distinguished U hU) _ hi.symm
    change d = T.mor₃
    exact third_arrow_unique_of_no_return T.mor₁ T.mor₂ d T.mor₃ hd hT hzero

  have realized_suspension_normalization_on_third
      (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
      (L : SyntheticTriangleLift model T)
      (hzero : ∀ z : T.obj₁⟦(1:ℤ)⟧ ⟶ T.obj₃, z = 0) :
      letI := model.exactness.realizationShift
      letI := realization_lambda_iso (model.nu.functor.obj (T.obj₁⟦(1:ℤ)⟧))
      T.mor₃ ≫ (model.recovery.nuRealizationIso.inv.app (T.obj₁⟦(1:ℤ)⟧) ≫
        inv (model.recovery.realization.map (SyntheticCategory.lam.app _)) ≫
        model.recovery.realization.map (model.nu.boundaryLandingIso T.obj₁).hom ≫
        (model.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
        (shiftFunctor Spectrum (1:ℤ)).map (model.recovery.nuRealizationIso.hom.app T.obj₁)) = T.mor₃ := by
    letI := model.exactness.realizationShift
    letI := realization_lambda_iso (model.nu.functor.obj (T.obj₁⟦(1:ℤ)⟧))
    let F := model.recovery.realization
    let e := model.recovery.nuRealizationIso
    have hf : e.inv.app T.obj₃ ≫ F.map L.connecting =
        T.mor₃ ≫ e.inv.app (T.obj₁⟦(1:ℤ)⟧) ≫
          inv (F.map (SyntheticCategory.lam.app _)) := by
      apply (cancel_mono (F.map (SyntheticCategory.lam.app
        (model.nu.functor.obj (T.obj₁⟦(1:ℤ)⟧))))).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← F.map_comp, L.factorization]
      have hn := e.inv.naturality T.mor₃
      exact hn.symm
    have hd := realized_triangle_lift_third T hT L hzero
    change e.inv.app T.obj₃ ≫ F.map (L.connecting ≫ (model.nu.boundaryLandingIso T.obj₁).hom) ≫
      (F.commShiftIso (1:ℤ)).hom.app _ ≫
      (shiftFunctor Spectrum (1:ℤ)).map (e.hom.app T.obj₁) = T.mor₃ at hd
    simp only [F.map_comp, Category.assoc] at hd
    rw [← Category.assoc (e.inv.app T.obj₃) (F.map L.connecting), hf] at hd
    simpa only [Category.assoc] using hd

  have normalization_fixes_shift_of_tensor_zero


      {X Y : Spectrum} (f : X ⟶ Y) (hf : ZeroOnModTwoHomology model.coefficients f)
      (hzero : ∀ z : Y⟦(1:ℤ)⟧ ⟶ X⟦(1:ℤ)⟧, z = 0) :
      letI := model.exactness.realizationShift
      letI := realization_lambda_iso (model.nu.functor.obj (Y⟦(1:ℤ)⟧))
      (shiftFunctor Spectrum (1:ℤ)).map f ≫
        (model.recovery.nuRealizationIso.inv.app (Y⟦(1:ℤ)⟧) ≫
          inv (model.recovery.realization.map (SyntheticCategory.lam.app _)) ≫
          model.recovery.realization.map (model.nu.boundaryLandingIso Y).hom ≫
          (model.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor Spectrum (1:ℤ)).map (model.recovery.nuRealizationIso.hom.app Y)) =
        (shiftFunctor Spectrum (1:ℤ)).map f := by
    letI := model.exactness.realizationShift
    letI := realization_lambda_iso (model.nu.functor.obj (Y⟦(1:ℤ)⟧))
    let T := (Triangle.mk f (HasFunctorialCofiber.cofibι f)
      (HasFunctorialCofiber.cofibδ f)).rotate
    have hT : T ∈ distTriang Spectrum := rot_of_distTriang _
      (HasFunctorialCofiber.cofib_distinguished f)
    obtain ⟨L,hL⟩ := actual_rotated_cofiber_lift f hf
    have ht := realized_suspension_normalization_on_third T hT L hzero
    change (-(shiftFunctor Spectrum (1:ℤ)).map f) ≫ _ = -(shiftFunctor Spectrum (1:ℤ)).map f at ht
    simpa only [T, Triangle.rotate_obj₁, Triangle.mk_obj₂, Preadditive.neg_comp, neg_inj] using ht

  have realized_boundary_square_of_normalization_natural
      {X Y : Spectrum} (f : X ⟶ Y) :
      letI := model.exactness.realizationShift
      let κ (A : Spectrum) : A⟦(1:ℤ)⟧ ⟶ A⟦(1:ℤ)⟧ :=
        letI := realization_lambda_iso (model.nu.functor.obj (A⟦(1:ℤ)⟧))
        model.recovery.nuRealizationIso.inv.app (A⟦(1:ℤ)⟧) ≫
          inv (model.recovery.realization.map (SyntheticCategory.lam.app _)) ≫
          model.recovery.realization.map (model.nu.boundaryLandingIso A).hom ≫
          (model.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor Spectrum (1:ℤ)).map (model.recovery.nuRealizationIso.hom.app A)
      (shiftFunctor Spectrum (1:ℤ)).map f ≫ κ Y = κ X ≫ (shiftFunctor Spectrum (1:ℤ)).map f →
        model.recovery.realization.map ((SyntheticCategory.biShift (0,-1)).map
          (model.nu.functor.map ((shiftFunctor Spectrum (1:ℤ)).map f)) ≫
          (model.nu.boundaryLandingIso Y).hom) =
        model.recovery.realization.map ((model.nu.boundaryLandingIso X).hom ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (model.nu.functor.map f)) := by
    letI := model.exactness.realizationShift
    dsimp only
    intro hk
    let F := model.recovery.realization
    let e := model.recovery.nuRealizationIso
    let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
    let S := shiftFunctor Spectrum (1:ℤ)
    letI (A : Spectrum) := realization_lambda_iso (model.nu.functor.obj (S.obj A))
    let β (A : Spectrum) : S.obj A ≅ F.obj (G.obj (model.nu.functor.obj (S.obj A))) :=
      (e.app (S.obj A)).symm ≪≫ (asIso (F.map (SyntheticCategory.lam.app _))).symm
    let j (A : Spectrum) : F.obj ((shiftFunctor SyntheticSpectrum (1:ℤ)).obj (model.nu.functor.obj A)) ≅ S.obj A :=
      (F.commShiftIso (1:ℤ)).app _ ≪≫ S.mapIso (e.app A)
    have hβ : S.map f ≫ (β Y).hom = (β X).hom ≫
        F.map (G.map (model.nu.functor.map (S.map f))) := by
      apply (cancel_mono (F.map (SyntheticCategory.lam.app
        (model.nu.functor.obj (S.obj Y))))).mp
      dsimp only [β, Iso.trans_hom, Iso.symm_hom, asIso_inv]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← F.map_comp]
      have hn := SyntheticCategory.lam.naturality (model.nu.functor.map (S.map f))
      change G.map (model.nu.functor.map (S.map f)) ≫ SyntheticCategory.lam.app _ =
        SyntheticCategory.lam.app _ ≫ model.nu.functor.map (S.map f) at hn
      rw [hn, F.map_comp]
      simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      exact e.inv.naturality (S.map f)
    have hj : F.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (model.nu.functor.map f)) ≫ (j Y).hom =
        (j X).hom ≫ S.map f := by
      have hn := (F.commShiftIso (1:ℤ)).hom.naturality (model.nu.functor.map f)
      change F.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (model.nu.functor.map f)) ≫
        (F.commShiftIso (1:ℤ)).hom.app _ =
        (F.commShiftIso (1:ℤ)).hom.app _ ≫ S.map (F.map (model.nu.functor.map f)) at hn
      change F.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (model.nu.functor.map f)) ≫
          ((F.commShiftIso (1:ℤ)).hom.app _ ≫ S.map (e.hom.app Y)) =
        ((F.commShiftIso (1:ℤ)).hom.app _ ≫ S.map (e.hom.app X)) ≫ S.map f
      rw [← Category.assoc, hn]
      simp only [Category.assoc, ← S.map_comp]
      have he := model.recovery.nuRealizationIso.hom.naturality f
      change F.map (model.nu.functor.map f) ≫ e.hom.app Y = e.hom.app X ≫ f at he
      rw [he]
    apply (cancel_epi (β X).hom).mp
    apply (cancel_mono (j Y).hom).mp
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc (β X).hom (F.map (G.map (model.nu.functor.map (S.map f)))), ← hβ]
    rw [← Category.assoc (F.map (model.nu.boundaryLandingIso X).hom)
      (F.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (model.nu.functor.map f)))]
    rw [Category.assoc _ _ (j Y).hom, hj]
    dsimp only [β, j, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, F, e, S]
    simpa only [Category.assoc] using hk

  have suspension_square_of_boundary_square (N : NuFunctorData Spectrum SyntheticSpectrum)
      {X Y : Spectrum} (f : X ⟶ Y)
      (hb : (SyntheticCategory.biShift (0,-1)).map
          (N.functor.map ((shiftFunctor Spectrum (1:ℤ)).map f)) ≫
          (N.boundaryLandingIso Y).hom =
        (N.boundaryLandingIso X).hom ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map (N.functor.map f)) :
      N.functor.map ((shiftFunctor Spectrum (1:ℤ)).map f) ≫ (N.suspensionIso Y).hom =
        (N.suspensionIso X).hom ≫ (SyntheticCategory.biShift (1,1)).map (N.functor.map f) := by
    let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
    let j : SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,1) ⋙ G ≅ shiftFunctor SyntheticSpectrum (1:ℤ) :=
      SyntheticCategory.biShift_comp (1,1) (0,-1) ≪≫ SyntheticCategory.biShift_compat 1
    apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,-1)).map_injective
    apply (cancel_mono (j.hom.app (N.functor.obj Y))).mp
    simp only [Functor.map_comp, Category.assoc]
    change G.map (N.functor.map ((shiftFunctor Spectrum (1:ℤ)).map f)) ≫
        G.map (N.suspensionIso Y).hom ≫ j.hom.app (N.functor.obj Y) =
      G.map (N.suspensionIso X).hom ≫
        G.map ((SyntheticCategory.biShift (1,1)).map (N.functor.map f)) ≫
          j.hom.app (N.functor.obj Y)
    have hn := j.hom.naturality (N.functor.map f)
    change G.map ((SyntheticCategory.biShift (1,1)).map (N.functor.map f)) ≫
      j.hom.app (N.functor.obj Y) = j.hom.app (N.functor.obj X) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (N.functor.map f) at hn
    rw [hn]
    change G.map (N.functor.map ((shiftFunctor Spectrum (1:ℤ)).map f)) ≫
        (G.map (N.suspensionIso Y).hom ≫ j.hom.app (N.functor.obj Y)) =
      (G.map (N.suspensionIso X).hom ≫ j.hom.app (N.functor.obj X)) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (N.functor.map f) at hb
    simpa only [Category.assoc] using hb

  have suspension_square_of_realized_boundary_square

      (hb : model.recovery.realization.map ((SyntheticCategory.biShift (0,-1)).map
          (model.nu.functor.map ((shiftFunctor Spectrum (1:ℤ)).map model.auxiliary.nuMap)) ≫
          (model.nu.boundaryLandingIso SphereSpectrum).hom) =
        model.recovery.realization.map ((model.nu.boundaryLandingIso (Sphere (C:=Spectrum) 3)).hom ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (model.nu.functor.map model.auxiliary.nuMap))) :
      model.nu.functor.map ((shiftFunctor Spectrum (1:ℤ)).map model.auxiliary.nuMap) ≫
          (model.nu.suspensionIso SphereSpectrum).hom =
        (model.nu.suspensionIso (Sphere (C:=Spectrum) 3)).hom ≫
          (SyntheticCategory.biShift (1,1)).map (model.nu.functor.map model.auxiliary.nuMap) := by
    letI := model.exactness.realizationShift
    letI := model.recovery.adjunction.isLeftAdjoint
    letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts model.recovery.realization
    letI := Functor.additive_of_preservesBinaryBiproducts model.recovery.realization
    let F := model.recovery.realization
    let S := shiftFunctor SyntheticSpectrum (1:ℤ)
    let A := model.nu.functor.obj (Sphere (C:=Spectrum) 3)
    let B := model.nu.functor.obj SphereSpectrum
    have hinj : Function.Injective (fun a : A ⟶ B => F.map a) := by
      intro a b hab
      have hz : F.map ((nuSphereThree model).inv ≫ (a-b) ≫ model.nu.unitIso.hom) = 0 := by
        simp only [F.map_comp, Functor.map_sub, hab, sub_self, zero_comp, comp_zero]
      have ht := (low_realization_zero_iff (m:=3) (wt:=3) (by omega)
        ((nuSphereThree model).inv ≫ (a-b) ≫ model.nu.unitIso.hom)).mp hz
      apply sub_eq_zero.mp
      apply (cancel_mono model.nu.unitIso.hom).mp
      apply (cancel_epi (nuSphereThree model).inv).mp
      simpa only [Category.assoc, comp_zero, zero_comp] using ht
    have hshift : Function.Injective (fun a : S.obj A ⟶ S.obj B => F.map a) := by
      intro a b hab
      change F.map a = F.map b at hab
      have ha := S.map_preimage a
      have hb := S.map_preimage b
      have he : F.map (S.preimage a) = F.map (S.preimage b) := by
        apply (shiftFunctor Spectrum (1:ℤ)).map_injective
        apply (cancel_epi ((F.commShiftIso (1:ℤ)).hom.app A)).mp
        have hna := (F.commShiftIso (1:ℤ)).hom.naturality (S.preimage a)
        have hnb := (F.commShiftIso (1:ℤ)).hom.naturality (S.preimage b)
        change F.map (S.map (S.preimage a)) ≫ (F.commShiftIso (1:ℤ)).hom.app B =
          (F.commShiftIso (1:ℤ)).hom.app A ≫ (shiftFunctor Spectrum (1:ℤ)).map (F.map (S.preimage a)) at hna
        change F.map (S.map (S.preimage b)) ≫ (F.commShiftIso (1:ℤ)).hom.app B =
          (F.commShiftIso (1:ℤ)).hom.app A ≫ (shiftFunctor Spectrum (1:ℤ)).map (F.map (S.preimage b)) at hnb
        rw [ha] at hna
        rw [hb] at hnb
        rw [← hna, ← hnb, hab]
      calc a = S.map (S.preimage a) := ha.symm
           _ = S.map (S.preimage b) := congrArg S.map (hinj he)
           _ = b := hb
    apply suspension_square_of_boundary_square model.nu model.auxiliary.nuMap
    apply (cancel_epi (model.nu.boundaryLandingIso (Sphere (C:=Spectrum) 3)).inv).mp
    apply hshift
    simpa only [Functor.map_comp, Category.assoc] using congrArg (fun z =>
      F.map (model.nu.boundaryLandingIso (Sphere (C:=Spectrum) 3)).inv ≫ z) hb

  letI := model.exactness.realizationShift
  let S := shiftFunctor Spectrum (1:ℤ)
  let Z := Sphere (C:=Spectrum) 3
  let f := model.auxiliary.nuMap
  letI (X : Spectrum) := realization_lambda_iso (model.nu.functor.obj (S.obj X))
  let κ (X : Spectrum) : S.obj X ⟶ S.obj X :=
    model.recovery.nuRealizationIso.inv.app (S.obj X) ≫
      inv (model.recovery.realization.map (SyntheticCategory.lam.app _)) ≫
      model.recovery.realization.map (model.nu.boundaryLandingIso X).hom ≫
      (model.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
      S.map (model.recovery.nuRealizationIso.hom.app X)
  have hneg (a : (𝟙_ Spectrum) ⟶ Z) : a = 0 := by
    let F := shiftFunctor Spectrum (-3:ℤ)
    let e : F.obj Z ≅ 𝟙_ Spectrum :=
      (shiftFunctorCompIsoId Spectrum 3 (-3) (by omega)).app (𝟙_ Spectrum)
    have hz : F.map a ≫ e.hom = 0 := by
      haveI : Subsingleton (HomotopyGroup (-3) (SphereSpectrum : Spectrum)) :=
        sphere_connected (-3) (by omega)
      exact Subsingleton.elim _ _
    apply F.map_injective
    rw [Functor.map_zero]
    apply (cancel_mono e.hom).mp
    simpa only [zero_comp] using hz
  have hF : MapFiltrationAtLeast model.classicalTower f 1 := by
    classical
    have he := nuCofiber_nu_exponent
    change (if MapFiltrationAtLeast model.classicalTower f 1 then 1 else 0)=1 at he
    by_contra hn
    simp only [if_neg hn] at he
    contradiction
  have hf : ZeroOnModTwoHomology model.coefficients f := by
    have hfac := (KIP126.AdamsSynthetic.Standard.factorization_filtration_iff f 1).mpr hF
    exact nuFactorizationZeroOnHomology (hfac 1 (by decide) (by decide))
  have hret (a : S.obj (𝟙_ Spectrum) ⟶ S.obj Z) : a = 0 := by
    have ha := S.map_preimage a
    rw [hneg (S.preimage a), Functor.map_zero] at ha
    exact ha.symm
  have hy : S.map f ≫ κ (𝟙_ Spectrum) = S.map f :=
    normalization_fixes_shift_of_tensor_zero f hf hret
  obtain ⟨hfullZ,hfaithZ⟩ := sphere_tensorRight_fullyFaithful 3
  letI : (tensorRight Z).Full := hfullZ
  letI : (tensorRight Z).Faithful := hfaithZ
  let q : Z ⊗ Z ⟶ Z := (f ▷ Z) ≫ (λ_ Z).hom
  have hq : ZeroOnModTwoHomology model.coefficients q := by
    let H := model.coefficients.object
    let F := tensorRight Z
    intro i x
    let e : Sphere (C:=Spectrum) (i-3) ⊗ Z ≅ Sphere i :=
      KIP126.AdamsSynthetic.Standard.closedBackground.smashSpheres (i-3) 3 ≪≫
        eqToIso (by congr 1; omega)
    let b : HomotopyGroup (i-3) (H ⊗ Z) :=
      F.preimage (e.hom ≫ x ≫ (α_ H Z Z).inv)
    have hb : F.map b = e.hom ≫ x ≫ (α_ H Z Z).inv := F.map_preimage _
    have hz := congrArg F.map (hf (i-3) b)
    change F.map (b ≫ (H ◁ f)) = F.map 0 at hz
    rw [Functor.map_comp, Functor.map_zero, hb] at hz
    have hz' := congrArg (fun z => z ≫ (α_ H (𝟙_ Spectrum) Z).hom) hz
    change ((e.hom ≫ x ≫ (α_ H Z Z).inv) ≫ ((H ◁ f) ▷ Z)) ≫
      (α_ H (𝟙_ Spectrum) Z).hom = _ at hz'
    simp only [Category.assoc, associator_naturality_middle, zero_comp] at hz'
    change e.hom ≫ x ≫ (α_ H Z Z).inv ≫ (α_ H Z Z).hom ≫
      H ◁ (f ▷ Z) = 0 at hz'
    simp only [Iso.inv_hom_id_assoc] at hz'
    have hz'' : x ≫ (H ◁ (f ▷ Z)) = 0 := by
      apply (cancel_epi e.hom).mp
      simpa only [Category.assoc, comp_zero] using hz'
    change x ≫ (H ◁ ((f ▷ Z) ≫ (λ_ Z).hom)) = 0
    rw [whiskerLeft_comp, ← Category.assoc, hz'', zero_comp]
  have hretq (a : S.obj Z ⟶ S.obj (Z ⊗ Z)) : a = 0 := by
    have ha := S.map_preimage a
    have hb := (tensorRight Z).map_preimage ((λ_ Z).hom ≫ S.preimage a)
    have hz := hneg ((tensorRight Z).preimage ((λ_ Z).hom ≫ S.preimage a))
    rw [hz, Functor.map_zero] at hb
    have hz' : S.preimage a = 0 := by
      apply (cancel_epi (λ_ Z).hom).mp
      simpa only [comp_zero] using hb.symm
    rw [hz', Functor.map_zero] at ha
    exact ha.symm
  have hxq : S.map q ≫ κ Z = S.map q :=
    normalization_fixes_shift_of_tensor_zero q hq hretq
  let e : S.obj (𝟙_ Spectrum) ⊗ Z ≅ S.obj Z :=
    ((tensorRight Z).commShiftIso (1:ℤ)).app (𝟙_ Spectrum) ≪≫ S.mapIso (λ_ Z)
  let j : S.obj Z ⊗ Z ≅ S.obj (Z ⊗ Z) :=
    ((tensorRight Z).commShiftIso (1:ℤ)).app Z
  have hj : (S.map f ▷ Z) ≫ e.hom = j.hom ≫ S.map q := by
    have hn := ((tensorRight Z).commShiftIso (1:ℤ)).hom.naturality f
    change (S.map f ▷ Z) ≫ ((tensorRight Z).commShiftIso (1:ℤ)).hom.app (𝟙_ Spectrum) =
      ((tensorRight Z).commShiftIso (1:ℤ)).hom.app Z ≫ S.map (f ▷ Z) at hn
    change (S.map f ▷ Z) ≫ (((tensorRight Z).commShiftIso (1:ℤ)).hom.app (𝟙_ Spectrum) ≫
      S.map (λ_ Z).hom) = _
    rw [← Category.assoc, hn, Category.assoc, ← S.map_comp]
    rfl
  have hκ : ((S.map f ▷ Z) ≫ e.hom) ≫ κ Z = (S.map f ▷ Z) ≫ e.hom := by
    rw [hj, Category.assoc, hxq]
  let a : S.obj Z ≅ Sphere (C:=Spectrum) 4 :=
    ((shiftFunctorAdd' Spectrum 3 1 4 (by omega)).app (𝟙_ Spectrum)).symm
  let ai : S.obj Z ⊗ Sphere (C:=Spectrum) (-4) ≅ 𝟙_ Spectrum :=
    (tensorRight (Sphere (C:=Spectrum) (-4))).mapIso a ≪≫
      ((tensorRight (Sphere (C:=Spectrum) (-4))).commShiftIso (4:ℤ)).app (𝟙_ Spectrum) ≪≫
      (shiftFunctor Spectrum (4:ℤ)).mapIso (λ_ (Sphere (C:=Spectrum) (-4))) ≪≫
      (shiftFunctorCompIsoId Spectrum (-4) 4 (by omega)).app (𝟙_ Spectrum)
  obtain ⟨hfullA,hfaithA⟩ := tensorRight_fullyFaithful_of_inverse
    (S.obj Z) (Sphere (C:=Spectrum) (-4)) ai
  letI : (tensorRight (S.obj Z)).Full := hfullA
  have hx : κ Z ≫ S.map f = S.map f :=
    scalar_end_cancellation (S.obj Z) (S.obj (𝟙_ Spectrum)) Z e (S.map f) (κ Z) hκ
  apply suspension_square_of_realized_boundary_square
  apply realized_boundary_square_of_normalization_natural f
  exact hy.trans hx.symm



private theorem nuCofiber_triangle_candidate :
  ∀ he :
      (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.f : ℤ) +
        normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g +
        normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h = 1,
    KIP126.Literature.NormalizedTriangleCompatible model model.auxiliary.nuRouteTriangle he :=
  triangle_of_suspension_square nu_suspension_square_candidate

end TensorSupport
end
end NuCofiberMigration
end NuCofiberMigrationScope

/-- The prescribed normalized arrows form a distinguished triangle. -/
public theorem nuCofiber_triangle :
  ∀ he :
      (normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.f : ℤ) +
        normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g +
        normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.h = 1,
    NormalizedTriangleCompatible model model.auxiliary.nuRouteTriangle he := by
  exact NuCofiberMigration.nuCofiber_triangle_candidate

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
public theorem bhs_bockstein :
  BocksteinDifferential model := by
  sorry

/-- Source or comparison proof remains to be supplied. -/
public theorem bhs_differentials :
  DifferentialRigidity model := by
  sorry

public def realizeNu := realizeNuZero model realizationData

section SelectedFiltrationLambdaConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/- The finite-quotient argument was independently checked in the 2026-10-18
upstream-fidelity review. Reconstruct its filtration steps here from the public
foundational interfaces, preserving the Literature dependency boundary. -/
section General
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X : Syn}

private theorem selectedFiltration_filtration_at_zero (P : SyntheticTowerPresentation unit F)
    (X : Syn) (m w : ℤ) (a : BiHom m w X) : FiltrationAtLeast P 0 a := by
  refine ⟨a ≫ (P.tower X).zeroIso.inv, ?_⟩
  change (a ≫ (P.tower X).zeroIso.inv) ≫ (P.tower X).projection 0 = a
  simp only [AbstractAdamsTower.projection, Int.toNat_zero, (P.tower X).map_self]
  erw [Category.assoc, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private theorem selectedFiltration_filtration_iff_of_infinity_zero (c : SyntheticTowerConvergence P X)
    (s t m w : ℤ) (hst : s ≤ t)
    (hz : ∀ j, s ≤ j → j < t → IsZero (((F.obj X).sequence.ssData (j,m+j,w)).eInfty))
    (a : BiHom m w X) : FiltrationAtLeast P s a ↔ FiltrationAtLeast P t a := by
  have hgraded (j : ℤ) (hj : s ≤ j) (hjt : j < t) :
      IsZero ((P.filtration X).associatedGraded j (m,w)) :=
    (hz j hj hjt).of_iso (towerGradedIso c (m,w) j).symm
  have he := (P.filtration X).eq_of_associatedGraded_isZero s t (m,w) hst hgraded
  have he' := congrArg (fun Q => a ∈ (ModuleCat.subobjectModule (syntheticHomotopy X (m,w))) Q) he
  simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
    FiltrationAtLeast] using Iff.of_eq he'
end General

private theorem selectedFiltration_finite_infinity_zero_outside (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t w : ℤ) (hw : ¬ (0 ≤ t-w ∧ t-w < q)) :
    IsZero (((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData
      (s,t,w)).eInfty) := by
  haveI : Subsingleton (KIP126.Literature.finiteEInftyModel model X q (s,t) w) := by
    delta KIP126.Literature.finiteEInftyModel; simp only [hw, ite_false]
    infer_instance
  haveI : Subsingleton (((model.family.quotient
      (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData (s,t,w)).eInfty) :=
    (KIP126.Literature.Standard.eInfinity_finite X q hq (s,t) w).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem selectedFiltration_finite_high_filtration_zero (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
    (a : BiHom m w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : FiltrationAtLeast model.syntheticTower s a) : a = 0 := by
  apply KIP126.AdamsSynthetic.Standard.synthetic_homotopy_separated (.nu X) q m w a
  intro j
  by_cases hj : s ≤ (j:ℤ)
  · exact (selectedFiltration_filtration_iff_of_infinity_zero (model.convergence (.quotient q (.nu X)))
      s j m w hj (fun k hk _ => selectedFiltration_finite_infinity_zero_outside X q hq k (m+k) w (by omega)) a).mp ha
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) ha


-- Definition calculation, as in the existing Coherence.lambda_regrade_eq.
private theorem selectedFiltration_regrade_lambda (m u : ℤ) (k : ℕ) (w : ℤ) (h : u-k=w)
    (A : SyntheticSpectrum) (b : BiHom m u A) :
    homotopyRegrade rfl h (lambdaMultiply k b) =
      (biShiftAddIso (m,u) (0,-(k:ℤ)) (m,w) (by ext <;> dsimp <;> omega)).inv.app S_0_0 ≫
        lambdaPow k (Smn m u) ≫ b := by
  subst w
  delta KIP126.Synthetic.Context.homotopyRegrade KIP126.Synthetic.Context.lambdaMultiply
  simp only [biShiftAddIso, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app, Category.assoc]

private theorem selectedFiltration_lambda_filtration {A : SyntheticSpectrum} {m w : ℤ}
    (k : ℕ) (s : ℤ) (a : BiHom m w A)
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    FiltrationAtLeast model.syntheticTower s (lambdaMultiply k a) := by
  obtain ⟨z,hz⟩ := ha
  refine ⟨lambdaMultiply k z,?_⟩
  change lambdaMultiply k z ≫ (model.syntheticTower.tower A).projection s = _
  change z ≫ (model.syntheticTower.tower A).projection s = a at hz
  delta KIP126.Synthetic.Context.lambdaMultiply
  simp only [Category.assoc,hz]

private theorem selectedFiltration_regrade_filtration {A : SyntheticSpectrum} {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') (s : ℤ) (a : BiHom m w A)
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    FiltrationAtLeast model.syntheticTower s (homotopyRegrade hm hw a) := by
  subst m'; subst w'; exact ha

private theorem selectedFiltration_map_filtration {A B : SyntheticSpectrum} (f : A ⟶ B)
    (m w s : ℤ) (a : BiHom m w A)
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    FiltrationAtLeast model.syntheticTower s (a ≫ f) := by
  obtain ⟨z,hz⟩ := ha
  let φ := model.syntheticTower.map f
  refine ⟨z ≫ φ.stage s.toNat, ?_⟩
  change (z ≫ φ.stage s.toNat) ≫ (model.syntheticTower.tower B).projection s = a ≫ f
  change z ≫ (model.syntheticTower.tower A).projection s = a at hz
  rw [Category.assoc, TowerMap.projection, ←Category.assoc, hz]

private theorem selectedFiltration_nu_above_zero (X : ClassicalObject) (s t w : ℤ) (hw : t<w) :
    IsZero (((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w)).eInfty) := by
  haveI : Subsingleton (nuEInftyModel model X (s,t) w) := by
    delta KIP126.Literature.nuEInftyModel; simp only [not_le.mpr hw, ite_false]
    infer_instance
  haveI : Subsingleton (((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData (s,t,w)).eInfty) :=
    (KIP126.Literature.Standard.eInfinity_nu X (s,t) w).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem selectedFiltration_nu_bottom (X : ClassicalObject) (m s : ℤ)
    (b : BiHom m (m+s) (model.nu.functor.obj (X.obj model.auxiliary))) :
    FiltrationAtLeast model.syntheticTower s b := by
  have hb0 := selectedFiltration_filtration_at_zero model.syntheticTower _ m (m+s) b
  by_cases hs : s ≤ 0
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (m,m+s) hs hb0
  · exact (selectedFiltration_filtration_iff_of_infinity_zero (model.convergence (.nu X))
      0 s m (m+s) (by omega)
      (fun j _ hj => selectedFiltration_nu_above_zero X j (m+j) (m+s) (by omega)) b).mp hb0

private theorem selectedFiltration_divide_of_quotient_zero (X : ClassicalObject) (m u w : ℤ)
    (k : ℕ) (h : u-k=w)
    (a : BiHom m w (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : quotientClass k a=0) :
    ∃ b : BiHom m u (model.nu.functor.obj (X.obj model.auxiliary)),
      homotopyRegrade rfl h (lambdaMultiply k b)=a := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  obtain ⟨c,hc⟩ := (XModLambdaN.cofiberTriangle A k).coyoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished A k) a ha
  change a = c ≫ lambdaPow k A at hc
  let e := (biShiftAddIso (m,u) (0,-(k:ℤ)) (m,w) (by ext <;> dsimp <;> omega)).app
    (S_0_0:SyntheticSpectrum)
  obtain ⟨b,hb⟩ := (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum)
    (0,-(k:ℤ))).homEquiv.surjective (e.hom ≫ c)
  change (SyntheticCategory.biShift (0,-(k:ℤ))).map b = e.hom ≫ c at hb
  refine ⟨b,?_⟩
  rw [selectedFiltration_regrade_lambda]
  change e.inv ≫ lambdaPow k (Smn m u) ≫ b = a
  rw [←lambdaPow_naturality, hb]
  simpa only [Category.assoc,e.inv_hom_id_assoc] using hc.symm

/-- Finite quotient vanishing and exactness identify filtration with the actual λ divisibility. -/
public theorem selected_filtration_lambda :
    ∀ X : ClassicalObject, FiltrationLambdaAt model X := by
  intro X m w s h a
  let k := (m+s-w).toNat
  have hk : (k:ℤ)=m+s-w := Int.toNat_of_nonneg (by omega)
  constructor
  · intro ha
    by_cases hk0 : k=0
    · have hz : quotientClass k a=0 := by
        rw [hk0]
        let A := model.nu.functor.obj (X.obj model.auxiliary)
        letI : IsIso (lambdaPow 0 A) := by
          change IsIso (SyntheticCategory.biShift_zero.hom.app A)
          infer_instance
        have hi : XModLambdaN.incl A 0 = 0 := by
          apply (cancel_epi (lambdaPow 0 A)).mp
          simpa only [comp_zero] using XModLambdaN.lambdaPow_comp_incl A 0
        exact (congrArg (fun f => a ≫ f) hi).trans (comp_zero)
      exact selectedFiltration_divide_of_quotient_zero X m (m+s) w k (by omega) a hz
    · have hq : 0<k := Nat.pos_of_ne_zero hk0
      have himage : FiltrationAtLeast model.syntheticTower s (quotientClass k a) :=
        selectedFiltration_map_filtration (XModLambdaN.incl _ k) m w s a ha
      have hz : quotientClass k a=0 :=
        selectedFiltration_finite_high_filtration_zero X k hq m w s (by omega) _ himage
      exact selectedFiltration_divide_of_quotient_zero X m (m+s) w k (by omega) a hz
  · rintro ⟨b,hb⟩
    rw [←hb]
    exact selectedFiltration_regrade_filtration rfl (by omega) s _ (selectedFiltration_lambda_filtration k s b (selectedFiltration_nu_bottom X m s b))


end SelectedFiltrationLambdaConstruction


/- Filtered detection and lambda transport, adapted from the proved
GeneralizedMahowald argument in donor c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
Main/ExtensionLaws/GeneralizedMahowald/Proofs.lean. These private helpers use
only the fixed foundational and Literature comparisons. -/
namespace SelectedLifetimeConstruction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 6000000
private theorem family_infinity_representative_map {X Y : SyntheticSpectrum}
    (g : X ⟶ Y) (i : Tridegree) (x : (model.family.obj X).Page 2 i)
    (e : ((model.family.obj X).sequence.ssData i).eInfty)
    (h : HasInfinityRepresentative (model.family.obj X) 2 i x e) :
    HasInfinityRepresentative (model.family.obj Y) 2 i
      (model.family.pageMap g 2 i x) ((model.family.map g).eInftyMap i e) :=
  KIP126.Literature.Standard.rhoInfinityRepresentativeMap g i h
private theorem family_page_comp {X Y Z : SyntheticSpectrum}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap model.family f r i ≫ familyPageMap model.family g r i =
      familyPageMap model.family (f ≫ g) r i := by
  change (model.family.map f).pageMap r i ≫ (model.family.map g).pageMap r i = _
  rw [← SpectralSequenceMorphism.pageMap_comp, ← SyntheticAdamsFamily.map_comp]
  rfl
private theorem graded_map_representative {ι : Type} {A B : ι → ModuleCat.{0} ℤ}
    {F : Filtration A} {G : Filtration B} (f : FilteredMorphism F G) (s : ℤ) (i : ι)
    (a : (Subobject.underlying.obj (F.F s i) : ModuleCat ℤ)) :
    f.inducedGrMap s i (F.toAssociatedGraded s i a) =
      G.toAssociatedGraded s i ((f.compat s i).choose a) := by
  have h : F.toAssociatedGraded s i ≫ f.inducedGrMap s i =
      (f.compat s i).choose ≫ G.toAssociatedGraded s i := by
    unfold Filtration.toAssociatedGraded FilteredMorphism.inducedGrMap
      Filtration.inducedAssocGradedMap
    dsimp only [cokernel.map]
    exact cokernel.π_desc _ _ _
  exact ConcreteCategory.congr_hom h a
private theorem filtration_representative_exists (A : SyntheticSpectrum) (p : ℤ × ℤ)
    (s : ℤ) (a : BiHom p.1 p.2 A)
    (ha : a ∈ model.syntheticTower.filtrationSubmodule A s p) :
    ∃ a' : (Subobject.underlying.obj ((model.syntheticTower.filtration A).F s p) : ModuleCat ℤ),
      ((model.syntheticTower.filtration A).F s p).arrow a' = a := by
  have hm : a ∈ ModuleCat.subobjectModule _ ((model.syntheticTower.filtration A).F s p) := by
    change a ∈ (ModuleCat.subobjectModule (syntheticHomotopy A p))
      ((ModuleCat.subobjectModule (syntheticHomotopy A p)).symm
        (model.syntheticTower.filtrationSubmodule A s p))
    simpa only [OrderIso.apply_symm_apply] using ha
  exact hm
private theorem grade_natural (A B : SyntheticObject)
    (f : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary) (i : Tridegree)
    (a : (Subobject.underlying.obj ((model.syntheticTower.filtration
      (A.obj model.nu model.auxiliary)).F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ))
    (b : (Subobject.underlying.obj ((model.syntheticTower.filtration
      (B.obj model.nu model.auxiliary)).F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ))
    (hab : ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F
      i.1 (i.2.1-i.1,i.2.2)).arrow a ≫ f =
      ((model.syntheticTower.filtration (B.obj model.nu model.auxiliary)).F
        i.1 (i.2.1-i.1,i.2.2)).arrow b) :
    ((model.convergence B).identification i).inv
      ((model.syntheticTower.filtration (B.obj model.nu model.auxiliary)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) b) =
      (model.family.map f).eInftyMap i (((model.convergence A).identification i).inv
        ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).toAssociatedGraded
          i.1 (i.2.1-i.1,i.2.2) a)) := by
  let M := model.convergentMap A B f
  let FA := model.syntheticTower.filtration (A.obj model.nu model.auxiliary)
  let FB := model.syntheticTower.filtration (B.obj model.nu model.auxiliary)
  let p := (i.2.1-i.1,i.2.2)
  have hb : (M.filteredMap.compat i.1 p).choose a = b := by
    apply (ModuleCat.mono_iff_injective (FB.F i.1 p).arrow).mp inferInstance
    have h := ConcreteCategory.congr_hom (M.filteredMap.compat i.1 p).choose_spec a
    change (FB.F i.1 p).arrow ((M.filteredMap.compat i.1 p).choose a) =
      M.filteredMap.map p ((FA.F i.1 p).arrow a) at h
    have hm := ConcreteCategory.congr_hom (M.filteredMap_map p) ((FA.F i.1 p).arrow a)
    change M.filteredMap.map p ((FA.F i.1 p).arrow a) = (FA.F i.1 p).arrow a ≫ f at hm
    exact h.trans (hm.trans hab)
  have hp := graded_map_representative M.filteredMap i.1 p a
  rw [hb] at hp
  apply ((model.convergence B).identification i).toLinearEquiv.injective
  have hn := ConcreteCategory.congr_hom (M.infinity_action_graded i)
    (((model.convergence A).identification i).inv (FA.toAssociatedGraded i.1 p a))
  change M.filteredMap.inducedGrMap i.1 p
      (((model.convergence A).identification i).hom
        (((model.convergence A).identification i).inv (FA.toAssociatedGraded i.1 p a))) =
    ((model.convergence B).identification i).hom
      ((model.family.map f).eInftyMap i
        (((model.convergence A).identification i).inv (FA.toAssociatedGraded i.1 p a))) at hn
  have hA := ((model.convergence A).identification i).toLinearEquiv.apply_symm_apply
    (FA.toAssociatedGraded i.1 p a)
  have hB := ((model.convergence B).identification i).toLinearEquiv.apply_symm_apply
    (FB.toAssociatedGraded i.1 p b)
  exact hB.trans (hp.symm.trans
    ((congrArg (M.filteredMap.inducedGrMap i.1 p) hA.symm).trans hn))

private theorem detects_map (A B : SyntheticObject)
    (f : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary) (i : Tridegree)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (A.obj model.nu model.auxiliary))
    (ha : Detects (model.convergence A) i x a) :
    Detects (model.convergence B) i (familyPageMap model.family f 2 i x) (a ≫ f) := by
  obtain ⟨e,he,a',ha',hga⟩ := ha
  let M := model.convergentMap A B f
  let b := (M.filteredMap.compat i.1 (i.2.1-i.1,i.2.2)).choose a'
  have hb : ((model.syntheticTower.filtration (B.obj model.nu model.auxiliary)).F
      i.1 (i.2.1-i.1,i.2.2)).arrow b = a ≫ f := by
    have h := ConcreteCategory.congr_hom
      (M.filteredMap.compat i.1 (i.2.1-i.1,i.2.2)).choose_spec a'
    change _ = M.filteredMap.map (i.2.1-i.1,i.2.2) _ at h
    have hm := ConcreteCategory.congr_hom (M.filteredMap_map (i.2.1-i.1,i.2.2))
      (((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F
        i.1 (i.2.1-i.1,i.2.2)).arrow a')
    change _ = _ ≫ f at hm
    exact h.trans (hm.trans (congrArg (fun z => z ≫ f) ha'))
  refine ⟨_,family_infinity_representative_map f i x e he,b,hb,?_⟩
  have h := grade_natural A B f i a' b (by rw [ha',hb])
  have haE : ((model.convergence A).identification i).inv
      ((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) a') = e := by
    rw [← hga]
    exact ((model.convergence A).identification i).toLinearEquiv.symm_apply_apply e
  rw [haE] at h
  exact (congrArg ((model.convergence B).identification i).hom h).symm.trans
    (((model.convergence B).identification i).toLinearEquiv.apply_symm_apply _)

private theorem detects_reflect (A B : SyntheticObject)
    (f : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary) (i : Tridegree)
    (hf : Function.Injective ((model.family.map f).eInftyMap i).hom)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ i)
    (e : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData i).eInfty)
    (he : HasInfinityRepresentative _ 2 i x e)
    (a : BiHom (i.2.1-i.1) i.2.2 (A.obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower i.1 a)
    (hb : Detects (model.convergence B) i (familyPageMap model.family f 2 i x) (a ≫ f)) :
    Detects (model.convergence A) i x a := by
  obtain ⟨a',ha'⟩ := filtration_representative_exists
    (A.obj model.nu model.auxiliary) (i.2.1-i.1,i.2.2) i.1 a ha
  obtain ⟨eB,heB,b,hb,hgb⟩ := hb
  have huniq := heB.unique (family_infinity_representative_map f i x e he)
  have h := grade_natural A B f i a' b (by rw [ha',hb])
  have hB : ((model.convergence B).identification i).inv
      ((model.syntheticTower.filtration (B.obj model.nu model.auxiliary)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) b) = (model.family.map f).eInftyMap i e := by
    rw [← hgb]
    exact (((model.convergence B).identification i).toLinearEquiv.symm_apply_apply eB).trans huniq
  have hA := hf (h.symm.trans hB)
  refine ⟨e,he,a',ha',?_⟩
  exact (congrArg ((model.convergence A).identification i).hom hA).symm.trans
    (((model.convergence A).identification i).toLinearEquiv.apply_symm_apply _)

section Frames
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

/-- A filtration frame, reindexed by the same stem, gives detection. -/
theorem source_frame_detects (cx : SyntheticTowerConvergence P X)
    (p : ℤ × ℤ) (s : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (x0 : (F.obj X).E₂ (s,p.1+s,p.2))
    (hx : HasInfinityRepresentative _ 2 _ x0 x)
    (a : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ))
    (ha : (P.filtration X).toAssociatedGraded s p a = (towerGradedIso cx p s).hom x) :
    Detects cx (s,p.1+s,p.2) x0
      (homotopyRegrade (by dsimp; omega) rfl (((P.filtration X).F s p).arrow a)) := by
  have lift_frame (m m' w s : ℤ) (hm : m=m') {V : ModuleCat.{v} ℤ} (e : V)
      (I : V ≅ (P.filtration X).associatedGraded s (m',w))
      (a : (Subobject.underlying.obj ((P.filtration X).F s (m,w)) : ModuleCat.{v} ℤ))
      (ha : (P.filtration X).toAssociatedGraded s (m,w) a =
        (I ≪≫ eqToIso (congrArg
          (fun z => (P.filtration X).associatedGraded s (z,w)) hm.symm)).hom e) :
      ∃ a' : (Subobject.underlying.obj ((P.filtration X).F s (m',w)) : ModuleCat.{v} ℤ),
        ((P.filtration X).F s (m',w)).arrow a' =
          homotopyRegrade hm rfl (((P.filtration X).F s (m,w)).arrow a) ∧
        I.hom e = (P.filtration X).toAssociatedGraded s (m',w) a' := by
    subst m'
    refine ⟨a,rfl,?_⟩
    simpa only [eqToIso_refl, Iso.trans_refl] using ha.symm
  obtain ⟨a',ha',hga⟩ := lift_frame p.1 ((p.1+s)-s) p.2 s (by omega) x
    (cx.identification (s,p.1+s,p.2)) a ha
  exact ⟨x,hx,a',ha',hga⟩

/-- Detection supplies a frame in the original stem coordinates. -/
theorem frame_of_source_detects (cx : SyntheticTowerConvergence P X)
    (p : ℤ × ℤ) (s : ℤ) (x0 : (F.obj X).E₂ (s,p.1+s,p.2))
    (a0 : BiHom p.1 p.2 X)
    (ha0 : Detects cx (s,p.1+s,p.2) x0 (homotopyRegrade (by dsimp; omega) rfl a0)) :
    ∃ x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty,
      HasInfinityRepresentative _ 2 _ x0 x ∧
      ∃ a : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ),
        ((P.filtration X).F s p).arrow a = a0 ∧
        (P.filtration X).toAssociatedGraded s p a = (towerGradedIso cx p s).hom x := by
  have lower_frame (m m' w s : ℤ) (hm : m=m') {V : ModuleCat.{v} ℤ} (e : V)
      (I : V ≅ (P.filtration X).associatedGraded s (m',w))
      (a0 : BiHom m w X)
      (a' : (Subobject.underlying.obj ((P.filtration X).F s (m',w)) : ModuleCat.{v} ℤ))
      (ha' : ((P.filtration X).F s (m',w)).arrow a' = homotopyRegrade hm rfl a0)
      (hga : I.hom e = (P.filtration X).toAssociatedGraded s (m',w) a') :
      ∃ a : (Subobject.underlying.obj ((P.filtration X).F s (m,w)) : ModuleCat.{v} ℤ),
        ((P.filtration X).F s (m,w)).arrow a = a0 ∧
        (P.filtration X).toAssociatedGraded s (m,w) a =
          (I ≪≫ eqToIso (congrArg
            (fun z => (P.filtration X).associatedGraded s (z,w)) hm.symm)).hom e := by
    subst m'
    exact ⟨a',ha',hga.symm⟩
  obtain ⟨e,he,a',ha',hga⟩ := ha0
  obtain ⟨a,ha,hg⟩ := lower_frame p.1 ((p.1+s)-s) p.2 s (by omega) e
    (cx.identification (s,p.1+s,p.2)) a0 a' ha' hga
  exact ⟨e,he,a,ha,hg⟩

end Frames
private theorem shift_frame (A : SyntheticObject) (δ p : ℤ × ℤ) (s : ℤ)
    (e : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (a : (Subobject.underlying.obj ((model.syntheticTower.filtration
      (A.obj model.nu model.auxiliary)).F s p) : ModuleCat ℤ))
    (ha : (model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).toAssociatedGraded s p a =
      (towerGradedIso (model.convergence A) p s).hom e) :
    ∃ b : (Subobject.underlying.obj ((model.syntheticTower.filtration
      ((SyntheticObject.shift δ A).obj model.nu model.auxiliary)).F s (p+δ)) : ModuleCat ℤ),
      ((model.syntheticTower.filtration ((SyntheticObject.shift δ A).obj model.nu model.auxiliary)).F
        s (p+δ)).arrow b = shiftHomotopyClass δ p
          (((model.syntheticTower.filtration (A.obj model.nu model.auxiliary)).F s p).arrow a) ∧
      (model.syntheticTower.filtration ((SyntheticObject.shift δ A).obj model.nu model.auxiliary)).toAssociatedGraded
        s (p+δ) b = (towerGradedIso (model.convergence (.shift δ A)) (p+δ) s).hom
          ((towerInfinityIso (model.convergence A) (model.convergence (.shift δ A))
            ((essShift δ).filtered A p) s).hom e) := by
  let S := (essShift δ).filtered A p
  refine ⟨(S.level s).hom a,?_,?_⟩
  · exact (ConcreteCategory.congr_hom (S.level_arrow s) a).trans
      ((essShift δ).ambient_eq A p _)
  · have h := ConcreteCategory.congr_hom (S.projection_comm s) a
    simp only [ModuleCat.comp_apply] at h
    rw [ha] at h
    rw [←h]
    change (S.gradedIso s).hom ((towerGradedIso (model.convergence A) p s).hom e) =
      (towerGradedIso (model.convergence (.shift δ A)) (p+δ) s).hom
        ((towerInfinityIso (model.convergence A) (model.convergence (.shift δ A)) S s).hom e)
    simp only [towerInfinityIso, Iso.trans_hom, Iso.symm_hom, ←ModuleCat.comp_apply,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem detects_shift (A : SyntheticObject) (δ p : ℤ × ℤ) (s : ℤ)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2))
    (a : BiHom p.1 p.2 (A.obj model.nu model.auxiliary))
    (ha : Detects (model.convergence A) (s,p.1+s,p.2) x
      (homotopyRegrade (by dsimp; omega) rfl a)) :
    Detects (model.convergence (.shift δ A)) (s,(p+δ).1+s,(p+δ).2)
      (((essShift δ).page A 2 (by decide) p s).hom x)
      (homotopyRegrade (by dsimp; omega) rfl (shiftHomotopyClass δ p a)) := by
  obtain ⟨e,he,a',ha',hga⟩ := frame_of_source_detects (model.convergence A) p s x a ha
  obtain ⟨b,hb,hgb⟩ := shift_frame A δ p s e a' hga
  have hdet := source_frame_detects (model.convergence (.shift δ A)) (p+δ) s _ _
    ((essShift δ).representative_iff A 2 (by decide) p s x e |>.mp he) b
    hgb
  rw [hb,ha'] at hdet
  exact hdet

private theorem regrade_comp {m m' w w' : ℤ} {A B : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) (f : A ⟶ B) :
    homotopyRegrade hm hw (a≫f) = homotopyRegrade hm hw a ≫ f := by
  subst m'; subst w'; rfl

private theorem shifted_map_detects (A B : SyntheticObject) (δ p : ℤ × ℤ) (s : ℤ)
    (g : (SyntheticObject.shift δ A).obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2))
    (a : BiHom p.1 p.2 (A.obj model.nu model.auxiliary))
    (ha : Detects (model.convergence A) (s,p.1+s,p.2) x (homotopyRegrade (by dsimp; omega) rfl a)) :
    Detects (model.convergence B) (s,(p+δ).1+s,(p+δ).2)
      (familyPageMap model.family g 2 (s,(p+δ).1+s,(p+δ).2)
        (((essShift δ).page A 2 (by decide) p s).hom x))
      (homotopyRegrade (by dsimp; omega) rfl (shiftHomotopyClass δ p a) ≫ g) :=
  detects_map (.shift δ A) B g (s,(p+δ).1+s,(p+δ).2) _ _
    (detects_shift A δ p s x a ha)

private theorem shifted_representative_map (A B : SyntheticObject) (δ p : ℤ × ℤ) (s : ℤ)
    (g : (SyntheticObject.shift δ A).obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ (s,p.1+s,p.2))
    (e : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (he : HasInfinityRepresentative _ 2 (s,p.1+s,p.2) x e) :
    HasInfinityRepresentative _ 2 (s,(p+δ).1+s,(p+δ).2)
      (familyPageMap model.family g 2 (s,(p+δ).1+s,(p+δ).2)
        (((essShift δ).page A 2 (by decide) p s).hom x))
      ((model.family.map g).eInftyMap (s,(p+δ).1+s,(p+δ).2)
        ((towerInfinityIso (model.convergence A) (model.convergence (.shift δ A))
          ((essShift δ).filtered A p) s).hom e)) :=
  family_infinity_representative_map g (s,(p+δ).1+s,(p+δ).2) _ _
    (((essShift δ).representative_iff A 2 (by decide) p s x e).mp he)

private theorem detects_transport {A : SyntheticObject} {i j : Tridegree} (h : i=j)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (A.obj model.nu model.auxiliary))
    (ha : Detects (model.convergence A) i x a) :
    Detects (model.convergence A) j (regradeE2 h x)
      (homotopyRegrade (congrArg (fun k : Tridegree => k.2.1-k.1) h)
        (congrArg (fun k : Tridegree => k.2.2) h) a) := by
  subst j
  exact ha

private theorem representative_transport {A : SyntheticAdamsSS.{0}} {i j : Tridegree} (h : i=j)
    (x : A.E₂ i) (e : (A.sequence.ssData i).eInfty)
    (he : HasInfinityRepresentative A 2 i x e) :
    HasInfinityRepresentative A 2 j (regradeE2 h x)
      ((eqToHom (congrArg (fun k => (A.sequence.ssData k).eInfty) h)) e) := by
  subst j
  exact he

private theorem map_regrade {A B : SyntheticSpectrum} (f : A ⟶ B) {i j : Tridegree} (h : i=j)
    (x : (model.family.obj A).E₂ i) :
    familyPageMap model.family f 2 j (regradeE2 h x) =
      regradeE2 h (familyPageMap model.family f 2 i x) := by
  subst j
  rfl

private theorem zero_weight_label (X : ClassicalObject) (q : ℕ) (s t : ℤ) (y : ((model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))) :
    (model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap 2 (s,t,t)
      (nuWeightLabel model X s t t (by omega) y) =
    regradeE2 (by simp) (finiteTargetLabel model X q s t 0 y) := by
  unfold nuWeightLabel
  have transport (j : ℕ) (hj : j=0) (h : (s,t,t-j)=(s,t,t)) :
      familyPageMap model.family (XModLambdaN.incl _ q) 2 (s,t,t)
        (regradeE2 h (targetNuLabel model X s t j y)) =
      regradeE2 (by simp) (finiteTargetLabel model X q s t 0 y) := by
    subst j
    exact map_regrade _ h _
  exact transport _ (by omega) _

private theorem infinity_map_regrade {A B : SyntheticSpectrum} (f : A ⟶ B) {i j : Tridegree} (h : i=j)
    (x : ((model.family.obj A).sequence.ssData i).eInfty) :
    ((eqToHom (congrArg (fun k => ((model.family.obj B).sequence.ssData k).eInfty) h)))
      ((model.family.map f).eInftyMap i x) =
    (model.family.map f).eInftyMap j
      ((eqToHom (congrArg (fun k => ((model.family.obj A).sequence.ssData k).eInfty) h)) x) := by
  subst j
  rfl

private theorem regrade_precomp {m m' w w' : ℤ} {A : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) :
    homotopyRegrade hm hw a =
      eqToHom (congrArg (fun p : ℤ × ℤ => Smn p.1 p.2 (Syn := SyntheticSpectrum))
        (show (m',w')=(m,w) by rw [hm,hw])) ≫ a := by
  subst m'; subst w'
  change a = 𝟙 _ ≫ a
  simp only [Category.id_comp]

private theorem first_label_detects_unshifted
    (X : ClassicalObject) (s t : ℤ) (x : ((model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (ha : a = KIP126.Literature.firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (model.convergence (.quotient 1 (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X 1 s t 0 x)) a := by
  let Z := model.nu.functor.obj (X.obj model.auxiliary)
  let f : KIP126.Literature.nuZero model X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
  have h0 : (s,t,t+0-(0:ℕ))=(s,t,t) := by simp
  let x0 : (model.family.obj (KIP126.Literature.nuZero model X)).E₂ (s,t,t) :=
    (congrArg (fun i => ((model.family.obj (KIP126.Literature.nuZero model X)).E₂ i : Type)) h0).mp
      (model.comparison.nuE2 X 0 s t 0 x)
  let xq0 (n : ℕ) := familyPageMap model.family (XModLambdaN.incl (KIP126.Literature.nuZero model X) n) 2 (s,t,t) x0
  let xq (n : ℕ) := familyPageMap model.family (XModLambdaN.incl Z n) 2 (s,t,t)
    (familyPageMap model.family f 2 (s,t,t) x0)
  have map_label (n : ℕ) :
      familyPageMap model.family (XModLambdaN.map f n) 2 (s,t,t) (xq0 n) = xq n := by
    dsimp only [xq0,xq]
    rw [←ModuleCat.comp_apply,family_page_comp,←XModLambdaN.incl_naturality]
    rw [←family_page_comp,ModuleCat.comp_apply]
  have map_cast {A B : SyntheticSpectrum} (g : A ⟶ B) {i j : Tridegree} (h : i=j)
      (x : (model.family.obj A).E₂ i) :
      (congrArg (fun k => ((model.family.obj B).E₂ k : Type)) h).mp
        (familyPageMap model.family g 2 i x) =
      familyPageMap model.family g 2 j
        ((congrArg (fun k => ((model.family.obj A).E₂ k : Type)) h).mp x) := by
    subst j
    rfl
  have hb0 : Detects (model.convergence (.quotient 1 (.shift (0,0) (.nu X))))
      (s,t,t) (xq0 1) (KIP126.Literature.firstLabel model X s t x) := by
    have transport_detects {A : SyntheticObject} {i j : Tridegree} (h : i=j)
        (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ i)
        (a : BiHom (i.2.1-i.1) i.2.2 (A.obj model.nu model.auxiliary))
        (ha : Detects (model.convergence A) i x a) :
        Detects (model.convergence A) j
          ((congrArg (fun k => ((model.family.obj (A.obj model.nu model.auxiliary)).E₂ k : Type)) h).mp x)
          ((congrArg (fun k : Tridegree => BiHom (k.2.1-k.1) k.2.2 (A.obj model.nu model.auxiliary)) h).mp a) := by
      subst j
      exact ha
    have h1 : (s,t,t+0)=(s,t,t) := by simp
    have h01 : (s,t,t+0-(0:ℕ))=(s,t,t+0) := by simp only [Nat.cast_zero,sub_zero]
    let x1 : (model.family.obj (KIP126.Literature.nuZero model X)).E₂ (s,t,t+0) :=
      (congrArg (fun k => ((model.family.obj (KIP126.Literature.nuZero model X)).E₂ k : Type)) h01).mp
        (model.comparison.nuE2 X 0 s t 0 x)
    let a1 : BiHom (t-s) (t+0) (XModLambdaN (KIP126.Literature.nuZero model X) 1) :=
      (model.firstQuotient X 0 s t).symm x
    have hr : Detects (model.convergence (.quotient 1 (.shift (0,0) (.nu X)))) (s,t,t+0)
        (familyPageMap model.family (XModLambdaN.incl (KIP126.Literature.nuZero model X) 1) 2 (s,t,t+0) x1) a1 :=
      model.comparisonCompatible.first_quotient X 0 s t x
    have hh := transport_detects h1 _ _ hr
    have cast_comp {A B C : Type} (hAB : A=B) (hBC : B=C) (hAC : A=C) (a : A) :
        hBC.mp (hAB.mp a) = hAC.mp a := by
      subst B
      subst C
      rfl
    have hx1 : (congrArg (fun k => ((model.family.obj (KIP126.Literature.nuZero model X)).E₂ k : Type)) h1).mp x1 = x0 := by
      exact cast_comp
        (congrArg (fun k => ((model.family.obj (KIP126.Literature.nuZero model X)).E₂ k : Type)) h01)
        (congrArg (fun k => ((model.family.obj (KIP126.Literature.nuZero model X)).E₂ k : Type)) h1)
        (congrArg (fun k => ((model.family.obj (KIP126.Literature.nuZero model X)).E₂ k : Type)) h0)
        (model.comparison.nuE2 X 0 s t 0 x)
    have hlabel : (congrArg (fun k => ((model.family.obj (XModLambdaN (KIP126.Literature.nuZero model X) 1)).E₂ k : Type)) h1).mp
        (familyPageMap model.family (XModLambdaN.incl (KIP126.Literature.nuZero model X) 1) 2 (s,t,t+0) x1) = xq0 1 :=
      (map_cast _ h1 x1).trans (congrArg (familyPageMap model.family (XModLambdaN.incl (KIP126.Literature.nuZero model X) 1)
        2 (s,t,t)) hx1)
    have halabel : (congrArg (fun k : Tridegree => BiHom (k.2.1-k.1) k.2.2
        (XModLambdaN (KIP126.Literature.nuZero model X) 1)) h1).mp a1 = KIP126.Literature.firstLabel model X s t x := by
      rfl
    exact (congrArg₂ (fun z a => Detects (model.convergence (.quotient 1 (.shift (0,0) (.nu X))))
      (s,t,t) z a) hlabel halabel).mp hh
  have hb := detects_map (.quotient 1 (.shift (0,0) (.nu X))) (.quotient 1 (.nu X))
    (XModLambdaN.map f 1) (s,t,t) _ _ hb0
  have hb' : Detects (model.convergence (.quotient 1 (.nu X))) (s,t,t) (xq 1)
      (KIP126.Literature.firstLabel model X s t x ≫ XModLambdaN.map f 1) :=
    (congrArg (fun z => Detects (model.convergence (.quotient 1 (.nu X))) (s,t,t) z
      (KIP126.Literature.firstLabel model X s t x ≫ XModLambdaN.map f 1)) (map_label 1)).mp hb
  rw [ha]
  convert hb' using 1
  unfold finiteTargetLabel
  rw [← map_regrade]
  unfold targetNuLabel
  rw [← map_regrade]
  congr 2
  have cast_heq {A B : Type} (h : A=B) (a : A) : HEq (h.mp a) a := by cases h; rfl
  have eqToHom_heq {A B : ModuleCat.{0} ℤ} (h : A=B) (a : A) : HEq ((eqToHom h) a) a := by
    cases h; rfl
  exact eq_of_heq ((eqToHom_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))
private theorem subquotientMap_injective {R : Type*} [Ring R] {A : Type*} [AddCommGroup A] [Module R A]
    {Z Z' B : Submodule R A} (hZ : Z ≤ Z') :
    Function.Injective (KIP126.Literature.subquotientMap hZ (le_rfl : B ≤ B)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro x hx
    obtain ⟨x,rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change KIP126.Literature.subquotientMap hZ (le_rfl : B ≤ B) (Submodule.Quotient.mk x) = 0 at hx
    change Submodule.Quotient.mk (Submodule.inclusion hZ x) = 0 at hx
    have hxB := (Submodule.Quotient.mk_eq_zero _).mp hx
    change x.val ∈ B at hxB
    change Submodule.Quotient.mk x = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hxB
  · exact bot_le

private theorem nu_bottom_filtration (X : ClassicalObject) (s t : ℤ)
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary))) :
    FiltrationAtLeast model.syntheticTower s a := by
  have hzero := KIP126.Literature.Standard.selectedFiltration_filtration_at_zero model.syntheticTower _ (t-s) t a
  by_cases hs : s ≤ 0
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (t-s,t) hs hzero
  · exact (KIP126.Literature.Standard.selectedFiltration_filtration_iff_of_infinity_zero (model.convergence (.nu X))
      0 s (t-s) t (by omega)
      (fun k _ hk => KIP126.Literature.Standard.selectedFiltration_nu_above_zero X k (t-s+k) t (by omega)) a).mp hzero

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
    (x : ((model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))) (hx : x ∈ KIP126.Literature.permanentCycles model X (s,t))
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1 = KIP126.Literature.firstLabel model X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (model.convergence (.nu X)) (s,t,t)
      (nuWeightLabel model X s t t (by omega) x) a := by
  let e := (KIP126.Literature.Standard.infinityNuWindow X (s,t) t (by omega)).symm
    (subquotientClass (KIP126.Literature.permanentCycles model X (s,t)) (KIP126.Literature.boundaries model X (1+t-t) (s,t)) ⟨x,hx⟩)
  have he : HasInfinityRepresentative _ 2 (s,t,t) (nuWeightLabel model X s t t (by omega) x) e := by
    apply (KIP126.Literature.Standard.eInfinity_nu_labels X s t t (by omega) x e).mpr
    exact ⟨hx,(KIP126.Literature.Standard.infinityNuWindow X (s,t) t (by omega)).apply_symm_apply _⟩
  apply detects_reflect (.nu X) (.quotient 1 (.nu X)) (XModLambdaN.incl _ 1)
    (s,t,t) (nu_projection_infinity_injective X 1 (by omega) s t t (by omega))
    _ e he a (nu_bottom_filtration X s t a)
  have hz := zero_weight_label X 1 s t x
  change familyPageMap model.family (XModLambdaN.incl _ 1) 2 (s,t,t)
    (nuWeightLabel model X s t t (by omega) x) = _ at hz
  have hd := first_label_detects_unshifted X s t x (a ≫ XModLambdaN.incl _ 1) ha
  exact (congrArg (fun z => Detects (model.convergence (.quotient 1 (.nu X))) (s,t,t) z
    (a ≫ XModLambdaN.incl _ 1)) hz).mpr hd

private theorem nu_lambda_detects (X : ClassicalObject) (k : ℕ) (hk : 0 < k)
    (s t : ℤ) (y : ((model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)))
    (hy : y ∈ KIP126.Literature.permanentCycles model X (s,t))
    (α : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (hα : α ≫ XModLambdaN.incl _ 1 = KIP126.Literature.firstLabel model X s t y ≫
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
    delta KIP126.Literature.Standard.infinityLambda
      InfinityShiftCoordinates.lambdaMap InfinityShiftCoordinates.shift infinityShift
      KIP126.Literature.Standard.infinityShiftData
      KIP126.Literature.Standard.infinityShift_comparison
    dsimp only []
    simp only [show k ≠ 0 by omega, ↓reduceDIte,
      Iso.trans_hom, ModuleCat.comp_apply, eqToIso.hom]
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
  repeat rw [regrade_precomp]
  delta lambdaMultiply
  simp only [L, shiftHomotopyClass, Category.assoc]
  simp only [A]
  erw [lambdaPow_naturality k α]
  simp only [←Category.assoc,eqToHom_trans]

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


private theorem normalizeInitialProjection
    (P : SSData (ModuleCat.{0} ℤ)) (n m : WithTop ℕ)
    (hn : n = 0) (hnm : n ≤ m) :
    Subobject.ofLE (P.Z m) (P.Z n) (P.Z_anti hnm) ≫ P.pageπ n =
      Subobject.ofLE (P.Z m) (P.Z 0) (P.Z_anti bot_le) ≫ P.pageπ 0 ≫
        eqToHom (congrArg P.page hn.symm) := by
  subst n
  simp only [eqToHom_refl, Category.comp_id]

private theorem boundary_represents_zero (X : ClassicalObject) (r : ℤ) (hr : 2 ≤ r)
    (p : Bidegree) (y : (model.classical.obj (X.obj model.auxiliary)).Page 2 p)
    (hy : y ∈ KIP126.Literature.boundaries model X (r-1) p) :
    RepresentsOnPage (model.classical.obj (X.obj model.auxiliary)) r p y 0 := by
  let E := model.classical.obj (X.obj model.auxiliary)
  let P := E.ssData p
  let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  have hn₀ : n₀=0 := by dsimp [n₀,E]; rw [model.classical.firstPage]; rfl
  have hn : (↑(r-1-1).toNat : WithTop ℕ)=n := by
    dsimp [n,E]; rw [model.classical.firstPage]; congr 2; omega
  change ∃ b, boundaryLabel model X (↑(r-1-1).toNat) p b = y at hy
  rw [hn] at hy
  obtain ⟨b,hb⟩ := hy
  let j := Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n)
  refine ⟨hr,j b,?_,?_⟩
  · change (j ≫ Subobject.ofLE (P.Z n) (P.Z n₀) _ ≫ P.pageπ n₀) b=y
    rw [normalizeInitialProjection P n₀ n hn₀ (by rw [hn₀]; exact bot_le)]
    change ((j ≫ Subobject.ofLE (P.Z n) (P.Z 0) _) ≫ P.pageπ 0 ≫ _) b=y
    rw [show j ≫ Subobject.ofLE (P.Z n) (P.Z 0) _ =
      Subobject.ofLE (P.B n) (P.Z 0) _ by simp only [j,Subobject.ofLE_comp_ofLE]]
    exact hb
  · exact (P.pageπ_eq_zero_iff n (j b)).mpr ⟨b,rfl⟩

private theorem permanent_membership (X : ClassicalObject) (s t : ℤ)
    (y : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (hy : ClassicalPermanentCycle model X (s,t) y) : y ∈ KIP126.Literature.permanentCycles model X (s,t) := by
  obtain ⟨z,hz⟩ := hy
  refine ⟨z,?_⟩
  have h := normalizeInitialProjection ((model.classical.obj (X.obj model.auxiliary)).ssData (s,t))
    (↑(2-(model.classical.obj (X.obj model.auxiliary)).r₀).toNat)
    ⊤ (by rw [model.classical.firstPage]; rfl) le_top
  exact (congrArg (fun f => f z) h).symm.trans hz

private theorem subquotient_zero_iff {R A : Type*} [Ring R] [AddCommGroup A] [Module R A]
    (Z B : Submodule R A) (y : Z) : subquotientClass Z B y = 0 ↔ y.val ∈ B :=
  Submodule.Quotient.mk_eq_zero _

private theorem lifetime_candidate :
  ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (a : BiHom (t-s) t (KIP126.Literature.nuZero model X)),
    ClassicalPermanentCycle model X (s,t) x →
    SurvivesTo (model.classical.obj (X.obj model.auxiliary)) (r+1) (s,t) x →
    quotientClass 1 a = KIP126.Literature.firstLabel model X s t x → lambdaMultiply (r-1) a ≠ 0 := by
  intro X s t r hr x a hx hsurv hlabel hz
  let α := a ≫ SyntheticCategory.biShift_zero.hom.app _
  have hα : α ≫ XModLambdaN.incl _ 1 = KIP126.Literature.firstLabel model X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
    dsimp only [α]
    rw [Category.assoc, XModLambdaN.incl_naturality, ←Category.assoc]
    exact congrArg (fun z => z ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) hlabel
  have hzero : lambdaMultiply (r-1) α = 0 := by
    have h : lambdaMultiply (r-1) a ≫ SyntheticCategory.biShift_zero.hom.app _ = 0 := by
      rw [hz, zero_comp]
    delta lambdaMultiply at h ⊢
    simpa only [α, Category.assoc] using h
  have hmem := permanent_membership X s t x hx
  have hbound : x ∈ KIP126.Literature.boundaries model X r (s,t) := by
    by_cases hk : 0 < r-1
    · have hd := nu_lambda_detects X (r-1) hk s t x hmem α hα
      rw [hzero] at hd
      have he := detected_zero_infinity (.nu X) (s,t,t-(r-1:ℕ)) _ hd
      have hclass := (KIP126.Literature.Standard.eInfinity_nu_labels X s t (t-(r-1:ℕ)) (by omega) x 0).mp he
      have hb : x ∈ KIP126.Literature.boundaries model X (1+t-(t-(r-1:ℕ))) (s,t) :=
        (subquotient_zero_iff _ _ ⟨x,hclass.1⟩).mp (by rw [←hclass.2,map_zero])
      convert hb using 1
      congr 1
      omega
    · have hr1 : r=1 := by omega
      subst r
      have hzα : α=0 := by
        have h := KIP126.Literature.Standard.lambdaMultiplyZero α
        have hz' : lambdaMultiply 0 α=0 := hzero
        have zero_cast {w w' : ℤ} (h : w=w') : HEq (0 : BiHom (t-s) w (model.nu.functor.obj (X.obj model.auxiliary))) (0 : BiHom (t-s) w' (model.nu.functor.obj (X.obj model.auxiliary))) := by cases h; rfl
        exact eq_of_heq (h.symm.trans ((heq_of_eq hz').trans (zero_cast (by simp))))
      have hd := nu_first_label_detects X s t x hmem α hα
      rw [hzα] at hd
      have he := detected_zero_infinity (.nu X) (s,t,t) _ hd
      have hclass := (KIP126.Literature.Standard.eInfinity_nu_labels X s t t (by omega) x 0).mp he
      have hb : x ∈ KIP126.Literature.boundaries model X (1+t-t) (s,t) :=
        (subquotient_zero_iff _ _ ⟨x,hclass.1⟩).mp (by rw [←hclass.2,map_zero])
      convert hb using 1
      congr 1
      omega
  obtain ⟨xr,hrep,hne⟩ := hsurv
  exact hne (hrep.unique (boundary_represents_zero X (r+1) (by omega) (s,t) x (by
    simpa only [add_sub_cancel_right] using hbound)))


private theorem permanent_of_membership (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (hx : x ∈ KIP126.Literature.permanentCycles model X (s,t)) :
    ClassicalPermanentCycle model X (s,t) x := by
  obtain ⟨z,hz⟩ := hx
  refine ⟨z,?_⟩
  have h := normalizeInitialProjection ((model.classical.obj (X.obj model.auxiliary)).ssData (s,t))
    (↑(2-(model.classical.obj (X.obj model.auxiliary)).r₀).toNat)
    ⊤ (by rw [model.classical.firstPage]; rfl) le_top
  exact (congrArg (fun f => f z) h).trans hz

private theorem finite_first_detection_unique (X : ClassicalObject) (s t : ℤ)
    (x : (model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) 1).E₂ (s,t,t))
    (a b : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (ha : Detects (model.convergence (.quotient 1 (.nu X))) (s,t,t) x a)
    (hb : Detects (model.convergence (.quotient 1 (.nu X))) (s,t,t) x b) : a=b := by
  have hf := detects_sub_filtration (model.convergence (.quotient 1 (.nu X))) (s,t,t) ha hb
  apply sub_eq_zero.mp
  exact Standard.selectedFiltration_finite_high_filtration_zero X 1 (by decide)
    (t-s) t (s+1) (by omega) (a-b) hf

private theorem projection_eq_first_of_detects (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : Detects (model.convergence (.nu X)) (s,t,t)
      (nuWeightLabel model X s t t (by omega) x) a) :
    a ≫ XModLambdaN.incl _ 1 = firstLabel model X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  have hp := detects_map (.nu X) (.quotient 1 (.nu X)) (XModLambdaN.incl _ 1)
    (s,t,t) _ _ ha
  have hz := zero_weight_label X 1 s t x
  change familyPageMap model.family (XModLambdaN.incl _ 1) 2 (s,t,t)
    (nuWeightLabel model X s t t (by omega) x) = _ at hz
  have hp' := (congrArg (fun z => Detects (model.convergence (.quotient 1 (.nu X)))
    (s,t,t) z (a ≫ XModLambdaN.incl _ 1)) hz).mp hp
  exact finite_first_detection_unique X s t _ _ _ hp'
    (first_label_detects_unshifted X s t x _ rfl)

private theorem detects_lift_exists (X : ClassicalObject) (s t : ℤ)
    (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (hx : x ∈ KIP126.Literature.permanentCycles model X (s,t)) :
    ∃ a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)),
      Detects (model.convergence (.nu X)) (s,t,t)
        (nuWeightLabel model X s t t (by omega) x) a := by
  let e := (Standard.infinityNuWindow X (s,t) t (by omega)).symm
    (subquotientClass (KIP126.Literature.permanentCycles model X (s,t))
      (KIP126.Literature.boundaries model X (1+t-t) (s,t)) ⟨x,hx⟩)
  have he : HasInfinityRepresentative _ 2 (s,t,t) (nuWeightLabel model X s t t (by omega) x) e := by
    apply (Standard.eInfinity_nu_labels X s t t (by omega) x e).mpr
    exact ⟨hx,(Standard.infinityNuWindow X (s,t) t (by omega)).apply_symm_apply _⟩
  let F := model.syntheticTower.filtration (model.nu.functor.obj (X.obj model.auxiliary))
  letI : Epi (F.toAssociatedGraded s (t-s,t)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨b,hb⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s (t-s,t))).mp
    inferInstance (((model.convergence (.nu X)).identification (s,t,t)).hom e)
  exact ⟨(F.F s (t-s,t)).arrow b,e,he,b,rfl,hb.symm⟩

private theorem subquotientClass_surjective {R A : Type*} [Ring R]
    [AddCommGroup A] [Module R A] (Z B : Submodule R A) :
    Function.Surjective (subquotientClass Z B) :=
  Submodule.mkQ_surjective _

private theorem detects_permanent_label (X : ClassicalObject) (s t : ℤ)
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary))) :
    ∃ x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t),
      ClassicalPermanentCycle model X (s,t) x ∧
      Detects (model.convergence (.nu X)) (s,t,t)
        (nuWeightLabel model X s t t (by omega) x) a := by
  obtain ⟨b,hb⟩ := filtration_representative_exists _ (t-s,t) s a (nu_bottom_filtration X s t a)
  let e := ((model.convergence (.nu X)).identification (s,t,t)).inv
    ((model.syntheticTower.filtration _).toAssociatedGraded s (t-s,t) b)
  obtain ⟨x,hx⟩ := subquotientClass_surjective _ _
    (Standard.infinityNuWindow X (s,t) t (by omega) e)
  refine ⟨x.val,permanent_of_membership X s t x.val x.property,e,?_,b,hb,?_⟩
  · exact (Standard.eInfinity_nu_labels X s t t (by omega) x.val e).mpr ⟨x.property,hx.symm⟩
  · exact ((model.convergence (.nu X)).identification (s,t,t)).toLinearEquiv.apply_symm_apply _

private theorem first_label_injective (X : ClassicalObject) (s t : ℤ) :
    Function.Injective (firstLabel model X s t) := by
  intro x y h
  apply (model.firstQuotient X 0 s t).symm.injective
  have cast_inj {A B : Type} (hAB : A=B) (x y : A) (h : hAB.mp x = hAB.mp y) : x=y := by
    cases hAB
    exact h
  unfold firstLabel at h
  exact cast_inj _ _ _ h

private theorem permanent_lift_candidate : ∀ X : ClassicalObject, PermanentLiftAt model X := by
  intro X s t x
  let Z := model.nu.functor.obj (X.obj model.auxiliary)
  let f : nuZero model X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
  let g : Z ⟶ nuZero model X := SyntheticCategory.biShift_zero.inv.app _
  letI : IsIso f := inferInstanceAs (IsIso (SyntheticCategory.biShift_zero.hom.app _))
  letI : IsIso (XModLambdaN.map f 1) :=
    inferInstanceAs (IsIso ((model.quotients.functoriality.functor 1).map f))
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := detects_lift_exists X s t x (permanent_membership X s t x hx)
    refine ⟨a ≫ g,?_⟩
    have hp := projection_eq_first_of_detects X s t x a ha
    apply (cancel_mono (XModLambdaN.map f 1)).mp
    change ((a ≫ g) ≫ XModLambdaN.incl _ 1) ≫ XModLambdaN.map f 1 = _
    rw [Category.assoc]
    rw [←XModLambdaN.incl_naturality]
    simpa only [f,g,Category.assoc,Iso.inv_hom_id_app_assoc] using hp
  · rintro ⟨a,ha⟩
    obtain ⟨y,hy,hd⟩ := detects_permanent_label X s t (a ≫ f)
    have hp := projection_eq_first_of_detects X s t y (a ≫ f) hd
    have hh : firstLabel model X s t x = firstLabel model X s t y := by
      apply (cancel_mono (XModLambdaN.map f 1)).mp
      rw [←hp,Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
      exact congrArg (fun z => z ≫ XModLambdaN.map f 1) ha.symm
    exact (first_label_injective X s t hh).symm ▸ hy


private theorem reaches_iff_cycle (X : ClassicalObject) (q : ℕ) (hq : 0<q)
    (s t : ℤ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t)) :
    ReachesPage (model.classical.obj (X.obj model.auxiliary)) (q+1) (s,t) x ↔
      x ∈ KIP126.Literature.cycles model X q (s,t) := by
  let E := model.classical.obj (X.obj model.auxiliary)
  let P := E.ssData (s,t)
  let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
  let n : WithTop ℕ := ↑((q:ℤ)+1-E.r₀).toNat
  have hn₀ : n₀=0 := by dsimp [n₀,E]; rw [model.classical.firstPage]; rfl
  have hn : (↑((q:ℤ)-1).toNat : WithTop ℕ)=n := by
    dsimp [n,E]; rw [model.classical.firstPage]; congr 2; omega
  change (∃ xr, RepresentsOnPage E (q+1) (s,t) x xr) ↔
    ∃ z, cycleLabel model X (↑((q:ℤ)-1).toNat) (s,t) z = x
  rw [hn]
  constructor
  · rintro ⟨xr,hr,z,hz,_⟩
    refine ⟨z,?_⟩
    have h := normalizeInitialProjection P n₀ n hn₀ (by rw [hn₀]; exact bot_le)
    exact (congrArg (fun f => f z) h).symm.trans hz
  · rintro ⟨z,hz⟩
    refine ⟨P.pageπ n z,by omega,z,?_,rfl⟩
    have h := normalizeInitialProjection P n₀ n hn₀ (by rw [hn₀]; exact bot_le)
    exact (congrArg (fun f => f z) h).trans hz

private theorem finite_bottom_filtration (X : ClassicalObject) (q : ℕ) (hq : 0<q)
    (s t : ℤ) (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    FiltrationAtLeast model.syntheticTower s a := by
  have hzero := Standard.selectedFiltration_filtration_at_zero model.syntheticTower _ (t-s) t a
  by_cases hs : s ≤ 0
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (t-s,t) hs hzero
  · exact (Standard.selectedFiltration_filtration_iff_of_infinity_zero
      (model.convergence (.quotient q (.nu X))) 0 s (t-s) t (by omega)
      (fun k _ hk => Standard.selectedFiltration_finite_infinity_zero_outside X q hq k
        (t-s+k) t (by omega)) a).mp hzero

private theorem finite_detects_lift_exists (X : ClassicalObject) (q : ℕ) (hq : 0<q)
    (s t : ℤ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (hx : x ∈ KIP126.Literature.cycles model X q (s,t)) :
    ∃ a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
      Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
        (familyPageMap model.family (XModLambdaN.incl _ q) 2 (s,t,t)
          (nuWeightLabel model X s t t (by omega) x)) a := by
  have hx' : x ∈ KIP126.Literature.cycles model X ((q:ℤ)-t+t) (s,t) := by simpa using hx
  let e := (Standard.infinityFiniteWindow X q hq (s,t) t (by omega)).symm
    (subquotientClass (KIP126.Literature.cycles model X ((q:ℤ)-t+t) (s,t))
      (KIP126.Literature.boundaries model X (1+t-t) (s,t)) ⟨x,hx'⟩)
  have he : HasInfinityRepresentative _ 2 (s,t,t)
      (familyPageMap model.family (XModLambdaN.incl _ q) 2 (s,t,t)
        (nuWeightLabel model X s t t (by omega) x)) e := by
    apply (Standard.eInfinity_finite_labels X q hq s t t (by omega) x e).mpr
    exact ⟨hx',(Standard.infinityFiniteWindow X q hq (s,t) t (by omega)).apply_symm_apply _⟩
  let F := model.syntheticTower.filtration (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)
  letI : Epi (F.toAssociatedGraded s (t-s,t)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨b,hb⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s (t-s,t))).mp
    inferInstance (((model.convergence (.quotient q (.nu X))).identification (s,t,t)).hom e)
  exact ⟨(F.F s (t-s,t)).arrow b,e,he,b,rfl,hb.symm⟩

private theorem finite_detects_cycle_label (X : ClassicalObject) (q : ℕ) (hq : 0<q)
    (s t : ℤ) (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    ∃ x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t),
      x ∈ KIP126.Literature.cycles model X q (s,t) ∧
      Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
        (familyPageMap model.family (XModLambdaN.incl _ q) 2 (s,t,t)
          (nuWeightLabel model X s t t (by omega) x)) a := by
  obtain ⟨b,hb⟩ := filtration_representative_exists _ (t-s,t) s a
    (finite_bottom_filtration X q hq s t a)
  let e := ((model.convergence (.quotient q (.nu X))).identification (s,t,t)).inv
    ((model.syntheticTower.filtration _).toAssociatedGraded s (t-s,t) b)
  obtain ⟨x,hx⟩ := subquotientClass_surjective _ _
    (Standard.infinityFiniteWindow X q hq (s,t) t (by omega) e)
  refine ⟨x.val,by simpa using x.property,e,?_,b,hb,?_⟩
  · exact (Standard.eInfinity_finite_labels X q hq s t t (by omega) x.val e).mpr ⟨x.property,hx.symm⟩
  · exact ((model.convergence (.quotient q (.nu X))).identification (s,t,t)).toLinearEquiv.apply_symm_apply _

private theorem finite_restrict_eq_first_of_detects (X : ClassicalObject) (q : ℕ) (hq : 0<q)
    (s t : ℤ) (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (familyPageMap model.family (XModLambdaN.incl _ q) 2 (s,t,t)
        (nuWeightLabel model X s t t (by omega) x)) a) :
    a ≫ (model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho 1 q (by omega) =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  let rho := (model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho 1 q (by omega)
  have hp := detects_map (.quotient q (.nu X)) (.quotient 1 (.nu X)) rho (s,t,t) _ _ ha
  have hz : familyPageMap model.family rho 2 (s,t,t)
      (familyPageMap model.family (XModLambdaN.incl _ q) 2 (s,t,t)
        (nuWeightLabel model X s t t (by omega) x)) =
      regradeE2 (by simp) (finiteTargetLabel model X 1 s t 0 x) := by
    rw [←ModuleCat.comp_apply,family_page_comp]
    dsimp only [rho]
    rw [(model.quotients.tower _).rho_quotient]
    exact zero_weight_label X 1 s t x
  have hp' := (congrArg (fun z => Detects (model.convergence (.quotient 1 (.nu X)))
    (s,t,t) z (a ≫ rho)) hz).mp hp
  exact finite_first_detection_unique X s t _ _ _ hp'
    (first_label_detects_unshifted X s t x _ rfl)

private theorem finite_lift_candidate : FiniteLiftCriterion model := by
  intro X q hq s t x
  let Z := model.nu.functor.obj (X.obj model.auxiliary)
  let f : nuZero model X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
  let g : Z ⟶ nuZero model X := SyntheticCategory.biShift_zero.inv.app _
  letI : IsIso f := inferInstanceAs (IsIso (SyntheticCategory.biShift_zero.hom.app _))
  letI : IsIso (XModLambdaN.map f 1) :=
    inferInstanceAs (IsIso ((model.quotients.functoriality.functor 1).map f))
  have hgf : XModLambdaN.map g 1 ≫ XModLambdaN.map f 1 = 𝟙 _ := by
    rw [←model.quotients.functoriality.map_comp]
    simp only [g,f,Iso.inv_hom_id_app]
    exact model.quotients.functoriality.map_id _ _
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := finite_detects_lift_exists X q hq s t x ((reaches_iff_cycle X q hq s t x).mp hx)
    refine ⟨a ≫ XModLambdaN.map g q,?_⟩
    apply (cancel_mono (XModLambdaN.map f 1)).mp
    have hp := finite_restrict_eq_first_of_detects X q hq s t x a ha
    have hrho := (model.quotients.natural g).rho_naturality (i:=1) (j:=q) (by omega)
    have he := congrArg (fun z => (a ≫ z) ≫ XModLambdaN.map f 1) hrho.symm
    have he' : ((a ≫ XModLambdaN.map g q) ≫
        (model.quotients.tower (nuZero model X)).rho 1 q (by omega)) ≫ XModLambdaN.map f 1 =
        a ≫ (model.quotients.tower Z).rho 1 q (by omega) := by
      repeat rw [Category.assoc] at he
      rw [hgf, Category.comp_id] at he
      repeat rw [Category.assoc]
      exact he
    exact he'.trans hp
  · rintro ⟨a,ha⟩
    obtain ⟨y,hy,hd⟩ := finite_detects_cycle_label X q hq s t (a ≫ XModLambdaN.map f q)
    have hp := finite_restrict_eq_first_of_detects X q hq s t y _ hd
    have hh : firstLabel model X s t x = firstLabel model X s t y := by
      apply (cancel_mono (XModLambdaN.map f 1)).mp
      rw [←hp,Category.assoc,←(model.quotients.natural f).rho_naturality,←Category.assoc]
      exact congrArg (fun z => z ≫ XModLambdaN.map f 1) ha.symm
    exact (first_label_injective X s t hh).symm ▸ (reaches_iff_cycle X q hq s t y).mpr hy


private theorem zero_rep_boundary (X : ClassicalObject) (r : ℤ) (p : Bidegree)
    (y : (model.classical.obj (X.obj model.auxiliary)).Page 2 p)
    (hy : RepresentsOnPage (model.classical.obj (X.obj model.auxiliary)) r p y 0) :
    y ∈ KIP126.Literature.boundaries model X (r-1) p := by
  let E := model.classical.obj (X.obj model.auxiliary)
  let P := E.ssData p
  let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  have hn₀ : n₀=0 := by dsimp [n₀,E]; rw [model.classical.firstPage]; rfl
  have hn : (↑(r-1-1).toNat : WithTop ℕ)=n := by
    dsimp [n,E]; rw [model.classical.firstPage]; congr 2; omega
  obtain ⟨hr,z,hz,hz0⟩ := hy
  have hproj := normalizeInitialProjection P n₀ n hn₀ (by rw [hn₀]; exact bot_le)
  have hlabel : cycleLabel model X n p z = y := (congrArg (fun f => f z) hproj).symm.trans hz
  obtain ⟨b,hb⟩ := (P.pageπ_eq_zero_iff n z).mp hz0
  change ∃ b, boundaryLabel model X (↑(r-1-1).toNat) p b = y
  rw [hn]
  refine ⟨b,?_⟩
  have hcomp : Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n) ≫
      cycleLabel model X n p = boundaryLabel model X n p := by
    dsimp only [P,E]
    delta cycleLabel boundaryLabel
    simp only [←Category.assoc,Subobject.ofLE_comp_ofLE]
  rw [←hcomp,ModuleCat.comp_apply,hb]
  exact hlabel

private theorem hit_boundary (X : ClassicalObject) (r : ℕ) (hr : 2≤r)
    (p : Bidegree) (y : (model.classical.obj (X.obj model.auxiliary)).Page 2 p)
    (hy : HitOnPage (model.classical.obj (X.obj model.auxiliary)) r p y) :
    y ∈ KIP126.Literature.boundaries model X r p := by
  obtain ⟨q,h,z,yr,hyr,_,hd⟩ := hy
  obtain ⟨x,hx⟩ := FinitePageCalculus.page_has_representative (by omega : 2≤(r:ℤ)) z
  have heq : HasDifferential (model.classical.obj (X.obj model.auxiliary)) r q p x y :=
    ⟨h,z,yr,hx,hyr,hd⟩
  have hz := FinitePageCalculus.differential_target_later_zero
    (t:=(r:ℤ)+1) (by rw [model.classical.firstPage]; omega) (by omega) heq
  simpa only [add_sub_cancel_right] using zero_rep_boundary X ((r:ℤ)+1) p y hz

private theorem regrade_heq {m m' w w' : ℤ} {A : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) : HEq (homotopyRegrade hm hw a) a := by
  subst m'; subst w'; rfl

private theorem regrade_zero {m m' w w' : ℤ} {A : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') : homotopyRegrade hm hw (0 : BiHom m w A) = 0 := by
  subst m'; subst w'; rfl

private theorem lambda_quotient_zero {m w : ℤ} {A : SyntheticSpectrum}
    (a : BiHom m w A) : quotientClass 1 (lambdaMultiply 1 a) = 0 := by
  delta quotientClass lambdaMultiply
  rw [←lambdaPow_naturality]
  simp only [Category.assoc,XModLambdaN.lambdaPow_comp_incl,comp_zero]

private theorem boundary_lift_unshifted (X : ClassicalObject) (r : ℕ) (hr : 2≤r)
    (s t : ℤ) (y : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
    (hy : ClassicalPermanentCycle model X (s,t) y)
    (hhit : HitOnPage (model.classical.obj (X.obj model.auxiliary)) r (s,t) y) :
    ∃ a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)),
      a ≫ XModLambdaN.incl _ 1 = firstLabel model X s t y ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      lambdaMultiply (r-1) a = 0 := by
  let k := r-1
  have hk : 0<k := by dsimp [k]; omega
  have hym := permanent_membership X s t y hy
  obtain ⟨α,hα⟩ := detects_lift_exists X s t y hym
  have hlabel := projection_eq_first_of_detects X s t y α hα
  have hdet := nu_lambda_detects X k hk s t y hym α hlabel
  have hbound := hit_boundary X r hr (s,t) y hhit
  have hinf0 : HasInfinityRepresentative _ 2 (s,t,t-k)
      (nuWeightLabel model X s t (t-k) (by omega) y) 0 := by
    apply (Standard.eInfinity_nu_labels X s t (t-k) (by omega) y 0).mpr
    refine ⟨hym,?_⟩
    rw [map_zero]
    symm
    apply (subquotient_zero_iff _ _ ⟨y,hym⟩).mpr
    convert hbound using 1
    congr 1
    dsimp [k]
    omega
  have hf := detects_zero_infinity_filtration (model.convergence (.nu X)) (s,t,t-k) hdet hinf0
  obtain ⟨β,hβ⟩ := (Standard.selected_filtration_lambda X (t-s) (t-k) (s+1) (by omega)
    (lambdaMultiply k α)).mp hf
  let b : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)) :=
    homotopyRegrade rfl (by omega : ((t-s)+(s+1))-(1:ℕ)=t) (lambdaMultiply 1 β)
  have hb0 : b ≫ XModLambdaN.incl _ 1 = 0 := by
    change homotopyRegrade _ _ (lambdaMultiply 1 β) ≫ XModLambdaN.incl _ 1 = 0
    rw [←regrade_comp]
    have hz := lambda_quotient_zero β
    change lambdaMultiply 1 β ≫ XModLambdaN.incl _ 1 = 0 at hz
    rw [hz]
    exact regrade_zero _ _
  have hbα : lambdaMultiply k b = lambdaMultiply k α := by
    have hN : ((t-s+(s+1)-(t-(k:ℤ))).toNat) = 1+k := by omega
    have exp_transport (i j : ℕ) (h : i=j) : HEq (lambdaMultiply i β) (lambdaMultiply j β) := by
      subst j
      rfl
    have hβ0 : HEq (lambdaMultiply (1+k) β) (lambdaMultiply k α) :=
      (exp_transport _ _ hN.symm).trans ((regrade_heq _ _ _).symm.trans (heq_of_eq hβ))
    have hbheq := Standard.multiply_heq k (by omega : t=((t-s)+(s+1))-(1:ℕ))
      (regrade_heq rfl (by omega) (lambdaMultiply 1 β))
    have hc := Standard.lambda_multiply_compose 1 k β
    exact eq_of_heq (hbheq.trans (hc.trans hβ0))
  refine ⟨α-b,?_,?_⟩
  · rw [Preadditive.sub_comp,hlabel,hb0,sub_zero]
  · change lambdaMultiply k (α-b)=0
    have hsub : lambdaMultiply k (α-b)=lambdaMultiply k α-lambdaMultiply k b := by
      delta lambdaMultiply
      simp only [Preadditive.comp_sub]
    rw [hsub,hbα,sub_self]

private theorem boundary_lift_candidate :
  ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ y : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t),
    ClassicalPermanentCycle model X (s,t) y →
    HitOnPage (model.classical.obj (X.obj model.auxiliary)) r (s,t) y →
    ∃ a : BiHom (t-s) t (nuZero model X), quotientClass 1 a = firstLabel model X s t y ∧
      lambdaMultiply (r-1) a = 0 := by
  intro X s t r hr y hy hhit
  obtain ⟨a,ha,hak⟩ := boundary_lift_unshifted X r hr s t y hy hhit
  let Z := model.nu.functor.obj (X.obj model.auxiliary)
  let f : nuZero model X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
  let g : Z ⟶ nuZero model X := SyntheticCategory.biShift_zero.inv.app _
  letI : IsIso f := inferInstanceAs (IsIso (SyntheticCategory.biShift_zero.hom.app _))
  letI : IsIso (XModLambdaN.map f 1) :=
    inferInstanceAs (IsIso ((model.quotients.functoriality.functor 1).map f))
  refine ⟨a ≫ g,?_,?_⟩
  · apply (cancel_mono (XModLambdaN.map f 1)).mp
    change ((a ≫ g) ≫ XModLambdaN.incl _ 1) ≫ XModLambdaN.map f 1 = _
    rw [Category.assoc,←XModLambdaN.incl_naturality]
    simpa only [f,g,Category.assoc,Iso.inv_hom_id_app_assoc] using ha
  · have he : lambdaMultiply (r-1) (a ≫ g) = lambdaMultiply (r-1) a ≫ g := by
      delta lambdaMultiply
      simp only [Category.assoc]
    rw [he,hak,zero_comp]

end
end SelectedLifetimeConstruction

/-- Actual finite-window representatives and the fixed restriction maps
identify reaching a page with a lift of the same first-quotient label. -/
public theorem bhs_finite_lift :
  FiniteLiftCriterion model := by
  exact SelectedLifetimeConstruction.finite_lift_candidate

/-- The one-step quotient is concentrated at the matching filtration, so
its detection class determines the actual first-quotient lift. -/
public theorem selected_permanent_lift :
  ∀ X : ClassicalObject, PermanentLiftAt model X := by
  exact SelectedLifetimeConstruction.permanent_lift_candidate

/-- A zero lambda power would put the same first-quotient label in the
earlier boundary submodule, contradicting its specified nonzero survival. -/
public theorem selected_realization_lifetime :
  ∀ (X : ClassicalObject) (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : (model.classical.obj (X.obj model.auxiliary)).Page 2 (s,t))
      (a : BiHom (t-s) t (nuZero model X)),
    ClassicalPermanentCycle model X (s,t) x →
    SurvivesTo (model.classical.obj (X.obj model.auxiliary)) (r+1) (s,t) x →
    quotientClass 1 a = firstLabel model X s t x → lambdaMultiply (r-1) a ≠ 0 := by
  exact SelectedLifetimeConstruction.lifetime_candidate

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
  exact SelectedLifetimeConstruction.boundary_lift_candidate

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
public noncomputable def mapping :
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
