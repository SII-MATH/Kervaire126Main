module

public import KIP126.AdamsSynthetic.System
public import KIP126.AdamsSynthetic.Context
public import KIP126.AdamsSynthetic.Families
public import KIP126.AdamsSynthetic.Sphere
public import KIP126.AdamsSynthetic.Configuration
public import KIP126.SpectralSequence
import all KIP126.AdamsSynthetic.Internal.Milnor.Cohomology
public import KIP126.AdamsSynthetic.Source

/-! The fixed classical and synthetic background used in this project.
Every unfinished construction is named at its mathematical boundary; the
assembled model below has no separate existence assumption. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route
noncomputable section

/-- The category of spectra; its concrete model is a deferred construction. -/
public def Spectrum : Type 1 := by sorry
/-- The category of HF₂-synthetic spectra; its construction is deferred. -/
public def SyntheticSpectrum : Type 1 := by sorry
public instance spectrumCategory : StableHomotopyCategory.{1,0} Spectrum := by sorry
public instance syntheticCategory : SyntheticCategory.{1,0} SyntheticSpectrum := by sorry
public instance spectrumCofiber : HasFunctorialCofiber (C := Spectrum) := by sorry
public instance syntheticCofiber : HasFunctorialCofiber (C := SyntheticSpectrum) := by sorry

/-- HF₂ and its homotopy identification on the fixed category. -/
public def coefficients : ModTwoCoefficients Spectrum := by sorry
/-- The classical Adams functor, including its first page and differential degree. -/
public def classical : ClassicalAdamsFamily Spectrum := by sorry
/-- The fixed ν functor, including its sphere and suspension comparisons. -/
public def nu : NuFunctorData Spectrum SyntheticSpectrum := by sorry
/-- The synthetic Adams functor on the fixed synthetic category. -/
public def family : SyntheticAdamsFamily SyntheticSpectrum := by sorry

/-- ν preserves a distinguished triangle under the complete HF₂ short-exactness hypothesis. -/
public theorem nu_preserves_triangle (T : CategoryTheory.Pretriangulated.Triangle Spectrum)
    (hT : T ∈ distTriang Spectrum) (hH : HomologyShortExact coefficients T) :
    ∃ h : nu.functor.obj T.obj₃ ⟶
        (shiftFunctor SyntheticSpectrum (1 : ℤ)).obj (nu.functor.obj T.obj₁),
      CategoryTheory.Pretriangulated.Triangle.mk
        (nu.functor.map T.mor₁) (nu.functor.map T.mor₂) h ∈ distTriang SyntheticSpectrum := by
  sorry

/-- The λ-localization and its equivalence with this classical category. -/
public def recovery : LambdaRecovery nu := by sorry
/-- Exactness of the same suspension and realization functors. -/
public def exactness : StructuralExactness nu recovery := by sorry
/-- The fixed auxiliary spectra used in the selected object closure. -/
public def auxiliary : AuxiliaryData Spectrum := by sorry
/-- Multiplication on the actual sphere E₂, not an independent formal algebra. -/
public def sphereAlgebra : SphereE2Algebra classical := by sorry

/-- The fixed comparison with the independently defined normalized Milnor cobar
cohomology. Its construction and compatibility with the actual first tower
differential are separate registered obligations; an arbitrary linear
isomorphism is not a completed source identification. The public recognition
statements are in `Standard.Source`. -/
public def sphereE2_milnorEquiv (s t : ℕ) :
    classical.sphere.Page 2 ((s : ℤ), (t : ℤ)) ≃ₗ[ℤ]
      MilnorCohomology s t := by
  sorry

/-- Pull back the specified Milnor cocycles to the actual sphere E₂.
The fixed comparison remains a registered construction obligation.
Its source recognition is separate; the pullback does not complete it.
No source comparison is completed. -/
public def standardHi (i : ℕ) : ActualE2At classical (hiDegree i) := (sphereE2_milnorEquiv 1 (2 ^ i)).symm (milnorHiClass i)
public def standardClasses : StandardSphereClasses classical sphereAlgebra := ⟨standardHi⟩
public def classicalTower : ClassicalTowerPresentation coefficients.unit classical := by sorry
public def classicalSuspension (X : ClassicalObject) :
    ClassicalTowerSuspension classicalTower (X.obj auxiliary) := by sorry
public def syntheticTower : SyntheticTowerPresentation (nuCoefficientUnit coefficients nu) family := by sorry
public def comparison : E2Comparison classical family nu auxiliary := by sorry
public def quotients : LambdaQuotientSystem SyntheticSpectrum := by sorry
public def normalizedMap (X Y : ClassicalObject) (f : X.obj auxiliary ⟶ Y.obj auxiliary) :
    NormalizedSyntheticMap classicalTower nu f := by sorry
public def classicalConvergence (X : ClassicalObject) :
    ClassicalTowerConvergence classicalTower (X.obj auxiliary) := by sorry
public def convergence (X : SyntheticObject) :
    SyntheticTowerConvergence syntheticTower (X.obj nu auxiliary) := by sorry
public def firstQuotient : FirstQuotientComparison classical nu auxiliary := by sorry


open CategoryTheory.Limits CategoryTheory.Pretriangulated KIP126.Core.SpectralSequence
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- An ambient element in every finite cycle module belongs to the specified limit subobject. -/
private theorem mem_top_cycles (D : SSData (ModuleCat.{v} ℤ)) (a : D.V)
    (ha : ∀ n : ℕ, a ∈ ModuleCat.subobjectModule _ (D.Z n)) :
    a ∈ ModuleCat.subobjectModule _ (D.Z ⊤) := by
  have hspan : (ModuleCat.subobjectModule _).symm (Submodule.span ℤ {a}) ≤ D.Z ⊤ := by
    apply D.Z_top_greatest
    intro n
    apply (ModuleCat.subobjectModule _).le_iff_le.mp
    simp only [OrderIso.apply_symm_apply, Submodule.span_le, Set.singleton_subset_iff]
    exact ha n
  have h := (ModuleCat.subobjectModule _).monotone hspan
  apply h
  rw [OrderIso.apply_symm_apply]
  exact Submodule.subset_span (by simp)

private theorem layerMap_mem_cycles {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
    {X : C} (T : AbstractAdamsTower unit X) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1))
    (r : ℕ) (hr : 1 ≤ r) : T.layerMap p a ∈ T.cycles r hr p := by
  change T.connecting p (T.layerMap p a) ∈ LinearMap.range _
  have hz : T.connecting p (T.layerMap p a) = 0 := by
    change AbstractAdamsTower.desuspend _ _
      ((a ≫ HasFunctorialCofiber.cofibι _) ≫ HasFunctorialCofiber.cofibδ _) = 0
    have he : HasFunctorialCofiber.cofibι (T.mapAt (show p.1 ≤ p.1+1 by omega)) ≫
        HasFunctorialCofiber.cofibδ (T.mapAt (show p.1 ≤ p.1+1 by omega)) = 0 :=
      comp_distTriang_mor_zero₂₃ _ (HasFunctorialCofiber.cofib_distinguished _)
    rw [Category.assoc, he, comp_zero, map_zero]
  rw [hz]
  exact Submodule.zero_mem _

/-- Actual tower lifts supply common infinite representatives without a separation premise. -/
private theorem representative_of_lift {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
    {X : C} {T : AbstractAdamsTower unit X}
    {D : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
    {d : ∀ (r : ℤ) (p : ℤ × ℤ), (D p).page (↑(r - 2).toNat : WithTop ℕ) ⟶
      (D (p + (r, r - 1))).page (↑(r - 2).toNat : WithTop ℕ)}
    (P : TowerSequencePresentation unit T D d) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    ∃ z : (Subobject.underlying.obj ((D p).Z ⊤) : ModuleCat ℤ),
      P.infiniteRepresentativeE1 p z = T.layerMap p a := by
  let a₂ : T.cycles 2 (by decide) p := ⟨T.layerMap p a, layerMap_mem_cycles T p a 2 (by decide)⟩
  let v : (D p).V := (P.ambient p).inv a₂
  have hv : ∀ n : ℕ, v ∈ ModuleCat.subobjectModule _ ((D p).Z n) := by
    intro n
    apply (P.cycles p n v).mpr
    have he : (P.ambient p).hom v = a₂ := by simp only [v, Iso.inv_hom_id_apply]
    rw [he]
    exact layerMap_mem_cycles T p a (n+2) (by omega)
  obtain ⟨z, hz⟩ := mem_top_cycles (D p) v hv
  refine ⟨z, ?_⟩
  change ((P.ambient p).hom (((D p).Z ⊤).arrow z)).val = T.layerMap p a
  rw [hz]
  simp only [v, Iso.inv_hom_id_apply, a₂]

private theorem filtration_maps {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
    {F : SyntheticAdamsFamily Syn} (P : SyntheticTowerPresentation unit F)
    {X Y : Syn} (f : X ⟶ Y) (s : ℤ) (p : ℤ × ℤ)
    (a : BiHom p.1 p.2 X) (ha : a ∈ P.filtrationSubmodule X s p) :
    a ≫ f ∈ P.filtrationSubmodule Y s p := by
  obtain ⟨b, hb⟩ := ha
  refine ⟨b ≫ (P.map f).stage s.toNat, ?_⟩
  change (b ≫ (P.map f).stage s.toNat) ≫ (P.tower Y).projection s = a ≫ f
  rw [Category.assoc, (P.map f).projection, ← Category.assoc]
  exact congrArg (fun q => q ≫ f) hb

private theorem restrict_subobject_le {A B : ModuleCat.{v} ℤ} (S : Subobject A)
    (T : Subobject B) (f : A ⟶ B)
    (h : ∀ a : (S : ModuleCat ℤ), f (S.arrow a) ∈ ModuleCat.subobjectModule _ T) :
    imageSubobject (S.arrow ≫ f) ≤ T := by
  apply (ModuleCat.subobjectModule _).le_iff_le.mp
  rw [subobjectModule_image]
  rintro _ ⟨a, rfl⟩
  exact h a

private def restrict_subobject {A B : ModuleCat.{v} ℤ} (S : Subobject A)
    (T : Subobject B) (f : A ⟶ B)
    (h : ∀ a : (S : ModuleCat ℤ), f (S.arrow a) ∈ ModuleCat.subobjectModule _ T) :
    (S : ModuleCat ℤ) ⟶ (T : ModuleCat ℤ) :=
  factorThruImageSubobject (S.arrow ≫ f) ≫
    Subobject.ofLE _ _ (restrict_subobject_le S T f h)

private theorem restrict_subobject_arrow {A B : ModuleCat.{v} ℤ} (S : Subobject A)
    (T : Subobject B) (f : A ⟶ B)
    (h : ∀ a : (S : ModuleCat ℤ), f (S.arrow a) ∈ ModuleCat.subobjectModule _ T) :
    restrict_subobject S T f h ≫ T.arrow = S.arrow ≫ f := by
  simp only [restrict_subobject, Category.assoc, Subobject.ofLE_arrow,
    imageSubobject_arrow_comp]

private theorem filtration_arrow_mem {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
    {F : SyntheticAdamsFamily Syn} (P : SyntheticTowerPresentation unit F)
    (X : Syn) (s : ℤ) (p : ℤ × ℤ)
    (b : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat ℤ)) :
    ((P.filtration X).F s p).arrow b ∈ P.filtrationSubmodule X s p := by
  have h : ((P.filtration X).F s p).arrow b ∈
      ModuleCat.subobjectModule _ ((P.filtration X).F s p) := ⟨b, rfl⟩
  simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply] using h

private theorem infty_eq_of_ambient_boundary (D : SSData (ModuleCat.{v} ℤ))
    (z z' : (Subobject.underlying.obj (D.Z ⊤) : ModuleCat ℤ))
    (h : (D.Z ⊤).arrow z - (D.Z ⊤).arrow z' ∈
      ModuleCat.subobjectModule _ (D.B 0)) : D.pageπ ⊤ z = D.pageπ ⊤ z' := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (subobject_cokernel_π_eq_zero_iff (D.B ⊤) (D.Z ⊤) (D.B_le_Z ⊤) _).mpr
  rw [map_sub]
  exact (ModuleCat.subobjectModule _).monotone (D.B_mono le_top) h

private theorem layerMap_natural {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
    {X Y : C} {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y}
    {f : X ⟶ Y} (φ : TowerMap unit T U f) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    T.layerMap p a ≫ φ.layer p.1 = U.layerMap p (a ≫ φ.stage p.1.toNat) := by
  change (a ≫ HasFunctorialCofiber.cofibι _) ≫ φ.layer p.1 =
    (a ≫ φ.stage p.1.toNat) ≫ HasFunctorialCofiber.cofibι _
  rw [Category.assoc]
  change a ≫ HasFunctorialCofiber.cofibι _ ≫
    HasFunctorialCofiber.cofibMap _ _ _ _ _ = _
  rw [← HasFunctorialCofiber.cofibMap_ι, ← Category.assoc]

/-- The allowed initial-boundary error in tower naturality vanishes on E∞. -/
private theorem mapped_representative_eq {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
    {F : SyntheticAdamsFamily Syn} (P : SyntheticTowerPresentation unit F)
    {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
    (a : HomotopyGroup (i.2.1-i.1)
      ((P.tower ((SyntheticCategory.biShift (0,-i.2.2)).obj X)).stageAt i.1))
    (z : (Subobject.underlying.obj (((F.obj X).sequence.ssData i).Z ⊤) : ModuleCat ℤ))
    (hz : (P.sequence X i.2.2).infiniteRepresentativeE1 (i.1,i.2.1) z =
      (P.tower ((SyntheticCategory.biShift (0,-i.2.2)).obj X)).layerMap (i.1,i.2.1) a)
    (z' : (Subobject.underlying.obj (((F.obj Y).sequence.ssData i).Z ⊤) : ModuleCat ℤ))
    (hz' : (P.sequence Y i.2.2).infiniteRepresentativeE1 (i.1,i.2.1) z' =
      (P.tower ((SyntheticCategory.biShift (0,-i.2.2)).obj Y)).layerMap (i.1,i.2.1)
        (a ≫ (P.map ((SyntheticCategory.biShift (0,-i.2.2)).map f)).stage i.1.toNat)) :
    (F.map f).eInftyMap i (((F.obj X).sequence.ssData i).pageπ ⊤ z) =
      ((F.obj Y).sequence.ssData i).pageπ ⊤ z' := by
  let zf := (F.map f).toSSDataMorphism.cycleMap i ⊤ z
  have hzf : (((F.obj Y).sequence.ssData i).Z ⊤).arrow zf =
      (F.map f).φ i ((((F.obj X).sequence.ssData i).Z ⊤).arrow z) := by
    exact ConcreteCategory.congr_hom ((F.map f).preserves_Z i ⊤).choose_spec z
  have hn := P.natural_e2 f i.2.2 (i.1,i.2.1)
    ((((F.obj X).sequence.ssData i).Z ⊤).arrow z)
  have he1 : (P.sequence Y i.2.2).infiniteRepresentativeE1 (i.1,i.2.1) zf -
      (P.sequence Y i.2.2).infiniteRepresentativeE1 (i.1,i.2.1) z' ∈
      (P.tower ((SyntheticCategory.biShift (0,-i.2.2)).obj Y)).boundaries 2 (by decide)
        (i.1,i.2.1) := by
    rw [hz', ← layerMap_natural, ← hz]
    change (((P.sequence Y i.2.2).ambient (i.1,i.2.1)).hom
        ((((F.obj Y).sequence.ssData i).Z ⊤).arrow zf)).val -
      (((P.sequence X i.2.2).ambient (i.1,i.2.1)).hom
        ((((F.obj X).sequence.ssData i).Z ⊤).arrow z)).val ≫
          (P.map ((SyntheticCategory.biShift (0,-i.2.2)).map f)).layer i.1 ∈ _
    rw [hzf]
    exact hn
  have hb : (((F.obj Y).sequence.ssData i).Z ⊤).arrow zf -
      (((F.obj Y).sequence.ssData i).Z ⊤).arrow z' ∈
      ModuleCat.subobjectModule _ (((F.obj Y).sequence.ssData i).B 0) := by
    apply ((P.sequence Y i.2.2).boundaries (i.1,i.2.1) 0 _).mpr
    change (((P.sequence Y i.2.2).ambient (i.1,i.2.1)).hom
      ((((F.obj Y).sequence.ssData i).Z ⊤).arrow zf -
        (((F.obj Y).sequence.ssData i).Z ⊤).arrow z')).val ∈
      (P.tower ((SyntheticCategory.biShift (0,-i.2.2)).obj Y)).boundaries 2 (by decide)
        (i.1,i.2.1)
    have hsub := congrArg Subtype.val (map_sub
      (((P.sequence Y i.2.2).ambient (i.1,i.2.1)).hom.hom)
      ((((F.obj Y).sequence.ssData i).Z ⊤).arrow zf)
      ((((F.obj Y).sequence.ssData i).Z ⊤).arrow z'))
    exact hsub.symm ▸ he1
  have hinfty := infty_eq_of_ambient_boundary ((F.obj Y).sequence.ssData i) zf z' hb
  have hmap := ConcreteCategory.congr_hom
    ((F.map f).toSSDataMorphism.pageπ_pageMap i ⊤) z
  exact hmap.trans hinfty

private theorem weightMap_natural {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    {X Y : Syn} (f : X ⟶ Y) (m w : ℤ) (a : BiHom m w X) :
    weightHomotopyMap m w Y (a ≫ f) =
      weightHomotopyMap m w X a ≫ (SyntheticCategory.biShift (0,-w)).map f := by
  change (weightSourceIso m w).inv ≫ (SyntheticCategory.biShift (0,-w)).map (a ≫ f) =
    ((weightSourceIso m w).inv ≫ (SyntheticCategory.biShift (0,-w)).map a) ≫
      (SyntheticCategory.biShift (0,-w)).map f
  rw [Functor.map_comp, Category.assoc]

/-- Canonical identifications are natural on actual lifts; the graded quotient is epi. -/
private theorem canonical_convergence_natural {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
    {F : SyntheticAdamsFamily Syn} (P : SyntheticTowerPresentation unit F)
    {X Y : Syn} (f : X ⟶ Y)
    (cx : SyntheticTowerConvergence P X) (cy : SyntheticTowerConvergence P Y) :
    Nonempty (ConvergentMap F f cx.toConvergence cy.toConvergence) := by
  let hpres : ∀ (s : ℤ) (p : ℤ × ℤ),
      ∃ φ : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat ℤ) ⟶
        (Subobject.underlying.obj ((P.filtration Y).F s p) : ModuleCat ℤ),
        φ ≫ ((P.filtration Y).F s p).arrow =
          ((P.filtration X).F s p).arrow ≫ syntheticHomotopyMap f p := by
    intro s p
    have h : ∀ b : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat ℤ),
        syntheticHomotopyMap f p (((P.filtration X).F s p).arrow b) ∈
          ModuleCat.subobjectModule _ ((P.filtration Y).F s p) := by
      intro b
      have hb := filtration_maps P f s p _ (filtration_arrow_mem P X s p b)
      simp only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply]
      change (((P.filtration X).F s p).arrow b ≫ f) ∈ P.filtrationSubmodule Y s p
      exact hb
    exact ⟨restrict_subobject _ _ _ h, restrict_subobject_arrow _ _ _ h⟩
  refine ⟨{
    comparison := {
      eMap := (F.map f).eInftyMap
      aMap := syntheticHomotopyMap f
      filtration_compat := hpres
      reindex_eq := rfl
      iso_compat := ?_ }
    abutment_eq := rfl
    infinity_eq := rfl }⟩
  intro i
  dsimp only [SyntheticTowerConvergence.toConvergence]
  simp only [Filtration.transportGraded_self, Category.comp_id]
  apply (cancel_epi (cx.identification i).inv).mp
  letI : Epi ((P.filtration X).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2)) := by
    change Epi (cokernel.π _)
    infer_instance
  apply (cancel_epi ((P.filtration X).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2))).mp
  ext b
  obtain ⟨a, ha⟩ := (cx.canonical.1 i.1 (i.2.1-i.1) i.2.2
    (((P.filtration X).F i.1 (i.2.1-i.1,i.2.2)).arrow b)).mp
      (filtration_arrow_mem P X i.1 (i.2.1-i.1,i.2.2) b)
  obtain ⟨z, hz⟩ := representative_of_lift (P.sequence X i.2.2) (i.1,i.2.1) a
  have hx := cx.canonical.2 i a z hz b ha.symm
  have hxi : (cx.identification i).inv
      ((P.filtration X).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) b) =
      ((F.obj X).sequence.ssData i).pageπ ⊤ z := by
    rw [← hx, Iso.hom_inv_id_apply]
  let a' := a ≫ (P.map ((SyntheticCategory.biShift (0,-i.2.2)).map f)).stage i.1.toNat
  obtain ⟨z', hz'⟩ := representative_of_lift (P.sequence Y i.2.2) (i.1,i.2.1) a'
  have hm := mapped_representative_eq P f i a z hz z' hz'
  let b' := (hpres i.1 (i.2.1-i.1,i.2.2)).choose b
  have hb' : ((P.filtration Y).F i.1 (i.2.1-i.1,i.2.2)).arrow b' =
      ((P.filtration X).F i.1 (i.2.1-i.1,i.2.2)).arrow b ≫ f :=
    ConcreteCategory.congr_hom (hpres i.1 (i.2.1-i.1,i.2.2)).choose_spec b
  have ha' : weightHomotopyMap (i.2.1-i.1) i.2.2 Y
      (((P.filtration Y).F i.1 (i.2.1-i.1,i.2.2)).arrow b') =
      a' ≫ (P.tower ((SyntheticCategory.biShift (0,-i.2.2)).obj Y)).projection i.1 := by
    rw [hb', weightMap_natural, ← ha]
    change (a ≫ (P.tower ((SyntheticCategory.biShift (0,-i.2.2)).obj X)).projection i.1) ≫
      (SyntheticCategory.biShift (0,-i.2.2)).map f =
      (a ≫ (P.map ((SyntheticCategory.biShift (0,-i.2.2)).map f)).stage i.1.toNat) ≫
        (P.tower ((SyntheticCategory.biShift (0,-i.2.2)).obj Y)).projection i.1
    calc
      _ = a ≫ ((P.tower ((SyntheticCategory.biShift (0,-i.2.2)).obj X)).projection i.1 ≫
          (SyntheticCategory.biShift (0,-i.2.2)).map f) := Category.assoc _ _ _
      _ = a ≫ ((P.map ((SyntheticCategory.biShift (0,-i.2.2)).map f)).stage i.1.toNat ≫
          (P.tower ((SyntheticCategory.biShift (0,-i.2.2)).obj Y)).projection i.1) :=
        congrArg (fun z => a ≫ z)
          ((P.map ((SyntheticCategory.biShift (0,-i.2.2)).map f)).projection i.1).symm
      _ = _ := (Category.assoc _ _ _).symm

  have hy := cy.canonical.2 i a' z' hz' b' ha'
  have hg : (P.filtration X).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) ≫
      Filtration.inducedAssocGradedMap (syntheticHomotopyMap f) hpres
        i.1 (i.2.1-i.1,i.2.2) =
      (hpres i.1 (i.2.1-i.1,i.2.2)).choose ≫
        (P.filtration Y).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) := by
    exact cokernel.π_desc _ _ _
  change (cy.identification i).hom ((F.map f).eInftyMap i
      ((cx.identification i).inv
        ((P.filtration X).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) b))) = _
  rw [hxi, hm, hy]
  have hg' := ConcreteCategory.congr_hom hg b
  simpa only [ModuleCat.comp_apply, b', ← Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Category.id_comp] using hg'.symm


public theorem convergence_natural : ∀ (X Y : SyntheticObject)
      (f : X.obj nu auxiliary ⟶ Y.obj nu auxiliary),
    Nonempty (ConvergentMap family f (convergence X).toConvergence
      (convergence Y).toConvergence) := by
  intro X Y f
  exact canonical_convergence_natural syntheticTower f (convergence X) (convergence Y)

public theorem first_quotient : ∀ (X : ClassicalObject) (a s t : ℤ)
      (x : (classical.obj (X.obj auxiliary)).Page 2 (s,t)),
    KIP126.AdamsSynthetic.Detects
      (convergence (.quotient 1 (.shift (0,a) (.nu X)))) (s,t,t+a)
      (family.pageMap
        (HasFunctorialCofiber.cofibι (lambdaPow 1
          ((SyntheticCategory.biShift (0,a)).obj (nu.functor.obj (X.obj auxiliary)))))
        2 (s,t,t+a) (by simpa only [Nat.cast_zero, sub_zero] using comparison.nuE2 X a s t 0 x))
      ((firstQuotient X a s t).symm x) := by sorry


private theorem infinity_rep_morphism
    {E E' : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Tridegree}
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

private theorem infinity_rep_map {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    {F : SyntheticAdamsFamily Syn} {X Y : Syn} (g : X ⟶ Y)
    (i : Tridegree) {x : (F.obj X).Page 2 i}
    {e : ((F.obj X).sequence.ssData i).eInfty}
    (h : HasInfinityRepresentative (F.obj X) 2 i x e) :
    HasInfinityRepresentative (F.obj Y) 2 i (F.pageMap g 2 i x)
      ((F.map g).eInftyMap i e) := by
  obtain ⟨hr,z,hz,he⟩ := h
  obtain ⟨z',hz',he'⟩ := infinity_rep_morphism (F.map g) i ⟨z,hz,he⟩
  exact ⟨hr,z',hz',he'⟩

/-- Detection is natural for the prescribed homotopy and E∞ maps of one convergent map. -/
private theorem detects_map {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
    {F : SyntheticAdamsFamily Syn} {P : SyntheticTowerPresentation unit F}
    {X Y : Syn} {g : X ⟶ Y} {cx : SyntheticTowerConvergence P X}
    {cy : SyntheticTowerConvergence P Y}
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (i : Tridegree) {x : (F.obj X).Page 2 i}
    {a : BiHom (i.2.1-i.1) i.2.2 X}
    (h : KIP126.AdamsSynthetic.Detects cx i x a) :
    KIP126.AdamsSynthetic.Detects cy i (F.pageMap g 2 i x) (a ≫ g) := by
  obtain ⟨e, he, b, hb, hgr⟩ := h
  let hc := M.comparison.filtration_compat i.1 (i.2.1-i.1,i.2.2)
  let b' := hc.choose b
  refine ⟨(F.map g).eInftyMap i e, infinity_rep_map g i he, b', ?_, ?_⟩
  · have hmap := ConcreteCategory.congr_hom hc.choose_spec b
    have heq := ConcreteCategory.congr_hom
      (congrFun M.abutment_eq (i.2.1-i.1,i.2.2))
      (((P.filtration X).F i.1 (i.2.1-i.1,i.2.2)).arrow b)
    change ((P.filtration Y).F i.1 (i.2.1-i.1,i.2.2)).arrow b' = _
    exact hmap.trans (heq.trans (congrArg (fun z => z ≫ g) hb))
  · have hm := M.comparison.iso_compat i
    simp only [SyntheticTowerConvergence.toConvergence, Filtration.transportGraded_self,
      Category.comp_id] at hm
    rw [M.infinity_eq] at hm
    have hm' := ConcreteCategory.congr_hom hm e
    change (cy.identification i).hom ((F.map g).eInftyMap i e) =
      Filtration.inducedAssocGradedMap M.comparison.aMap M.comparison.filtration_compat
        i.1 (i.2.1-i.1,i.2.2) ((cx.identification i).hom e) at hm'
    rw [hgr] at hm'
    have hg : (P.filtration X).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) ≫
        Filtration.inducedAssocGradedMap M.comparison.aMap M.comparison.filtration_compat
          i.1 (i.2.1-i.1,i.2.2) =
        hc.choose ≫ (P.filtration Y).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) := by
      exact cokernel.π_desc _ _ _
    exact hm'.trans (ConcreteCategory.congr_hom hg b)

private theorem familyPageMap_comp {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    (F : SyntheticAdamsFamily Syn) {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : ℤ) (i : Tridegree) :
    F.pageMap (f ≫ g) r i = F.pageMap f r i ≫ F.pageMap g r i := by
  change (F.map (f ≫ g)).pageMap r i =
    (F.map f).pageMap r i ≫ (F.map g).pageMap r i
  rw [F.map_comp, SpectralSequenceMorphism.pageMap_comp]

private def trPage {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    {F : SyntheticAdamsFamily Syn} {X : Syn} {s t w w' : ℤ} (h : w = w')
    (x : (F.obj X).Page 2 (s,t,w)) : (F.obj X).Page 2 (s,t,w') :=
  cast (congrArg (fun q => ↥((F.obj X).Page 2 (s,t,q))) h) x

private def trHom {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    {X : Syn} {m w w' : ℤ} (h : w = w') (x : BiHom m w X) : BiHom m w' X :=
  cast (congrArg (fun q => BiHom m q X) h) x

private theorem detects_tr {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
    {F : SyntheticAdamsFamily Syn} {P : SyntheticTowerPresentation unit F}
    {X : Syn} (c : SyntheticTowerConvergence P X) {s t w w' : ℤ}
    (h : w = w') {x : (F.obj X).Page 2 (s,t,w)} {a : BiHom (t-s) w X}
    (hd : KIP126.AdamsSynthetic.Detects c (s,t,w) x a) :
    KIP126.AdamsSynthetic.Detects c (s,t,w') (trPage h x) (trHom h a) := by
  subst w'
  exact hd

private theorem pageMap_tr {Syn : Type u} [SyntheticCategory.{u,v} Syn]
    (F : SyntheticAdamsFamily Syn) {X Y : Syn} (f : X ⟶ Y) {s t w w' : ℤ}
    (h : w = w') (x : (F.obj X).Page 2 (s,t,w)) :
    trPage h (F.pageMap f 2 (s,t,w) x) =
      F.pageMap f 2 (s,t,w') (trPage h x) := by
  subst w'
  rfl

private theorem linearEquiv_cast_symm {A : ℤ → Type v}
    [∀ w, AddCommGroup (A w)] [∀ w, Module ℤ (A w)]
    {B : Type v} [AddCommGroup B] [Module ℤ B]
    {w w' : ℤ} (h : w = w') (e : A w ≃ₗ[ℤ] B) (x : B) :
    (cast (congrArg (fun q => A q ≃ₗ[ℤ] B) h) e).symm x =
      cast (congrArg A h) (e.symm x) := by
  subst w'
  rfl


public theorem sphere_first_quotient : ∀ (s t : ℤ) (x : classical.sphere.Page 2 (s,t)),
    Detects (convergence (.quotient 1 .sphere)) (s,t,t)
      (family.pageMap (XModLambdaN.incl S_0_0 1) 2 (s,t,t)
        (by simpa only [SyntheticAdamsFamily.sphere, SyntheticAdamsSS.Page,
          Nat.cast_zero, sub_zero] using comparison.sphereE2 s t 0 x))
      ((sphereFirstQuotient nu quotients.functoriality firstQuotient s t).symm x) := by
  intro s t x
  let Z := (SyntheticCategory.biShift (0,0)).obj (nu.functor.obj SphereSpectrum)
  let e : Z ≅ (S_0_0 : SyntheticSpectrum) :=
    SyntheticCategory.biShift_zero.app _ ≪≫ nu.unitIso
  let q := (quotients.functoriality.functor 1).mapIso e
  let u0 : (family.obj Z).Page 2 (s,t,t+0) := by
    simpa only [Nat.cast_zero, sub_zero, ClassicalObject.obj] using
      comparison.nuE2 .sphere 0 s t 0 x
  let u := trPage (Int.add_zero t) u0
  let b0 := (firstQuotient .sphere 0 s t).symm x
  let b := trHom (Int.add_zero t) b0
  have hd0 := first_quotient .sphere 0 s t x
  have hd : KIP126.AdamsSynthetic.Detects
      (convergence (.quotient 1 (.shift (0,0) (.nu .sphere)))) (s,t,t)
      (family.pageMap (XModLambdaN.incl Z 1) 2 (s,t,t) u) b := by
    have ht := detects_tr _ (Int.add_zero t) hd0
    have htr := pageMap_tr family (XModLambdaN.incl Z 1) (Int.add_zero t) u0
    exact htr ▸ ht
  let M := Classical.choice (canonical_convergence_natural syntheticTower q.hom
    (convergence (.quotient 1 (.shift (0,0) (.nu .sphere))))
    (convergence (.quotient 1 .sphere)))
  have hm := detects_map M (s,t,t) hd
  have hn : family.pageMap e.hom 2 (s,t,t) u =
      (by simpa only [SyntheticAdamsFamily.sphere, SyntheticAdamsSS.Page,
        Nat.cast_zero, sub_zero] using comparison.sphereE2 s t 0 x) := by
    let un0 : (family.obj Z).Page 2 (s,t,t-(0 : ℕ)) := by
      simpa only [add_zero, ClassicalObject.obj] using comparison.nuE2 .sphere 0 s t 0 x
    have h0 := comparison.sphere_nu s t 0 x
    change family.pageMap e.hom 2 (s,t,t-(0 : ℕ)) un0 = comparison.sphereE2 s t 0 x at h0
    have ht := congrArg (trPage (F := family) (X := (S_0_0 : SyntheticSpectrum))
      (s := s) (t := t) (show t-(0 : ℕ) = t by simp)) h0
    have htr := pageMap_tr family e.hom (show t-(0 : ℕ) = t by simp) un0
    rw [htr] at ht
    simpa only [u, u0, un0, trPage, eq_mp_eq_cast, cast_cast, id_eq] using ht
  have hp : family.pageMap q.hom 2 (s,t,t)
      (family.pageMap (XModLambdaN.incl Z 1) 2 (s,t,t) u) =
      family.pageMap (XModLambdaN.incl S_0_0 1) 2 (s,t,t)
        (by simpa only [SyntheticAdamsFamily.sphere, SyntheticAdamsSS.Page,
          Nat.cast_zero, sub_zero] using comparison.sphereE2 s t 0 x) := by
    change (family.pageMap (XModLambdaN.incl Z 1) 2 (s,t,t) ≫
      family.pageMap q.hom 2 (s,t,t)) u = _
    rw [← familyPageMap_comp]
    change family.pageMap (XModLambdaN.incl Z 1 ≫ XModLambdaN.map e.hom 1) 2 (s,t,t) u = _
    rw [← XModLambdaN.incl_naturality, familyPageMap_comp]
    change family.pageMap (XModLambdaN.incl S_0_0 1) 2 (s,t,t)
      (family.pageMap e.hom 2 (s,t,t) u) = _
    rw [hn]
  have hb : b ≫ q.hom = (sphereFirstQuotient nu quotients.functoriality firstQuotient s t).symm x := by
    have hcast := linearEquiv_cast_symm
      (A := fun w => BiHom (t-s) w (XModLambdaN Z 1))
      (Int.add_zero t) (firstQuotient .sphere 0 s t) x
    exact (congrArg (fun z : BiHom (t-s) t (XModLambdaN Z 1) => z ≫ q.hom) hcast).symm
  exact hp ▸ hb ▸ hm

public theorem sphere_homotopy_lambda : ∀ (s t : ℤ) (k : ℕ) (x : BiHom (t-s) t (S_0_0 : SyntheticSpectrum)),
    Detects (convergence .sphere) (s,t,t-k)
      (comparison.sphereE2 s t k (sphereFirstQuotient nu quotients.functoriality firstQuotient s t (quotientClass 1 x)))
      (lambdaMultiply k x) := by sorry

public theorem multiplicationCompatible :
    MultiplicationCompatible comparison sphereAlgebra (convergence .sphere) := by sorry
public theorem sphereProductCommutative : SphereProductCommutative (Syn := SyntheticSpectrum) := by sorry

/-- Internal organization of the already selected objects and named theorems.
Consumers never need to supply a model instance or prove this structure exists. -/
public def model : Model Spectrum SyntheticSpectrum where
  coefficients := coefficients
  classical := classical
  nu := nu
  family := family
  nuExactTriangle := nu_preserves_triangle
  recovery := recovery
  exactness := exactness
  auxiliary := auxiliary
  sphereAlgebra := sphereAlgebra
  standardClasses := standardClasses
  classicalTower := classicalTower
  classicalSuspension := classicalSuspension
  syntheticTower := syntheticTower
  comparison := comparison
  quotients := quotients
  normalizedMap := normalizedMap
  classicalConvergence := classicalConvergence
  convergence := convergence
  firstQuotient := firstQuotient
  comparisonCompatible := ⟨convergence_natural, first_quotient⟩
  sphereDetectionCompatible := ⟨sphere_first_quotient, sphere_homotopy_lambda⟩
  multiplicationCompatible := multiplicationCompatible
  sphereProductCommutative := sphereProductCommutative

end
end KIP126.AdamsSynthetic.Standard
