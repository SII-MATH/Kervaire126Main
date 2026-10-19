# 原接口读取证据

本次只读摘录；不是接口新定义，也未编译。完整文件哈希见read-manifest.json。

## KIP126/AdamsSynthetic/Internal/Source/Recognition.lean:34–100

```lean

/-- Recognition of one background by the explicit ordinary stable source,
including its sphere, shifts, integer stable homotopy, and mod-two unit. -/
structure SourceRecognition (C : Type u) [StableHomotopyCategory.{u,v} C]
    (H : ModTwoCoefficients C) where
  equivalence : SourceCategory.{0} ≌ C
  sphereIso : equivalence.functor.obj (sourceLocalization.obj Prespectrum.sphere) ≅
    SphereSpectrum
  suspensionIso : ∀ (X : Prespectrum.{0}), X.IsWellBased →
    (equivalence.functor.obj (sourceLocalization.obj X.suspension) ≅
      (shiftFunctor C (1 : ℤ)).obj
        (equivalence.functor.obj (sourceLocalization.obj X)))
  suspension_natural : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y)
      (hX : X.IsWellBased) (hY : Y.IsWellBased),
    equivalence.functor.map (sourceLocalization.map (Prespectrum.suspensionMap f)) ≫
      (suspensionIso Y hY).hom =
        (suspensionIso X hX).hom ≫ (shiftFunctor C (1 : ℤ)).map
          (equivalence.functor.map (sourceLocalization.map f))
  desuspensionIso : ∀ X : Prespectrum.{0},
    equivalence.functor.obj (sourceLocalization.obj X.desuspension) ≅
      (shiftFunctor C (-1 : ℤ)).obj
        (equivalence.functor.obj (sourceLocalization.obj X))
  desuspension_natural : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y),
    equivalence.functor.map (sourceLocalization.map (Prespectrum.desuspensionMap f)) ≫
      (desuspensionIso Y).hom =
        (desuspensionIso X).hom ≫ (shiftFunctor C (-1 : ℤ)).map
          (equivalence.functor.map (sourceLocalization.map f))
  homotopy : ∀ (X : Prespectrum.{0}) (d : ℤ),
    HomotopyGroup d (equivalence.functor.obj (sourceLocalization.obj X)) ≃
      Prespectrum.StableHomotopy X d
  homotopy_natural : ∀ {X Y : Prespectrum.{0}} (f : X ⟶ Y) (d : ℤ)
      (a : HomotopyGroup d (equivalence.functor.obj (sourceLocalization.obj X))),
    homotopy Y d (a ≫ equivalence.functor.map (sourceLocalization.map f)) =
      Prespectrum.stableHomotopyMap f d (homotopy X d a)
  homotopy_zero : ∀ (X : Prespectrum.{0}) (d : ℤ) (n r : ℕ)
      (h : (r : ℤ) = d + n),
    homotopy X d 0 = Prespectrum.loopClass X d n r h GenLoop.const
  /-- Stable addition is the actual concatenation of cubical loops. Two
  coordinates ensure the displayed representative lies in the abelian range. -/
  homotopy_add : ∀ (X : Prespectrum.{0}) (d : ℤ) (n r : ℕ)
      (h : ((r + 2 : ℕ) : ℤ) = d + n)
      (p q : GenLoop (Fin (r + 2)) (X.level n) (X.level n).point),
    (homotopy X d).symm
        (Prespectrum.loopClass X d n (r + 2) h (GenLoop.transAt 0 p q)) =
      (homotopy X d).symm (Prespectrum.loopClass X d n (r + 2) h p) +
        (homotopy X d).symm (Prespectrum.loopClass X d n (r + 2) h q)
  /-- The identity of the selected sphere has the actual positive point-set
  generator, fixing the normalization of the source sphere comparison. -/
  sphere_identity : homotopy Prespectrum.sphere 0
      ((shiftFunctorZero C ℤ).hom.app SphereSpectrum ≫ sphereIso.inv) =
    Prespectrum.sphereGenerator
  sourceHF2 : Prespectrum.{0}
  sourceHF2Pi0 : Prespectrum.StableHomotopy sourceHF2 0 ≃ ZMod 2
  sourceHF2Vanishes : ∀ d : ℤ, d ≠ 0 →
    Subsingleton (Prespectrum.StableHomotopy sourceHF2 d)
  hf2Iso : equivalence.functor.obj (sourceLocalization.obj sourceHF2) ≅ H.object
  /-- The source coefficient coordinate is the selected target coordinate on
  the same homotopy comparison, not a separately named two-element set. -/
  hf2_pi0 : ∀ a : HomotopyGroup 0
      (equivalence.functor.obj (sourceLocalization.obj sourceHF2)),
    H.pi0Equiv (a ≫ hf2Iso.hom) = sourceHF2Pi0 (homotopy sourceHF2 0 a)
  sourceUnit : Prespectrum.sphere ⟶ sourceHF2
  /-- The actual point-set unit represents this same selected coefficient
  unit under the fixed sphere and coefficient comparisons. -/
  unit_compat : equivalence.functor.map (sourceLocalization.map sourceUnit) ≫
      hf2Iso.hom = sphereIso.hom ≫ H.unit

```

## KIP126/AdamsSynthetic/Standard/Source.lean:29–46

```lean
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Recognition of the fixed ordinary category, sphere, integer homotopy,
HF₂ object, coordinate and normalized actual point-set unit. -/
public def sourceRecognition : ClassicalSourceRecognition Spectrum coefficients := by
  sorry

/-- Tensor comparison on actual good suspension-spectrum generators. This
does not assert an arbitrary-prespectrum derived-smash construction. -/
public def sourceGeneratorTensorRecognition :
    ClassicalSourceGeneratorTensorRecognition sourceRecognition := by
  sorry

/-- Actual mapping-cone comparison, including its inclusion and boundary. -/
public def sourceCofiberRecognition :
    ClassicalSourceCofiberRecognition sourceRecognition := by
  sorry
```

## KIP126/AdamsSynthetic/Source.lean:140–181

```lean
/-- Exactly the maps whose precomposition maps into every recognized integer
shift of the same HF₂ are bijective. -/
@[no_expose] public def classicalHF2Equivalences
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) : MorphismProperty ClassicalSource :=
  Source.HF2Equivalences R

public theorem classicalHF2Equivalences_iff
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) {X Y : ClassicalSource} (f : X ⟶ Y) :
    classicalHF2Equivalences R f ↔ ∀ d : ℤ,
      Function.Bijective (fun a : Y ⟶ R.shiftedCoefficient d => f ≫ a) := Iff.rfl

/-- The actual categorical localization at this explicit HF₂ cohomology
equivalence class. Identification with a completion model is a separate theorem. -/
@[no_expose] public def ClassicalHF2LocalizedSource
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) : Type 1 := Source.HF2LocalizedSource R

@[no_expose] public noncomputable instance classicalHF2LocalizedSourceCategory
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) : Category (ClassicalHF2LocalizedSource R) :=
  inferInstanceAs (Category (Source.HF2LocalizedSource R))

@[no_expose] public noncomputable def classicalHF2Localization
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) : ClassicalSource ⥤ ClassicalHF2LocalizedSource R :=
  Source.hf2Localization R

public theorem classicalHF2Localization_isLocalization
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) :
    (classicalHF2Localization R).IsLocalization (classicalHF2Equivalences R) := by
  change (Source.hf2Localization R).IsLocalization (Source.HF2Equivalences R)
  infer_instance

public noncomputable def classicalHF2LocalizedSphere
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : ClassicalSourceRecognition C H) : ClassicalHF2LocalizedSource R :=
  (classicalHF2Localization R).obj classicalSourceSphere

@[no_expose] public def ClassicalSourceReplacementData : Type 1 := Source.SourceReplacementData
```

## KIP126/AdamsSynthetic/Internal/Source/Completion.lean:17–28

```lean

Every detector is the inverse image of an integer shift of the same selected
HF₂ object under the same source equivalence. This uses the recognized stable
shift, without asserting that an unrestricted point-set reduced suspension is
a derived suspension. A morphism is inverted precisely when precomposition
induces a bijection into every one of these fixed integer detectors.

The category below is the actual categorical localization at that explicit
class of maps. Its definition does not identify this localization with a
reflective subcategory, Moore(2)-completion, or the paper's completion of
connective spectra of finite type; those require further comparison proofs.
-/
```

## KIP126/AdamsSynthetic/Standard/Source.lean:228–251

```lean
    classicalHF2Localization sourceRecognition ⋙ localizedClassical ≅ sourceClassical := by
  letI := classicalHF2Localization_isLocalization sourceRecognition
  exact CategoryTheory.Localization.fac sourceClassical sourceClassical_inverts_hf2
    (classicalHF2Localization sourceRecognition)

public def localizedSphereSequence :
    KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ) :=
  localizedClassical.obj (classicalHF2LocalizedSphere sourceRecognition)

public def localizedSphere_classicalIso : localizedSphereSequence ≅ classical.sphere :=
  sourceLocalizationAdamsIso.app classicalSourceSphere ≪≫
    classical.functor.mapIso sourceRecognition.sphereIso

public def localizedH6Square : localizedSphereSequence.Page 2 (2,128) :=
  localizedSphere_classicalIso.inv.pageMap 2 (2,128) standardH6Square

/-- The unchanged Main target transports to the actual localized sphere,
conditional only on the separately registered source constructions. -/
public theorem nonzeroSurvival_localized_iff :
    NonzeroSurvival localizedSphereSequence (2,128) localizedH6Square ↔
      NonzeroSurvival classical.sphere (2,128) standardH6Square :=
  Internal.Source.nonzeroSurvival_iso_iff localizedSphere_classicalIso.symm
    (2,128) standardH6Square

```

## KIP126/AdamsSynthetic/Recovery.lean:111–121

```lean
    Functor.isoWhiskerRight R.nuLocalization R.equivalence.functor ≪≫ R.equivalence.counitIso

/-- The canonical map from ν to spectral Yoneda factors through the actual
localization unit and the supplied natural comparison. -/
public def LambdaRecovery.nuToSpectralYoneda (R : LambdaRecovery N) :
    N.functor ⟶ R.spectralYoneda :=
  Functor.whiskerLeft N.functor R.localization.unit ≫
    (Functor.isoWhiskerRight R.nuLocalization (lambdaInclusion Syn)).hom

end KIP126.Synthetic.Context

```

## KIP126/AdamsSynthetic/Configuration.lean:31–61

```lean
  | detector
  | shift (n : ℤ) (X : ClassicalObject)

public noncomputable def ClassicalObject.obj [HasFunctorialCofiber (C := C)]
    (A : AuxiliaryData C) : ClassicalObject → C
  | .sphere => SphereSpectrum
  | .nuCofiber => HasFunctorialCofiber.cofib A.nuMap
  | .detector => A.detector
  | .shift n X => (shiftFunctor C n).obj (X.obj A)

/-- Synthetic objects used by normalized maps, finite λ/ρ/δ triangles,
and the untruncated argument. Closure includes all shifts and quotients,
but does not demand convergence on every object of the ambient category. -/
public inductive SyntheticObject
  | sphere
  | nu (X : ClassicalObject)
  | shift (p : ℤ × ℤ) (X : SyntheticObject)
  | quotient (n : ℕ) (X : SyntheticObject)

public noncomputable def SyntheticObject.obj [HasFunctorialCofiber (C := C)]
    {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
    (N : NuFunctorData C Syn) (A : AuxiliaryData C) : SyntheticObject → Syn
  | .sphere => S_0_0
  | .nu X => N.functor.obj (X.obj A)
  | .shift p X => (SyntheticCategory.biShift p).obj (X.obj N A)
  | .quotient n X => XModLambdaN (X.obj N A) n

/-- A distinguished triangle within the selected classical object closure.
The connecting map lands in the actual suspension of X. -/
public structure TriangleData [HasFunctorialCofiber (C := C)] (A : AuxiliaryData C) where
  X : ClassicalObject
```

## KIP126/AdamsSynthetic/AdamsFiltration.lean:22–33

```lean
/-- The finite sphere/shift/cofiber closure, independently of the smaller
configuration selected by the main proof. -/
public inductive IsFiniteSpectrum : C → Prop where
  | sphere : IsFiniteSpectrum SphereSpectrum
  | shift {X : C} (n : ℤ) : IsFiniteSpectrum X → IsFiniteSpectrum (X⟦n⟧)
  | cofiber {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧} :
      Triangle.mk f g h ∈ distTriang C →
      IsFiniteSpectrum X → IsFiniteSpectrum Y → IsFiniteSpectrum Z

/-- Homology uses this coefficient object and the actual tensor product. -/
public abbrev ModTwoHomology (H : ModTwoCoefficients C) (n : ℤ) (X : C) :=
  HomotopyGroup n (H.object ⊗ X)
```
