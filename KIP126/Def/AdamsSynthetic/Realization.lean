module

public import KIP126.Def.AdamsSynthetic.Background
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-! Optional point-set realizations of a given consumer category.

The localization target is the already given category, with its existing
shift and triangulation. The canonical equivalence with `Ho` is derived
from the localization property. No global model is chosen.

The stable-square, model, pushout-product, unit and generating-class
contracts retain the mathematical data from KIPBase
`StableHomotopy/{StableModelCategory,MonoidalModelCategory,SpectrumModel,
SyntheticStableModel}.lean`, baseline 5aa845241533. -/

@[expose] section
namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Pretriangulated

attribute [local instance] HasZeroObject.zero'

universe u v w z

section LocalizationSquares
variable {P : Type u} [Category.{v} P] [ModelCategory P]
  {C : Type w} [Category.{z} C] (L : P ⥤ C)

/-- A homotopy pushout presented by a point-set pushout along a cofibration.
All four comparison isomorphisms belong to the same localization functor. -/
public def IsModelPushout {X Y Z W : C}
    (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) (k : Z ⟶ W) : Prop :=
  ∃ (A B D E : P) (f' : A ⟶ B) (g' : A ⟶ D)
      (h' : B ⟶ E) (k' : D ⟶ E),
    cofibrations P f' ∧ IsPushout f' g' h' k' ∧
    ∃ (iX : L.obj A ≅ X) (iY : L.obj B ≅ Y)
      (iZ : L.obj D ≅ Z) (iW : L.obj E ≅ W),
      iX.hom ≫ f = L.map f' ≫ iY.hom ∧
      iX.hom ≫ g = L.map g' ≫ iZ.hom ∧
      iY.hom ≫ h = L.map h' ≫ iW.hom ∧
      iZ.hom ≫ k = L.map k' ≫ iW.hom

/-- A homotopy pullback presented by a point-set pullback along a fibration. -/
public def IsModelPullback {X Y Z W : C}
    (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) (k : Z ⟶ W) : Prop :=
  ∃ (A B D E : P) (f' : A ⟶ B) (g' : A ⟶ D)
      (h' : B ⟶ E) (k' : D ⟶ E),
    fibrations P h' ∧ IsPullback f' g' h' k' ∧
    ∃ (iX : L.obj A ≅ X) (iY : L.obj B ≅ Y)
      (iZ : L.obj D ≅ Z) (iW : L.obj E ≅ W),
      iX.hom ≫ f = L.map f' ≫ iY.hom ∧
      iX.hom ≫ g = L.map g' ≫ iZ.hom ∧
      iY.hom ≫ h = L.map h' ≫ iW.hom ∧
      iZ.hom ≫ k = L.map k' ≫ iW.hom

end LocalizationSquares

/-- Stability on the actual localization target, including the model-square
comparison contracts. The supplied derived suspension is identified with
the already chosen shift, and model cofiber squares give distinguished
triangles in the already chosen triangulation. -/
public structure StableLocalization
    {P : Type u} [Category.{v} P] [ModelCategory P]
    {C : Type w} [StableHomotopyCategory.{w,z} C] (L : P ⥤ C) where
  localizes : L.IsLocalization (weakEquivalences P)
  suspension : C ⥤ C
  loop : C ⥤ C
  suspensionLoop : suspension ⊣ loop
  suspensionIso : suspension ≅ shiftFunctor C (1 : ℤ)
  bicartesian : ∀ {X Y Z W : C}
      (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) (k : Z ⟶ W),
    f ≫ h = g ≫ k → (IsModelPushout L f g h k ↔ IsModelPullback L f g h k)
  pullbackComparison : ∀ {A B D E : P}
      (f : A ⟶ B) (g : A ⟶ D) (h : B ⟶ E) (k : D ⟶ E)
      (sq : f ≫ h = g ≫ k),
    fibrations P h →
    IsModelPullback L (L.map f) (L.map g) (L.map h) (L.map k) →
    IsIso (L.map (pullback.lift f g sq))
  pushoutComparison : ∀ {A B D E : P}
      (f : A ⟶ B) (g : A ⟶ D) (h : B ⟶ E) (k : D ⟶ E)
      (sq : f ≫ h = g ≫ k),
    cofibrations P f →
    IsModelPushout L (L.map f) (L.map g) (L.map h) (L.map k) →
    IsIso (L.map (pushout.desc h k sq))
  cofiberTriangle : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    IsModelPushout L f (0 : X ⟶ 0) g (0 : 0 ⟶ Z) →
    ∃ δ : Z ⟶ (shiftFunctor C (1 : ℤ)).obj X,
      Triangle.mk f g δ ∈ distTriang C

namespace StableLocalization
variable {P : Type u} [Category.{v} P] [ModelCategory P]
  {C : Type w} [StableHomotopyCategory.{w,z} C] {L : P ⥤ C}

/-- Stability of the unit follows from the supplied identification of
derived suspension with the actual integer shift. -/
public theorem unitIsIso (S : StableLocalization L) (X : C) :
    IsIso (S.suspensionLoop.unit.app X) := by
  letI : S.suspension.IsEquivalence :=
    Functor.isEquivalence_of_iso S.suspensionIso.symm
  infer_instance

/-- The counit is also derived, rather than requested as a second proof
input to the realization. -/
public theorem counitIsIso (S : StableLocalization L) (X : C) :
    IsIso (S.suspensionLoop.counit.app X) := by
  letI : S.suspension.IsEquivalence :=
    Functor.isEquivalence_of_iso S.suspensionIso.symm
  infer_instance

end StableLocalization

set_option linter.checkUnivs false in
/-- A point-set stable model realizing this same consumer category. Model
category instances remain fields of the supplied record. -/
public structure StableModelRealization (C : Type w)
    [StableHomotopyCategory.{w,z} C] where
  PointSet : Type u
  pointSetCategory : Category.{v} PointSet
  pointSetModel : ModelCategory PointSet
  zeroMorphisms : HasZeroMorphisms PointSet
  zeroObject : HasZeroObject PointSet
  localization : PointSet ⥤ C
  stable : StableLocalization localization

namespace StableModelRealization
variable {C : Type w} [StableHomotopyCategory.{w,z} C]

/-- The actual weak-equivalence localization of the supplied point-set model. -/
public abbrev Ho (R : StableModelRealization.{u,v,w,z} C) : Type u :=
  letI := R.pointSetCategory
  letI := R.pointSetModel
  (weakEquivalences R.PointSet).Localization

/-- The same localization target, rather than a second unbound homotopy
category. This equivalence follows from `localizes`. -/
public noncomputable def homotopyEquivalence (R : StableModelRealization.{u,v,w,z} C) :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    (weakEquivalences R.PointSet).Localization ≌ C := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.stable.localizes
  exact Localization.equivalenceFromModel R.localization (weakEquivalences R.PointSet)

/-- The canonical quotient followed by the comparison is the supplied
localization functor, up to its canonical natural isomorphism. -/
public noncomputable def localizationComparison
    (R : StableModelRealization.{u,v,w,z} C) :
    letI := R.pointSetCategory
    letI := R.pointSetModel
    (weakEquivalences R.PointSet).Q ⋙ R.homotopyEquivalence.functor ≅ R.localization := by
  letI := R.pointSetCategory
  letI := R.pointSetModel
  letI := R.stable.localizes
  exact Localization.qCompEquivalenceFromModelFunctorIso
    R.localization (weakEquivalences R.PointSet)

end StableModelRealization

/-- Generating classes for the supplied model structure, including the
smallness hypotheses used for functorial replacement. -/
public structure CofibrantGeneration (P : Type u)
    [Category.{v} P] [ModelCategory P] where
  generatingCofibrations : MorphismProperty P
  generatingTrivialCofibrations : MorphismProperty P
  cofibrationsRlp : generatingCofibrations.rlp = trivialFibrations P
  trivialCofibrationsRlp : generatingTrivialCofibrations.rlp = fibrations P
  cofibrationsSmall : MorphismProperty.HasSmallObjectArgument.{u} generatingCofibrations
  trivialCofibrationsSmall :
    MorphismProperty.HasSmallObjectArgument.{u} generatingTrivialCofibrations

/-- The pushout-product and unit conditions for the same point-set tensor
and model structure. The monoidal unit need not itself be cofibrant. -/
public structure MonoidalModelCompatibility (P : Type u)
    [Category.{v} P] [ModelCategory P] [MonoidalCategory P] where
  pushoutProduct : ∀ {A B X Y : P} (f : A ⟶ B) (g : X ⟶ Y),
    cofibrations P f → cofibrations P g →
    cofibrations P (MonoidalCategory.Arrow.pushoutProduct.obj
      (Arrow.mk f) |>.obj (Arrow.mk g)).hom
  pushoutProductTrivialLeft : ∀ {A B X Y : P} (f : A ⟶ B) (g : X ⟶ Y),
    trivialCofibrations P f → cofibrations P g →
    trivialCofibrations P (MonoidalCategory.Arrow.pushoutProduct.obj
      (Arrow.mk f) |>.obj (Arrow.mk g)).hom
  pushoutProductTrivialRight : ∀ {A B X Y : P} (f : A ⟶ B) (g : X ⟶ Y),
    cofibrations P f → trivialCofibrations P g →
    trivialCofibrations P (MonoidalCategory.Arrow.pushoutProduct.obj
      (Arrow.mk f) |>.obj (Arrow.mk g)).hom
  unit : ∀ {QI : P} (q : QI ⟶ 𝟙_ P),
    IsCofibrant QI → weakEquivalences P q →
    ∀ X : P, IsCofibrant X → weakEquivalences P (q ▷ X)

set_option linter.checkUnivs false in
/-- Optional point-set realization of the classical background. Its model
tensor is identified with the current homotopy-category tensor on cofibrant
inputs, and the replacement of its unit is the current sphere. -/
public structure SpectrumModelRealization (C : Type w)
    [StableHomotopyCategory.{w,z} C] extends StableModelRealization.{u,v,w,z} C where
  monoidal : MonoidalCategory PointSet
  symmetric : SymmetricCategory PointSet
  closed : MonoidalClosed PointSet
  limits : HasLimits.{v,u} PointSet
  colimits : HasColimits.{v,u} PointSet
  generation : CofibrantGeneration PointSet
  monoidalModel : MonoidalModelCompatibility PointSet
  tensorComparison : ∀ X Y : PointSet, IsCofibrant X → IsCofibrant Y →
    (localization.obj (X ⊗ Y) ≅ localization.obj X ⊗ localization.obj Y)
  tensorNaturality : ∀ {X X' Y Y' : PointSet} (f : X ⟶ X') (g : Y ⟶ Y')
      (hX : IsCofibrant X) (hX' : IsCofibrant X')
      (hY : IsCofibrant Y) (hY' : IsCofibrant Y'),
    localization.map (f ⊗ₘ g) ≫ (tensorComparison X' Y' hX' hY').hom =
      (tensorComparison X Y hX hY).hom ≫ (localization.map f ⊗ₘ localization.map g)
  unitComparison : ∀ {QI : PointSet} (q : QI ⟶ 𝟙_ PointSet),
    IsCofibrant QI → weakEquivalences PointSet q →
    (localization.obj QI ≅ SphereSpectrum (C := C))

set_option linter.checkUnivs false in
/-- Optional point-set realization of the already supplied synthetic
category. Its inherited localization target is `Syn` itself, not `Ho Syn`. -/
public abbrev SyntheticModelRealization (Syn : Type w)
    [KIP126.Synthetic.Context.SyntheticCategory.{w,z} Syn] :=
  StableModelRealization.{u,v,w,z} Syn

end KIP126.StableHomotopy
