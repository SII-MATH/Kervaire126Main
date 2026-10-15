module

public import KIP126.Def.StableHomotopy.Spectra.Comparison
public import KIP126.Def.StableHomotopy.Spectra.Smash
public import Mathlib.CategoryTheory.Limits.Shapes.Products

@[expose] public section

/-! Recognition of the HF₂-local derived smash. Suspension spectra use the
actual based-space smash; exactness and countable coproducts extend across
the displayed stable generating class. No levelwise Xₙ∧Yₙ spectrum is used.
The target coproduct is the coproduct in the HF₂-local category, not the
ordinary uncompleted coproduct of local objects. -/
namespace KIP126.StableHomotopy.Spectra
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)}
  {Q : CompletionModel}

namespace SourceComparison
noncomputable def spaceObj (S : SourceComparison Q H) (A : BasedSpace.{0}) : C :=
  S.equivalence.functor.obj (Q.localization.obj (Prespectrum.suspensionSpectrum A))

noncomputable def spaceMap (S : SourceComparison Q H) {A B : BasedSpace.{0}} (f : A ⟶ B) :
    S.spaceObj A ⟶ S.spaceObj B :=
  S.equivalence.functor.map (Q.localization.map (Prespectrum.suspensionSpectrumMap f))

noncomputable def spaceUnit (S : SourceComparison Q H) :
    S.spaceObj BasedSpace.zeroSphere ≅ 𝟙_ C :=
  S.equivalence.functor.mapIso
    (Q.localization.mapIso (eqToIso Prespectrum.suspensionSpectrum_zeroSphere)) ≪≫ S.sphere
noncomputable def spaceSuspension (S : SourceComparison Q H) (A : BasedSpace.{0})
    (hA : A.IsGood) :
    S.spaceObj A.suspension ≅ (shiftFunctor C (1 : ℤ)).obj (S.spaceObj A) :=
  S.equivalence.functor.mapIso (Q.localization.mapIso
      (Prespectrum.suspensionSpectrumSuspensionIso A)) ≪≫
    S.suspension (Prespectrum.suspensionSpectrum A) (Prespectrum.suspensionSpectrum_good A hA)

end SourceComparison

/-- This recognition is attached to the SAME symmetric tensor, shifts,
cofiber and coproducts as the stable category. Its generator comparison is
natural and respects unit, associator and symmetry. Exactness in both
variables and coproduct preservation are the extension conditions. -/
structure TensorComparison (S : SourceComparison Q H) [SymmetricCategory C]
    [HasCoproductsOfShape ℕ C]
    [∀ W : C, (tensorLeft W).CommShift ℤ]
    [∀ W : C, (tensorRight W).CommShift ℤ] where
  smash : ∀ (A B : BasedSpace.{0}), A.IsGood → B.IsGood →
    (S.spaceObj A ⊗ S.spaceObj B ≅ S.spaceObj (A.smash B))
  natural : ∀ {A B A' B' : BasedSpace.{0}} (f : A ⟶ A') (g : B ⟶ B')
      (hA : A.IsGood) (hB : B.IsGood) (hA' : A'.IsGood) (hB' : B'.IsGood),
    (S.spaceMap f ⊗ₘ S.spaceMap g) ≫ (smash A' B' hA' hB').hom =
      (smash A B hA hB).hom ≫ S.spaceMap (BasedSpace.smashMap f g)
  associativity : ∀ (A B D : BasedSpace.{0})
      (hA : A.IsGood) (hB : B.IsGood) (hD : D.IsGood),
    ((smash A B hA hB).hom ▷ S.spaceObj D) ≫
        (smash (A.smash B) D (BasedSpace.good_smash hA hB) hD).hom ≫
        S.spaceMap (BasedSpace.smashAssoc A B D) =
      (α_ (S.spaceObj A) (S.spaceObj B) (S.spaceObj D)).hom ≫
        (S.spaceObj A ◁ (smash B D hB hD).hom) ≫
        (smash A (B.smash D) hA (BasedSpace.good_smash hB hD)).hom
  symmetry : ∀ (A B : BasedSpace.{0}) (hA : A.IsGood) (hB : B.IsGood),
    (smash A B hA hB).hom ≫ S.spaceMap (BasedSpace.smashSwap A B) =
      (β_ (S.spaceObj A) (S.spaceObj B)).hom ≫ (smash B A hB hA).hom
  unit : ∀ (A : BasedSpace.{0}) (hA : A.IsGood),
    (smash BasedSpace.zeroSphere A BasedSpace.good_zeroSphere hA).hom ≫
        S.spaceMap (BasedSpace.smashUnit A hA) =
      (S.spaceUnit.hom ▷ S.spaceObj A) ≫ (λ_ (S.spaceObj A)).hom
  /-- The generator comparison uses the selected tensor/shift structure,
  with the actual coordinate-rotation map fixing the suspension sign. -/
  suspension : ∀ (A B : BasedSpace.{0}) (hA : A.IsGood) (hB : B.IsGood),
    (smash A.suspension B (BasedSpace.good_suspension hA) hB).hom ≫
        S.spaceMap (BasedSpace.suspensionSmash A B hA hB) ≫
        (S.spaceSuspension (A.smash B) (BasedSpace.good_smash hA hB)).hom =
      ((S.spaceSuspension A hA).hom ▷ S.spaceObj B) ≫
        ((tensorRight (S.spaceObj B)).commShiftIso (1 : ℤ)).hom.app (S.spaceObj A) ≫
        (shiftFunctor C (1 : ℤ)).map (smash A B hA hB).hom
  /-- Recognition on good prespectra against the actual even-indexed
  prespectrum smash, followed by the specified completion. -/
  allSmash : ∀ (X Y : Prespectrum.{0}), X.IsGood → Y.IsGood →
    (S.equivalence.functor.obj (Q.localization.obj X) ⊗
      S.equivalence.functor.obj (Q.localization.obj Y) ≅
        S.equivalence.functor.obj (Q.localization.obj (X.diagonalSmash Y)))
  allSmash_natural : ∀ {X Y X' Y' : Prespectrum.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
      (hX : X.IsGood) (hY : Y.IsGood) (hX' : X'.IsGood) (hY' : Y'.IsGood),
    (S.equivalence.functor.map (Q.localization.map f) ⊗ₘ
        S.equivalence.functor.map (Q.localization.map g)) ≫
        (allSmash X' Y' hX' hY').hom =
      (allSmash X Y hX hY).hom ≫
        S.equivalence.functor.map (Q.localization.map (Prespectrum.diagonalSmashMap f g))
  /-- The full-range comparison restricts to the SAME generator pairing.
  This fixes its normalization on the actual free/evaluation counit. -/
  allSmash_zeroStage : ∀ (X Y : Prespectrum.{0}) (hX : X.IsGood) (hY : Y.IsGood),
    (smash (X.level 0) (Y.level 0) (hX 0) (hY 0)).hom ≫
        S.equivalence.functor.map
          (Q.localization.map (Prespectrum.zeroStage (X.diagonalSmash Y))) =
      (S.equivalence.functor.map (Q.localization.map (Prespectrum.zeroStage X)) ⊗ₘ
        S.equivalence.functor.map (Q.localization.map (Prespectrum.zeroStage Y))) ≫
          (allSmash X Y hX hY).hom
  exactLeft : ∀ W : C, (tensorLeft W).IsTriangulated
  exactRight : ∀ W : C, (tensorRight W).IsTriangulated
  coproductLeft : ∀ W : C, PreservesColimitsOfShape (Discrete ℕ) (tensorLeft W)
  coproductRight : ∀ W : C, PreservesColimitsOfShape (Discrete ℕ) (tensorRight W)
  /-- Closure under arbitrary integer shifts, cofibers and sequential
  coproducts of the actual suspension spectra generates the stable category. -/
  generates : ∀ (P : C → Prop),
    (∀ (A : BasedSpace.{0}), A.IsGood → P (S.spaceObj A)) →
    (∀ (X Y : C), (X ≅ Y) → P X → P Y) →
    (∀ (X : C) (d : ℤ), P X → P ((shiftFunctor C d).obj X)) →
    (∀ {X Y : C} (f : X ⟶ Y), P X → P Y → P (HasFunctorialCofiber.cofib f)) →
    (∀ (X : ℕ → C), (∀ n, P (X n)) → P (∐ X)) →
    ∀ X : C, P X

end KIP126.StableHomotopy.Spectra
