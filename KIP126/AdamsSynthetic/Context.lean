module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Data.ZMod.Basic

@[expose] section

/-!
# Stable-homotopy context interfaces

These interfaces package the structures of one given homotopy-category
background. Chosen cofibers, synthetic grading, and the ν functor remain
associated data. No global instance is selected by declaring the records.
-/

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory Pretriangulated

universe u v

/-- The structural part of a stable homotopy category.

The fields are bundled so a concrete model can supply its additive, shifted,
monoidal, and triangulated structures together.  In particular, this class
does not assert the extra closedness, cofiber choices, or sign conventions
used by particular constructions; those belong to separate witness records.
-/
public class StableHomotopyCategory (C : Type u) extends
    Category.{v} C,
    Preadditive C,
    HasShift C ℤ,
    MonoidalCategory C where
  /-- Every shift functor is additive. -/
  shiftAdditive : ∀ (n : ℤ), (shiftFunctor C n).Additive
  /-- The category has a zero object. -/
  hasZeroObject : HasZeroObject C
  /-- The category is pretriangulated. -/
  pretriangulated : Pretriangulated C

attribute [instance] StableHomotopyCategory.shiftAdditive
attribute [instance] StableHomotopyCategory.hasZeroObject
attribute [reducible] StableHomotopyCategory.pretriangulated
attribute [instance] StableHomotopyCategory.pretriangulated

variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-! ### Explicit cofiber and tensor-triangulated witnesses -/

/-- A chosen functorial cofiber construction on a stable category.

This is data supplied by a concrete model.  Keeping it as a class preserves
the convenient Mathlib notation without introducing a global postulate that
would silently choose a cofiber for every map.
-/
public class HasFunctorialCofiber where
  cofib : {X Y : C} → (X ⟶ Y) → C
  cofibι : {X Y : C} → (f : X ⟶ Y) → Y ⟶ cofib f
  cofibδ : {X Y : C} → (f : X ⟶ Y) → cofib f ⟶ (shiftFunctor C (1 : ℤ)).obj X
  cofib_distinguished : ∀ {X Y : C} (f : X ⟶ Y),
    Triangle.mk f (cofibι f) (cofibδ f) ∈ distTriang C
  cofibMap : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂), α ≫ f₂ = f₁ ≫ β →
    (cofib f₁ ⟶ cofib f₂)
  cofibMap_ι : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂) (h : α ≫ f₂ = f₁ ≫ β),
    β ≫ cofibι f₂ = cofibι f₁ ≫ cofibMap f₁ f₂ α β h
  cofibMap_δ : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂) (h : α ≫ f₂ = f₁ ≫ β),
    cofibMap f₁ f₂ α β h ≫ cofibδ f₂ =
      cofibδ f₁ ≫ (shiftFunctor C (1 : ℤ)).map α

/-- The sphere spectrum is the monoidal unit. -/
public abbrev SphereSpectrum : C := 𝟙_ C

/-- The `n`-sphere is the `n`-fold shift of the sphere spectrum. -/
public abbrev Sphere (n : ℤ) : C := (shiftFunctor C n).obj SphereSpectrum

/-- Stable homotopy classes represented by maps from the `n`-sphere. -/
public abbrev HomotopyGroup (n : ℤ) (X : C) : Type v := Sphere n ⟶ X

/-- The selected mod-two coefficient object and unit on this same background.
The record specifies its homotopy groups; it does not construct a spectrum. -/
public structure ModTwoCoefficients (C : Type u) [StableHomotopyCategory.{u, v} C] where
  object : C
  pi0Equiv : HomotopyGroup 0 object ≃+ ZMod 2
  homotopy_vanishes : ∀ n : ℤ, n ≠ 0 → Subsingleton (HomotopyGroup n object)

/-- The unit is the element `1` in the same specified zeroth homotopy group. -/
public def ModTwoCoefficients.unit (H : ModTwoCoefficients C) :
    SphereSpectrum ⟶ H.object :=
  (shiftFunctorZero C ℤ).inv.app SphereSpectrum ≫ H.pi0Equiv.symm 1

/-- The graded homotopy groups of a spectrum, as additive-group objects. -/
public noncomputable def HomotopyGroups (X : C) : ℤ → AddCommGrpCat.{v} :=
  fun n => AddCommGrpCat.mk (HomotopyGroup n X)

/-! ### Distinguished cofiber triangles and induced maps -/

/-- A chosen distinguished triangle `X → Y → Z → ΣX`. -/
public structure HoCofiberSequence where
  X : C
  Y : C
  Z : C
  f : X ⟶ Y
  g : Y ⟶ Z
  h : Z ⟶ (shiftFunctor C (1 : ℤ)).obj X
  distinguished : Triangle.mk f g h ∈ distTriang C

/-- The map on homotopy groups induced by postcomposition with `f`. -/
public def inducedMap {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    HomotopyGroup n X →+ HomotopyGroup n Y where
  toFun := fun α => α ≫ f
  map_zero' := Limits.zero_comp
  map_add' := fun a b => Preadditive.add_comp _ _ _ a b f

end KIP126.StableHomotopy

namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy

attribute [local instance] HasZeroObject.zero'

universe u v u' v'

/-- A stable category with a coherent bigraded suspension and deformation map.

The parent class supplies the additive, shifted, monoidal, and triangulated
structure.  `biShift` records the extra synthetic grading, while `lam` is the
natural transformation
`Σ^(0,-1) ⟶ Id` used to define the λ-power quotients.
-/
public class SyntheticCategory (Syn : Type u) extends
    StableHomotopyCategory.{u, v} Syn where
  biShift : ℤ × ℤ → Syn ⥤ Syn
  biShift_comp : ∀ (a b : ℤ × ℤ),
    biShift a ⋙ biShift b ≅ biShift (a + b)
  biShift_zero : biShift (0, 0) ≅ 𝟭 Syn
  biShift_compat : ∀ n : ℤ, biShift (n, 0) ≅ shiftFunctor Syn n
  /-- Each bigraded suspension is fully faithful (the inverse suspension is
      supplied by the same coherence data in a concrete model). -/
  biShift_fullyFaithful : ∀ p : ℤ × ℤ, (biShift p).FullyFaithful
  lam : biShift (0, -1) ⟶ 𝟭 Syn
  biShift_tensor_comm : ∀ (p : ℤ × ℤ) (X Y : Syn),
    (biShift p).obj (MonoidalCategory.tensorObj X Y) ≅
      MonoidalCategory.tensorObj ((biShift p).obj X) Y

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The `n`-fold composite of the deformation map `λ` on `X`.

The recursive definition follows the coherence isomorphism supplied by
`biShift_comp`; in particular `lambdaPow 0 X` is the chosen identity
isomorphism from `Σ^(0,0)X` to `X`.
-/
public noncomputable def lambdaPow : (n : ℕ) → (X : Syn) →
    (SyntheticCategory.biShift (0, -(n : ℤ))).obj X ⟶ X
  | 0, X => SyntheticCategory.biShift_zero.hom.app X
  | n + 1, X => by
      have step1 :
          (SyntheticCategory.biShift ((0 : ℤ), -1) ⋙
            SyntheticCategory.biShift ((0 : ℤ), -(n : ℤ))).obj X ⟶ X :=
        (SyntheticCategory.biShift ((0 : ℤ), -(n : ℤ))).map
            (SyntheticCategory.lam.app X) ≫ lambdaPow n X
      have step2 :
          (SyntheticCategory.biShift ((0, -1) + (0, -(n : ℤ)))).obj X ⟶ X :=
        (SyntheticCategory.biShift_comp (0, -1) (0, -(n : ℤ))).inv.app X ≫ step1
      have heq :
          ((0 : ℤ), (-1 : ℤ)) + ((0 : ℤ), -(n : ℤ)) =
            ((0 : ℤ), -(↑(n + 1) : ℤ)) := by
        simp
      exact heq ▸ step2

/-- The chosen cofiber of `λ_X`. -/
public noncomputable def XModLambda (X : Syn) [HasFunctorialCofiber (C := Syn)] : Syn :=
  HasFunctorialCofiber.cofib (SyntheticCategory.lam.app X)

/-- The chosen cofiber of `λⁿ_X`. -/
public noncomputable def XModLambdaN (X : Syn) (n : ℕ)
    [HasFunctorialCofiber (C := Syn)] : Syn :=
  HasFunctorialCofiber.cofib (lambdaPow n X)

/-- The explicit ν-interface from a stable category into the synthetic one.

The compatibility fields are hypotheses supplied by a concrete construction;
they are deliberately stored in a record instead of declared as axioms.
-/
public structure NuFunctorData (Stable : Type u) [StableHomotopyCategory.{u, v} Stable]
    (Syn : Type u') [SyntheticCategory.{u', v'} Syn] where
  functor : Stable ⥤ Syn
  additive : functor.Additive
  zeroIso : functor.obj 0 ≅ (0 : Syn)
  /-- The synthetic analogue of the ordinary sphere is the synthetic unit.
  This is explicit model data, not a claim that ν is strong monoidal on all
  spectra. Source: Pstrągowski, Definition 4.6 and its following discussion
  (`Source/Pst/source/synthetic_spectra.tex`, lines 1935–1938). -/
  unitIso : functor.obj (SphereSpectrum (C := Stable)) ≅ SphereSpectrum (C := Syn)
  suspensionIso : ∀ X : Stable,
    functor.obj ((shiftFunctor Stable (1 : ℤ)).obj X) ≅
      (SyntheticCategory.biShift (1, 1)).obj (functor.obj X)

/-- The landing of a normalized synthetic connecting map:
`Σ^(0,-1) ν(ΣX) ≅ Σ^(1,0) νX ≅ (νX)[1]`.
Every comparison is supplied by the same ν datum and synthetic grading. -/
public noncomputable def NuFunctorData.boundaryLandingIso
    {Stable : Type u} [StableHomotopyCategory.{u, v} Stable]
    {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
    (N : NuFunctorData Stable Syn) (X : Stable) :
    (SyntheticCategory.biShift (0, -1)).obj
        (N.functor.obj ((shiftFunctor Stable (1 : ℤ)).obj X)) ≅
      (shiftFunctor Syn (1 : ℤ)).obj (N.functor.obj X) :=
  (SyntheticCategory.biShift (0, -1)).mapIso (N.suspensionIso X) ≪≫
    (SyntheticCategory.biShift_comp (1, 1) (0, -1)).app (N.functor.obj X) ≪≫
    (SyntheticCategory.biShift_compat (Syn := Syn) 1).app (N.functor.obj X)

end KIP126.Synthetic.Context

namespace KIP126.Synthetic.Context

open CategoryTheory MonoidalCategory

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The synthetic sphere `S^(0,0)`, the monoidal unit. -/
public noncomputable def S_0_0 : Syn := 𝟙_ Syn

/-- The bigraded synthetic sphere `S^(m,n)`. -/
public noncomputable def Smn (m n : ℤ) : Syn :=
  (SyntheticCategory.biShift (m, n)).obj S_0_0

/-- The bigraded homotopy class type `[S^(m,n), X]`. -/
public abbrev BiHom (m n : ℤ) (X : Syn) : Type v := Smn m n ⟶ X

end KIP126.Synthetic.Context
