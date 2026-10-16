module

public import KIP126.AdamsSynthetic.Context
public import KIP126.SpectralSequence
public import KIP126.SpectralSequence.Basic.Category.Proofs

@[expose] section

/-! Given Adams systems. Every page and induced map is evaluated from one
functor; declaring these records does not select or construct an instance. -/

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v u'

namespace KIP126.Classical.Adams

public abbrev Bidegree := ℤ × ℤ

public structure ClassicalAdamsFamily (C : Type u) [StableHomotopyCategory.{u, v} C] where
  functor : C ⥤ KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Bidegree
  firstPage : ∀ X, (functor.obj X).r₀ = 2
  differentialDegree : ∀ X r, (functor.obj X).diffDeg r = (r, r - 1)

namespace ClassicalAdamsFamily
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

public abbrev obj (A : ClassicalAdamsFamily C) (X : C) := A.functor.obj X
public abbrev sphere (A : ClassicalAdamsFamily C) := A.obj SphereSpectrum

public def map (A : ClassicalAdamsFamily C) {X Y : C} (f : X ⟶ Y) :
    A.obj X ⟶ A.obj Y := A.functor.map f

@[simp] public theorem map_id (A : ClassicalAdamsFamily C) (X : C) :
    A.map (𝟙 X) = 𝟙 (A.obj X) := A.functor.map_id X

@[simp] public theorem map_comp (A : ClassicalAdamsFamily C) {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) : A.map (f ≫ g) = A.map f ≫ A.map g :=
  A.functor.map_comp f g

public noncomputable def pageMap (A : ClassicalAdamsFamily C) {X Y : C}
    (f : X ⟶ Y) (r : ℤ) (p : Bidegree) :
    (A.obj X).Page r p ⟶ (A.obj Y).Page r p := (A.map f).pageMap r p

end ClassicalAdamsFamily
end KIP126.Classical.Adams

namespace KIP126.Synthetic.SpectralSequence

public abbrev Tridegree := ℤ × ℤ × ℤ
public def syntheticAdamsRawShift (r : ℤ) : Tridegree := (r, r - 1, 0)
public abbrev SyntheticAdamsSpectralSequence :=
  KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Tridegree

public structure SyntheticAdamsSS where
  sequence : SyntheticAdamsSpectralSequence.{v}
  firstPage : sequence.r₀ = 2
  differentialDegree : ∀ r : ℤ, sequence.diffDeg r = syntheticAdamsRawShift r

namespace SyntheticAdamsSS
public noncomputable abbrev Page (A : SyntheticAdamsSS.{v}) (r : ℤ) (i : Tridegree) :=
  A.sequence.Page r i
public noncomputable abbrev E₂ (A : SyntheticAdamsSS.{v}) := A.Page 2
public noncomputable abbrev E₃ (A : SyntheticAdamsSS.{v}) := A.Page 3

public noncomputable def d (A : SyntheticAdamsSS.{v}) (r : ℤ) (i : Tridegree) :
    A.Page r i ⟶ A.Page r (i + syntheticAdamsRawShift r) :=
  A.sequence.d r i ≫ eqToHom (by rw [A.differentialDegree])
end SyntheticAdamsSS

public structure SyntheticAdamsFamily (Syn : Type u) [SyntheticCategory.{u, v} Syn] where
  functor : Syn ⥤ KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Tridegree
  firstPage : ∀ X, (functor.obj X).r₀ = 2
  differentialDegree : ∀ X r, (functor.obj X).diffDeg r = syntheticAdamsRawShift r

namespace SyntheticAdamsFamily
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

public def obj (F : SyntheticAdamsFamily Syn) (X : Syn) : SyntheticAdamsSS.{v} where
  sequence := F.functor.obj X
  firstPage := F.firstPage X
  differentialDegree := F.differentialDegree X

public noncomputable def sphere (F : SyntheticAdamsFamily Syn) : SyntheticAdamsSS.{v} :=
  F.obj S_0_0

public def nu {C : Type u'} [StableHomotopyCategory.{u', v} C]
    (F : SyntheticAdamsFamily Syn) (N : NuFunctorData C Syn) (X : C) :
    SyntheticAdamsSS.{v} := F.obj (N.functor.obj X)

public noncomputable def nuSphereIso {C : Type u'} [StableHomotopyCategory.{u', v} C]
    (F : SyntheticAdamsFamily Syn) (N : NuFunctorData C Syn) :
    (F.nu N SphereSpectrum).sequence ≅ F.sphere.sequence := F.functor.mapIso N.unitIso

public noncomputable def quotient [HasFunctorialCofiber (C := Syn)]
    (F : SyntheticAdamsFamily Syn) (X : Syn) (n : ℕ) : SyntheticAdamsSS.{v} :=
  F.obj (XModLambdaN X n)

public def map (F : SyntheticAdamsFamily Syn) {X Y : Syn} (f : X ⟶ Y) :
    (F.obj X).sequence ⟶ (F.obj Y).sequence := F.functor.map f

@[simp] public theorem map_id (F : SyntheticAdamsFamily Syn) (X : Syn) :
    F.map (𝟙 X) = 𝟙 (F.obj X).sequence := F.functor.map_id X

@[simp] public theorem map_comp (F : SyntheticAdamsFamily Syn) {X Y Z : Syn}
    (f : X ⟶ Y) (g : Y ⟶ Z) : F.map (f ≫ g) = F.map f ≫ F.map g :=
  F.functor.map_comp f g

public noncomputable def pageMap (F : SyntheticAdamsFamily Syn) {X Y : Syn}
    (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
    (F.obj X).Page r i ⟶ (F.obj Y).Page r i := (F.map f).pageMap r i

public noncomputable def quotientProjection [HasFunctorialCofiber (C := Syn)]
    (F : SyntheticAdamsFamily Syn) (X : Syn) (n : ℕ) :
    (F.obj X).sequence ⟶ (F.quotient X n).sequence :=
  F.map (HasFunctorialCofiber.cofibι (lambdaPow n X))

public def deformationMap (F : SyntheticAdamsFamily Syn) (X : Syn) :
    (F.obj ((SyntheticCategory.biShift (0, -1)).obj X)).sequence ⟶
      (F.obj X).sequence := F.map (SyntheticCategory.lam.app X)

end SyntheticAdamsFamily

public noncomputable abbrev familyPageMap {Syn : Type u} [SyntheticCategory.{u, v} Syn]
    (F : SyntheticAdamsFamily Syn) {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :=
  F.pageMap f r i

public noncomputable def syntheticHomotopy {Syn : Type u} [SyntheticCategory.{u, v} Syn]
    (X : Syn) (p : ℤ × ℤ) : ModuleCat.{v} ℤ :=
  ModuleCat.of ℤ (BiHom p.1 p.2 X)

end KIP126.Synthetic.SpectralSequence
