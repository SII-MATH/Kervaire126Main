module

public import KIP126.Def.ClassicalAdams.TowerLayer.Proofs
public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Data

@[expose] public section

/-! A realization map on Adams pages, induced by the ACTUAL exact strong
monoidal functor. The layer map is a formula in F.map, F's monoidal maps,
the coefficient identification and the tower identification. There is no
freely supplied map of E1/E2 groups. This is the direction of tau inversion
in BHS, SynRevAdams.tex (before Theorem `thm:synth-ASS`).

The comparisons are structural model data; existence and compatibility
proofs are separate obligations. No BHS differential or survivor is assumed.
-/
namespace KIP126.Comparison.ClassicalSynthetic.RealizationTower
open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams
universe u v w
noncomputable section
variable {S : Type u} [StableHomotopyCategory.{u, v} S]
  [HasFunctorialCofiber (C := S)]
  {C : Type w} [StableHomotopyCategory.{w, v} C]
  [HasFunctorialCofiber (C := C)]
  (F : S ⥤ C) [F.Monoidal] [F.CommShift ℤ] [F.Additive]
  {HS : S} {HC : C} (unitS : 𝟙_ S ⟶ HS) (unitC : 𝟙_ C ⟶ HC)
  (coefficient : F.obj HS ≅ HC)

/-- The coefficient identification must send the actual synthetic unit
to the same classical unit, with F's fixed monoidal unit map. -/
def CoefficientUnitCompatible : Prop :=
  (Functor.Monoidal.εIso F).hom ≫ F.map unitS ≫ coefficient.hom = unitC

variable (Y : S) (X : C)

abbrev TowerIdentifications := ∀ n : ℕ,
  F.obj (adamsTower unitS Y n) ≅ adamsTower unitC X n

/-- Nonnegative layers are identified by their actual maps to H tensor T.
The map uses F's inverse monoidal product comparison. -/
def layerMapNat (e : TowerIdentifications F unitS unitC Y X) (n : ℕ) :
    F.obj (adamsLayerAt unitS Y n) ⟶ adamsLayerAt unitC X n :=
  F.map (adamsLayerIso unitS Y n).hom ≫
    (Functor.Monoidal.μIso F HS (adamsTower unitS Y n)).inv ≫
    (coefficient.hom ⊗ₘ (e n).hom) ≫ (adamsLayerIso unitC X n).inv

/-- Below filtration zero both actual layers are cofibers of identities;
the unique map between these zero objects is the zero morphism. -/
def layerMap (e : TowerIdentifications F unitS unitC Y X) (s : ℤ) :
    F.obj (adamsLayerAt unitS Y s) ⟶ adamsLayerAt unitC X s :=
  if hs : 0 ≤ s then by
    simpa only [Int.toNat_of_nonneg hs] using
      layerMapNat F unitS unitC coefficient Y X e s.toNat
  else 0

-- Keep the established public declaration name.
set_option linter.dupNamespace false in
/-- A comparison of the actual Adams towers and every triangle arrow.
The zero-stage map is prescribed. Layers are defined above, not chosen.
The third equation retains F's exact suspension comparison and hence the
sign in the actual connecting map. -/
structure Comparison (base : F.obj Y ≅ X) where
  tower : TowerIdentifications F unitS unitC Y X
  zero : tower 0 = base
  unit : CoefficientUnitCompatible F unitS unitC coefficient
  step : ∀ n : ℕ,
    F.map (adamsTowerStep unitS Y n) ≫ (tower n).hom =
      (tower (n+1)).hom ≫ adamsTowerStep unitC X n
  cofiber : ∀ s : ℤ,
    F.map (HasFunctorialCofiber.cofibι
        (adamsTowerMapAt unitS Y s (s+1) (by omega))) ≫
      layerMap F unitS unitC coefficient Y X tower s =
    (tower s.toNat).hom ≫ HasFunctorialCofiber.cofibι
      (adamsTowerMapAt unitC X s (s+1) (by omega))
  connecting : ∀ s : ℤ,
    layerMap F unitS unitC coefficient Y X tower s ≫
      HasFunctorialCofiber.cofibδ (adamsTowerMapAt unitC X s (s+1) (by omega)) =
    F.map (HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt unitS Y s (s+1) (by omega))) ≫
      (F.commShiftIso (1 : ℤ)).hom.app _ ≫
      (shiftFunctor C (1 : ℤ)).map (tower (s+1).toNat).hom

/-- F's sphere comparison is induced by its own monoidal unit and ordinary
suspension compatibility. It is not supplied independently on each degree. -/
def sphereIso (n : ℤ) : F.obj (Sphere (C := S) n) ≅ Sphere (C := C) n :=
  (F.commShiftIso n).app (𝟙_ S) ≪≫
    (shiftFunctor C n).mapIso (Functor.Monoidal.εIso F).symm

variable {F unitS unitC coefficient Y X}
  {base : F.obj Y ≅ X} (P : Comparison F unitS unitC coefficient Y X base)

/-- The actual map of E1 representatives: apply realization to the map
from a sphere, then apply the displayed layer comparison. -/
def e1Map (s t : ℤ) : adamsE1 unitS Y s t →ₗ[ℤ] adamsE1 unitC X s t :=
  ({ toFun := fun a => (sphereIso F (t-s)).inv ≫ F.map a ≫
        layerMap F unitS unitC coefficient Y X P.tower s
     map_zero' := by simp
     map_add' := by intros; simp [Functor.map_add, Preadditive.comp_add,
       Preadditive.add_comp] } :
    adamsE1 unitS Y s t →+ adamsE1 unitC X s t).toIntLinearMap

end
end KIP126.Comparison.ClassicalSynthetic.RealizationTower
