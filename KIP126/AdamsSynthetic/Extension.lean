module

public import KIP126.AdamsSynthetic.Detection
public import KIP126.SpectralSequence.Consumer.Extension
public import Mathlib.Algebra.Module.ULift

/-! Extension equations on the same map and the same convergence data.
No independent ESS relation, target ambiguity, or homotopy map is chosen. -/

@[expose] section
namespace KIP126.AdamsSynthetic

open CategoryTheory KIP126.Core.SpectralSequence
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence

universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]

/-- A convergence morphism tied to the actual map, on both abutment and E∞.
The chosen source and target convergence data remain parameters of the type. -/
public structure ConvergentMap (F : SyntheticAdamsFamily Syn)
    {X Y : Syn} (g : X ⟶ Y)
    {FX : Filtration (syntheticHomotopy X)} {FY : Filtration (syntheticHomotopy Y)}
    (cx : Convergence (F.obj X).sequence (syntheticHomotopy X) FX)
    (cy : Convergence (F.obj Y).sequence (syntheticHomotopy Y) FY) where
  comparison : ConvergenceMorphism cx cy
  abutment_eq : comparison.aMap = syntheticHomotopyMap g
  infinity_eq : comparison.eMap = (F.functor.map g).eInftyMap

/-- An element as a map from the free rank-one module in the same universe. -/
public noncomputable def elementMap {A : ModuleCat.{v} ℤ} (x : A) :
    ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ A :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton ℤ A x).comp ULift.moduleEquiv.toLinearMap)

namespace ConvergentMap
variable {F : SyntheticAdamsFamily Syn} {X Y : Syn} {g : X ⟶ Y}
  {FX : Filtration (syntheticHomotopy X)} {FY : Filtration (syntheticHomotopy Y)}
  {cx : Convergence (F.obj X).sequence (syntheticHomotopy X) FX}
  {cy : Convergence (F.obj Y).sequence (syntheticHomotopy Y) FY}

/-- The filtered map uses the same `g`; compatibility is supplied by its
convergence naturality witness, not by choosing another map. -/
public noncomputable def filteredMap (M : ConvergentMap F g cx cy) : FilteredMorphism FX FY :=
  M.comparison.filteredMap

@[simp] public theorem filteredMap_map (M : ConvergentMap F g cx cy) (p : ℤ × ℤ) :
    M.filteredMap.map p = syntheticHomotopyMap g p := congrFun M.abutment_eq p

end ConvergentMap

/-- Send an infinity-page arrow to the prescribed associated-graded piece.
The equality transports indices of the same convergence, not its objects. -/
public noncomputable def toGraded
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Tridegree}
    {A : (ℤ × ℤ) → ModuleCat.{v} ℤ} {G : Filtration A}
    (c : Convergence E A G) {i : Tridegree} {s : ℤ} {p : ℤ × ℤ}
    (h : c.reindex i = (s,p)) {T : ModuleCat.{v} ℤ}
    (x : T ⟶ (E.ssData i).eInfty) : T ⟶ G.associatedGraded s p :=
  x ≫ (c.iso i).hom ≫ G.transportGraded h

namespace ConvergentMap
variable {F : SyntheticAdamsFamily Syn} {X Y : Syn} {g : X ⟶ Y}
  {FX : Filtration (syntheticHomotopy X)} {FY : Filtration (syntheticHomotopy Y)}
  {cx : Convergence (F.obj X).sequence (syntheticHomotopy X) FX}
  {cy : Convergence (F.obj Y).sequence (syntheticHomotopy Y) FY}
  (M : ConvergentMap F g cx cy)
  (p : ℤ × ℤ) (s n : ℤ) {i j : Tridegree}
  (hi : cx.reindex i = (s,p)) (hj : cy.reindex j = (s+n,p))
  {T : ModuleCat.{v} ℤ}

/-- The actual filtered extension equation, with the original nonnegative length. -/
public def ExtensionEquation (x : T ⟶ ((F.obj X).sequence.ssData i).eInfty)
    (y : T ⟶ ((F.obj Y).sequence.ssData j).eInfty) : Prop :=
  FilteredMapExtension.Relation M.filteredMap p s n
    (toGraded cx hi x) (toGraded cy hj y)

/-- Essentiality modulo the entire homogeneous target solution space. -/
public def EssentialExtension (x : T ⟶ ((F.obj X).sequence.ssData i).eInfty)
    (y : T ⟶ ((F.obj Y).sequence.ssData j).eInfty) : Prop :=
  FilteredMapExtension.Essential M.filteredMap p s n
    (toGraded cx hi x) (toGraded cy hj y)

/-- A consumer obtains actual lifts without expanding any filtered complex. -/
public theorem extensionEquation_iff
    (x : T ⟶ ((F.obj X).sequence.ssData i).eInfty)
    (y : T ⟶ ((F.obj Y).sequence.ssData j).eInfty) :
    M.ExtensionEquation p s n hi hj x y ↔
      0 ≤ n ∧ ∃ (a : T ⟶ Subobject.underlying.obj (FX.F s p))
        (b : T ⟶ Subobject.underlying.obj (FY.F (s+n) p)),
        a ≫ FX.toAssociatedGraded s p = toGraded cx hi x ∧
        b ≫ FY.toAssociatedGraded (s+n) p = toGraded cy hj y ∧
        a ≫ (FX.F s p).arrow ≫ syntheticHomotopyMap g p = b ≫ (FY.F (s+n) p).arrow := by
  simp only [ExtensionEquation, FilteredMapExtension.Relation, filteredMap_map]

/-- All targets for this source, expressed as the full homogeneous coset. -/
public theorem targets_iff_coset
    (x : T ⟶ ((F.obj X).sequence.ssData i).eInfty)
    (y z : T ⟶ ((F.obj Y).sequence.ssData j).eInfty)
    (h : M.ExtensionEquation p s n hi hj x y) :
    M.ExtensionEquation p s n hi hj x z ↔
      toGraded cy hj z ∈ FilteredMapExtension.TargetCoset
        M.filteredMap p s n (toGraded cy hj y) :=
  (FilteredMapExtension.Relation.mem_targetCoset_iff h).symm

public theorem essential_iff_no_zero_target
    (x : T ⟶ ((F.obj X).sequence.ssData i).eInfty)
    (y : T ⟶ ((F.obj Y).sequence.ssData j).eInfty)
    (h : M.ExtensionEquation p s n hi hj x y) :
    M.EssentialExtension p s n hi hj x y ↔
      ¬ M.ExtensionEquation p s n hi hj x 0 := by
  simpa only [EssentialExtension, ExtensionEquation, toGraded,
    Limits.zero_comp] using FilteredMapExtension.essential_iff h

end ConvergentMap

section Tower
variable [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

/-- Element form of the same extension relation, with canonical tower degrees.
The equation remains meaningful without a bounded ESS construction. -/
public def TowerExtensionEquation
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty) : Prop :=
  M.ExtensionEquation p s n (by simp [SyntheticTowerConvergence.toConvergence])
    (by simp [SyntheticTowerConvergence.toConvergence]) (elementMap x) (elementMap y)

public def TowerEssentialExtension
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty) : Prop :=
  M.EssentialExtension p s n (by simp [SyntheticTowerConvergence.toConvergence])
    (by simp [SyntheticTowerConvergence.toConvergence]) (elementMap x) (elementMap y)
end Tower
end KIP126.AdamsSynthetic
