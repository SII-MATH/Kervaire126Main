module

public import KIP126.Def.AdamsSynthetic.Families
public import KIP126.Def.SpectralSequence.Convergence.Data
public import Mathlib.Algebra.Category.ModuleCat.Subobject

@[expose] section

/-! Given coefficient towers, with the full representative-level comparison.
No tower is recursively constructed here. The spectral sequence comparison
retains all finite cycles, boundaries, and the actual differential relation. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Core.SpectralSequence KIP126.Synthetic.SpectralSequence
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : SphereSpectrum ⟶ H)

/-- An abstract presentation of the coefficient-unit fiber tower. Integer
indices below zero are extended constantly, just as in the source model. -/
public structure AbstractAdamsTower (X : C) where
  stage : ℕ → C
  map : ∀ {s t : ℕ}, s ≤ t → (stage t ⟶ stage s)
  map_self : ∀ s, map (le_refl s) = 𝟙 _
  map_comp : ∀ {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t),
    map hst ≫ map hrs = map (hrs.trans hst)
  zeroIso : stage 0 ≅ X
  /-- The cofiber of a nonnegative step is the coefficient smash of that
  same stage. This assertion is intentionally not made at negative stages. -/
  layerIso : ∀ s : ℕ,
    HasFunctorialCofiber.cofib (map (Nat.le_succ s)) ≅ H ⊗ stage s
  layer_unit : ∀ s : ℕ,
    HasFunctorialCofiber.cofibι (map (Nat.le_succ s)) ≫ (layerIso s).hom =
      (λ_ (stage s)).inv ≫ unit ▷ (stage s)

namespace AbstractAdamsTower
variable {unit} {X : C} (T : AbstractAdamsTower unit X)
public abbrev stageAt (s : ℤ) := T.stage s.toNat
public def mapAt {s t : ℤ} (h : s ≤ t) : T.stageAt t ⟶ T.stageAt s :=
  T.map (show s.toNat ≤ t.toNat by omega)
public def projection (s : ℤ) : T.stageAt s ⟶ X :=
  T.map (Nat.zero_le s.toNat) ≫ T.zeroIso.hom
public def layer (s : ℤ) := HasFunctorialCofiber.cofib (T.mapAt (show s ≤ s + 1 by omega))
public abbrev FirstPage (p : ℤ × ℤ) := HomotopyGroup (p.2 - p.1) (T.layer p.1)
public def layerMap (p : ℤ × ℤ) :
    HomotopyGroup (p.2 - p.1) (T.stageAt p.1) →ₗ[ℤ] T.FirstPage p :=
  (inducedMap (HasFunctorialCofiber.cofibι (T.mapAt (show p.1 ≤ p.1 + 1 by omega)))
    (p.2 - p.1)).toIntLinearMap

/-- Desuspension uses the shift structure of this category. -/
public def desuspend (Y : C) (n : ℤ) :
    HomotopyGroup n (Y⟦(1 : ℤ)⟧) →+ HomotopyGroup (n - 1) Y where
  toFun z := (shiftFunctorAdd' C n (-1) (n - 1) (by omega)).hom.app SphereSpectrum ≫
    (shiftFunctor C (-1)).map z ≫ (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app Y
  map_zero' := by simp only [Functor.map_zero, zero_comp, comp_zero]
  map_add' a b := by rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

public def connecting (p : ℤ × ℤ) : T.FirstPage p →ₗ[ℤ]
    HomotopyGroup (p.2 - p.1 - 1) (T.stageAt (p.1 + 1)) :=
  ((desuspend (T.stageAt (p.1 + 1)) (p.2 - p.1)).comp
    (inducedMap (HasFunctorialCofiber.cofibδ (T.mapAt (show p.1 ≤ p.1 + 1 by omega)))
      (p.2 - p.1))).toIntLinearMap

public def cycles (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    Submodule ℤ (T.FirstPage p) :=
  (LinearMap.range (inducedMap (T.mapAt (show p.1 + 1 ≤ p.1 + r by omega))
    (p.2 - p.1 - 1)).toIntLinearMap).comap (T.connecting p)
public def boundaries (r : ℕ) (hr : 1 ≤ r) (p : ℤ × ℤ) :
    Submodule ℤ (T.FirstPage p) :=
  (LinearMap.ker (inducedMap (T.mapAt (show p.1 - r + 1 ≤ p.1 by omega))
    (p.2 - p.1)).toIntLinearMap).map (T.layerMap p)

public def homotopy (X : C) (m : ℤ) : ModuleCat.{v} ℤ :=
  ModuleCat.of ℤ (HomotopyGroup m X)
public def filtrationSubmodule (s m : ℤ) : Submodule ℤ (HomotopyGroup m X) :=
  LinearMap.range (inducedMap (T.projection s) m).toIntLinearMap

public theorem projection_compat {s t : ℤ} (h : s ≤ t) :
    T.mapAt h ≫ T.projection s = T.projection t := by
  simp only [projection, mapAt, ← Category.assoc, T.map_comp]

public theorem filtrationSubmodule_antitone (m : ℤ) : Antitone (fun s => T.filtrationSubmodule s m) := by
  intro s t h a ha
  obtain ⟨b, rfl⟩ := ha
  refine ⟨b ≫ T.mapAt h, ?_⟩
  change (b ≫ T.mapAt h) ≫ T.projection s = b ≫ T.projection t
  rw [Category.assoc, T.projection_compat h]

public def filtration : Filtration (homotopy X) where
  F s m := (ModuleCat.subobjectModule _).symm (T.filtrationSubmodule s m)
  mono s m := (ModuleCat.subobjectModule _).symm.monotone
    (T.filtrationSubmodule_antitone m (by omega : s ≤ s + 1))
end AbstractAdamsTower

/-- Comparison with a given page-two spectral sequence. Its ambient is the
actual Z₂ in the tower's first page, and all Z/B subobjects are constrained.
The last equation is the actual lift-and-cofiber differential, not a freely
chosen page map. Both zero and nonzero representatives are included. -/
public structure TowerSequencePresentation {X : C} (T : AbstractAdamsTower unit X)
    (D : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ))
    (d : ∀ (r : ℤ) (p : ℤ × ℤ), (D p).page (↑(r - 2).toNat : WithTop ℕ) ⟶
      (D (p + (r, r - 1))).page (↑(r - 2).toNat : WithTop ℕ)) where
  ambient : ∀ p, (D p).V ≅ ModuleCat.of ℤ (T.cycles 2 (by decide) p)
  cycles : ∀ p (n : ℕ) (a : (D p).V),
    a ∈ (ModuleCat.subobjectModule _ ((D p).Z n)) ↔
      ((ambient p).hom a).val ∈ T.cycles (n + 2) (by omega) p
  boundaries : ∀ p (n : ℕ) (a : (D p).V),
    a ∈ (ModuleCat.subobjectModule _ ((D p).B n)) ↔
      ((ambient p).hom a).val ∈ T.boundaries (n + 2) (by omega) p
  differential : ∀ (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ)
      (z : (Subobject.underlying.obj ((D p).Z (↑(r - 2).toNat : WithTop ℕ)) : ModuleCat ℤ))
      (a : HomotopyGroup (p.2 - p.1 - 1) (T.stageAt (p.1 + r)))
      (z' : (Subobject.underlying.obj ((D (p + (r, r - 1))).Z (↑(r - 2).toNat : WithTop ℕ)) : ModuleCat ℤ)),
    T.connecting p (((ambient p).hom (((D p).Z _).arrow z)).val) =
      a ≫ T.mapAt (show p.1 + 1 ≤ p.1 + r by omega) →
    (((ambient (p + (r, r - 1))).hom (((D (p + (r, r - 1))).Z _).arrow z')).val) =
      T.layerMap (p + (r, r - 1))
        (Eq.mp (congrArg (fun m => HomotopyGroup m (T.stageAt (p.1 + r)))
          (by dsimp; omega : p.2 - p.1 - 1 = (p + (r, r - 1)).2 - (p + (r, r - 1)).1)) a) →
    d r p ((D p).pageπ _ z) = (D (p + (r, r - 1))).pageπ _ z'

namespace TowerSequencePresentation
variable {unit} {X : C} {T : AbstractAdamsTower unit X}
  {D : (ℤ × ℤ) → SSData (ModuleCat.{v} ℤ)}
  {d : ∀ (r : ℤ) (p : ℤ × ℤ), (D p).page (↑(r - 2).toNat : WithTop ℕ) ⟶
      (D (p + (r, r - 1))).page (↑(r - 2).toNat : WithTop ℕ)}
public def infiniteRepresentativeE1 (P : TowerSequencePresentation unit T D d)
    (p : ℤ × ℤ) (z : (Subobject.underlying.obj ((D p).Z ⊤) : ModuleCat ℤ)) : T.FirstPage p :=
  ((P.ambient p).hom (((D p).Z ⊤).arrow z)).val
end TowerSequencePresentation

/-- Tower morphisms fix the actual map at stage zero. -/
public structure TowerMap {X Y : C} (T : AbstractAdamsTower unit X)
    (U : AbstractAdamsTower unit Y) (f : X ⟶ Y) where
  stage : ∀ n, T.stage n ⟶ U.stage n
  natural : ∀ {s t : ℕ} (h : s ≤ t), stage t ≫ U.map h = T.map h ≫ stage s
  zero : stage 0 ≫ U.zeroIso.hom = T.zeroIso.hom ≫ f

namespace TowerMap
variable {unit} {X Y : C} {T : AbstractAdamsTower unit X}
  {U : AbstractAdamsTower unit Y} {f : X ⟶ Y}
public theorem projection (φ : TowerMap unit T U f) (s : ℤ) :
    φ.stage s.toNat ≫ U.projection s = T.projection s ≫ f := by
  dsimp [AbstractAdamsTower.projection]
  rw [← Category.assoc, φ.natural, Category.assoc, φ.zero, ← Category.assoc]

/-- The cofiber-layer map induced by the same tower morphism. -/
public def layer (φ : TowerMap unit T U f) (s : ℤ) : T.layer s ⟶ U.layer s :=
  HasFunctorialCofiber.cofibMap (T.mapAt (show s ≤ s + 1 by omega))
    (U.mapAt (show s ≤ s + 1 by omega)) (φ.stage (s + 1).toNat) (φ.stage s.toNat)
    (φ.natural (show s.toNat ≤ (s + 1).toNat by omega))
end TowerMap

/-- Differential on the page-two normalized quotient indices. -/
public def normalizedDifferential
    (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
    (h0 : E.r₀ = 2) (hd : ∀ r, E.diffDeg r = (r, r - 1))
    (r : ℤ) (p : ℤ × ℤ) :
    (E.ssData p).page (↑(r - 2).toNat : WithTop ℕ) ⟶
      (E.ssData (p + (r, r - 1))).page (↑(r - 2).toNat : WithTop ℕ) :=
  eqToHom (by simp only [h0]) ≫
    E.d r p ≫ eqToHom (by simp only [h0, hd])

/-- One coefficient tower on each object, with representative-level naturality
for the same Adams functor. Concrete tower construction is left to a producer. -/
public structure ClassicalTowerPresentation
    (A : KIP126.Classical.Adams.ClassicalAdamsFamily C) where
  tower : ∀ X, AbstractAdamsTower unit X
  map : ∀ {X Y : C} (f : X ⟶ Y), TowerMap unit (tower X) (tower Y) f
  sequence : ∀ X, TowerSequencePresentation unit (tower X) (A.obj X).ssData
    (normalizedDifferential (A.obj X) (A.firstPage X) (A.differentialDegree X))
  natural : ∀ {X Y : C} (f : X ⟶ Y) (p : ℤ × ℤ) (a : ((A.obj X).ssData p).V),
    (((sequence Y).ambient p).hom ((A.map f).φ p a)).val =
      (((sequence X).ambient p).hom a).val ≫ (map f).layer p.1

section Synthetic
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {HS : Syn} (synUnit : S_0_0 ⟶ HS)

/-- Fixed-weight differential of the given synthetic family. -/
public def fixedWeightDifferential (A : SyntheticAdamsSS.{v}) (w r : ℤ) (p : ℤ × ℤ) :
    (A.sequence.ssData (p.1,p.2,w)).page (↑(r - 2).toNat : WithTop ℕ) ⟶
      (A.sequence.ssData ((p + (r,r-1)).1,(p + (r,r-1)).2,w)).page
        (↑(r - 2).toNat : WithTop ℕ) :=
  eqToHom (by simp only [A.firstPage]) ≫
    A.sequence.d r (p.1,p.2,w) ≫ eqToHom (by
      simp only [A.firstPage, A.differentialDegree,
        syntheticAdamsRawShift, Prod.fst_add, Prod.snd_add]
      congr 2
      exact Prod.ext rfl (Prod.ext rfl (add_zero w)))

/-- The chosen synthetic family is the same coefficient tower in every fixed
weight. The comparison includes all cycles/boundaries and actual differentials;
its naturality is tied to the actual stage and cofiber maps. -/
public structure SyntheticTowerPresentation (F : SyntheticAdamsFamily Syn) where
  tower : ∀ X, AbstractAdamsTower synUnit X
  map : ∀ {X Y : Syn} (f : X ⟶ Y), TowerMap synUnit (tower X) (tower Y) f
  sequence : ∀ (X : Syn) (w : ℤ), TowerSequencePresentation synUnit
    (tower ((SyntheticCategory.biShift (0, -w)).obj X))
    (fun p => (F.obj X).sequence.ssData (p.1,p.2,w))
    (fixedWeightDifferential (F.obj X) w)
  /-- Naturality on E₂: raw first-page representatives may differ by a
  genuine initial boundary. This retains the source `natural_e2` contract
  without imposing a stronger equality before quotienting. -/
  natural_e2 : ∀ {X Y : Syn} (f : X ⟶ Y) (w : ℤ) (p : ℤ × ℤ)
      (a : ((F.obj X).sequence.ssData (p.1,p.2,w)).V),
    (((sequence Y w).ambient p).hom ((F.map f).φ (p.1,p.2,w) a)).val -
      (((sequence X w).ambient p).hom a).val ≫
        (map ((SyntheticCategory.biShift (0,-w)).map f)).layer p.1 ∈
      (tower ((SyntheticCategory.biShift (0,-w)).obj Y)).boundaries 2 (by decide) p
end Synthetic
end
end KIP126.AdamsSynthetic
