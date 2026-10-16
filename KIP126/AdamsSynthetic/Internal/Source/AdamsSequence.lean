module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
-/

import KIP126.AdamsSynthetic.Tower
import all KIP126.AdamsSynthetic.Internal.Source.AdamsTower

/-! The nested-subobject sequence of the recursively constructed coefficient
tower. Its ambient representatives, finite cycles/boundaries and infinite
intersection/union are fixed definitions. The deferred differential-existence
proof retains the actual connecting/lift/cofiber equation. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace KIP126.AdamsSynthetic.Internal.Source

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Core.SpectralSequence

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H} {X : C}

private noncomputable def towerI (T : AbstractAdamsTower unit X) (m s t : ℤ) (h : s ≤ t) :
    HomotopyGroup m (T.stageAt t) →ₗ[ℤ] HomotopyGroup m (T.stageAt s) :=
  (inducedMap (T.mapAt h) m).toIntLinearMap

private theorem towerI_comp (T : AbstractAdamsTower unit X) (m s t z : ℤ)
    (hst : s ≤ t) (htz : t ≤ z) (a : HomotopyGroup m (T.stageAt z)) :
    towerI T m s t hst (towerI T m t z htz a) = towerI T m s z (hst.trans htz) a := by
  change (a ≫ T.mapAt htz) ≫ T.mapAt hst = a ≫ T.mapAt (hst.trans htz)
  rw [Category.assoc]
  congr 1
  exact T.map_comp _ _

private abbrev cycleAmbient (T : AbstractAdamsTower unit X) (p : ℤ × ℤ) :=
  T.cycles 2 (by decide) p

private noncomputable def finiteCycles (T : AbstractAdamsTower unit X) (p : ℤ × ℤ) (n : ℕ) :
    Submodule ℤ (cycleAmbient T p) :=
  (T.cycles (n + 2) (by omega) p).comap (T.cycles 2 (by decide) p).subtype

private noncomputable def finiteBoundaries (T : AbstractAdamsTower unit X) (p : ℤ × ℤ)
    (n : ℕ) : Submodule ℤ (cycleAmbient T p) :=
  (T.boundaries (n + 2) (by omega) p).comap (T.cycles 2 (by decide) p).subtype

private noncomputable def allCycles (T : AbstractAdamsTower unit X) (p : ℤ × ℤ) :
    WithTop ℕ → Submodule ℤ (cycleAmbient T p)
  | ⊤ => ⨅ n : ℕ, finiteCycles T p n
  | (n : ℕ) => finiteCycles T p n

private noncomputable def allBoundaries (T : AbstractAdamsTower unit X) (p : ℤ × ℤ) :
    WithTop ℕ → Submodule ℤ (cycleAmbient T p)
  | ⊤ => ⨆ n : ℕ, finiteBoundaries T p n
  | (n : ℕ) => finiteBoundaries T p n

private theorem finiteCycles_antitone (T : AbstractAdamsTower unit X) (p : ℤ × ℤ) :
    Antitone (finiteCycles T p) := by
  intro i j hij x hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨towerI T (p.2-p.1-1) (p.1+(i+2:ℕ)) (p.1+(j+2:ℕ)) (by omega) y, ?_⟩
  change towerI T (p.2-p.1-1) (p.1+1) (p.1+(i+2:ℕ)) _ _ = _
  rw [towerI_comp]
  exact hy

private theorem finiteBoundaries_monotone (T : AbstractAdamsTower unit X) (p : ℤ × ℤ) :
    Monotone (finiteBoundaries T p) := by
  intro i j hij x hx
  obtain ⟨y, hy, hj⟩ := hx
  refine ⟨y, ?_, hj⟩
  change towerI T (p.2-p.1) (p.1-(i+2:ℕ)+1) p.1 _ y = 0 at hy
  change towerI T (p.2-p.1) (p.1-(j+2:ℕ)+1) p.1 _ y = 0
  rw [← towerI_comp T (p.2-p.1) (p.1-(j+2:ℕ)+1)
    (p.1-(i+2:ℕ)+1) p.1 (by omega) (by omega), hy, map_zero]

private theorem connecting_layerMap (T : AbstractAdamsTower unit X) (p : ℤ × ℤ)
    (a : HomotopyGroup (p.2-p.1) (T.stageAt p.1)) :
    T.connecting p (T.layerMap p a) = 0 := by
  let f := T.mapAt (show p.1 ≤ p.1+1 by omega)
  have hzero : HasFunctorialCofiber.cofibι f ≫ HasFunctorialCofiber.cofibδ f = 0 :=
    comp_distTriang_mor_zero₂₃ _ (HasFunctorialCofiber.cofib_distinguished f)
  change (AbstractAdamsTower.desuspend _ _)
    ((a ≫ HasFunctorialCofiber.cofibι f) ≫ HasFunctorialCofiber.cofibδ f) = 0
  rw [Category.assoc, hzero, comp_zero, map_zero]

private theorem finiteBoundaries_le_cycles (T : AbstractAdamsTower unit X) (p : ℤ × ℤ)
    (i j : ℕ) : finiteBoundaries T p i ≤ finiteCycles T p j := by
  intro x hx
  obtain ⟨y, _, hj⟩ := hx
  change T.layerMap p y = x.val at hj
  change T.connecting p x.val ∈ LinearMap.range _
  rw [← hj, connecting_layerMap]
  exact Submodule.zero_mem _

private theorem allCycles_antitone (T : AbstractAdamsTower unit X) (p : ℤ × ℤ) :
    Antitone (allCycles T p) := by
  intro i j hij
  cases i using WithTop.recTopCoe with
  | top => have h : j = ⊤ := top_le_iff.mp hij; subst j; exact le_rfl
  | coe i =>
    cases j using WithTop.recTopCoe with
    | top => exact iInf_le _ i
    | coe j => exact finiteCycles_antitone T p (WithTop.coe_le_coe.mp hij)

private theorem allBoundaries_monotone (T : AbstractAdamsTower unit X) (p : ℤ × ℤ) :
    Monotone (allBoundaries T p) := by
  intro i j hij
  cases i using WithTop.recTopCoe with
  | top => have h : j = ⊤ := top_le_iff.mp hij; subst j; exact le_rfl
  | coe i =>
    cases j using WithTop.recTopCoe with
    | top => exact le_iSup (finiteBoundaries T p) i
    | coe j => exact finiteBoundaries_monotone T p (WithTop.coe_le_coe.mp hij)

private theorem allBoundaries_le_cycles (T : AbstractAdamsTower unit X) (p : ℤ × ℤ)
    (r : WithTop ℕ) : allBoundaries T p r ≤ allCycles T p r := by
  cases r using WithTop.recTopCoe with
  | top => exact iSup_le fun i => le_iInf fun j => finiteBoundaries_le_cycles T p i j
  | coe n => exact finiteBoundaries_le_cycles T p n n

private noncomputable def towerSSData (T : AbstractAdamsTower unit X) (p : ℤ × ℤ) :
    SSData (ModuleCat.{v} ℤ) where
  V := ModuleCat.of ℤ (cycleAmbient T p)
  Z r := (ModuleCat.subobjectModule _).symm (allCycles T p r)
  B r := (ModuleCat.subobjectModule _).symm (allBoundaries T p r)
  Z_anti := (ModuleCat.subobjectModule _).symm.monotone.comp_antitone (allCycles_antitone T p)
  B_mono := (ModuleCat.subobjectModule _).symm.monotone.comp (allBoundaries_monotone T p)
  Z_zero := by
    change (ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p))).symm
      ((T.cycles 2 (by decide) p).comap (T.cycles 2 (by decide) p).subtype) = ⊤
    rw [Submodule.comap_subtype_self, OrderIso.map_top]
  B_le_Z r := (ModuleCat.subobjectModule _).symm.monotone (allBoundaries_le_cycles T p r)
  Z_top_greatest A h := by
    apply (ModuleCat.subobjectModule _).le_iff_le.mp
    change (ModuleCat.subobjectModule _) A ≤ (ModuleCat.subobjectModule _)
      ((ModuleCat.subobjectModule _).symm _)
    rw [OrderIso.apply_symm_apply]
    refine le_iInf fun n => ?_
    have hn := (ModuleCat.subobjectModule _).monotone (h n)
    rw [OrderIso.apply_symm_apply] at hn
    exact hn
  B_top_least A h := by
    apply (ModuleCat.subobjectModule _).le_iff_le.mp
    change (ModuleCat.subobjectModule _) ((ModuleCat.subobjectModule _).symm _) ≤
      (ModuleCat.subobjectModule _) A
    rw [OrderIso.apply_symm_apply]
    refine iSup_le fun n => ?_
    have hn := (ModuleCat.subobjectModule _).monotone (h n)
    rw [OrderIso.apply_symm_apply] at hn
    exact hn

private theorem towerSSData_cycles (T : AbstractAdamsTower unit X) (p : ℤ × ℤ)
    (n : ℕ) (a : (towerSSData T p).V) :
    a ∈ (ModuleCat.subobjectModule _ ((towerSSData T p).Z n)) ↔
      a.val ∈ T.cycles (n + 2) (by omega) p := by
  change a ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p)))
    ((ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p))).symm
      (finiteCycles T p n)) ↔ _
  rw [OrderIso.apply_symm_apply]
  rfl

private theorem towerSSData_boundaries (T : AbstractAdamsTower unit X) (p : ℤ × ℤ)
    (n : ℕ) (a : (towerSSData T p).V) :
    a ∈ (ModuleCat.subobjectModule _ ((towerSSData T p).B n)) ↔
      a.val ∈ T.boundaries (n + 2) (by omega) p := by
  change a ∈ (ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p)))
    ((ModuleCat.subobjectModule (ModuleCat.of ℤ (cycleAmbient T p))).symm
      (finiteBoundaries T p n)) ↔ _
  rw [OrderIso.apply_symm_apply]
  rfl

/-- Every representative is evaluated through the same connecting map,
the same actual tower lift and the same cofiber projection. -/
private def TowerDifferentialRule (T : AbstractAdamsTower unit X) (r : ℤ)
    (hr : 2 ≤ r) (p : ℤ × ℤ)
    (d : (towerSSData T p).page (↑(r - 2).toNat : WithTop ℕ) ⟶
      (towerSSData T (p + (r,r-1))).page (↑(r - 2).toNat : WithTop ℕ)) : Prop :=
  ∀ (z : (Subobject.underlying.obj ((towerSSData T p).Z (↑(r - 2).toNat : WithTop ℕ)) :
        ModuleCat ℤ))
    (a : HomotopyGroup (p.2 - p.1 - 1) (T.stageAt (p.1 + r)))
    (z' : (Subobject.underlying.obj
        ((towerSSData T (p + (r,r-1))).Z (↑(r - 2).toNat : WithTop ℕ)) : ModuleCat ℤ)),
    T.connecting p ((((towerSSData T p).Z _).arrow z).val) =
      a ≫ T.mapAt (show p.1 + 1 ≤ p.1 + r by omega) →
    ((((towerSSData T (p + (r,r-1))).Z _).arrow z').val) =
      T.layerMap (p + (r,r-1))
        (Eq.mp (congrArg (fun m => HomotopyGroup m (T.stageAt (p.1 + r)))
          (by dsimp; omega : p.2 - p.1 - 1 = (p + (r,r-1)).2 - (p + (r,r-1)).1)) a) →
    d ((towerSSData T p).pageπ _ z) = (towerSSData T (p + (r,r-1))).pageπ _ z'

/-- Existence and well-definedness of the linear map of quotient pages,
with its actual lift/cofiber formula. This does not choose an arbitrary d. -/
private theorem towerDifferential_exists (T : AbstractAdamsTower unit X) (r : ℤ)
    (hr : 2 ≤ r) (p : ℤ × ℤ) :
    ∃ d : (towerSSData T p).page (↑(r - 2).toNat : WithTop ℕ) ⟶
        (towerSSData T (p + (r,r-1))).page (↑(r - 2).toNat : WithTop ℕ),
      TowerDifferentialRule T r hr p d := by
  sorry

private noncomputable def towerD (T : AbstractAdamsTower unit X) (r : ℤ) (p : ℤ × ℤ) :
    (towerSSData T p).page (↑(r - 2).toNat : WithTop ℕ) ⟶
      (towerSSData T (p + (r,r-1))).page (↑(r - 2).toNat : WithTop ℕ) :=
  if hr : 2 ≤ r then (towerDifferential_exists T r hr p).choose else 0

private theorem towerD_rule (T : AbstractAdamsTower unit X) (r : ℤ) (hr : 2 ≤ r)
    (p : ℤ × ℤ) : TowerDifferentialRule T r hr p (towerD T r p) := by
  simpa only [towerD, dif_pos hr] using (towerDifferential_exists T r hr p).choose_spec

private noncomputable def towerPreSS (T : AbstractAdamsTower unit X) :
    PreSS (ModuleCat.{v} ℤ) (ℤ × ℤ) where
  r₀ := 2
  ssData := towerSSData T
  diffDeg r := (r,r-1)
  d := towerD T

private theorem towerD_comp (T : AbstractAdamsTower unit X) (r : ℤ) (p : ℤ × ℤ) :
    towerD T r p ≫ towerD T r (p + (r,r-1)) = 0 := by
  sorry

private theorem towerD_kernel (T : AbstractAdamsTower unit X) (r : ℤ) (p : ℤ × ℤ)
    (hr : 2 ≤ r) :
    let n := (r - 2).toNat
    kernelSubobject (towerD T r p) =
      imageSubobject (Subobject.ofLE
        ((towerSSData T p).Z ↑(n + 1)) ((towerSSData T p).Z ↑n)
        ((towerSSData T p).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
        (towerSSData T p).pageπ ↑n) := by
  sorry

private theorem towerD_image (T : AbstractAdamsTower unit X) (r : ℤ) (p : ℤ × ℤ)
    (hr : 2 ≤ r) :
    let n := (r - 2).toNat
    let D := towerSSData T (p + (r,r-1))
    imageSubobject (towerD T r p) =
      imageSubobject (Subobject.ofLE (D.B ↑(n + 1)) (D.Z ↑n)
        (le_trans (D.B_le_Z ↑(n + 1))
          (D.Z_anti (by exact_mod_cast Nat.le_succ n))) ≫ D.pageπ ↑n) := by
  sorry

private noncomputable def towerSequence (T : AbstractAdamsTower unit X) :
    KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ) where
  toPreSS := towerPreSS T
  d_comp_d := towerD_comp T
  Z_succ := towerD_kernel T
  B_succ := towerD_image T

private noncomputable def towerSequencePresentation (T : AbstractAdamsTower unit X) :
    TowerSequencePresentation unit T (towerSequence T).ssData
      (normalizedDifferential (towerSequence T) rfl (fun _ => rfl)) where
  ambient p := Iso.refl (ModuleCat.of ℤ (cycleAmbient T p))
  cycles := towerSSData_cycles T
  boundaries := towerSSData_boundaries T
  differential r hr p := towerD_rule T r hr p

private noncomputable def canonicalSequence (unit : SphereSpectrum ⟶ H) (X : C) :
    KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ) :=
  towerSequence (canonicalTower unit X)

private noncomputable def canonicalSequencePresentation (unit : SphereSpectrum ⟶ H) (X : C) :
    TowerSequencePresentation unit (canonicalTower unit X) (canonicalSequence unit X).ssData
      (normalizedDifferential (canonicalSequence unit X) rfl (fun _ => rfl)) :=
  towerSequencePresentation (canonicalTower unit X)

end KIP126.AdamsSynthetic.Internal.Source
