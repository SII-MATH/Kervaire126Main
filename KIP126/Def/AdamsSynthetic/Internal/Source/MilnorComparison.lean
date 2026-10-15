module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
-/

import KIP126.Def.AdamsSynthetic.Tower
import KIP126.Def.SpectralSequence
import all KIP126.Def.AdamsSynthetic.Internal.Source.AdamsTower
import all KIP126.Def.AdamsSynthetic.Internal.Source.AdamsSequence

/-! Actual first-page differential and the canonical quotient passage from
coefficient-tower cycles to its E₂ page. No comparison map is supplied here. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace KIP126.AdamsSynthetic.Internal.Source

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Core.SpectralSequence

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H} {X : C}

private def homotopyDegreeEquiv (Y : C) {m n : ℤ} (h : m = n) :
    HomotopyGroup m Y ≃ₗ[ℤ] HomotopyGroup n Y := by
  subst n
  exact LinearEquiv.refl ℤ _

private theorem homotopyDegreeEquiv_postcomp {Y Z : C} {m n : ℤ} (h : m = n)
    (a : HomotopyGroup m Y) (f : Y ⟶ Z) :
    homotopyDegreeEquiv Z h (a ≫ f) = homotopyDegreeEquiv Y h a ≫ f := by
  subst n
  rfl

/-- The actual exact-couple first differential, including the ordinary
homotopy-degree identification at its target. -/
private noncomputable def towerFirstDifferential (T : AbstractAdamsTower unit X)
    (p : ℤ × ℤ) : T.FirstPage p →ₗ[ℤ] T.FirstPage (p.1+1,p.2) :=
  (T.layerMap (p.1+1,p.2)).comp
    ((homotopyDegreeEquiv (T.stageAt (p.1+1))
      (by dsimp; omega : p.2-p.1-1 = (p.1+1,p.2).2-(p.1+1,p.2).1)).toLinearMap.comp
        (T.connecting p))

private theorem towerFirstDifferential_eq_zero_iff (T : AbstractAdamsTower unit X)
    (p : ℤ × ℤ) (x : T.FirstPage p) :
    towerFirstDifferential T p x = 0 ↔ x ∈ T.cycles 2 (by decide) p := by
  let hdegree : p.2-p.1-1 = p.2-(p.1+1) := by omega
  let f := T.mapAt (show p.1+1 ≤ (p.1+1)+1 by omega)
  let e := homotopyDegreeEquiv (T.stageAt (p.1+1)) hdegree
  let e' := homotopyDegreeEquiv (T.stageAt ((p.1+1)+1)) hdegree
  change e (T.connecting p x) ≫ HasFunctorialCofiber.cofibι f = 0 ↔
    ∃ a, a ≫ T.mapAt (show p.1+1 ≤ p.1+2 by omega) = T.connecting p x
  have hrange (q : ℤ) (hq : q = (p.1+1)+1) :
      (∃ a : HomotopyGroup (p.2-p.1-1) (T.stageAt q),
        a ≫ T.mapAt (show p.1+1 ≤ q by omega) = T.connecting p x) ↔
      ∃ a : HomotopyGroup (p.2-p.1-1) (T.stageAt ((p.1+1)+1)),
        a ≫ f = T.connecting p x := by
    subst q
    rfl
  rw [hrange (p.1+2) (by omega)]
  constructor
  · intro h
    obtain ⟨a,ha⟩ := Triangle.coyoneda_exact₂ _
      (HasFunctorialCofiber.cofib_distinguished f) (e (T.connecting p x)) h
    refine ⟨e'.symm a, ?_⟩
    apply e.injective
    change homotopyDegreeEquiv _ hdegree (e'.symm a ≫ f) = _
    rw [homotopyDegreeEquiv_postcomp]
    change e' (e'.symm a) ≫ f = _
    rw [LinearEquiv.apply_symm_apply]
    exact ha.symm
  · rintro ⟨a,ha⟩
    rw [← ha]
    change homotopyDegreeEquiv _ hdegree (a ≫ f) ≫ _ = 0
    rw [homotopyDegreeEquiv_postcomp, Category.assoc]
    have hzero : f ≫ HasFunctorialCofiber.cofibι f = 0 :=
      comp_distTriang_mor_zero₁₂ _ (HasFunctorialCofiber.cofib_distinguished f)
    rw [hzero, comp_zero]

private def firstPageDegreeEquiv (T : AbstractAdamsTower unit X)
    {p q : ℤ × ℤ} (h : p = q) : T.FirstPage p ≃ₗ[ℤ] T.FirstPage q := by
  subst q
  exact LinearEquiv.refl ℤ _

private noncomputable def towerFirstDifferentialNat (T : AbstractAdamsTower unit X)
    (s t : ℕ) : T.FirstPage ((s:ℤ),(t:ℤ)) →ₗ[ℤ]
      T.FirstPage (((s+1:ℕ):ℤ),(t:ℤ)) :=
  (firstPageDegreeEquiv T
    (show ((s:ℤ)+1,(t:ℤ)) = (((s+1:ℕ):ℤ),(t:ℤ)) by simp)).toLinearMap.comp
      (towerFirstDifferential T ((s:ℤ),(t:ℤ)))

private theorem towerFirstDifferentialNat_eq_zero_iff (T : AbstractAdamsTower unit X)
    (s t : ℕ) (x : T.FirstPage ((s:ℤ),(t:ℤ))) :
    towerFirstDifferentialNat T s t x = 0 ↔
      x ∈ T.cycles 2 (by decide) ((s:ℤ),(t:ℤ)) := by
  let e := firstPageDegreeEquiv T
    (show ((s:ℤ)+1,(t:ℤ)) = (((s+1:ℕ):ℤ),(t:ℤ)) by simp)
  change e (towerFirstDifferential T ((s:ℤ),(t:ℤ)) x) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, towerFirstDifferential_eq_zero_iff]

private instance zeroCycleArrow_isIso (D : SSData (ModuleCat.{v} ℤ)) :
    IsIso (D.Z 0).arrow :=
  (Subobject.isIso_arrow_iff_eq_top _).mpr D.Z_zero

private noncomputable def ambientToZeroPage (D : SSData (ModuleCat.{v} ℤ)) :
    D.V →ₗ[ℤ] D.page 0 :=
  (inv (D.Z 0).arrow ≫ D.pageπ 0).hom

private theorem ambientToZeroPage_eq_zero_iff (D : SSData (ModuleCat.{v} ℤ))
    (a : D.V) : ambientToZeroPage D a = 0 ↔ a ∈ ModuleCat.subobjectModule _ (D.B 0) := by
  change D.pageπ 0 (inv (D.Z 0).arrow a) = 0 ↔ _
  have hz := subobject_cokernel_π_eq_zero_iff (D.B 0) (D.Z 0) (D.B_le_Z 0)
    (inv (D.Z 0).arrow a)
  change D.pageπ 0 (inv (D.Z 0).arrow a) = 0 ↔ _ at hz
  have h := congrArg (fun f => f a) (IsIso.inv_hom_id (D.Z 0).arrow)
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at h
  exact hz.trans (by rw [h])

private theorem ambientToZeroPage_surjective (D : SSData (ModuleCat.{v} ℤ)) :
    Function.Surjective (ambientToZeroPage D) := by
  letI : Epi (D.pageπ 0) := by dsimp only [SSData.pageπ]; infer_instance
  exact (ModuleCat.epi_iff_surjective (inv (D.Z 0).arrow ≫ D.pageπ 0)).mp inferInstance

/-- The actual E₂ quotient map on the ambient module of second-page cycles. -/
private noncomputable def towerE2ClassMap (T : AbstractAdamsTower unit X) (p : ℤ × ℤ) :
    T.cycles 2 (by decide) p →ₗ[ℤ] (towerSequence T).Page 2 p :=
  ambientToZeroPage (towerSSData T p)

private noncomputable def towerE2ClassOfCycle (T : AbstractAdamsTower unit X)
    (p : ℤ × ℤ) (x : T.FirstPage p) (hx : x ∈ T.cycles 2 (by decide) p) :
    (towerSequence T).Page 2 p :=
  towerE2ClassMap T p ⟨x,hx⟩

private theorem towerE2ClassOfCycle_eq_zero_iff (T : AbstractAdamsTower unit X)
    (p : ℤ × ℤ) (x : T.FirstPage p) (hx : x ∈ T.cycles 2 (by decide) p) :
    towerE2ClassOfCycle T p x hx = 0 ↔ x ∈ T.boundaries 2 (by decide) p := by
  exact (ambientToZeroPage_eq_zero_iff (towerSSData T p) ⟨x,hx⟩).trans
    (towerSSData_boundaries T p 0 ⟨x,hx⟩)

private theorem towerE2ClassOfCycle_surjective (T : AbstractAdamsTower unit X)
    (p : ℤ × ℤ) (y : (towerSequence T).Page 2 p) :
    ∃ (x : T.FirstPage p) (hx : x ∈ T.cycles 2 (by decide) p),
      towerE2ClassOfCycle T p x hx = y := by
  obtain ⟨a,ha⟩ := ambientToZeroPage_surjective (towerSSData T p) y
  exact ⟨a.val,a.property,ha⟩

private theorem towerE2ClassMap_eq_iff (T : AbstractAdamsTower unit X) (p : ℤ × ℤ)
    (x y : T.cycles 2 (by decide) p) :
    towerE2ClassMap T p x = towerE2ClassMap T p y ↔
      x.val-y.val ∈ T.boundaries 2 (by decide) p := by
  rw [← sub_eq_zero, ← map_sub]
  exact towerE2ClassOfCycle_eq_zero_iff T p (x-y).val (x-y).property

private noncomputable def canonicalFirstDifferential (unit : SphereSpectrum ⟶ H)
    (X : C) (p : ℤ × ℤ) :
    (canonicalTower unit X).FirstPage p →ₗ[ℤ]
      (canonicalTower unit X).FirstPage (p.1+1,p.2) :=
  towerFirstDifferential (canonicalTower unit X) p

private noncomputable def canonicalE2ClassOfCycle (unit : SphereSpectrum ⟶ H)
    (X : C) (p : ℤ × ℤ) (x : (canonicalTower unit X).FirstPage p)
    (hx : x ∈ (canonicalTower unit X).cycles 2 (by decide) p) :
    (canonicalSequence unit X).Page 2 p :=
  towerE2ClassOfCycle (canonicalTower unit X) p x hx

private noncomputable def canonicalE2ClassOfFirstCocycle (unit : SphereSpectrum ⟶ H)
    (X : C) (p : ℤ × ℤ) (x : (canonicalTower unit X).FirstPage p)
    (hx : canonicalFirstDifferential unit X p x = 0) :
    (canonicalSequence unit X).Page 2 p :=
  canonicalE2ClassOfCycle unit X p x
    ((towerFirstDifferential_eq_zero_iff (canonicalTower unit X) p x).mp hx)

end KIP126.AdamsSynthetic.Internal.Source
