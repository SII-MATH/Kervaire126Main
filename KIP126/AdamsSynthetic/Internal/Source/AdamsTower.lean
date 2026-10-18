module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
-/

import KIP126.AdamsSynthetic.Tower

/-! The coefficient-unit Adams tower is constructed by actual iterated fibers.
The stage and transition maps are not supplied by an implementation record.
The proved rotation comparison identifies the chosen cofiber of a fiber inclusion
with its original target, including the original map out of the source. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Internal.Source

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

private def fiber {X Y : C} (f : X ⟶ Y) : C :=
  (HasFunctorialCofiber.cofib f)⟦(-1 : ℤ)⟧

private def fiberι {X Y : C} (f : X ⟶ Y) : fiber f ⟶ X :=
  (HasFunctorialCofiber.cofibδ f)⟦(-1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).hom.app X

private def adamsUnit {H : C} (unit : SphereSpectrum ⟶ H) (X : C) : X ⟶ H ⊗ X :=
  (λ_ X).inv ≫ unit ▷ X

private def adamsStage {H : C} (unit : SphereSpectrum ⟶ H) (X : C) : ℕ → C
  | 0 => X
  | s + 1 => fiber (adamsUnit unit (adamsStage unit X s))

private def adamsStep {H : C} (unit : SphereSpectrum ⟶ H) (X : C) (s : ℕ) :
    adamsStage unit X (s + 1) ⟶ adamsStage unit X s :=
  fiberι (adamsUnit unit (adamsStage unit X s))

private def adamsComposite {H : C} (unit : SphereSpectrum ⟶ H) (X : C) (s : ℕ) :
    (length : ℕ) → (adamsStage unit X (s + length) ⟶ adamsStage unit X s)
  | 0 => 𝟙 _
  | length + 1 => adamsStep unit X (s + length) ≫ adamsComposite unit X s length

private def adamsMap {H : C} (unit : SphereSpectrum ⟶ H) (X : C)
    (s t : ℕ) (h : s ≤ t) : adamsStage unit X t ⟶ adamsStage unit X s :=
  eqToHom (congrArg (adamsStage unit X) (by omega : t = s + (t - s))) ≫
    adamsComposite unit X s (t - s)

variable {H : C} (unit : SphereSpectrum ⟶ H) (X : C)

@[simp] private theorem adamsMap_self (s : ℕ) :
    adamsMap unit X s s le_rfl = 𝟙 _ := by
  apply eq_of_heq
  unfold adamsMap
  rw [eqToHom_comp_heq_iff, Nat.sub_self]
  rfl

private theorem adamsMap_succ (s t : ℕ) (h : s ≤ t) :
    adamsMap unit X s (t + 1) (by omega) =
      adamsStep unit X t ≫ adamsMap unit X s t h := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  apply eq_of_heq
  simp only [adamsMap, eqToHom_comp_heq_iff]
  have h : adamsComposite unit X s (s + n + 1 - s) ≍
      adamsStep unit X (s + n) ≫ adamsComposite unit X s n := by
    have hn : s + n + 1 - s = n + 1 := by omega
    rw [hn]
    rfl
  apply h.trans
  apply CategoryTheory.heq_comp rfl rfl rfl (HEq.rfl)
  symm
  rw [eqToHom_comp_heq_iff, Nat.add_sub_cancel_left]

private theorem adamsMap_comp (s t z : ℕ) (hst : s ≤ t) (htz : t ≤ z) :
    adamsMap unit X t z htz ≫ adamsMap unit X s t hst =
      adamsMap unit X s z (by omega) := by
  induction z, htz using Nat.le_induction with
  | base => simp
  | succ z htz ih =>
    rw [adamsMap_succ unit X t z htz,
      adamsMap_succ unit X s z (by omega), Category.assoc, ih]

omit unit X in
/-- The rotation comparison for the actual chosen fiber/cofiber, with the
source-to-target map fixed. The negative first isomorphism retains the
positive convention used in `fiberι`. -/
private theorem fiberLayerComparison_exists {A B : C} (f : A ⟶ B) :
    Nonempty {e : HasFunctorialCofiber.cofib (fiberι f) ≅ B //
      HasFunctorialCofiber.cofibι (fiberι f) ≫ e.hom = f} := by
  let T := (Triangle.mk f (HasFunctorialCofiber.cofibι f)
    (HasFunctorialCofiber.cofibδ f)).invRotate
  have hT : T ∈ distTriang C :=
    inv_rot_of_distTriang _ (HasFunctorialCofiber.cofib_distinguished f)
  have hfirst : T.mor₁ = -fiberι f := by
    simp only [T, Triangle.invRotate, Triangle.mk, fiberι]
    rfl
  let e : Triangle.mk (fiberι f) (HasFunctorialCofiber.cofibι (fiberι f))
      (HasFunctorialCofiber.cofibδ (fiberι f)) ≅ T :=
    isoTriangleOfIso₁₂ _ _ (HasFunctorialCofiber.cofib_distinguished (fiberι f)) hT
      (-(Iso.refl _)) (Iso.refl _) (by
        simp only [Triangle.mk, hfirst]
        change fiberι f ≫ 𝟙 A = (-𝟙 (fiber f)) ≫ (-fiberι f)
        simp)
  refine ⟨⟨Triangle.π₃.mapIso e, ?_⟩⟩
  have h := e.hom.comm₂
  change HasFunctorialCofiber.cofibι (fiberι f) ≫ e.hom.hom₃ = 𝟙 A ≫ f at h
  exact h.trans (Category.id_comp f)

private noncomputable def adamsLayerComparison (s : ℕ) :
    {e : HasFunctorialCofiber.cofib (adamsMap unit X s (s + 1) (Nat.le_succ s)) ≅
      H ⊗ adamsStage unit X s //
      HasFunctorialCofiber.cofibι (adamsMap unit X s (s + 1) (Nat.le_succ s)) ≫ e.hom =
        adamsUnit unit (adamsStage unit X s)} := by
  have hstep : adamsMap unit X s (s + 1) (Nat.le_succ s) =
      fiberι (adamsUnit unit (adamsStage unit X s)) := by
    rw [adamsMap_succ unit X s s le_rfl, adamsMap_self, Category.comp_id]
    rfl
  rw [hstep]
  exact Classical.choice (fiberLayerComparison_exists (adamsUnit unit (adamsStage unit X s)))

private noncomputable def canonicalTower : AbstractAdamsTower unit X where
  stage := adamsStage unit X
  map {s t} h := adamsMap unit X s t h
  map_self := adamsMap_self unit X
  map_comp {r s t} hrs hst := adamsMap_comp unit X r s t hrs hst
  zeroIso := Iso.refl X
  layerIso s := (adamsLayerComparison unit X s).val
  layer_unit s := (adamsLayerComparison unit X s).property

end KIP126.AdamsSynthetic.Internal.Source
