module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

import KIP126.Def.AdamsSynthetic.Tower
import KIP126.Def.SpectralSequence.ModuleSubobject.Proofs
import all KIP126.Def.AdamsSynthetic.Internal.SphereBHS.Inverse
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.Types.Limits

/-! The old finite-kernel argument on the current actual Adams tower.
Nilpotent completeness is retained as invertibility of the actual 1-shift
map. No ordinary-to-completed source comparison is assumed or invented.
All declarations are private and no pending proof is added.
-/

@[expose] section
namespace KIP126.AdamsSynthetic.Internal.SphereBHS.Tower
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Internal.SphereBHS.Inverse
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {X : C} (T : AbstractAdamsTower unit X)

private def oneSubShift [HasProductsOfShape ℕ C] : ∏ᶜ T.stage ⟶ ∏ᶜ T.stage :=
  𝟙 _ - Pi.lift (fun s => Pi.π T.stage (s+1) ≫ T.map (Nat.le_succ s))

private theorem hom_delta_bijective [HasProductsOfShape ℕ C]
    (hT : IsIso (oneSubShift T)) (B : C) :
    Function.Bijective (fun z : ∀ s, B ⟶ T.stage s =>
      fun s => z s - z (s+1) ≫ T.map (Nat.le_succ s)) := by
  letI := hT
  have proj (z : ∀ s, B ⟶ T.stage s) (s : ℕ) :
      (Pi.lift z ≫ oneSubShift T) ≫ Pi.π T.stage s =
        z s - z (s+1) ≫ T.map (Nat.le_succ s) := by
    simp [oneSubShift, Preadditive.comp_sub, Preadditive.sub_comp]
  constructor
  · intro z w h
    have he : Pi.lift z ≫ oneSubShift T = Pi.lift w ≫ oneSubShift T := by
      apply Pi.hom_ext
      intro s
      simpa only [proj] using congrFun h s
    have he' := (cancel_mono (oneSubShift T)).mp he
    funext s
    simpa using congrArg (fun f => f ≫ Pi.π T.stage s) he'
  · intro y
    let z : ∀ s, B ⟶ T.stage s :=
      fun s => Pi.lift y ≫ inv (oneSubShift T) ≫ Pi.π T.stage s
    have hl : Pi.lift z = Pi.lift y ≫ inv (oneSubShift T) := by
      apply Pi.hom_ext
      intro s
      simp [z]
    refine ⟨z, funext fun s => ?_⟩
    change z s - z (s+1) ≫ T.map (Nat.le_succ s) = y s
    rw [← proj z s, hl]
    simp

private theorem separated_of_finite_kernels (n : ℤ)
    (hfinite : ∀ s, Finite (inducedMap (T.map (Nat.le_succ s)) n).ker)
    (hinj : Function.Injective (fun z : ∀ s, HomotopyGroup n (T.stage s) =>
      fun s => z s - z (s+1) ≫ T.map (Nat.le_succ s)))
    (a : ℕ) (x : HomotopyGroup n (T.stage a))
    (hx : ∀ b (hab : a ≤ b), x ∈ LinearMap.range
      (inducedMap (T.map hab) n).toIntLinearMap) : x = 0 := by
  apply separated_of_finite_ker (fun s => HomotopyGroup n (T.stage s))
    (fun a b hab => inducedMap (T.map hab) n)
    (fun a x => by simp only [T.map_self, inducedMap, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, Category.comp_id])
    (fun a b c hab hbc x => by
      change (x ≫ T.map hbc) ≫ T.map hab = _
      rw [Category.assoc, T.map_comp]
      rfl)
    hfinite ?_ a x hx
  intro z hz
  exact compatible_zero_of_difference_injective _
    (fun s => inducedMap (T.map (Nat.le_succ s)) n) hinj z hz

private theorem filtration_element_separated (n : ℤ)
    (hfinite : ∀ s, Finite (inducedMap (T.map (Nat.le_succ s)) n).ker)
    (hinj : Function.Injective (fun z : ∀ s, HomotopyGroup n (T.stage s) =>
      fun s => z s - z (s+1) ≫ T.map (Nat.le_succ s)))
    (x : HomotopyGroup n X)
    (hx : ∀ s : ℕ, x ∈ T.filtrationSubmodule s n) : x = 0 := by
  have hz : x ≫ T.zeroIso.inv = 0 := by
    apply separated_of_finite_kernels T n hfinite hinj 0 (x ≫ T.zeroIso.inv)
    intro s hs
    obtain ⟨y, hy⟩ := hx s
    refine ⟨y, ?_⟩
    apply (cancel_mono T.zeroIso.hom).mp
    change y ≫ (T.map (Nat.zero_le s) ≫ T.zeroIso.hom) = x at hy
    change (y ≫ T.map hs) ≫ T.zeroIso.hom = (x ≫ T.zeroIso.inv) ≫ T.zeroIso.hom
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hy
  have h := congrArg (fun z => z ≫ T.zeroIso.hom) hz
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] using h

private theorem filtration_separated
    (hsep : ∀ (n : ℤ) (x : HomotopyGroup n X),
      (∀ s : ℕ, x ∈ T.filtrationSubmodule s n) → x = 0)
    (n : ℤ) (S : Subobject (AbstractAdamsTower.homotopy X n))
    (hS : ∀ s : ℤ, S ≤ T.filtration.F s n) : S = ⊥ := by
  apply (ModuleCat.subobjectModule (AbstractAdamsTower.homotopy X n)).injective
  rw [OrderIso.map_bot]
  apply le_antisymm
  · intro x hx
    apply (Submodule.mem_bot ℤ).mpr
    apply hsep n x
    intro s
    have hs := (ModuleCat.subobjectModule _).monotone (hS (s : ℤ))
    have hx' := hs hx
    simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using hx'
  · exact bot_le

private theorem quotientProjection_eq_zero_iff
    (s n : ℤ) (x : AbstractAdamsTower.homotopy X n) :
    T.filtration.quotientProjection s n x = 0 ↔
      x ∈ T.filtrationSubmodule s n := by
  refine (cokernel_π_eq_zero_iff_mem_range
    (T.filtration.F s n).arrow x).trans ?_
  change x ∈ (ModuleCat.subobjectModule (AbstractAdamsTower.homotopy X n))
    ((ModuleCat.subobjectModule (AbstractAdamsTower.homotopy X n)).symm (T.filtrationSubmodule s n)) ↔ _
  rw [OrderIso.apply_symm_apply]

/-- The prescribed cokernel cone is limiting, not just abstractly isomorphic
to some complete group. Only surjectivity of the difference and separation
at stage zero are needed for this step. -/
private theorem adams_complete_of_difference (n : ℤ)
    (hdelta : Function.Surjective
      (fun z : ∀ s, HomotopyGroup n (T.stage s) =>
        fun s => z s - z (s+1) ≫ T.map (Nat.le_succ s)))
    (hsep : ∀ x : HomotopyGroup n X,
      (∀ s : ℕ, x ∈ T.filtrationSubmodule s n) → x = 0) :
    Nonempty (Filtration.CompletionWitness
      T.filtration n) := by
  classical
  let F := T.filtration
  let q (s : ℤ) := F.quotientProjection s n
  have hq (s : ℤ) : Function.Surjective (q s) := by
    apply (ModuleCat.epi_iff_surjective _).mp
    change Epi (cokernel.π _)
    infer_instance
  have hk (s : ℤ) (x : HomotopyGroup n X) :
      q s x = 0 ↔ x ∈ T.filtrationSubmodule s n :=
    quotientProjection_eq_zero_iff T s n x
  suffices ht : Nonempty (IsLimit ((forget (ModuleCat ℤ)).mapCone (F.quotientTowerCone n))) by
    exact ⟨⟨isLimitOfReflects (forget (ModuleCat ℤ)) (Classical.choice ht)⟩⟩
  rw [Types.isLimit_iff]
  intro c hc
  have hcn (s : ℕ) :
      F.quotientTransition (by omega : (s : ℤ) ≤ (s+1 : ℕ)) n (c (s+1 : ℕ)) = c s := by
    exact hc (homOfLE (show (s+1 : ℕ) ≤ (s : OrderDual ℤ) from by
      change (s : ℤ) ≤ (s+1 : ℕ); omega))
  choose x hx using fun s : ℕ => hq s (c s)
  change ℕ → HomotopyGroup n X at x
  have hdiff (s : ℕ) : ∃ y : HomotopyGroup n (T.stage s),
      inducedMap (T.projection (s : ℤ)) n y = x s - x (s+1) := by
    have hh : q s (x s - x (s+1)) = 0 := by
      rw [map_sub, hx, sub_eq_zero]
      calc
        c s = F.quotientTransition (by omega : (s : ℤ) ≤ (s+1 : ℕ)) n (q (s+1 : ℕ) (x (s+1))) := by
          rw [hx, hcn]
        _ = q s (x (s+1)) := by
          exact ConcreteCategory.congr_hom (F.quotientProjection_transition
            (by omega : (s : ℤ) ≤ (s+1 : ℕ)) n) _
    exact (hk s _).mp hh
  obtain ⟨a, ha⟩ := common_representative (A := HomotopyGroup n X)
    (fun s => HomotopyGroup n (T.stage s))
    (fun s => inducedMap (T.map (Nat.le_succ s)) n)
    (fun s => inducedMap (T.projection (s : ℤ)) n)
    (by
      intro s y
      change (y ≫ T.map (Nat.le_succ s)) ≫ T.projection (s : ℤ) = _
      rw [Category.assoc]
      exact congrArg (fun f => y ≫ f)
        (T.projection_compat (show (s : ℤ) ≤ (s+1 : ℕ) by omega))) hdelta x hdiff
  have han (s : ℕ) : q s a = c s := by
    have hmem : x s - a ∈ T.filtrationSubmodule s n := ha s
    have he := (hk s _).mpr hmem
    rw [map_sub, hx, sub_eq_zero] at he
    exact he.symm
  have haall (s : ℤ) : q s a = c s := by
    let k := s.toNat
    have hsk : s ≤ (k : ℤ) := by dsimp [k]; omega
    have hcs : F.quotientTransition hsk n (c k) = c s :=
      hc (homOfLE (show (k : OrderDual ℤ) ≤ s from hsk))
    rw [← hcs, ← han k]
    exact (ConcreteCategory.congr_hom (F.quotientProjection_transition hsk n) a).symm
  refine ⟨a, haall, ?_⟩
  intro b hb
  change HomotopyGroup n X at b
  change ∀ s : ℤ, q s b = c s at hb
  change (b : HomotopyGroup n X) = a
  apply sub_eq_zero.mp
  apply hsep
  intro s
  apply (hk s _).mp
  rw [map_sub]
  change q s b - q s a = 0
  rw [hb, haall, sub_self]


/-- Conditional producer for the complete, separated actual tower filtration.
The two hypotheses are retained; this is not an instance for Standard.Spectrum. -/
private theorem complete_and_separated_of_acyclic_and_finite
    [HasProductsOfShape ℕ C] (hT : IsIso (oneSubShift T))
    (hfinite : ∀ (n : ℤ) (s : ℕ),
      Finite (inducedMap (T.map (Nat.le_succ s)) n).ker) :
    (∀ n : ℤ, Nonempty (Filtration.CompletionWitness T.filtration n)) ∧
      (∀ (n : ℤ) (S : Subobject (AbstractAdamsTower.homotopy X n)),
        (∀ s : ℤ, S ≤ T.filtration.F s n) → S = ⊥) := by
  have hd (n : ℤ) := hom_delta_bijective T hT (Sphere (C := C) n)
  have hs := fun n => filtration_element_separated T n (hfinite n) (hd n).injective
  exact ⟨fun n => adams_complete_of_difference T n (hd n).surjective (hs n),
    filtration_separated T hs⟩

end
end KIP126.AdamsSynthetic.Internal.SphereBHS.Tower
