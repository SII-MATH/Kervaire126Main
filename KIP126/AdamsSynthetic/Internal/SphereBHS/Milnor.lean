module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Abel

/-! The kernel/cokernel and finite-geometric-sum part of the old Milnor-fiber
argument. These are conditional group-theoretic proofs, independent of a
choice of completed spectrum. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Internal.SphereBHS.Milnor
universe u
private theorem doubling_kernel_cokernel
    {B : Type u} [AddCommGroup B] (f : B →+ B)
    (hqsurj : ∀ b, ∃ x y, f x + (y + y) = b)
    (hqinj : ∀ x y, f x = y + y → ∃ z, x = z + z)
    (htsurj : ∀ b, b + b = 0 → ∃ x, x + x = 0 ∧ f x = b)
    (htinj : ∀ x, x + x = 0 → f x = 0 → x = 0) :
    (∀ x, f x = 0 → x + x = 0 → x = 0) ∧
    (∀ x, f x = 0 → ∃ y, f y = 0 ∧ y + y = x) ∧
    (∀ x, ∃ y z, y + y + f z = x) ∧
    (∀ x y, x + x = f y → ∃ z, f z = x) := by
  refine ⟨fun x hf hx => htinj x hx hf, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy⟩ := hqinj x 0 (by simpa using hx)
    have hfy : f y + f y = 0 := by rw [← map_add, ← hy, hx]
    obtain ⟨z, hz, hfz⟩ := htsurj (f y) hfy
    refine ⟨y - z, by simp [hfz], ?_⟩
    rw [hy]
    calc
      (y - z) + (y - z) = (y + y) - (z + z) := by abel
      _ = y + y := by rw [hz, sub_zero]
  · intro x
    obtain ⟨z, y, h⟩ := hqsurj x
    exact ⟨y, z, by simpa only [add_comm (f z)] using h⟩
  · intro x y h
    obtain ⟨z, hz⟩ := hqinj y x h.symm
    have ht : (x - f z) + (x - f z) = 0 := by
      rw [hz, map_add] at h
      calc
        (x - f z) + (x - f z) = (x + x) - (f z + f z) := by abel
        _ = 0 := sub_eq_zero.mpr h
    obtain ⟨w, _, hw⟩ := htsurj (x - f z) ht
    refine ⟨z + w, ?_⟩
    rw [map_add, hw]
    abel

private theorem shift_power_doubling_conditions
    {B : Type u} [AddCommGroup B] (sigma : Module.End ℤ B) (m : ℕ)
    (heven : ∀ x, ∃ y, (sigma ^ m) x = y + y)
    (htors : ∀ x, x + x = 0 → (sigma ^ m) x = 0) :
    (∀ b, ∃ x y, (1 - sigma) x + (y + y) = b) ∧
    (∀ x y, (1 - sigma) x = y + y → ∃ z, x = z + z) ∧
    (∀ b, b + b = 0 → ∃ x, x + x = 0 ∧ (1 - sigma) x = b) ∧
    (∀ x, x + x = 0 → (1 - sigma) x = 0 → x = 0) := by
  let S : Module.End ℤ B := ∑ i ∈ Finset.range m, sigma ^ i
  have hleft (x : B) : S ((1 - sigma) x) = x - (sigma ^ m) x := by
    have h := congrArg (fun f : Module.End ℤ B => f x) (geom_sum_mul_neg sigma m)
    exact h
  have hright (x : B) : (1 - sigma) (S x) = x - (sigma ^ m) x := by
    have h := congrArg (fun f : Module.End ℤ B => f x) (mul_neg_geom_sum sigma m)
    exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b
    obtain ⟨y, hy⟩ := heven b
    exact ⟨S b, y, by rw [hright, hy, sub_add_cancel]⟩
  · intro x y h
    obtain ⟨z, hz⟩ := heven x
    refine ⟨S y + z, ?_⟩
    have hh := hleft x
    rw [h, map_add, hz] at hh
    have hh' : x = (S y + S y) + (z + z) := (sub_eq_iff_eq_add).mp hh.symm
    rw [hh']
    abel
  · intro b hb
    refine ⟨S b, ?_, ?_⟩
    · rw [← map_add, hb, map_zero]
    · rw [hright, htors b hb, sub_zero]
  · intro x hx hd
    have hh := hleft x
    rw [hd, map_zero, htors x hx, sub_zero] at hh
    exact hh.symm

private theorem doubling_middle_of_exact
    {A B K C D : Type u} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup K] [AddCommGroup C] [AddCommGroup D]
    (f : A →+ B) (g : B →+ K) (i : K →+ C) (j : C →+ D)
    (hfg : ∀ b, g b = 0 ↔ ∃ a, f a = b)
    (hgi : ∀ z, i z = 0 ↔ ∃ b, g b = z)
    (hij : ∀ c, j c = 0 ↔ ∃ z, i z = c)
    (hkinj : ∀ c, j c = 0 → c + c = 0 → c = 0)
    (hksurj : ∀ c, j c = 0 → ∃ d, j d = 0 ∧ d + d = c)
    (hcsurj : ∀ b, ∃ c a, c + c + f a = b)
    (hcinj : ∀ b a, b + b = f a → ∃ c, f c = b) :
    Function.Bijective (fun z : K => z + z) := by
  have kill : ∀ z : K, z + z = 0 → z = 0 := by
    intro z hz
    have hiz : i z = 0 := hkinj (i z) ((hij _).mpr ⟨z, rfl⟩)
      (by rw [← map_add, hz, map_zero])
    obtain ⟨b, hb⟩ := (hgi z).mp hiz
    obtain ⟨a, ha⟩ := (hfg (b+b)).mp (by rw [map_add, hb, hz])
    obtain ⟨c, hc⟩ := hcinj b a ha.symm
    rw [← hb]
    exact (hfg b).mpr ⟨c, hc⟩
  constructor
  · intro x y hxy
    have hz : (x-y) + (x-y) = 0 := by
      have h : (x+x) - (y+y) = 0 := sub_eq_zero.mpr hxy
      calc
        (x-y) + (x-y) = (x+x) - (y+y) := by abel
        _ = 0 := h
    exact sub_eq_zero.mp (kill (x-y) hz)
  · intro z
    obtain ⟨c, hc, hd⟩ := hksurj (i z) ((hij _).mpr ⟨z, rfl⟩)
    obtain ⟨w, hw⟩ := (hij c).mp hc
    have hz : i (z - (w+w)) = 0 := by rw [map_sub, map_add, hw, hd, sub_self]
    obtain ⟨b, hb⟩ := (hgi _).mp hz
    obtain ⟨b', a, ha⟩ := hcsurj b
    have hfa : g (f a) = 0 := (hfg _).mpr ⟨a, rfl⟩
    refine ⟨w + g b', ?_⟩
    have hgb : g b = g b' + g b' := by rw [← ha, map_add, map_add, hfa, add_zero]
    rw [hgb] at hb
    calc
      (w + g b') + (w + g b') = (g b' + g b') + (w + w) := by abel
      _ = z := eq_sub_iff_add_eq.mp hb



end KIP126.AdamsSynthetic.Internal.SphereBHS.Milnor
