module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/BasedSpace/HomotopyExtension/Suspension/Proofs.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Suspension.Compact.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Retraction.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.BasedSpace

open CategoryTheory Set _root_.Topology
open KIP126.Topology.HomotopyExtension
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Actual reduced suspension preserves homotopy extension for based
injections between compact Hausdorff spaces. -/
theorem suspendMap_hasHomotopyExtension {A B : BasedSpace.{u}}
    [CompactSpace A] [CompactSpace B] [T2Space A] [T2Space B]
    (f : A ⟶ B) (hf : Function.Injective f.map)
    (hH : HasHomotopyExtension (TopCat.ofHom f.map)) :
    HasHomotopyExtension (TopCat.ofHom (suspendMap f).map) := by
  obtain ⟨rB, hB0, hBf, hBr⟩ := hH.exists_cylinder_retraction
  obtain ⟨rI, hI0, hIl, hIr, hIrange⟩ := exists_interval_boundary_retraction
  change ∀ x t, rB (f.map x, t) = (f.map x, t) at hBf
  change ∀ q, (rB q).2 = 0 ∨ (rB q).1 ∈ range f.map at hBr
  let u : C(B × I, I) := ⟨fun q => min (rB q).2 q.2, rB.continuous.snd.min continuous_snd⟩
  let v : C(B × I, I) := ⟨fun q => ⟨(q.2 : ℝ) - u q,
    ⟨sub_nonneg.mpr (min_le_right _ _), by
      have := (u q).property.1
      have := q.2.property.2
      linarith⟩⟩,
    ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp u.continuous)).subtype_mk _⟩
  let b : C((B × I) × I, B × I) :=
    rB.comp ⟨fun q => (q.1.1, q.2), continuous_fst.fst.prodMk continuous_snd⟩
  let a : C((B × I) × I, I) :=
    u.comp ⟨fun q => (q.1.1, q.2), continuous_fst.fst.prodMk continuous_snd⟩
  let c : C((B × I) × I, I) :=
    v.comp ⟨fun q => (q.1.1, q.2), continuous_fst.fst.prodMk continuous_snd⟩
  let j : C((B × I) × I, I × I) :=
    rI.comp ⟨fun q => (q.1.2, c q), continuous_fst.snd.prodMk c.continuous⟩
  let time : C((B × I) × I, I) := ⟨fun q => ⟨(a q : ℝ) + min ((j q).2 : ℝ) (c q : ℝ),
    ⟨add_nonneg (a q).property.1 (le_min (j q).2.property.1 (c q).property.1), by
      have h := min_le_right ((j q).2 : ℝ) (c q : ℝ)
      change (a q : ℝ) + min ((j q).2 : ℝ) (c q : ℝ) ≤ 1
      have hc : (c q : ℝ) = (q.2 : ℝ) - (a q : ℝ) := rfl
      linarith [q.2.property.2]⟩⟩,
    ((continuous_subtype_val.comp a.continuous).add
      ((continuous_subtype_val.comp j.continuous.snd).min
        (continuous_subtype_val.comp c.continuous))).subtype_mk _⟩
  let raw : C((B × I) × I, B.suspension × I) :=
    ⟨fun q => (suspensionProjection B ((b q).1, (j q).1), time q),
      ((suspensionProjection B).continuous.comp
        (b.continuous.fst.prodMk j.continuous.fst)).prodMk time.continuous⟩
  have ha_side (x : A) (s t : I) : a ((f.map x, s), t) = t := by
    change min (rB (f.map x, t)).2 t = t
    rw [hBf]
    exact min_self _
  have hc_of_ha (q : (B × I) × I) (h : a q = q.2) : c q = 0 := by
    apply Subtype.ext
    change (q.2 : ℝ) - (a q : ℝ) = 0
    rw [h, sub_self]
  have raw_side (x : A) (s t : I) :
      raw ((f.map x, s), t) = (suspensionProjection B (f.map x, s), t) := by
    have ha := ha_side x s t
    have hc := hc_of_ha ((f.map x, s), t) ha
    have hj : j ((f.map x, s), t) = (s, 0) := by
      change rI (s, c ((f.map x, s), t)) = _
      rw [hc, hI0]
    apply Prod.ext
    · change suspensionProjection B ((rB (f.map x, t)).1,
        (j ((f.map x, s), t)).1) = _
      rw [hBf, hj]
    · apply Subtype.ext
      change (a ((f.map x, s), t) : ℝ) +
        min ((j ((f.map x, s), t)).2 : ℝ) (c ((f.map x, s), t) : ℝ) = (t : ℝ)
      rw [ha, hj, hc]
      simp
  have raw_end (x : B) (s t : I) (hs : s = 0 ∨ s = 1) :
      raw ((x, s), t) = (B.suspension.point, t) := by
    have hj : j ((x, s), t) = (s, c ((x, s), t)) := by
      change rI (s, c ((x, s), t)) = _
      rcases hs with rfl | rfl
      · exact hIl _
      · exact hIr _
    apply Prod.ext
    · change suspensionProjection B ((b ((x, s), t)).1, (j ((x, s), t)).1) = _
      rw [hj]
      exact suspensionProjection_collapsed _ _ (Or.inr hs)
    · apply Subtype.ext
      change (a ((x, s), t) : ℝ) +
        min ((j ((x, s), t)).2 : ℝ) (c ((x, s), t) : ℝ) = (t : ℝ)
      rw [hj, min_self]
      change (a ((x, s), t) : ℝ) + ((t : ℝ) - (a ((x, s), t) : ℝ)) = (t : ℝ)
      ring
  have collapsed (p : B × I) (t : I) (hp : SuspensionCollapsed B p) :
      raw (p, t) = (B.suspension.point, t) := by
    rcases hp with hp | hp
    · have h := raw_side A.point p.2 t
      rw [f.point] at h
      have he : p = (B.point, p.2) := Prod.ext hp rfl
      rw [he, h]
      exact Prod.ext (suspensionProjection_collapsed _ _ (Or.inl rfl)) rfl
    · exact raw_end p.1 p.2 t hp
  let R : C(B.suspension × I, B.suspension × I) :=
    ⟨fun q => Quot.lift (fun p => raw (p, q.2))
      (fun p p' h => (collapsed p q.2 h.1).trans (collapsed p' q.2 h.2).symm) q.1, by
      apply isQuotientMap_quot_mk.continuous_lift_prod_left
      exact raw.continuous⟩
  apply hasHomotopyExtension_of_cylinder_retraction
    (TopCat.ofHom (suspendMap f).map) (suspendMap_isClosedEmbedding f hf) R
  · intro z
    refine Quot.inductionOn z ?_
    intro p
    change raw (p, 0) = (suspensionProjection B p, 0)
    have ha : a (p, 0) = 0 := by
      change min (rB (p.1, 0)).2 0 = 0
      rw [hB0]
      exact min_self _
    have hc := hc_of_ha (p, 0) ha
    have hj : j (p, 0) = (p.2, 0) := by
      change rI (p.2, c (p, 0)) = _
      rw [hc, hI0]
    apply Prod.ext
    · change suspensionProjection B ((rB (p.1, 0)).1, (j (p, 0)).1) = _
      rw [hB0, hj]
    · apply Subtype.ext
      change (a (p, 0) : ℝ) + min ((j (p, 0)).2 : ℝ) (c (p, 0) : ℝ) = 0
      rw [ha, hj, hc]
      norm_num
  · intro z t
    refine Quot.inductionOn z ?_
    intro p
    exact raw_side p.1 p.2 t
  · rintro ⟨z, t⟩
    refine Quot.inductionOn z ?_
    intro p
    change (raw (p, t)).2 = 0 ∨
      (raw (p, t)).1 ∈ range (TopCat.ofHom (suspendMap f).map)
    rcases hBr (p.1, t) with hb | ⟨x, hx⟩
    · rcases hIrange (p.2, c (p, t)) with hj | hj | hj
      · left
        apply Subtype.ext
        change (a (p, t) : ℝ) + min ((j (p, t)).2 : ℝ) (c (p, t) : ℝ) = 0
        have ha : a (p, t) = 0 := by
          change min (rB (p.1, t)).2 t = 0
          rw [hb]
          exact min_eq_left t.property.1
        change (j (p, t)).2 = 0 at hj
        rw [ha, hj]
        change 0 + min 0 (c (p, t) : ℝ) = 0
        rw [zero_add]
        exact min_eq_left (c (p, t)).property.1
      · right
        refine ⟨A.suspension.point, ?_⟩
        exact (suspendMap f).point.trans
          (suspensionProjection_collapsed B _ (Or.inr (Or.inl hj))).symm
      · right
        refine ⟨A.suspension.point, ?_⟩
        exact (suspendMap f).point.trans
          (suspensionProjection_collapsed B _ (Or.inr (Or.inr hj))).symm
    · right
      refine ⟨suspensionProjection A (x, (j (p, t)).1), ?_⟩
      change suspensionProjection B (f.map x, (j (p, t)).1) =
        suspensionProjection B ((rB (p.1, t)).1, (j (p, t)).1)
      rw [hx]

/-- Every iterated actual suspension of a compact Hausdorff based
homotopy-extension injection again has full homotopy extension. -/
theorem iterateSuspensionMap_hasHomotopyExtension {A B : BasedSpace.{u}}
    [CompactSpace A] [CompactSpace B] [T2Space A] [T2Space B]
    (f : A ⟶ B) (hf : Function.Injective f.map)
    (hH : HasHomotopyExtension (TopCat.ofHom f.map)) (n : ℕ) :
    HasHomotopyExtension (TopCat.ofHom (iterateSuspensionMap f n).map) := by
  induction n with
  | zero => exact hH
  | succ n ih =>
    letI := (iterateSuspension_compact_t2 A n).1
    letI := (iterateSuspension_compact_t2 A n).2
    letI := (iterateSuspension_compact_t2 B n).1
    letI := (iterateSuspension_compact_t2 B n).2
    exact suspendMap_hasHomotopyExtension (iterateSuspensionMap f n)
      (iterateSuspensionMap_injective f hf n) ih

end KIP126.AdamsSynthetic.Source.BasedSpace
