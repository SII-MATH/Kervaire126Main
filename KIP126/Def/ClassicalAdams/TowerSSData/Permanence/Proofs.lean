module

public import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data
public import KIP126.Def.ClassicalAdams.TowerSSData.Page.Proofs
public import KIP126.Def.SpectralSequence.Permanence.Predicates

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Zero in a tower quotient means membership in its actual boundary submodule. -/
theorem adamsPage_mk_eq_zero (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (z : adamsCycles unit X r hr s t) :
    (adamsCycleBoundaries unit X r hr s t).mkQ z = 0 ↔
      z.val ∈ adamsBoundaries unit X r hr s t :=
  Submodule.Quotient.mk_eq_zero (adamsCycleBoundaries unit X r hr s t)

/-- Changing a page representative by a boundary preserves next-cycle
membership and the specified next-page class. -/
theorem adamsNextPage_representative_independence (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (z : adamsCycles unit X r hr s t)
    (w : adamsCycles unit X (r + 1) (by omega) s t)
    (h : adamsNextCycleToPage unit X r hr s t w =
      (adamsCycleBoundaries unit X r hr s t).mkQ z) :
    ∃ hz : z.val ∈ adamsCycles unit X (r + 1) (by omega) s t,
      (adamsCycleBoundaries unit X (r + 1) (by omega) s t).mkQ ⟨z.val, hz⟩ =
        (adamsCycleBoundaries unit X (r + 1) (by omega) s t).mkQ w := by
  have hd : z.val - w.val ∈ adamsBoundaries unit X r hr s t :=
    (Submodule.Quotient.eq (adamsCycleBoundaries unit X r hr s t)).mp h.symm
  have hdZ : z.val - w.val ∈ adamsCycles unit X (r + 1) (by omega) s t := by
    obtain ⟨a, _, ha⟩ := hd
    rw [← ha]
    exact adamsJ_mem_cycles unit X (r + 1) (by omega) s t a
  have hz : z.val ∈ adamsCycles unit X (r + 1) (by omega) s t := by
    simpa only [sub_add_cancel] using
      (adamsCycles unit X (r + 1) (by omega) s t).add_mem hdZ w.property
  exact ⟨hz, (Submodule.Quotient.eq (adamsCycleBoundaries unit X (r + 1) (by omega) s t)).mpr
    (adamsBoundaries_le_succ unit X r hr s t hd)⟩

/-- A compatible family of finite quotient classes has a single tower
representative on every page. No inverse-limit or compactness assumption is used. -/
theorem adamsPages_common_representative (s t : ℤ)
    (x : ∀ n : ℕ, adamsPage unit X (n + 2) (by omega) s t)
    (h : ∀ n : ℕ, ∃ w : adamsCycles unit X (n + 2 + 1) (by omega) s t,
      adamsNextCycleToPage unit X (n + 2) (by omega) s t w = x n ∧
        (adamsCycleBoundaries unit X (n + 2 + 1) (by omega) s t).mkQ w = x (n + 1)) :
    ∃ z : adamsCycleAmbient unit X s t,
      ∀ n : ℕ, ∃ hz : z.val ∈ adamsCycles unit X (n + 2) (by omega) s t,
        (adamsCycleBoundaries unit X (n + 2) (by omega) s t).mkQ ⟨z.val, hz⟩ = x n := by
  obtain ⟨z, hz⟩ := (adamsCycleBoundaries unit X 2 (by omega) s t).mkQ_surjective (x 0)
  refine ⟨z, ?_⟩
  intro n
  induction n with
  | zero => exact ⟨z.property, hz⟩
  | succ n ih =>
    obtain ⟨hn, hx⟩ := ih
    obtain ⟨w, hw, hw'⟩ := h n
    obtain ⟨hn', heq⟩ := adamsNextPage_representative_independence unit X
      (n + 2) (by omega) s t ⟨z.val, hn⟩ w (hw.trans hx.symm)
    exact ⟨hn', heq.trans hw'⟩

/-- Nonzero on the infinite quotient means not a boundary at any finite stage. -/
theorem adamsTowerSSData_top_projection_ne_zero (s t : ℤ)
    (w : adamsCycleSubmodule unit X s t ⊤) :
    (adamsTowerSSData unit X s t).pageπ ⊤
      ((submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
        (adamsCycleSubmodule unit X s t ⊤)).inv w) ≠ 0 ↔
      ∀ n : ℕ, w.val.val ∉ adamsBoundaries unit X (n + 2) (by omega) s t := by
  let e := submoduleCokernelIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
    (adamsBoundarySubmodule unit X s t ⊤) (adamsCycleSubmodule unit X s t ⊤)
    (adamsBoundarySubmodule_le_cycle unit X s t ⊤)
  have hp := congrArg (fun f => f.hom w) (submoduleCokernelIso_π
    (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
    (adamsBoundarySubmodule unit X s t ⊤) (adamsCycleSubmodule unit X s t ⊤)
    (adamsBoundarySubmodule_le_cycle unit X s t ⊤))
  change e.hom ((adamsTowerSSData unit X s t).pageπ ⊤
    ((submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
      (adamsCycleSubmodule unit X s t ⊤)).inv w)) =
    ((adamsBoundarySubmodule unit X s t ⊤).comap
      (adamsCycleSubmodule unit X s t ⊤).subtype).mkQ w at hp
  have hz : (adamsTowerSSData unit X s t).pageπ ⊤
      ((submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
        (adamsCycleSubmodule unit X s t ⊤)).inv w) = 0 ↔
      w.val ∈ adamsBoundarySubmodule unit X s t ⊤ := by
    exact e.toLinearEquiv.map_eq_zero_iff.symm.trans
      ((Iff.of_eq (congrArg (fun z => z = 0) hp)).trans
        (Submodule.Quotient.mk_eq_zero ((adamsBoundarySubmodule unit X s t ⊤).comap
          (adamsCycleSubmodule unit X s t ⊤).subtype)))
  exact (not_congr hz).trans
    ((not_congr (mem_adamsBoundarySubmodule_top unit X s t w.val)).trans not_exists)

/-- Internal survival is precisely a single actual tower representative which
lifts through every finite stage and is never a finite-stage boundary. -/
theorem adamsTower_nonzeroSurvival_iff (s t : ℤ)
    (x : (adamsTowerInternalSpectralSequence unit X).Page 2 (s, t)) :
    NonzeroSurvival (adamsTowerInternalSpectralSequence unit X) (s, t) x ↔
      ∃ z : adamsCycleAmbient unit X s t,
        (∀ n : ℕ, z.val ∈ adamsCycles unit X (n + 2) (by omega) s t) ∧
        (∀ n : ℕ, z.val ∉ adamsBoundaries unit X (n + 2) (by omega) s t) ∧
        (adamsCycleBoundaries unit X 2 (by omega) s t).mkQ z =
          (adamsTowerSSDataPageIso unit X s t 0).hom x := by
  let e := submoduleUnderlyingIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t))
    (adamsCycleSubmodule unit X s t ⊤)
  have hp (w : adamsCycleSubmodule unit X s t ⊤) :
      (adamsTowerSSDataPageIso unit X s t 0).hom
        ((Subobject.ofLE ((adamsTowerSSData unit X s t).Z ⊤)
          ((adamsTowerSSData unit X s t).Z (0 : WithTop ℕ))
          ((adamsTowerSSData unit X s t).Z_anti le_top) ≫
          (adamsTowerSSData unit X s t).pageπ (0 : WithTop ℕ)) (e.inv w)) =
        (adamsCycleBoundaries unit X 2 (by omega) s t).mkQ w.val := by
    exact congrArg (fun f => f.hom w) (adamsTowerSSDataPageIso_submodule_π unit X s t 0
      (adamsCycleSubmodule unit X s t ⊤)
      (adamsCycleSubmodule_antitone unit X s t (show (↑(0 : ℕ) : WithTop ℕ) ≤ ⊤ from le_top)))
  constructor
  · rintro ⟨w, hx, hw⟩
    obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective e.inv).mp inferInstance w
    refine ⟨w.val, (mem_adamsCycleSubmodule_top unit X s t w.val).mp w.property,
      (adamsTowerSSData_top_projection_ne_zero unit X s t w).mp hw, ?_⟩
    exact (hp w).symm.trans (congrArg (adamsTowerSSDataPageIso unit X s t 0).hom hx)
  · rintro ⟨z, hz, hb, hx⟩
    let w : adamsCycleSubmodule unit X s t ⊤ :=
      ⟨z, (mem_adamsCycleSubmodule_top unit X s t z).mpr hz⟩
    refine ⟨e.inv w, ?_, (adamsTowerSSData_top_projection_ne_zero unit X s t w).mpr hb⟩
    exact (adamsTowerSSDataPageIso unit X s t 0).toLinearEquiv.injective ((hp w).trans hx)

/-- Nonzero survival is equivalent to compatible nonzero classes on the
actual finite tower quotients. Next-cycle representatives encode the
successor relation, and in particular force every outgoing differential to vanish. -/
theorem adamsTower_nonzeroSurvival_iff_compatible (s t : ℤ)
    (x : (adamsTowerInternalSpectralSequence unit X).Page 2 (s, t)) :
    NonzeroSurvival (adamsTowerInternalSpectralSequence unit X) (s, t) x ↔
      ∃ y : ∀ n : ℕ, adamsPage unit X (n + 2) (by omega) s t,
        y 0 = (adamsTowerSSDataPageIso unit X s t 0).hom x ∧
        (∀ n : ℕ, y n ≠ 0) ∧
        (∀ n : ℕ, ∃ w : adamsCycles unit X (n + 2 + 1) (by omega) s t,
          adamsNextCycleToPage unit X (n + 2) (by omega) s t w = y n ∧
          (adamsCycleBoundaries unit X (n + 2 + 1) (by omega) s t).mkQ w = y (n + 1)) := by
  rw [adamsTower_nonzeroSurvival_iff]
  constructor
  · rintro ⟨z, hz, hb, hx⟩
    let y (n : ℕ) :=
      (adamsCycleBoundaries unit X (n + 2) (by omega) s t).mkQ ⟨z.val, hz n⟩
    refine ⟨y, hx, ?_, ?_⟩
    · intro n hn
      have hq := adamsPage_mk_eq_zero unit X (n + 2) (by omega) s t ⟨z.val, hz n⟩
      exact hb n (hq.mp hn)
    · intro n
      exact ⟨⟨z.val, hz (n + 1)⟩, rfl, rfl⟩
  · rintro ⟨y, hy, hnonzero, hnext⟩
    obtain ⟨z, hz⟩ := adamsPages_common_representative unit X s t y hnext
    refine ⟨z, fun n => (hz n).choose, ?_, ?_⟩
    · intro n hn
      have hq := adamsPage_mk_eq_zero unit X (n + 2) (by omega) s t
        ⟨z.val, (hz n).choose⟩
      exact hnonzero n ((hz n).choose_spec.symm.trans (hq.mpr hn))
    · exact (hz 0).choose_spec.trans hy

end
end KIP126.Classical.Adams
