module

public import KIP126.Def.ClassicalAdams.TowerSSData.Permanence.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  KIP126.StableHomotopy KIP126.SpectralSequence
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- The constant part of the integer-indexed tower has invertible transition maps. -/
theorem adamsTowerMapAt_isIso_of_nonpositive (s t : ℤ) (hst : s ≤ t) (ht : t ≤ 0) :
    IsIso (adamsTowerMapAt unit X s t hst) := by
  have hi (a b : ℕ) (hab : a ≤ b) (h : a = b) :
      IsIso (adamsTowerMap unit X a b hab) := by
    subst b
    rw [adamsTowerMap_self]
    infer_instance
  exact hi s.toNat t.toNat (by omega) (by omega)

/-- Negative-filtration layers are zero objects: their defining cofiber is
the cofiber of an isomorphism in the constant part of the tower. -/
theorem adamsLayerAt_isZero_of_negative (s : ℤ) (hs : s < 0) :
    IsZero (adamsLayerAt unit X s) := by
  let f := adamsTowerMapAt unit X s (s + 1) (by omega)
  haveI : IsIso f := adamsTowerMapAt_isIso_of_nonpositive unit X s (s + 1)
    (by omega) (by omega)
  exact Pretriangulated.Triangle.isZero₃_of_isIso₁
    (Pretriangulated.Triangle.mk f (HasFunctorialCofiber.cofibι f)
      (HasFunctorialCofiber.cofibδ f))
    (HasFunctorialCofiber.cofib_distinguished f) (show IsIso f from inferInstance)

/-- Every actual quotient page vanishes in negative filtration. -/
theorem adamsPage_subsingleton_of_negative (r : ℕ) (hr : 1 ≤ r)
    (s t : ℤ) (hs : s < 0) : Subsingleton (adamsPage unit X r hr s t) := by
  haveI : Subsingleton (adamsE1 unit X s t) :=
    ⟨fun x y => (adamsLayerAt_isZero_of_negative unit X s hs).eq_of_tgt x y⟩
  infer_instance

/-- Boundary submodules increase between any two ordered finite pages. -/
theorem adamsBoundaries_le_of_le (r q : ℕ) (hr : 1 ≤ r) (hq : 1 ≤ q)
    (hrq : r ≤ q) (s t : ℤ) :
    adamsBoundaries unit X r hr s t ≤ adamsBoundaries unit X q hq s t := by
  induction q, hrq using Nat.le_induction with
  | base => exact le_rfl
  | succ q hrq ih =>
    exact (ih (by omega)).trans (adamsBoundaries_le_succ unit X q (by omega) s t)

/-- Vanishing of an earlier tower page forces vanishing on every later page. -/
theorem adamsPage_subsingleton_of_le (r q : ℕ) (hr : 1 ≤ r) (hq : 1 ≤ q)
    (hrq : r ≤ q) (s t : ℤ) (h : Subsingleton (adamsPage unit X r hr s t)) :
    Subsingleton (adamsPage unit X q hq s t) := by
  have hz (z : adamsCycles unit X q hq s t) :
      (adamsCycleBoundaries unit X q hq s t).mkQ z = 0 := by
    let w : adamsCycles unit X r hr s t :=
      ⟨z.val, adamsCycles_le_of_le unit X s t r q hr hq hrq z.property⟩
    have hw := (adamsPage_mk_eq_zero unit X r hr s t w).mp
      (h.elim ((adamsCycleBoundaries unit X r hr s t).mkQ w) 0)
    exact (adamsPage_mk_eq_zero unit X q hq s t z).mpr
      (adamsBoundaries_le_of_le unit X r q hr hq hrq s t hw)
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := (adamsCycleBoundaries unit X q hq s t).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (adamsCycleBoundaries unit X q hq s t).mkQ_surjective y
  exact (hz a).trans (hz b).symm

/-- The internal SSData page inherits the actual negative-filtration vanishing. -/
theorem adamsTowerInternal_page_subsingleton_of_negative (r s t : ℤ) (hs : s < 0) :
    Subsingleton ((adamsTowerInternalSpectralSequence unit X).Page r (s, t)) := by
  haveI := adamsPage_subsingleton_of_negative unit X ((r - 2).toNat + 2) (by omega) s t hs
  exact (adamsTowerSSDataPageIso unit X s t (r - 2).toNat).toLinearEquiv.injective.subsingleton

-- Keep the existing named arguments for public API compatibility.
set_option linter.unusedVariables false in
/-- Transport the existing quotient-page vanishing theorem to the internal
sequence, retaining the starting-page and page-order hypotheses. -/
theorem adamsTowerInternal_page_subsingleton_of_le (r q s t : ℤ)
    (hr : 2 ≤ r) (hrq : r ≤ q)
    (h : Subsingleton ((adamsTowerInternalSpectralSequence unit X).Page r (s, t))) :
    Subsingleton ((adamsTowerInternalSpectralSequence unit X).Page q (s, t)) := by
  haveI : Subsingleton ((adamsTowerSSData unit X s t).page ↑(r - 2).toNat) := h
  have hraw : Subsingleton (adamsPage unit X ((r - 2).toNat + 2) (by omega) s t) :=
    (adamsTowerSSDataPageIso unit X s t (r - 2).toNat).toLinearEquiv.symm.injective.subsingleton
  haveI := adamsPage_subsingleton_of_le unit X
    ((r - 2).toNat + 2) ((q - 2).toNat + 2) (by omega) (by omega) (by omega) s t hraw
  exact (adamsTowerSSDataPageIso unit X s t (q - 2).toNat).toLinearEquiv.injective.subsingleton

end
end KIP126.Classical.Adams
