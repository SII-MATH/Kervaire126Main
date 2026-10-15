module

public import KIP126.Def.SpectralSequence.Computation.Predicates

@[expose] public section

namespace KIP126.SpectralSequence
open CategoryTheory
universe u v
variable {R : Type u} [Ring R]
  {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
  {r : ℤ} {p q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}

/-- At page two, the common representative identifies the same element. -/
theorem RepresentsOnPage.eq_on_page_two {a b : E.Page 2 p}
    (h : RepresentsOnPage E 2 p a b) : a = b := by
  obtain ⟨_, z, ha, hb⟩ := h
  simp only [Subobject.ofLE_refl, Category.id_comp] at ha
  exact ha.symm.trans hb

/-- Zero has a common zero representative on every allowed page. -/
theorem RepresentsOnPage.zero (hr : 2 ≤ r) :
    RepresentsOnPage E r p 0 0 := by
  refine ⟨hr, 0, ?_, ?_⟩ <;> exact map_zero _

theorem HasNonzeroDifferential.toHasDifferential
    (h : HasNonzeroDifferential E r p q x y) : HasDifferential E r p q x y := by
  obtain ⟨hdeg, xr, yr, hx, hy, hd, _⟩ := h
  exact ⟨hdeg, xr, yr, hx, hy, hd⟩

/-- A page-two statement yields an equation on the named E₂ elements. -/
theorem HasDifferential.eq_on_page_two {a : E.Page 2 p} {b : E.Page 2 q}
    (h : HasDifferential E 2 p q a b) :
    ∃ hdeg : p + E.diffDeg 2 = q,
      (E.d 2 p ≫ eqToHom (congrArg (E.Page 2) hdeg)) a = b := by
  obtain ⟨hdeg, xr, yr, hx, hy, hd⟩ := h
  exact ⟨hdeg, hx.eq_on_page_two ▸ hy.eq_on_page_two ▸ hd⟩

/-- A boundary is a cycle for that same page differential, not a nonzero
permanent cycle and not a synthetic homotopy class. -/
theorem IsPageBoundary.d_eq_zero {a : E.Page r (p + E.diffDeg r)}
    (ha : IsPageBoundary E r p a) : E.d r (p + E.diffDeg r) a = 0 := by
  obtain ⟨x, rfl⟩ := ha
  have h := congrArg (fun f : E.Page r p ⟶
    E.Page r (p + E.diffDeg r + E.diffDeg r) => f x) (E.d_comp_d r p)
  simpa using h

theorem HasNonzeroDifferential.target_survives
    (h : HasNonzeroDifferential E r p q x y) : SurvivesTo E r q y := by
  obtain ⟨_, _, yr, _, hy, _, hne⟩ := h
  exact ⟨yr, hy, hne⟩

theorem NeverHit.not_hit (h : NeverHit E p x) (hr : 2 ≤ r) :
    ¬ HitOnPage E r p x := by
  rintro ⟨q, hdeg, z, y, hy, hne, heq⟩
  exact h r hr q hdeg y hy hne z heq

end KIP126.SpectralSequence
