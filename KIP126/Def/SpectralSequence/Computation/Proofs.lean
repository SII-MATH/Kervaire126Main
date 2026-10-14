module

public import KIP126.Def.SpectralSequence.Computation.Predicates
import all KIP126.Def.SpectralSequence.Computation.Predicates

@[expose] section


namespace KIP126.Core.SpectralSequence
open CategoryTheory
universe u v
variable {R : Type u} [Ring R]
  {E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
  {r : ℤ} {p q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}

/-- At page two, the common representative identifies the same element. -/
public theorem RepresentsOnPage.eq_on_page_two {a b : E.Page 2 p}
    (h : RepresentsOnPage E 2 p a b) : a = b := by
  obtain ⟨_, z, ha, hb⟩ := h
  simp only [Subobject.ofLE_refl, Category.id_comp] at ha
  exact ha.symm.trans hb

/-- Every E₂ element has a cycle representative on E₂ itself. -/
public theorem RepresentsOnPage.self_two (a : E.Page 2 p) :
    RepresentsOnPage E 2 p a a := by
  let D := E.ssData p
  let n : WithTop ℕ := ↑(2 - E.r₀).toNat
  letI : Epi (D.pageπ n) := CategoryTheory.Limits.coequalizer.π_epi
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (D.pageπ n)).mp inferInstance a
  refine ⟨by omega, z, ?_, hz⟩
  simpa only [Subobject.ofLE_refl, Category.id_comp] using hz

/-- Zero has a common zero representative on every allowed page. -/
public theorem RepresentsOnPage.zero (hr : 2 ≤ r) :
    RepresentsOnPage E r p 0 0 := by
  refine ⟨hr, 0, ?_, ?_⟩ <;> exact map_zero _

public theorem HasNonzeroDifferential.toHasDifferential
    (h : HasNonzeroDifferential E r p q x y) : HasDifferential E r p q x y := by
  obtain ⟨hdeg, xr, yr, hx, hy, hd, _⟩ := h
  exact ⟨hdeg, xr, yr, hx, hy, hd⟩

/-- No differential equation can have the wrong target degree. -/
public theorem HasDifferential.target_degree (h : HasDifferential E r p q x y) :
    p + E.diffDeg r = q := h.choose

/-- A page-two statement yields an equation on the named E₂ elements. -/
public theorem HasDifferential.eq_on_page_two {a : E.Page 2 p} {b : E.Page 2 q}
    (h : HasDifferential E 2 p q a b) :
    ∃ hdeg : p + E.diffDeg 2 = q,
      (E.d 2 p ≫ eqToHom (congrArg (E.Page 2) hdeg)) a = b := by
  obtain ⟨hdeg, xr, yr, hx, hy, hd⟩ := h
  exact ⟨hdeg, hx.eq_on_page_two ▸ hy.eq_on_page_two ▸ hd⟩

/-- A genuine zero differential, using linearity rather than database input. -/
public theorem hasDifferential_zero (hr : 2 ≤ r) (hdeg : p + E.diffDeg r = q) :
    HasDifferential E r p q 0 0 :=
  ⟨hdeg, 0, 0, RepresentsOnPage.zero hr, RepresentsOnPage.zero hr, map_zero _⟩

/-- A zero target group forces every E₂ differential into it to vanish.
The source element need not be zero. -/
public theorem hasDifferential_two_of_subsingleton_target [Subsingleton (E.Page 2 q)]
    (hdeg : p + E.diffDeg 2 = q) (a : E.Page 2 p) :
    HasDifferential E 2 p q a 0 :=
  ⟨hdeg, a, 0, RepresentsOnPage.self_two a,
    RepresentsOnPage.zero (by omega), Subsingleton.elim _ _⟩

public theorem IsPageBoundary.zero : IsPageBoundary E r p 0 :=
  ⟨0, map_zero (E.d r p).hom⟩

public theorem IsPageBoundary.add {a b : E.Page r (p + E.diffDeg r)}
    (ha : IsPageBoundary E r p a) (hb : IsPageBoundary E r p b) :
    IsPageBoundary E r p (a + b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x + y, map_add (E.d r p).hom x y⟩

public theorem IsPageBoundary.smul {a : E.Page r (p + E.diffDeg r)}
    (ha : IsPageBoundary E r p a) (c : R) :
    IsPageBoundary E r p (c • a) := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨c • x, map_smul (E.d r p).hom c x⟩

/-- A boundary is a cycle for that same page differential, not a nonzero
permanent cycle and not a synthetic homotopy class. -/
public theorem IsPageBoundary.d_eq_zero {a : E.Page r (p + E.diffDeg r)}
    (ha : IsPageBoundary E r p a) : E.d r (p + E.diffDeg r) a = 0 := by
  obtain ⟨x, rfl⟩ := ha
  have h := congrArg (fun f : E.Page r p ⟶
    E.Page r (p + E.diffDeg r + E.diffDeg r) => f x) (E.d_comp_d r p)
  simpa using h

public theorem IsPageBoundary.isCycle {a : E.Page r (p + E.diffDeg r)}
    (ha : IsPageBoundary E r p a) : IsPageCycle E r (p + E.diffDeg r) a :=
  ha.d_eq_zero

public theorem HasNonzeroDifferential.d_ne_zero
    (h : HasNonzeroDifferential E r p q x y) : E.d r p ≠ 0 := by
  obtain ⟨hdeg, xr, yr, _, _, heq, hne⟩ := h
  intro hz
  apply hne
  rw [hz] at heq
  simpa using heq.symm

public theorem HasNonzeroDifferential.source_survives
    (h : HasNonzeroDifferential E r p q x y) : SurvivesTo E r p x := by
  obtain ⟨hdeg, xr, yr, hx, _, heq, hne⟩ := h
  refine ⟨xr, hx, ?_⟩
  intro hz
  apply hne
  rw [hz] at heq
  simpa using heq.symm

public theorem HasNonzeroDifferential.target_survives
    (h : HasNonzeroDifferential E r p q x y) : SurvivesTo E r q y := by
  obtain ⟨_, _, yr, _, hy, _, hne⟩ := h
  exact ⟨yr, hy, hne⟩

/-- A specified nonzero differential is an incoming hit of its target. -/
public theorem HasNonzeroDifferential.hit_target
    (h : HasNonzeroDifferential E r p q x y) : HitOnPage E r q y := by
  obtain ⟨hdeg, xr, yr, _, hy, heq, hne⟩ := h
  exact ⟨p, hdeg, xr, yr, hy, hne, heq⟩

/-- If every continuation has zero differential, no specified nonzero
differential can start at that E₂ class. -/
public theorem HasNonzeroDifferential.not_all_zero
    (h : HasNonzeroDifferential E r p q x y) :
    ¬ DifferentialVanishesOn E r p x := by
  obtain ⟨hdeg, xr, yr, hx, _, heq, hne⟩ := h
  intro hz
  rw [ModuleCat.comp_apply, hz xr hx, map_zero] at heq
  exact hne heq.symm

/-- Construct the nonzero differential relation without a degree cast when
the target is already written in the differential's target degree. -/
public theorem hasNonzeroDifferential_of_representatives
    (y' : E.Page 2 (p + E.diffDeg r))
    (xr : E.Page r p) (yr : E.Page r (p + E.diffDeg r))
    (hx : RepresentsOnPage E r p x xr)
    (hy : RepresentsOnPage E r (p + E.diffDeg r) y' yr)
    (hd : E.d r p xr = yr) (hne : yr ≠ 0) :
    HasNonzeroDifferential E r p (p + E.diffDeg r) x y' := by
  refine ⟨rfl, xr, yr, hx, hy, ?_, hne⟩
  simpa only [eqToHom_refl, Category.comp_id] using hd

/-- Exhaustive target data reduce vanishing to exclusion of the specified
nonzero differential, without asserting that the source survives. -/
public theorem differentialVanishesOn_iff_not_hasNonzeroDifferential
    (y' : E.Page 2 (p + E.diffDeg r))
    (htargets : DifferentialTargets E r p x y') :
    DifferentialVanishesOn E r p x ↔
      ¬ HasNonzeroDifferential E r p (p + E.diffDeg r) x y' := by
  constructor
  · exact fun hz hd => hd.not_all_zero hz
  · intro hn xr hx
    rcases htargets xr hx with hz | ⟨yr, hy, hd⟩
    · exact hz
    · by_contra hne
      exact hn (hasNonzeroDifferential_of_representatives y' xr yr hx hy hd
        (fun hy0 => hne (hd.trans hy0)))

public theorem NeverHit.not_hit (h : NeverHit E p x) (hr : 2 ≤ r) :
    ¬ HitOnPage E r p x := by
  rintro ⟨q, hdeg, z, y, hy, hne, heq⟩
  exact h r hr q hdeg y hy hne z heq

end KIP126.Core.SpectralSequence
