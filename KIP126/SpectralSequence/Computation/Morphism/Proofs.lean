module

public import KIP126.SpectralSequence.Computation.Proofs
import all KIP126.SpectralSequence.Computation.Proofs
public import KIP126.SpectralSequence.Basic.Category.Proofs
import all KIP126.SpectralSequence.Basic.Category.Proofs

@[expose] section


/-!
# Naturality of common representatives and differential equations

All maps here are the quotient maps induced by the ambient tower morphism.
No injectivity is assumed, so these results deliberately make no assertion
that a nonzero class stays nonzero.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

/-- A cycle-and-boundary-preserving ambient map carries common representatives
through any reindexing of the degrees, provided the starting pages agree.
Both displayed maps are the canonical quotient maps of this same `SSDataMorphism`.
No additivity of the reindexing or compatibility with differentials is needed. -/
public theorem SSDataMorphism.representsOnPage_reindexed
    {E E' : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
    {τ : (ℤ × ℤ) → (ℤ × ℤ)}
    (f : SSDataMorphism (ℤ × ℤ) E.ssData (fun p => E'.ssData (τ p)))
    (hstart : E.r₀ = E'.r₀) {r : ℤ} {p : ℤ × ℤ}
    {x : E.Page 2 p} {y : E.Page r p} (h : RepresentsOnPage E r p x y) :
    RepresentsOnPage E' r (τ p)
      ((f.pageMap p (↑(2 - E.r₀).toNat : WithTop ℕ) ≫ eqToHom
        (congrArg (fun a : ℤ => (E'.ssData (τ p)).page
          (↑(2 - a).toNat : WithTop ℕ)) hstart)) x)
      ((f.pageMap p (↑(r - E.r₀).toNat : WithTop ℕ) ≫ eqToHom
        (congrArg (fun a : ℤ => (E'.ssData (τ p)).page
          (↑(r - a).toNat : WithTop ℕ)) hstart)) y) := by
  rcases E with ⟨⟨r₀, D, δ, d⟩, dd, Zs, Bs⟩
  rcases E' with ⟨⟨r₀', D', δ', d'⟩, dd', Zs', Bs'⟩
  dsimp at hstart
  subst r₀'
  obtain ⟨hr, z, hx, hy⟩ := h
  let n : WithTop ℕ := ↑(2 - r₀).toNat
  let m : WithTop ℕ := ↑(r - r₀).toNat
  have hnm : n ≤ m := by
    dsimp [n, m]
    exact_mod_cast (show (2 - r₀).toNat ≤ (r - r₀).toNat by omega)
  refine ⟨hr, f.cycleMap p m z, ?_, ?_⟩
  · have hs := f.cycleMap_ofLE_assoc p hnm ((D' (τ p)).pageπ n)
    have hp := f.pageπ_pageMap p n
    have heq :
        (Subobject.ofLE ((D p).Z m) ((D p).Z n) ((D p).Z_anti hnm) ≫
          (D p).pageπ n) ≫ f.pageMap p n =
        f.cycleMap p m ≫
          Subobject.ofLE ((D' (τ p)).Z m) ((D' (τ p)).Z n)
            ((D' (τ p)).Z_anti hnm) ≫ (D' (τ p)).pageπ n := by
      rw [Category.assoc, hp]
      exact hs
    have hz := congrArg (fun a => a z) heq
    simpa only [ModuleCat.comp_apply, hx, eqToHom_refl, Category.comp_id, n, m]
      using hz.symm
  · have hz := congrArg (fun a => a z) (f.pageπ_pageMap p m)
    simpa only [ModuleCat.comp_apply, hy, eqToHom_refl, Category.comp_id, n, m]
      using hz.symm

/-- Differential equations transfer along a reindexed ambient morphism whose
induced quotient maps commute with the actual differentials. The reindexing
need only respect each differential translation; it need not be additive.
The commutation premise is a morphism law to be proved for any actual model. -/
public theorem SSDataMorphism.hasDifferential_reindexed
    {E E' : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
    {τ : (ℤ × ℤ) → (ℤ × ℤ)}
    (f : SSDataMorphism (ℤ × ℤ) E.ssData (fun p => E'.ssData (τ p)))
    (hstart : E.r₀ = E'.r₀)
    (hdegree : ∀ (r : ℤ) (p : ℤ × ℤ),
      τ (p + E.diffDeg r) = τ p + E'.diffDeg r)
    (hcomm :
      let Φ : ∀ (r : ℤ) (p : ℤ × ℤ), E.Page r p ⟶ E'.Page r (τ p) :=
        fun r p => f.pageMap p (↑(r - E.r₀).toNat : WithTop ℕ) ≫ eqToHom
          (congrArg (fun a : ℤ => (E'.ssData (τ p)).page
            (↑(r - a).toNat : WithTop ℕ)) hstart)
      ∀ (r : ℤ) (p : ℤ × ℤ),
        Φ r p ≫ E'.d r (τ p) =
          E.d r p ≫ Φ r (p + E.diffDeg r) ≫
            eqToHom (congrArg (E'.Page r) (hdegree r p)))
    {r : ℤ} {p q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
    (h : HasDifferential E r p q x y) :
    HasDifferential E' r (τ p) (τ q)
      ((f.pageMap p (↑(2 - E.r₀).toNat : WithTop ℕ) ≫ eqToHom
        (congrArg (fun a : ℤ => (E'.ssData (τ p)).page
          (↑(2 - a).toNat : WithTop ℕ)) hstart)) x)
      ((f.pageMap q (↑(2 - E.r₀).toNat : WithTop ℕ) ≫ eqToHom
        (congrArg (fun a : ℤ => (E'.ssData (τ q)).page
          (↑(2 - a).toNat : WithTop ℕ)) hstart)) y) := by
  let Φ : ∀ (r : ℤ) (p : ℤ × ℤ), E.Page r p ⟶ E'.Page r (τ p) :=
    fun r p => f.pageMap p (↑(r - E.r₀).toNat : WithTop ℕ) ≫ eqToHom
      (congrArg (fun a : ℤ => (E'.ssData (τ p)).page
        (↑(r - a).toNat : WithTop ℕ)) hstart)
  change ∀ (r : ℤ) (p : ℤ × ℤ),
    Φ r p ≫ E'.d r (τ p) = E.d r p ≫ Φ r (p + E.diffDeg r) ≫
      eqToHom (congrArg (E'.Page r) (hdegree r p)) at hcomm
  change HasDifferential E' r (τ p) (τ q) (Φ 2 p x) (Φ 2 q y)
  obtain ⟨hdeg, xr, yr, hx, hy, hd⟩ := h
  have hdeg' : τ p + E'.diffDeg r = τ q :=
    (hdegree r p).symm.trans (congrArg τ hdeg)
  refine ⟨hdeg', Φ r p xr, Φ r q yr, ?_, ?_, ?_⟩
  · exact f.representsOnPage_reindexed hstart hx
  · exact f.representsOnPage_reindexed hstart hy
  · have heq : Φ r p ≫ E'.d r (τ p) ≫ eqToHom (congrArg (E'.Page r) hdeg') =
        (E.d r p ≫ eqToHom (congrArg (E.Page r) hdeg)) ≫ Φ r q := by
      rw [← Category.assoc, hcomm, Category.assoc]
      subst q
      simp
    have hz := congrArg (fun a => a xr) heq
    simpa only [ModuleCat.comp_apply, hd] using hz

/-- A common cycle representative maps to a common cycle representative. -/
public theorem SpectralSequenceMorphism.representsOnPage
    {E E' : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
    (f : SpectralSequenceMorphism E E') {r : ℤ} {p : ℤ × ℤ}
    {x : E.Page 2 p} {y : E.Page r p} (h : RepresentsOnPage E r p x y) :
    RepresentsOnPage E' r p (f.pageMap 2 p x) (f.pageMap r p y) := by
  convert f.toSSDataMorphism.representsOnPage_reindexed (E := E) (E' := E')
    (τ := id) f.r₀_eq h using 1 <;> rfl

/-- Differential equations between named E₂ representatives are natural.
The image equation can have zero source or target. -/
public theorem SpectralSequenceMorphism.hasDifferential
    {E E' : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}
    (f : SpectralSequenceMorphism E E') {r : ℤ} {p q : ℤ × ℤ}
    {x : E.Page 2 p} {y : E.Page 2 q} (h : HasDifferential E r p q x y) :
    HasDifferential E' r p q (f.pageMap 2 p x) (f.pageMap 2 q y) := by
  have hdegree : ∀ (r : ℤ) (p : ℤ × ℤ),
      id (p + E.diffDeg r) = id p + E'.diffDeg r := by
    intro r p
    rw [f.diffDeg_eq]
    rfl
  have hf := f.toSSDataMorphism.hasDifferential_reindexed (E := E) (E' := E')
    (τ := id) f.r₀_eq hdegree (fun r p => by
      convert f.pageMap_comm_d r p using 1 <;> rfl) h
  convert hf using 1 <;> rfl

end KIP126.Core.SpectralSequence
