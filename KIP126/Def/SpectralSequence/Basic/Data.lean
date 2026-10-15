module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Abelian.Pseudoelements
public import Mathlib.Tactic.Abel

/-
Copyright (c) 2026 KIP126 contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KIP126 contributors
-/

@[expose] public section

/-!
# Nested-subobject spectral-sequence data

This is the axiom-free KIP126 migration of the data declarations in
`KIPBase/SpectralSequence/Basic.lean`.  It deliberately does not import the
historical `KIPBase` library or Mathlib's spectral-sequence structure.

At each grading, `SSData` records the classical nested chain

`V ⩾ Z₀ ⩾ Z₁ ⩾ ⋯ ⩾ Z∞ ⩾ B∞ ⩾ ⋯ ⩾ B₁ ⩾ B₀`,

and defines `E_r = Z_r / B_r`.  This file contains data and operations only;
predicates and named proofs live in the adjacent layers.
-/

namespace KIP126.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

/-- Nested cycle and boundary subobjects at one grading of a spectral sequence. -/
structure SSData (C : Type u) [Category.{v} C] [Abelian C] where
  /-- Ambient object. -/
  V : C
  /-- The decreasing family of cycle subobjects. -/
  Z : WithTop ℕ → Subobject V
  /-- The increasing family of boundary subobjects. -/
  B : WithTop ℕ → Subobject V
  /-- Cycles decrease with the page. -/
  Z_anti : Antitone Z
  /-- Boundaries increase with the page. -/
  B_mono : Monotone B
  /-- Every element is a zero-cycle. -/
  Z_zero : Z 0 = ⊤
  /-- Boundaries are cycles on every page. -/
  B_le_Z : ∀ r, B r ≤ Z r
  /-- `Z ⊤` is the infimum of the finite cycle stages. -/
  Z_top_greatest : ∀ (X : Subobject V), (∀ i : ℕ, X ≤ Z ↑i) → X ≤ Z ⊤
  /-- `B ⊤` is the supremum of the finite boundary stages. -/
  B_top_least : ∀ (X : Subobject V), (∀ i : ℕ, B ↑i ≤ X) → B ⊤ ≤ X

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The page `E_r = Z_r / B_r`. -/
noncomputable def SSData.page (D : SSData C) (r : WithTop ℕ) : C :=
  cokernel (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r))

/-- The infinity page `Z_∞ / B_∞`. -/
noncomputable def SSData.eInfty (D : SSData C) : C := D.page ⊤

/-- The quotient projection `Z_r ⟶ E_r`. -/
noncomputable def SSData.pageπ (D : SSData C) (r : WithTop ℕ) :
    Subobject.underlying.obj (D.Z r) ⟶ D.page r :=
  cokernel.π (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r))

/-- The data-only part of a spectral sequence. -/
structure PreSS (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] where
  /-- First displayed page. -/
  r₀ : ℤ
  /-- Nested-subobject data at each grading. -/
  ssData : ι → SSData C
  /-- Degree of the differential on each page. -/
  diffDeg : ℤ → ι
  /-- Page differential. -/
  d : (r : ℤ) → (k : ι) →
    ((ssData k).page ↑(r - r₀).toNat ⟶
      (ssData (k + diffDeg r)).page ↑(r - r₀).toNat)

/-- The page object derived from a `PreSS`. -/
@[reducible] noncomputable def PreSS.Page
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : PreSS C ι) (r : ℤ) (k : ι) : C :=
  (E.ssData k).page ↑(r - E.r₀).toNat

/-- A bare family of maps between the ambient objects of two `SSData` families. -/
structure UnderlyingMorphism
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι]
    (D D' : ι → SSData C) where
  /-- Map on each ambient object. -/
  φ : ∀ (k : ι), (D k).V ⟶ (D' k).V

/-- A morphism preserving the cycle and boundary towers. -/
structure SSDataMorphism
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι]
    (D D' : ι → SSData C) extends UnderlyingMorphism ι D D' where
  /-- The ambient maps preserve cycles. -/
  preserves_Z : ∀ (k : ι) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj ((D k).Z r) ⟶
      Subobject.underlying.obj ((D' k).Z r)),
      lift ≫ ((D' k).Z r).arrow = ((D k).Z r).arrow ≫ φ k
  /-- The ambient maps preserve boundaries. -/
  preserves_B : ∀ (k : ι) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj ((D k).B r) ⟶
      Subobject.underlying.obj ((D' k).B r)),
      lift ≫ ((D' k).B r).arrow = ((D k).B r).arrow ≫ φ k

/-- Identity on the ambient objects and their cycle and boundary towers. -/
def SSDataMorphism.id
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι] (D : ι → SSData C) :
    SSDataMorphism ι D D where
  φ := fun _ => 𝟙 _
  preserves_Z := fun _ _ => ⟨𝟙 _, by simp⟩
  preserves_B := fun _ _ => ⟨𝟙 _, by simp⟩

/-- Composition of ambient maps preserving both towers. -/
def SSDataMorphism.comp
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' D'' : ι → SSData C}
    (f : SSDataMorphism ι D D') (g : SSDataMorphism ι D' D'') :
    SSDataMorphism ι D D'' where
  φ := fun k => f.φ k ≫ g.φ k
  preserves_Z := fun k r =>
    ⟨(f.preserves_Z k r).choose ≫ (g.preserves_Z k r).choose, by
      rw [Category.assoc, (g.preserves_Z k r).choose_spec,
        ← Category.assoc, (f.preserves_Z k r).choose_spec, Category.assoc]⟩
  preserves_B := fun k r =>
    ⟨(f.preserves_B k r).choose ≫ (g.preserves_B k r).choose, by
      rw [Category.assoc, (g.preserves_B k r).choose_spec,
        ← Category.assoc, (f.preserves_B k r).choose_spec, Category.assoc]⟩

/-- The restriction of the ambient map to cycles.  The subobject arrow is mono,
so the preservation witness determines this map uniquely. -/
noncomputable def SSDataMorphism.cycleMap
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData C} (f : SSDataMorphism ι D D')
    (k : ι) (r : WithTop ℕ) :
    Subobject.underlying.obj ((D k).Z r) ⟶ Subobject.underlying.obj ((D' k).Z r) :=
  (f.preserves_Z k r).choose

/-- The canonical quotient map induced by the ambient map on `Z_r / B_r`.
This includes the infinity page and makes no independent choice of page maps. -/
noncomputable def SSDataMorphism.pageMap
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData C} (f : SSDataMorphism ι D D')
    (k : ι) (r : WithTop ℕ) : (D k).page r ⟶ (D' k).page r :=
  cokernel.map
    (Subobject.ofLE ((D k).B r) ((D k).Z r) ((D k).B_le_Z r))
    (Subobject.ofLE ((D' k).B r) ((D' k).Z r) ((D' k).B_le_Z r))
    (f.preserves_B k r).choose (f.cycleMap k r)
    (by
      apply (cancel_mono ((D' k).Z r).arrow).mp
      simp only [Category.assoc, SSDataMorphism.cycleMap,
        (f.preserves_Z k r).choose_spec, Subobject.ofLE_arrow,
        (f.preserves_B k r).choose_spec, Subobject.ofLE_arrow_assoc])

/-- The same quotient map with the displayed page numbering transported along
equality of starting pages. -/
noncomputable def SSDataMorphism.pageMapAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : PreSS C ι} (f : SSDataMorphism ι E.ssData E'.ssData)
    (h : E.r₀ = E'.r₀) (r : ℤ) (k : ι) : E.Page r k ⟶ E'.Page r k :=
  f.pageMap k ↑(r - E.r₀).toNat ≫ eqToHom (by rw [h])

/-- A morphism of pre-spectral sequences. -/
structure PreSSMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E E' : PreSS C ι) extends SSDataMorphism ι E.ssData E'.ssData where
  /-- Ordinary morphisms use the same displayed page numbering. -/
  r₀_eq : E.r₀ = E'.r₀
  /-- Ordinary morphisms preserve the differential degree on each page. -/
  diffDeg_eq : E.diffDeg = E'.diffDeg
  /-- The induced maps on pages commute with the differentials. -/
  comm_d : ∀ (r : ℤ) (k : ι),
    toSSDataMorphism.pageMapAt r₀_eq r k ≫ E'.d r k =
      E.d r k ≫ toSSDataMorphism.pageMapAt r₀_eq r (k + E.diffDeg r) ≫
        eqToHom (by rw [diffDeg_eq])

/-- The canonical page map of a pre-spectral-sequence morphism. -/
noncomputable def PreSSMorphism.pageMap
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : PreSS C ι} (f : PreSSMorphism E E') (r : ℤ) (k : ι) :
    E.Page r k ⟶ E'.Page r k :=
  f.toSSDataMorphism.pageMapAt f.r₀_eq r k

end KIP126.SpectralSequence

namespace KIP126

open CategoryTheory CategoryTheory.Limits

universe u v w

/-- A nested-subobject spectral sequence. -/
structure SpectralSequence (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι]
    extends SpectralSequence.PreSS C ι where
  /-- Every page differential squares to zero. -/
  d_comp_d : ∀ (r : ℤ) (k : ι), d r k ≫ d r (k + diffDeg r) = 0
  /-- The kernel of `d_r` is the image of `Z_(r+1)` on page `r`. -/
  Z_succ : ∀ (r : ℤ) (k : ι) (_ : r₀ ≤ r),
    let n := (r - r₀).toNat
    kernelSubobject (d r k) =
      imageSubobject (Subobject.ofLE
        ((ssData k).Z ↑(n + 1)) ((ssData k).Z ↑n)
        ((ssData k).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
        (ssData k).pageπ ↑n)
  /-- The image of `d_r` is the image of `B_(r+1)` on page `r`. -/
  B_succ : ∀ (r : ℤ) (k : ι) (_ : r₀ ≤ r),
    let n := (r - r₀).toNat
    imageSubobject (d r k) =
      imageSubobject (Subobject.ofLE
        ((ssData (k + diffDeg r)).B ↑(n + 1))
        ((ssData (k + diffDeg r)).Z ↑n)
        (le_trans ((ssData (k + diffDeg r)).B_le_Z ↑(n + 1))
          ((ssData (k + diffDeg r)).Z_anti (by exact_mod_cast Nat.le_succ n))) ≫
        (ssData (k + diffDeg r)).pageπ ↑n)

end KIP126

namespace KIP126.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The page object derived from a spectral sequence. -/
@[reducible] noncomputable def Page
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) : C :=
  (E.ssData k).page ↑(r - E.r₀).toNat

/-- The canonical quotient map `R/P ⟶ R/Q` for `P ≤ Q ≤ R`. -/
noncomputable def Subobject.cokernelDesc_ofLE {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.ofLE P R hPR) ⟶ cokernel (Subobject.ofLE Q R hQR) :=
  cokernel.desc _ (cokernel.π (Subobject.ofLE Q R hQR)) (by
    have : Subobject.ofLE P R hPR =
        Subobject.ofLE P Q hPQ ≫ Subobject.ofLE Q R hQR :=
      (Subobject.ofLE_comp_ofLE P Q R hPQ hQR).symm
    rw [this, Category.assoc, cokernel.condition, comp_zero])

/-- The canonical map `Q/P ⟶ R/P` for `P ≤ Q ≤ R`. -/
noncomputable def Subobject.cokernelMap_ofLE {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.ofLE P Q hPQ) ⟶ cokernel (Subobject.ofLE P R hPR) :=
  cokernel.desc _
    (Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR)) (by
      rw [← Category.assoc, Subobject.ofLE_comp_ofLE, cokernel.condition])

/-- The third-isomorphism identification `(R/P)/(Q/P) ≅ R/Q`. -/
noncomputable def Subobject.thirdIso {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR) ≅
      cokernel (Subobject.ofLE Q R hQR) :=
  { hom := cokernel.desc _ (Subobject.cokernelDesc_ofLE P Q R hPQ hQR hPR) (by
      ext
      simp only [Subobject.cokernelMap_ofLE, Subobject.cokernelDesc_ofLE,
        cokernel.π_desc_assoc, comp_zero]
      rw [Category.assoc, cokernel.π_desc, cokernel.condition])
    inv := cokernel.desc _ (cokernel.π (Subobject.ofLE P R hPR) ≫
        cokernel.π (Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR)) (by
      set f := Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR
      have h1 : cokernel.π (Subobject.ofLE P Q hPQ) ≫ f =
          Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR) :=
        cokernel.π_desc _ _ _
      calc
        Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR) ≫ cokernel.π f =
            (Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR)) ≫
              cokernel.π f := by rw [Category.assoc]
        _ = (cokernel.π (Subobject.ofLE P Q hPQ) ≫ f) ≫ cokernel.π f := by rw [h1]
        _ = cokernel.π (Subobject.ofLE P Q hPQ) ≫ (f ≫ cokernel.π f) := by
          rw [Category.assoc]
        _ = cokernel.π (Subobject.ofLE P Q hPQ) ≫ 0 := by rw [cokernel.condition]
        _ = 0 := comp_zero)
    hom_inv_id := by
      ext
      simp only [Category.comp_id, cokernel.π_desc,
        Subobject.cokernelDesc_ofLE, cokernel.π_desc_assoc]
    inv_hom_id := by
      ext
      simp only [Category.comp_id, Category.assoc, cokernel.π_desc_assoc,
        Subobject.cokernelDesc_ofLE, cokernel.π_desc] }

/-- The short complex centered at grading `k + diffDeg r` on page `r`. -/
noncomputable def pageShortComplex
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) : ShortComplex C :=
  ShortComplex.mk (E.d r k) (E.d r (k + E.diffDeg r)) (E.d_comp_d r k)

/-- A morphism of spectral sequences.  Its page maps are derived from `φ`,
not supplied independently. -/
structure SpectralSequenceMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E E' : SpectralSequence C ι) where
  /-- Map on each ambient object. -/
  φ : ∀ (k : ι), (E.ssData k).V ⟶ (E'.ssData k).V
  /-- The ambient maps preserve cycles. -/
  preserves_Z : ∀ (k : ι) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj ((E.ssData k).Z r) ⟶
      Subobject.underlying.obj ((E'.ssData k).Z r)),
      lift ≫ ((E'.ssData k).Z r).arrow = ((E.ssData k).Z r).arrow ≫ φ k
  /-- The ambient maps preserve boundaries. -/
  preserves_B : ∀ (k : ι) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj ((E.ssData k).B r) ⟶
      Subobject.underlying.obj ((E'.ssData k).B r)),
      lift ≫ ((E'.ssData k).B r).arrow = ((E.ssData k).B r).arrow ≫ φ k
  /-- Ordinary morphisms have the same displayed page numbering. -/
  r₀_eq : E.r₀ = E'.r₀
  /-- Ordinary morphisms have the same differential degrees. -/
  diffDeg_eq : E.diffDeg = E'.diffDeg
  /-- The canonical quotient maps commute with the differentials. -/
  comm_d : ∀ (r : ℤ) (k : ι),
    let f : SSDataMorphism ι E.ssData E'.ssData :=
      { φ := φ, preserves_Z := preserves_Z, preserves_B := preserves_B }
    f.pageMapAt (E := E.toPreSS) (E' := E'.toPreSS) r₀_eq r k ≫ E'.d r k =
      E.d r k ≫ f.pageMapAt (E := E.toPreSS) (E' := E'.toPreSS)
        r₀_eq r (k + E.diffDeg r) ≫ eqToHom (by rw [diffDeg_eq])

/-- Forget the differential law without changing the ambient map. -/
def SpectralSequenceMorphism.toSSDataMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι} (f : SpectralSequenceMorphism E E') :
    SSDataMorphism ι E.ssData E'.ssData where
  φ := f.φ
  preserves_Z := f.preserves_Z
  preserves_B := f.preserves_B

/-- The same morphism between the underlying pre-spectral sequences. -/
def SpectralSequenceMorphism.toPreSSMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι} (f : SpectralSequenceMorphism E E') :
    PreSSMorphism E.toPreSS E'.toPreSS where
  toSSDataMorphism := f.toSSDataMorphism
  r₀_eq := f.r₀_eq
  diffDeg_eq := f.diffDeg_eq
  comm_d := f.comm_d

/-- The canonical map on each displayed page. -/
noncomputable def SpectralSequenceMorphism.pageMap
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι} (f : SpectralSequenceMorphism E E')
    (r : ℤ) (k : ι) : E.Page r k ⟶ E'.Page r k :=
  f.toPreSSMorphism.pageMap r k

/-- The map induced by a spectral-sequence morphism on the infinity page. -/
noncomputable def SpectralSequenceMorphism.eInftyMap
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι} (f : SpectralSequenceMorphism E E') (k : ι) :
    (E.ssData k).eInfty ⟶ (E'.ssData k).eInfty :=
  f.toSSDataMorphism.pageMap k ⊤

end KIP126.SpectralSequence
