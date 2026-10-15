module

public import KIP126.Def.SpectralSequence.Basic.Predicates

@[expose] public section

/-!
# Elementary proofs for nested-subobject spectral sequences

The declarations here are source-ported from the proved part of
`KIPBase/SpectralSequence/Basic.lean`; no historical module is imported.
-/

namespace KIP126.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Bottom-page boundaries lie in the cycles on every page. -/
theorem SSData.B_bot_le_Z (D : SSData C) (r : WithTop ℕ) : D.B ⊥ ≤ D.Z r :=
  le_trans (D.B_mono bot_le) (D.B_le_Z r)

/-- If cycles and boundaries agree, the corresponding quotient page is zero. -/
theorem SSData.page_isZero_of_eq
    (D : SSData C) (r : WithTop ℕ) (h : D.B r = D.Z r) :
    IsZero (D.page r) := by
  unfold SSData.page
  have : IsIso (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)) := by
    rw [← Subobject.isoOfEq_hom _ _ h]
    infer_instance
  exact isZero_cokernel_of_epi _

/-- If a quotient page is zero, its cycles and boundaries agree. -/
theorem SSData.eq_of_page_isZero
    (D : SSData C) (r : WithTop ℕ) (h : IsZero (D.page r)) :
    D.B r = D.Z r := by
  unfold SSData.page at h
  have hepi : Epi (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)) := by
    rwa [Preadditive.epi_iff_isZero_cokernel]
  haveI : IsIso (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)) :=
    isIso_of_mono_of_epi _
  apply le_antisymm (D.B_le_Z r)
  exact Subobject.le_of_comm
    (inv (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)))
    (by simp [Subobject.ofLE_arrow])

/-- A spectral sequence with zero pages at one grading has zero infinity page there. -/
theorem eInfty_isZero_of_page_isZero
    {C : Type*} [Category C] [Abelian C]
    {α : Type*} [AddCommGroup α] [DecidableEq α]
    (E : SpectralSequence C α) (k : α)
    (h : ∀ r : ℤ, E.r₀ ≤ r → IsZero (E.Page r k)) :
    IsZero ((E.ssData k).eInfty) := by
  unfold SSData.eInfty
  apply SSData.page_isZero_of_eq
  set D := E.ssData k
  apply le_antisymm
  · exact D.B_le_Z ⊤
  · have hpage0 : IsZero (D.page (↑(0 : ℕ))) := by
      have hfirst := h E.r₀ (le_refl _)
      simp only [SpectralSequence.Page, SSData.page] at hfirst
      have hrr : (E.r₀ - E.r₀).toNat = 0 := by omega
      rw [hrr] at hfirst
      exact hfirst
    have hBZ : D.B ↑(0 : ℕ) = D.Z ↑(0 : ℕ) :=
      D.eq_of_page_isZero _ hpage0
    calc
      D.Z ⊤ ≤ D.Z ↑(0 : ℕ) := D.Z_anti le_top
      _ = D.B ↑(0 : ℕ) := hBZ.symm
      _ ≤ D.B ⊤ := D.B_mono le_top

/-- Extensionality for bare ambient morphisms. -/
@[ext]
theorem UnderlyingMorphism.ext
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData C} {f g : UnderlyingMorphism ι D D'}
    (h : f.φ = g.φ) : f = g := by
  rcases f with ⟨f_φ⟩
  rcases g with ⟨g_φ⟩
  congr!

/-- Preservation witnesses do not add choices to an ambient tower morphism. -/
@[ext]
theorem SSDataMorphism.ext
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {D D' : ι → SSData C} {f g : SSDataMorphism ι D D'}
    (h : f.φ = g.φ) : f = g := by
  cases f
  cases g
  congr 1
  exact UnderlyingMorphism.ext h

namespace SSDataMorphism

variable {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
variable {D D' D'' : ι → SSData C}

@[reassoc (attr := simp)]
theorem cycleMap_arrow (f : SSDataMorphism ι D D') (k : ι) (r : WithTop ℕ) :
    f.cycleMap k r ≫ ((D' k).Z r).arrow = ((D k).Z r).arrow ≫ f.φ k :=
  (f.preserves_Z k r).choose_spec

/-- The cycle restriction is uniquely determined by the ambient square. -/
theorem cycleMap_unique (f : SSDataMorphism ι D D') (k : ι) (r : WithTop ℕ)
    (m : Subobject.underlying.obj ((D k).Z r) ⟶
      Subobject.underlying.obj ((D' k).Z r))
    (hm : m ≫ ((D' k).Z r).arrow = ((D k).Z r).arrow ≫ f.φ k) :
    m = f.cycleMap k r := by
  apply (cancel_mono ((D' k).Z r).arrow).1
  rw [hm, cycleMap_arrow]

@[simp]
theorem cycleMap_id (D : ι → SSData C) (k : ι) (r : WithTop ℕ) :
    (id D).cycleMap k r = 𝟙 _ := by
  symm
  apply cycleMap_unique
  simp [id]

@[simp]
theorem cycleMap_comp (f : SSDataMorphism ι D D') (g : SSDataMorphism ι D' D'')
    (k : ι) (r : WithTop ℕ) :
    (f.comp g).cycleMap k r = f.cycleMap k r ≫ g.cycleMap k r := by
  symm
  apply cycleMap_unique
  simp [comp, Category.assoc]

/-- Cycle restrictions commute with inclusions between different pages. -/
@[reassoc]
theorem cycleMap_ofLE (f : SSDataMorphism ι D D') (k : ι)
    {r s : WithTop ℕ} (h : r ≤ s) :
    Subobject.ofLE ((D k).Z s) ((D k).Z r) ((D k).Z_anti h) ≫ f.cycleMap k r =
      f.cycleMap k s ≫
        Subobject.ofLE ((D' k).Z s) ((D' k).Z r) ((D' k).Z_anti h) := by
  apply (cancel_mono ((D' k).Z r).arrow).1
  simp [Category.assoc, Subobject.ofLE_arrow_assoc]

/-- The canonical page map sends a cycle representative to its ambient image. -/
@[reassoc (attr := simp)]
theorem pageπ_pageMap (f : SSDataMorphism ι D D') (k : ι) (r : WithTop ℕ) :
    (D k).pageπ r ≫ f.pageMap k r = f.cycleMap k r ≫ (D' k).pageπ r := by
  exact cokernel.π_desc _ _ _

/-- This representative identity uniquely determines the map of quotient pages. -/
theorem pageMap_unique (f : SSDataMorphism ι D D') (k : ι) (r : WithTop ℕ)
    (m : (D k).page r ⟶ (D' k).page r)
    (hm : (D k).pageπ r ≫ m = f.cycleMap k r ≫ (D' k).pageπ r) :
    m = f.pageMap k r := by
  apply (cancel_epi (cokernel.π
    (Subobject.ofLE ((D k).B r) ((D k).Z r) ((D k).B_le_Z r)))).1
  exact hm.trans (f.pageπ_pageMap k r).symm

@[simp]
theorem pageMap_id (D : ι → SSData C) (k : ι) (r : WithTop ℕ) :
    (id D).pageMap k r = 𝟙 _ := by
  symm
  apply pageMap_unique
  simp

@[simp]
theorem pageMap_comp (f : SSDataMorphism ι D D') (g : SSDataMorphism ι D' D'')
    (k : ι) (r : WithTop ℕ) :
    (f.comp g).pageMap k r = f.pageMap k r ≫ g.pageMap k r := by
  symm
  apply pageMap_unique
  simp [Category.assoc]

/-- Naturality for generalized cycle representatives, without projectivity
assumptions or a choice of a lift of an arbitrary quotient class. -/
@[reassoc]
theorem representative_naturality (f : SSDataMorphism ι D D') (k : ι)
    (r : WithTop ℕ) {T : C} (x : T ⟶ Subobject.underlying.obj ((D k).Z r)) :
    (x ≫ (D k).pageπ r) ≫ f.pageMap k r =
      (x ≫ f.cycleMap k r) ≫ (D' k).pageπ r := by
  simp [Category.assoc]

@[simp]
theorem pageMapAt_id (E : PreSS C ι) (r : ℤ) (k : ι) :
    (id E.ssData).pageMapAt (E := E) (E' := E) rfl r k = 𝟙 _ := by
  simp [pageMapAt]

theorem pageMapAt_comp {E E' E'' : PreSS C ι}
    (f : SSDataMorphism ι E.ssData E'.ssData)
    (g : SSDataMorphism ι E'.ssData E''.ssData)
    (hf : E.r₀ = E'.r₀) (hg : E'.r₀ = E''.r₀) (r : ℤ) (k : ι) :
    (f.comp g).pageMapAt (hf.trans hg) r k =
      f.pageMapAt hf r k ≫ g.pageMapAt hg r k := by
  rcases E with ⟨r₀, D, δ, d⟩
  rcases E' with ⟨r₀', D', δ', d'⟩
  rcases E'' with ⟨r₀'', D'', δ'', d''⟩
  dsimp at hf hg
  subst r₀'
  subst r₀''
  simp [pageMapAt]

end SSDataMorphism

/-- Extensionality for pre-spectral-sequence morphisms. -/
@[ext]
theorem PreSSMorphism.ext
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : PreSS C ι} {f g : PreSSMorphism E E'}
    (h : f.φ = g.φ) : f = g := by
  cases f with | mk f_sd _ _ _ => ?_
  cases f_sd with | mk f_u _ _ => ?_
  cases f_u with | mk f_φ => ?_
  cases g with | mk g_sd _ _ _ => ?_
  cases g_sd with | mk g_u _ _ => ?_
  cases g_u with | mk g_φ => ?_
  subst h
  rfl

/-- Extensionality for spectral-sequence morphisms. -/
@[ext]
theorem SpectralSequenceMorphism.ext
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι} {f g : SpectralSequenceMorphism E E'}
    (h : f.φ = g.φ) : f = g := by
  rcases f with ⟨f_φ, _, _, _, _, _⟩
  rcases g with ⟨g_φ, _, _, _, _, _⟩
  congr!

/-- Differential naturality refers to the page map induced by the ambient map. -/
@[reassoc]
theorem PreSSMorphism.pageMap_comm_d
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : PreSS C ι} (f : PreSSMorphism E E') (r : ℤ) (k : ι) :
    f.pageMap r k ≫ E'.d r k =
      E.d r k ≫ f.pageMap r (k + E.diffDeg r) ≫
        eqToHom (by rw [f.diffDeg_eq]) :=
  f.comm_d r k

/-- Differential naturality for the underlying canonical maps of spectral sequences. -/
@[reassoc]
theorem SpectralSequenceMorphism.pageMap_comm_d
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι} (f : SpectralSequenceMorphism E E')
    (r : ℤ) (k : ι) :
    f.pageMap r k ≫ E'.d r k =
      E.d r k ≫ f.pageMap r (k + E.diffDeg r) ≫
        eqToHom (by rw [f.diffDeg_eq]) :=
  f.comm_d r k

/-- Identity quotient maps commute with every page differential. -/
theorem PreSSMorphism.id_comm_d
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : PreSS C ι) (r : ℤ) (k : ι) :
    (SSDataMorphism.id E.ssData).pageMapAt (E := E) (E' := E) rfl r k ≫ E.d r k =
      E.d r k ≫ (SSDataMorphism.id E.ssData).pageMapAt
        (E := E) (E' := E) rfl r (k + E.diffDeg r) ≫ eqToHom rfl := by
  simp

/-- The composite of the canonical quotient maps commutes with differentials. -/
theorem PreSSMorphism.comp_comm_d
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' E'' : PreSS C ι} (f : PreSSMorphism E E') (g : PreSSMorphism E' E'')
    (r : ℤ) (k : ι) :
    (f.toSSDataMorphism.comp g.toSSDataMorphism).pageMapAt
        (f.r₀_eq.trans g.r₀_eq) r k ≫ E''.d r k =
      E.d r k ≫ (f.toSSDataMorphism.comp g.toSSDataMorphism).pageMapAt
        (f.r₀_eq.trans g.r₀_eq) r (k + E.diffDeg r) ≫
          eqToHom (by rw [f.diffDeg_eq, g.diffDeg_eq]) := by
  rcases E with ⟨r₀, D, δ, d⟩
  rcases E' with ⟨r₀', D', δ', d'⟩
  rcases E'' with ⟨r₀'', D'', δ'', d''⟩
  rcases f with ⟨f, hf, hδf, hdf⟩
  rcases g with ⟨g, hg, hδg, hdg⟩
  dsimp at hf hg hδf hδg
  subst r₀'
  subst r₀''
  subst δ'
  subst δ''
  simp only [SSDataMorphism.pageMapAt, eqToHom_refl, Category.comp_id,
    SSDataMorphism.pageMap_comp] at hdf hdg ⊢
  rw [Category.assoc, hdg, ← Category.assoc, hdf, Category.assoc]

/-! The following reusable lemmas support the page-homology construction. -/

namespace PageHomology

open CategoryTheory.Abelian in
/-- Composing an epimorphism on the left does not change the image subobject. -/
theorem imageSubobject_epi_comp
    {X₁ X₂ X₃ : C} (e : X₁ ⟶ X₂) [Epi e] (f : X₂ ⟶ X₃) :
    imageSubobject (e ≫ f) = imageSubobject f := by
  apply le_antisymm (imageSubobject_comp_le e f)
  have hle := imageSubobject_comp_le e f
  haveI : Epi (Subobject.ofLE _ _ hle) := imageSubobject_comp_le_epi_of_epi e f
  haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ hle))
    (by rw [IsIso.inv_comp_eq]; exact (Subobject.ofLE_arrow hle).symm)

/-- An image contained in a kernel gives a zero composite. -/
theorem comp_eq_zero_of_image_le_kernel
    {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (h : imageSubobject f ≤ kernelSubobject g) : f ≫ g = 0 := by
  rw [← imageSubobject_arrow_comp f, Category.assoc,
    show (imageSubobject f).arrow =
      Subobject.ofLE _ _ h ≫ (kernelSubobject g).arrow
      from (Subobject.ofLE_arrow h).symm,
    Category.assoc, kernelSubobject_arrow_comp, comp_zero, comp_zero]

/-- Factorization identity for the canonical map `Q/P ⟶ R/P`. -/
theorem factor_cokernelMap
    {V : C} (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR) =
      cokernel.π (Subobject.ofLE P Q hPQ) ≫
        Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR := by
  simp [Subobject.cokernelMap_ofLE, cokernel.π_desc]

/-- The canonical map `Q/P ⟶ R/P` is a monomorphism. -/
instance cokernelMap_ofLE_mono
    {V : C} (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    Mono (Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR) := by
  open CategoryTheory.Abelian.Pseudoelement in
  refine mono_of_zero_of_map_zero _ fun a ha => ?_
  obtain ⟨q, hq⟩ := pseudo_surjective_of_epi
    (cokernel.π (Subobject.ofLE P Q hPQ)) a
  rw [← hq] at ha ⊢
  have ha' : pseudoApply (cokernel.π (Subobject.ofLE P R hPR))
      (pseudoApply (Subobject.ofLE Q R hQR) q) = 0 := by
    have h1 := (Abelian.Pseudoelement.comp_apply
      (Subobject.ofLE Q R hQR) (cokernel.π (Subobject.ofLE P R hPR)) q).symm
    rw [h1, factor_cokernelMap P Q R hPQ hQR hPR,
      Abelian.Pseudoelement.comp_apply]
    exact ha
  have hexact : (ShortComplex.mk (Subobject.ofLE P R hPR)
      (cokernel.π (Subobject.ofLE P R hPR)) (cokernel.condition _)).Exact :=
    ShortComplex.cokernelSequence_exact (Subobject.ofLE P R hPR)
  obtain ⟨p, hp⟩ := pseudo_exact_of_exact hexact _ ha'
  have hp' : pseudoApply (Subobject.ofLE Q R hQR)
      (pseudoApply (Subobject.ofLE P Q hPQ) p) =
      pseudoApply (Subobject.ofLE Q R hQR) q := by
    rw [← Abelian.Pseudoelement.comp_apply, Subobject.ofLE_comp_ofLE]
    exact hp
  have hinj := pseudo_injective_of_mono (Subobject.ofLE Q R hQR) hp'
  rw [← hinj, ← Abelian.Pseudoelement.comp_apply, cokernel.condition, zero_apply]

end PageHomology

/-- Equal page classes of cycle representatives differ by a boundary in the ambient object. -/
theorem SSData.sub_factors_boundary_of_page_eq (D : SSData C)
    (n : WithTop ℕ) {T : C}
    (u v : T ⟶ Subobject.underlying.obj (D.Z n))
    (h : u ≫ D.pageπ n = v ≫ D.pageπ n) :
    Subobject.Factors (D.B n)
      (u ≫ (D.Z n).arrow - v ≫ (D.Z n).arrow) := by
  let i := Subobject.ofLE (D.B n) (D.Z n) (D.B_le_Z n)
  have hz : (u - v) ≫ cokernel.π i = 0 := by
    change (u - v) ≫ D.pageπ n = 0
    rw [Preadditive.sub_comp, h, sub_self]
  let b := Abelian.monoLift i (u - v) hz
  have hb : b ≫ (D.B n).arrow =
      u ≫ (D.Z n).arrow - v ≫ (D.Z n).arrow := by
    calc
      b ≫ (D.B n).arrow = b ≫ i ≫ (D.Z n).arrow := by
        rw [Subobject.ofLE_arrow]
      _ = (u - v) ≫ (D.Z n).arrow := by
        rw [← Category.assoc, Abelian.monoLift_comp]
      _ = u ≫ (D.Z n).arrow - v ≫ (D.Z n).arrow := by
        rw [Preadditive.sub_comp]
  rw [← hb]
  exact Subobject.factors_comp_arrow b

/-- A nonzero page boundary has a first finite stage at which it enters the boundary tower. -/
theorem SSData.first_boundary_page (D : SSData C) {T : C}
    (v : T ⟶ D.V) (n : ℕ)
    (hn : Subobject.Factors (D.B (↑n)) v)
    (hzero : ¬ Subobject.Factors (D.B (↑(0 : ℕ))) v) :
    ∃ m : ℕ, m < n ∧
      Subobject.Factors (D.B (↑(m + 1))) v ∧
      ¬ Subobject.Factors (D.B (↑m)) v := by
  classical
  let P : ℕ → Prop := fun j => Subobject.Factors (D.B (↑j)) v
  have hex : ∃ j : ℕ, P j := ⟨n, hn⟩
  let p := Nat.find hex
  have hp : P p := Nat.find_spec hex
  have hp0 : 0 < p := by
    by_contra h
    have h0 : p = 0 := by omega
    exact hzero (by simpa only [P, h0] using hp)
  have hple : p ≤ n := Nat.find_min' hex hn
  refine ⟨p - 1, by omega, ?_, ?_⟩
  · simpa only [show p - 1 + 1 = p by omega, P] using hp
  · exact Nat.find_min hex (by omega)

/-- The packaged infinity page vanishes when every finite page at the grading vanishes. -/
theorem EInftyData.eInfty_isZero_of_page_isZero
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (eData : EInftyData C ι) (k : ι)
    (h : ∀ r : ℤ, eData.ss.r₀ ≤ r → IsZero (eData.ss.Page r k)) :
    IsZero (eData.EInfty k) :=
  SpectralSequence.eInfty_isZero_of_page_isZero eData.ss k h

/-! Local stabilization, adapted from the generic proofs in
`KIPBase/Synthetic/AdamsVanishing.lean`; no synthetic model is used. -/

private theorem subobject_eq_of_quotient_epi
    {C : Type*} [Category C] [Abelian C] {V : C}
    (B P Q : Subobject V) (hBP : B ≤ P) (hPQ : P ≤ Q)
    [Epi (Subobject.ofLE P Q hPQ ≫
      cokernel.π (Subobject.ofLE B Q (hBP.trans hPQ)))] : P = Q := by
  let i := Subobject.ofLE P Q hPQ
  let b := Subobject.ofLE B Q (hBP.trans hPQ)
  have hi : Epi i := by
    apply (Preadditive.epi_iff_cancel_zero i).mpr
    intro R g hg
    have hbg : b ≫ g = 0 := by
      change Subobject.ofLE B Q _ ≫ g = 0
      rw [← Subobject.ofLE_comp_ofLE B P Q hBP hPQ, Category.assoc]
      change Subobject.ofLE B P hBP ≫ (i ≫ g) = 0
      rw [hg, comp_zero]
    let q := cokernel.desc b g hbg
    have hq : q = 0 := by
      apply zero_of_epi_comp (i ≫ cokernel.π b)
      rw [Category.assoc, cokernel.π_desc]
      exact hg
    calc
      g = cokernel.π b ≫ q := (cokernel.π_desc b g hbg).symm
      _ = 0 := by rw [hq, comp_zero]
  haveI : Epi (Subobject.ofLE P Q hPQ) := hi
  haveI : IsIso (Subobject.ofLE P Q hPQ) := isIso_of_mono_of_epi _
  exact le_antisymm hPQ
    (Subobject.le_of_comm (inv (Subobject.ofLE P Q hPQ))
      (by simp [Subobject.ofLE_arrow]))

/-- A zero outgoing differential preserves the cycle subobject. -/
theorem cycles_succ_of_zero
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (hr : E.r₀ ≤ r)
    (k : ι) (hd : E.d r k = 0) :
    (E.ssData k).Z ↑((r - E.r₀).toNat + 1) =
      (E.ssData k).Z ↑(r - E.r₀).toNat := by
  let n := (r - E.r₀).toNat
  let D := E.ssData k
  have hz := E.Z_succ r k hr
  rw [hd, kernelSubobject_zero] at hz
  let i := Subobject.ofLE (D.Z ↑(n + 1)) (D.Z ↑n)
    (D.Z_anti (by exact_mod_cast Nat.le_succ n))
  let p := i ≫ D.pageπ ↑n
  have hp : imageSubobject p = ⊤ := hz.symm
  haveI : IsIso (imageSubobject p).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).mpr hp
  haveI : Epi p := by
    rw [← imageSubobject_arrow_comp p]
    infer_instance
  let hBP : D.B ↑n ≤ D.Z ↑(n + 1) :=
    (D.B_mono (by exact_mod_cast Nat.le_succ n)).trans (D.B_le_Z _)
  let hPQ : D.Z ↑(n + 1) ≤ D.Z ↑n :=
    D.Z_anti (by exact_mod_cast Nat.le_succ n)
  have hEpi : Epi (Subobject.ofLE (D.Z ↑(n + 1)) (D.Z ↑n) hPQ ≫
      cokernel.π (Subobject.ofLE (D.B ↑n) (D.Z ↑n) (hBP.trans hPQ))) := by
    change Epi p
    infer_instance
  exact @subobject_eq_of_quotient_epi C _ _ D.V
    (D.B ↑n) (D.Z ↑(n + 1)) (D.Z ↑n) hBP hPQ hEpi

/-- A zero differential leaves its target boundary subobject unchanged. -/
theorem boundaries_succ_of_zero
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (hr : E.r₀ ≤ r)
    (k : ι) (hd : E.d r k = 0) :
    (E.ssData (k + E.diffDeg r)).B ↑((r - E.r₀).toNat + 1) =
      (E.ssData (k + E.diffDeg r)).B ↑(r - E.r₀).toNat := by
  let n := (r - E.r₀).toNat
  let D := E.ssData (k + E.diffDeg r)
  have hb := E.B_succ r k hr
  rw [hd, imageSubobject_zero] at hb
  let b := Subobject.ofLE (D.B ↑n) (D.Z ↑n) (D.B_le_Z _)
  let j := Subobject.ofLE (D.B ↑(n + 1)) (D.Z ↑n)
    ((D.B_le_Z _).trans (D.Z_anti (by exact_mod_cast Nat.le_succ n)))
  have hj : j ≫ cokernel.π b = 0 := by
    have hp : imageSubobject (j ≫ cokernel.π b) = ⊥ := hb.symm
    have ha : (imageSubobject (j ≫ cokernel.π b)).arrow = 0 := by
      rw [hp]
      exact Subobject.bot_arrow
    rw [← imageSubobject_arrow_comp (j ≫ cokernel.π b), ha, comp_zero]
  apply le_antisymm _ (D.B_mono (by exact_mod_cast Nat.le_succ n))
  apply Subobject.le_of_comm (Abelian.monoLift b j hj)
  have hcomp := congrArg (fun f => f ≫ (D.Z ↑n).arrow)
    (Abelian.monoLift_comp b j hj)
  simpa only [Category.assoc, b, j, Subobject.ofLE_arrow] using hcomp


/-- Vanishing of all later outgoing differentials stabilizes the cycles
at this grading, including the actual intersection at infinity. -/
theorem cycles_top_eq_of_d_eq_zero
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (N : ℤ) (hN : E.r₀ ≤ N) (k : ι)
    (hd : ∀ r : ℤ, N ≤ r → E.d r k = 0) :
    (E.ssData k).Z ⊤ = (E.ssData k).Z ↑(N - E.r₀).toNat := by
  let n₀ := (N - E.r₀).toNat
  let D := E.ssData k
  have hn₀ : (n₀ : ℤ) = N - E.r₀ := Int.toNat_of_nonneg (by omega)
  have htail : ∀ m : ℕ, D.Z (↑(n₀ + m) : WithTop ℕ) = D.Z ↑n₀ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hz := cycles_succ_of_zero E (E.r₀ + (n₀ + m : ℕ)) (by omega) k
        (hd _ (by rw [Nat.cast_add, hn₀]; omega))
      simp only [add_sub_cancel_left, Int.toNat_natCast] at hz
      exact hz.trans ih
  apply le_antisymm (D.Z_anti le_top)
  apply D.Z_top_greatest
  intro n
  by_cases hn : n₀ ≤ n
  · have h := (htail (n - n₀)).ge
    simpa only [Nat.add_sub_of_le hn] using h
  · exact D.Z_anti (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hn))

/-- Vanishing of all later incoming differentials stabilizes the boundaries
at this grading, including the actual union at infinity. -/
theorem boundaries_top_eq_of_d_eq_zero
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (N : ℤ) (hN : E.r₀ ≤ N) (k : ι)
    (hd : ∀ r : ℤ, N ≤ r → E.d r (k - E.diffDeg r) = 0) :
    (E.ssData k).B ⊤ = (E.ssData k).B ↑(N - E.r₀).toNat := by
  let n₀ := (N - E.r₀).toNat
  let D := E.ssData k
  have hn₀ : (n₀ : ℤ) = N - E.r₀ := Int.toNat_of_nonneg (by omega)
  have htail : ∀ m : ℕ, D.B (↑(n₀ + m) : WithTop ℕ) = D.B ↑n₀ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hb := boundaries_succ_of_zero E (E.r₀ + (n₀ + m : ℕ)) (by omega)
        (k - E.diffDeg (E.r₀ + (n₀ + m : ℕ)))
        (hd _ (by rw [Nat.cast_add, hn₀]; omega))
      simp only [add_sub_cancel_left, Int.toNat_natCast] at hb
      have hb' : D.B ↑(n₀ + m + 1) = D.B ↑(n₀ + m) :=
        (congrArg (fun j => (E.ssData j).B ↑(n₀ + m + 1) =
          (E.ssData j).B ↑(n₀ + m))
          (sub_add_cancel k (E.diffDeg (E.r₀ + (n₀ + m : ℕ))))).mp hb
      exact hb'.trans ih
  apply le_antisymm _ (D.B_mono le_top)
  apply D.B_top_least
  intro n
  by_cases hn : n₀ ≤ n
  · have h := (htail (n - n₀)).le
    simpa only [Nat.add_sub_of_le hn] using h
  · exact D.B_mono (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hn))

end KIP126.SpectralSequence
