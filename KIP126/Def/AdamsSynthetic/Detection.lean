module

public import KIP126.Def.AdamsSynthetic.Tower
public import KIP126.Def.SpectralSequence.Convergence.Proofs
public import KIP126.Def.SpectralSequence.Permanence.Proofs

@[expose] section

/-! Canonical convergence and detection for the given towers. Filtrations
are ranges of the actual tower projections, not independently chosen data.
Separation is a named proof obligation, never a field silently imposed here. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Core.SpectralSequence KIP126.Synthetic.SpectralSequence
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false

section Classical
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {A : KIP126.Classical.Adams.ClassicalAdamsFamily C}

/-- Canonical identification on lifts in the ONE supplied abstract tower.
The cofiber image and the actual homotopy class use the same lift. -/
public def ClassicalCanonicalIdentification (P : ClassicalTowerPresentation unit A) (X : C)
    (e : ∀ p : ℤ × ℤ, ((A.obj X).ssData p).eInfty ≅
      (P.tower X).filtration.associatedGraded p.1 (p.2-p.1)) : Prop :=
  ∀ (p : ℤ × ℤ) (a : HomotopyGroup (p.2-p.1) ((P.tower X).stageAt p.1))
    (z : (Subobject.underlying.obj (((A.obj X).ssData p).Z ⊤) : ModuleCat ℤ)),
    (P.sequence X).infiniteRepresentativeE1 p z = (P.tower X).layerMap p a →
    ∀ b : (Subobject.underlying.obj ((P.tower X).filtration.F p.1 (p.2-p.1)) : ModuleCat ℤ),
      ((P.tower X).filtration.F p.1 (p.2-p.1)).arrow b =
        a ≫ (P.tower X).projection p.1 →
      (e p).hom (((A.obj X).ssData p).pageπ ⊤ z) =
        (P.tower X).filtration.toAssociatedGraded p.1 (p.2-p.1) b

/-- Convergence is requested only for this object. It does not construct a
convergent instance or assert separation of its filtration. -/
public structure ClassicalTowerConvergence (P : ClassicalTowerPresentation unit A) (X : C) where
  identification : ∀ p : ℤ × ℤ, ((A.obj X).ssData p).eInfty ≅
    (P.tower X).filtration.associatedGraded p.1 (p.2-p.1)
  canonical : ClassicalCanonicalIdentification P X identification

public def ClassicalTowerConvergence.toConvergence
    {P : ClassicalTowerPresentation unit A} {X : C} (c : ClassicalTowerConvergence P X) :
    Convergence (A.obj X) (AbstractAdamsTower.homotopy X) (P.tower X).filtration where
  reindex p := (p.1,p.2-p.1)
  reindex_bijective := by
    constructor
    · rintro ⟨s,t⟩ ⟨s',t'⟩ h
      have hs := congrArg Prod.fst h
      have ht := congrArg Prod.snd h
      dsimp at hs ht
      ext <;> omega
    · rintro ⟨s,m⟩
      exact ⟨(s,m+s),by ext <;> simp⟩
  iso := c.identification

public def ClassicalDetects {P : ClassicalTowerPresentation unit A} {X : C}
    (c : ClassicalTowerConvergence P X) (p : ℤ × ℤ) (x : (A.obj X).Page 2 p)
    (a : HomotopyGroup (p.2-p.1) X) : Prop :=
  ∃ z : (Subobject.underlying.obj (((A.obj X).ssData p).Z ⊤) : ModuleCat ℤ),
    (Subobject.ofLE _ _ (((A.obj X).ssData p).Z_anti le_top) ≫
      ((A.obj X).ssData p).pageπ (↑(2-(A.obj X).r₀).toNat : WithTop ℕ)) z = x ∧
    ∃ b : (Subobject.underlying.obj ((P.tower X).filtration.F p.1 (p.2-p.1)) : ModuleCat ℤ),
      ((P.tower X).filtration.F p.1 (p.2-p.1)).arrow b = a ∧
      (c.identification p).hom (((A.obj X).ssData p).pageπ ⊤ z) =
        (P.tower X).filtration.toAssociatedGraded p.1 (p.2-p.1) b
end Classical

section Synthetic
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
  {F : SyntheticAdamsFamily Syn}

public def syntheticHomotopyMap {X Y : Syn} (f : X ⟶ Y) (p : ℤ × ℤ) :
    syntheticHomotopy X p ⟶ syntheticHomotopy Y p :=
  ModuleCat.ofHom ((Preadditive.rightComp (Smn p.1 p.2) f).toIntLinearMap)

/-- The fixed weight desuspension is dictated by the given grading. -/
public def weightSourceIso (m w : ℤ) :
    (SyntheticCategory.biShift (0,-w)).obj (Smn m w (Syn := Syn)) ≅ Sphere (C := Syn) m :=
  (SyntheticCategory.biShift_comp (m,w) (0,-w)).app S_0_0 ≪≫
    eqToIso (by simp) ≪≫
    (SyntheticCategory.biShift_compat (Syn := Syn) m).app S_0_0

public def weightHomotopyMap (m w : ℤ) (X : Syn) (a : BiHom m w X) :
    HomotopyGroup m ((SyntheticCategory.biShift (0,-w)).obj X) :=
  (weightSourceIso m w).inv ≫ (SyntheticCategory.biShift (0,-w)).map a

namespace SyntheticTowerPresentation
public def filtrationSubmodule (P : SyntheticTowerPresentation unit F) (X : Syn)
    (s : ℤ) (p : ℤ × ℤ) : Submodule ℤ (BiHom p.1 p.2 X) :=
  LinearMap.range ((Preadditive.rightComp (Smn p.1 p.2)
    ((P.tower X).projection s)).toIntLinearMap)

public theorem filtrationSubmodule_antitone (P : SyntheticTowerPresentation unit F)
    (X : Syn) (p : ℤ × ℤ) : Antitone (fun s => P.filtrationSubmodule X s p) := by
  intro s t h a ha
  obtain ⟨b, rfl⟩ := ha
  refine ⟨b ≫ (P.tower X).mapAt h, ?_⟩
  change (b ≫ (P.tower X).mapAt h) ≫ (P.tower X).projection s = b ≫ (P.tower X).projection t
  rw [Category.assoc, (P.tower X).projection_compat h]

public def filtration (P : SyntheticTowerPresentation unit F) (X : Syn) :
    Filtration (syntheticHomotopy X) where
  F s p := (ModuleCat.subobjectModule _).symm (P.filtrationSubmodule X s p)
  mono s p := (ModuleCat.subobjectModule _).symm.monotone
    (P.filtrationSubmodule_antitone X p (by omega : s ≤ s+1))
end SyntheticTowerPresentation

/-- Both clauses are necessary: agreement of the actual weight-shifted tower
filtrations, and the canonical cofiber/projection equation on the same lift. -/
public def SyntheticCanonicalIdentification (P : SyntheticTowerPresentation unit F) (X : Syn)
    (e : ∀ i : Tridegree, ((F.obj X).sequence.ssData i).eInfty ≅
      (P.filtration X).associatedGraded i.1 (i.2.1-i.1,i.2.2)) : Prop :=
  (∀ (s m w : ℤ) (a : BiHom m w X),
    a ∈ P.filtrationSubmodule X s (m,w) ↔
      weightHomotopyMap m w X a ∈
        (P.tower ((SyntheticCategory.biShift (0,-w)).obj X)).filtrationSubmodule s m) ∧
  ∀ (i : Tridegree)
    (a : HomotopyGroup (i.2.1-i.1)
      ((P.tower ((SyntheticCategory.biShift (0,-i.2.2)).obj X)).stageAt i.1))
    (z : (Subobject.underlying.obj (((F.obj X).sequence.ssData i).Z ⊤) : ModuleCat ℤ)),
    (P.sequence X i.2.2).infiniteRepresentativeE1 (i.1,i.2.1) z =
      (P.tower ((SyntheticCategory.biShift (0,-i.2.2)).obj X)).layerMap (i.1,i.2.1) a →
    ∀ b : (Subobject.underlying.obj ((P.filtration X).F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ),
      weightHomotopyMap (i.2.1-i.1) i.2.2 X
        (((P.filtration X).F i.1 (i.2.1-i.1,i.2.2)).arrow b) =
        a ≫ (P.tower ((SyntheticCategory.biShift (0,-i.2.2)).obj X)).projection i.1 →
      (e i).hom (((F.obj X).sequence.ssData i).pageπ ⊤ z) =
        (P.filtration X).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) b

public structure SyntheticTowerConvergence (P : SyntheticTowerPresentation unit F) (X : Syn) where
  identification : ∀ i : Tridegree, ((F.obj X).sequence.ssData i).eInfty ≅
    (P.filtration X).associatedGraded i.1 (i.2.1-i.1,i.2.2)
  canonical : SyntheticCanonicalIdentification P X identification

namespace SyntheticTowerConvergence
public abbrev filtration {P : SyntheticTowerPresentation unit F} {X : Syn}
    (_c : SyntheticTowerConvergence P X) := P.filtration X

public def toConvergence {P : SyntheticTowerPresentation unit F} {X : Syn}
    (c : SyntheticTowerConvergence P X) :
    Convergence (F.obj X).sequence (syntheticHomotopy X) (P.filtration X) where
  reindex i := (i.1,i.2.1-i.1,i.2.2)
  reindex_bijective := by
    constructor
    · rintro ⟨s,t,w⟩ ⟨s',t',w'⟩ h
      change (s,t-s,w) = (s',t'-s',w') at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨hs,ht,hw⟩ := h
      exact Prod.ext hs (Prod.ext (by dsimp; omega) hw)
    · rintro ⟨s,m,w⟩
      exact ⟨(s,m+s,w),by ext <;> simp⟩
  iso := c.identification
end SyntheticTowerConvergence

/-- A common infinite-cycle representative, including the zero case. -/
public def HasInfinityRepresentative (A : SyntheticAdamsSS.{v}) (r : ℤ) (i : Tridegree)
    (x : A.Page r i) (e : (A.sequence.ssData i).eInfty) : Prop :=
  2 ≤ r ∧ ∃ z : (Subobject.underlying.obj ((A.sequence.ssData i).Z ⊤) : ModuleCat ℤ),
    (Subobject.ofLE _ _ ((A.sequence.ssData i).Z_anti le_top) ≫
      (A.sequence.ssData i).pageπ (↑(r-A.sequence.r₀).toNat : WithTop ℕ)) z = x ∧
      (A.sequence.ssData i).pageπ ⊤ z = e

public def Detects {P : SyntheticTowerPresentation unit F} {X : Syn}
    (c : SyntheticTowerConvergence P X) (i : Tridegree) (x : (F.obj X).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 X) : Prop :=
  ∃ e : ((F.obj X).sequence.ssData i).eInfty,
    HasInfinityRepresentative (F.obj X) 2 i x e ∧
    ∃ b : (Subobject.underlying.obj ((P.filtration X).F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ),
      ((P.filtration X).F i.1 (i.2.1-i.1,i.2.2)).arrow b = a ∧
      (c.identification i).hom e =
        (P.filtration X).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) b

public def DetectsNonzero {P : SyntheticTowerPresentation unit F} {X : Syn}
    (c : SyntheticTowerConvergence P X) (i : Tridegree) (x : (F.obj X).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 X) : Prop :=
  Detects c i x a ∧ ∃ e, HasInfinityRepresentative (F.obj X) 2 i x e ∧ e ≠ 0

public def FiltrationAtLeast (P : SyntheticTowerPresentation unit F) {X : Syn}
    (s : ℤ) {m w : ℤ} (a : BiHom m w X) : Prop :=
  a ∈ P.filtrationSubmodule X s (m,w)

/-- A retained producer proof obligation. No convergence record assumes it. -/
public def HomotopySeparated (P : SyntheticTowerPresentation unit F) (X : Syn) : Prop :=
  ∀ (m w : ℤ) (a : BiHom m w X), (∀ s : ℕ, FiltrationAtLeast P s a) → a = 0

public theorem HasInfinityRepresentative.zero (A : SyntheticAdamsSS.{v})
    (r : ℤ) (hr : 2 ≤ r) (i : Tridegree) :
    HasInfinityRepresentative A r i 0 0 :=
  ⟨hr, 0, map_zero _, map_zero _⟩

public theorem HasInfinityRepresentative.unique {A : SyntheticAdamsSS.{v}}
    {r : ℤ} {i : Tridegree} {x : A.Page r i}
    {e e' : (A.sequence.ssData i).eInfty}
    (h : HasInfinityRepresentative A r i x e)
    (h' : HasInfinityRepresentative A r i x e') : e = e' := by
  obtain ⟨_, z, hz, he⟩ := h
  obtain ⟨_, z', hz', he'⟩ := h'
  exact he.symm.trans
    (((A.sequence.ssData i).infinity_projection_eq_of_page_projection_eq
      (↑(r - A.sequence.r₀).toNat) z z' (hz.trans hz'.symm)).trans he')

variable {P : SyntheticTowerPresentation unit F} {X : Syn}
  (c : SyntheticTowerConvergence P X) (i : Tridegree)

public theorem detects_add {x y : (F.obj X).E₂ i}
    {a b : BiHom (i.2.1-i.1) i.2.2 X}
    (ha : Detects c i x a) (hb : Detects c i y b) :
    Detects c i (x+y) (a+b) := by
  obtain ⟨e, ⟨hr, z, hz, he⟩, a', ha', hga⟩ := ha
  obtain ⟨e', ⟨_, z', hz', he'⟩, b', hb', hgb⟩ := hb
  refine ⟨e + e', ⟨hr, z + z', ?_, ?_⟩, a' + b', ?_, ?_⟩
  · rw [map_add, hz, hz']
  · rw [map_add, he, he']
  · rw [map_add, ha', hb']
  · rw [map_add, map_add, hga, hgb]

private theorem filtrationAtLeast_of_graded_eq_zero (s m w : ℤ)
    (a : (Subobject.underlying.obj ((P.filtration X).F s (m,w)) : ModuleCat ℤ))
    (ha : (P.filtration X).toAssociatedGraded s (m,w) a = 0) :
    FiltrationAtLeast P (s+1) (((P.filtration X).F s (m,w)).arrow a) := by
  have hmem := ((P.filtration X).toAssociatedGraded_eq_zero_iff s (m,w) a).mp ha
  simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
    FiltrationAtLeast] using hmem

/-- A zero infinity class raises actual filtration; it does not imply the
homotopy class itself vanishes. -/
public theorem detects_zero_infinity_filtration
    {x : (F.obj X).E₂ i} {a : BiHom (i.2.1-i.1) i.2.2 X}
    (ha : Detects c i x a)
    (hx : HasInfinityRepresentative (F.obj X) 2 i x 0) :
    FiltrationAtLeast P (i.1+1) a := by
  obtain ⟨e, he, a', ha', hgr⟩ := ha
  have he0 := he.unique hx
  rw [he0, map_zero] at hgr
  rw [← ha']
  exact filtrationAtLeast_of_graded_eq_zero i.1 (i.2.1-i.1) i.2.2 a' hgr.symm

public theorem detects_zero_filtration
    {a : BiHom (i.2.1-i.1) i.2.2 X} (ha : Detects c i 0 a) :
    FiltrationAtLeast P (i.1+1) a :=
  detects_zero_infinity_filtration c i ha
    (HasInfinityRepresentative.zero (F.obj X) 2 (by omega) i)

/-- Equal leading labels determine a coset of the next filtration step. -/
public theorem detects_sub_filtration {x : (F.obj X).E₂ i}
    {a b : BiHom (i.2.1-i.1) i.2.2 X}
    (ha : Detects c i x a) (hb : Detects c i x b) :
    FiltrationAtLeast P (i.1+1) (a-b) := by
  obtain ⟨e, he, a', ha', hga⟩ := ha
  obtain ⟨e', he', b', hb', hgb⟩ := hb
  have heq := he.unique he'
  have hzero : (P.filtration X).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) (a'-b') = 0 := by
    rw [map_sub, ← hga, ← hgb, heq, sub_self]
  have h := filtrationAtLeast_of_graded_eq_zero i.1 (i.2.1-i.1) i.2.2 (a'-b') hzero
  simpa only [map_sub, ha', hb'] using h
end Synthetic
end
end KIP126.AdamsSynthetic
