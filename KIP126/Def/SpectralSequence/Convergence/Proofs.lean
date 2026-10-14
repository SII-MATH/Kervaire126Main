module

public import KIP126.Def.SpectralSequence.Convergence.Predicates

import all KIP126.Def.SpectralSequence.Convergence.Predicates
import all KIP126.Def.Algebra.Filtration.Predicates
import all KIP126.Def.SpectralSequence.ModuleSubobject.Proofs
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] section

/-!
# Proofs for convergence of nested-subobject spectral sequences
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

omit [Abelian C] in
/-- A filtration decreases between any two ordered integer levels. -/
public theorem Filtration.le_of_le {ω : Type w} {A : ω → C}
    (F : Filtration A) {s t : ℤ} (h : s ≤ t) (k : ω) : F.F t k ≤ F.F s k := by
  induction t, h using Int.leInduction with
  | base => exact le_rfl
  | succ t _ ih => exact (F.mono t k).trans ih

/-- A filtration representative has zero graded class precisely when its
actual ambient element belongs to the next filtration level. -/
public theorem Filtration.toAssociatedGraded_eq_zero_iff
    {R : Type u} [Ring R] {ω : Type w} {A : ω → ModuleCat.{v} R}
    (F : Filtration A) (s : ℤ) (k : ω)
    (x : (Subobject.underlying.obj (F.F s k) : ModuleCat R)) :
    F.toAssociatedGraded s k x = 0 ↔
      (F.F s k).arrow x ∈ (ModuleCat.subobjectModule (A k)) (F.F (s + 1) k) :=
  subobject_cokernel_π_eq_zero_iff (F.F (s + 1) k) (F.F s k) (F.mono s k) x

@[simp]
public theorem Filtration.transportGraded_self
    {ω' : Type w} {A : ω' → C} (F : Filtration A)
    {r : ℤ × ω'} (h : r = r) :
    F.transportGraded h = 𝟙 (F.associatedGraded r.1 r.2) :=
  rfl

public theorem Filtration.transportGraded_trans
    {ω' : Type w} {A : ω' → C} (F : Filtration A)
    {r₁ r₂ r₃ : ℤ × ω'} (h₁₂ : r₁ = r₂) (h₂₃ : r₂ = r₃) :
    F.transportGraded h₁₂ ≫ F.transportGraded h₂₃ =
      F.transportGraded (h₁₂.trans h₂₃) := by
  subst h₁₂
  subst h₂₃
  simp only [Filtration.transportGraded_self, Category.id_comp]

omit [Abelian C] in
@[simp]
theorem Filtration.toAlgebra_toSpectralSequence
    {ω : Type w} {A : ω → C} (F : Filtration A) :
    F.toAlgebra.toSpectralSequence = F := by
  cases F
  rfl

omit [Abelian C] in
@[simp]
theorem _root_.KIP126.Core.Algebra.Filtration.toSpectralSequence_toAlgebra
    {ω : Type w} {A : ω → C} (F : KIP126.Core.Algebra.Filtration A) :
    F.toSpectralSequence.toAlgebra = F := by
  cases F
  rfl

/-- Detection by zero is equivalent to lifting one filtration level deeper. -/
public theorem detect_zero
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F)
    {T : C} {k : ω}
    (x : T ⟶ Subobject.underlying.obj
      (F.F (conv.reindex k).1 (conv.reindex k).2)) :
    Detects conv (0 : T ⟶ (E.ssData k).eInfty) x ↔
      ∃ (x' : T ⟶ Subobject.underlying.obj
        (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)),
        x' ≫ Subobject.ofLE
          (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)
          (F.F (conv.reindex k).1 (conv.reindex k).2)
          (F.mono (conv.reindex k).1 (conv.reindex k).2) = x := by
  simp only [Detects, Filtration.toAssociatedGraded, Filtration.associatedGraded,
    Limits.zero_comp]
  constructor
  · intro h
    exact ⟨Abelian.monoLift _ x (by rw [h]), Abelian.monoLift_comp _ x (by rw [h])⟩
  · rintro ⟨x', hx'⟩
    rw [← hx', Category.assoc, cokernel.condition, Limits.comp_zero]

/-- Two representatives detected by the same class differ by a deeper-filtration lift. -/
public theorem detect_difference
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F)
    {T : C} {k : ω}
    (y : T ⟶ (E.ssData k).eInfty)
    (x x' : T ⟶ Subobject.underlying.obj
      (F.F (conv.reindex k).1 (conv.reindex k).2)) :
    (Detects conv y x ∧ Detects conv y x') ↔
      (Detects conv y x ∧
        ∃ (z : T ⟶ Subobject.underlying.obj
          (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)),
          z ≫ Subobject.ofLE
            (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)
            (F.F (conv.reindex k).1 (conv.reindex k).2)
            (F.mono (conv.reindex k).1 (conv.reindex k).2) = x - x') := by
  constructor
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have key : (x - x') ≫
        F.toAssociatedGraded (conv.reindex k).1 (conv.reindex k).2 = 0 := by
      rw [Detects] at hx hx'
      rw [Preadditive.sub_comp, sub_eq_zero]
      exact hx.symm.trans hx'
    simp only [Filtration.toAssociatedGraded] at key
    exact ⟨Abelian.monoLift _ (x - x') key,
      Abelian.monoLift_comp _ (x - x') key⟩
  · rintro ⟨hx, z, hz⟩
    refine ⟨hx, ?_⟩
    change y ≫ (conv.iso k).hom =
      x' ≫ F.toAssociatedGraded (conv.reindex k).1 (conv.reindex k).2
    have hd : Detects conv y x := hx
    rw [Detects] at hd
    have hx'eq : x' = x - z ≫ Subobject.ofLE
        (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)
        (F.F (conv.reindex k).1 (conv.reindex k).2)
        (F.mono (conv.reindex k).1 (conv.reindex k).2) := by
      rw [hz, sub_sub_cancel]
    have hz0 : (z ≫ Subobject.ofLE
        (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)
        (F.F (conv.reindex k).1 (conv.reindex k).2)
        (F.mono (conv.reindex k).1 (conv.reindex k).2)) ≫
        F.toAssociatedGraded (conv.reindex k).1 (conv.reindex k).2 = 0 := by
      dsimp only [Filtration.toAssociatedGraded, Filtration.associatedGraded]
      rw [Category.assoc, cokernel.condition, comp_zero]
      rfl
    rw [hx'eq, Preadditive.sub_comp, hd, hz0, sub_zero]

/-- A two-sided bounded filtration is bounded below. -/
public def Filtration.IsBounded.toIsBoundedBelow
    {ω : Type w} {A : ω → C} {F : Filtration A}
    (h : F.IsBounded) : F.IsBoundedBelow where
  lo := h.lo
  boundedBelow := h.boundedBelow

/-- A two-sided bounded filtration is bounded above. -/
public def Filtration.IsBounded.toIsBoundedAbove
    {ω : Type w} {A : ω → C} {F : Filtration A}
    (h : F.IsBounded) : F.IsBoundedAbove where
  hi := h.hi
  boundedAbove := h.boundedAbove

omit [Abelian C] in
/-- A bounded-below filtration is exhaustive. -/
public theorem Filtration.IsBoundedBelow.toIsExhaustive
    {ω : Type w} {A : ω → C} {F : Filtration A}
    (h : F.IsBoundedBelow) : F.IsExhaustive := by
  intro k
  exact ⟨h.lo k, h.boundedBelow k (h.lo k) le_rfl⟩

/-- Eventual vanishing implies separatedness. The stronger premise uses
the existing algebra-filtration predicate on the same filtration. -/
theorem Filtration.isHausdorff_of_isEventuallyZero
    {ω : Type w} {A : ω → C} {F : Filtration A}
    (h : F.toAlgebra.IsEventuallyZero) : F.IsHausdorff := by
  intro k S hS
  obtain ⟨s, hs⟩ := h k
  change F.F s k = ⊥ at hs
  exact le_antisymm (by simpa only [hs] using hS s) bot_le

/-- A bounded-above filtration is Hausdorff. -/
public theorem Filtration.IsBoundedAbove.toIsHausdorff
    {ω : Type w} {A : ω → C} {F : Filtration A}
    (h : F.IsBoundedAbove) : F.IsHausdorff := by
  apply Filtration.isHausdorff_of_isEventuallyZero
  intro k
  exact ⟨h.hi k, h.boundedAbove k (h.hi k) le_rfl⟩

/-- Extensionality for convergence morphisms. -/
@[ext]
public theorem ConvergenceMorphism.ext
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {f g : ConvergenceMorphism conv₁ conv₂}
    (he : f.eMap = g.eMap) (ha : f.aMap = g.aMap) : f = g := by
  cases f with | mk f_data f_re f_iso => ?_
  cases f_data with | mk f_e f_a f_fil => ?_
  cases g with | mk g_data g_re g_iso => ?_
  cases g_data with | mk g_e g_a g_fil => ?_
  subst he
  subst ha
  rfl

omit [Abelian C] in
/-- Filtration compatibility witnesses for an identity map. -/
theorem Filtration.fcId
    {ω' : Type w} {A : ω' → C} (F : Filtration A)
    (s : ℤ) (k' : ω') :
    ∃ (φ : Subobject.underlying.obj (F.F s k') ⟶
      Subobject.underlying.obj (F.F s k')),
      φ ≫ (F.F s k').arrow = (F.F s k').arrow ≫ 𝟙 _ :=
  ⟨𝟙 _, by simp⟩

/-- Filtration compatibility witnesses for a composite convergence morphism. -/
theorem ConvergenceMorphismData.fcComp
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (f : ConvergenceMorphism conv₁ conv₂) (g : ConvergenceMorphism conv₂ conv₃)
    (s : ℤ) (k' : ω') :
    ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
      Subobject.underlying.obj (F₃.F s k')),
      φ ≫ (F₃.F s k').arrow =
        (F₁.F s k').arrow ≫ (f.aMap k' ≫ g.aMap k') :=
  ⟨(f.filtration_compat s k').choose ≫ (g.filtration_compat s k').choose, by
    rw [Category.assoc, (g.filtration_compat s k').choose_spec,
      ← Category.assoc, (f.filtration_compat s k').choose_spec, Category.assoc]⟩

/-- Congruence of explicitly lifted associated-graded maps. -/
theorem Filtration.inducedGradedMapOfMap_congr
    {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {φ ψ : ∀ (s : ℤ) (k' : ω'), Subobject.underlying.obj (F₁.F s k') ⟶
      Subobject.underlying.obj (F₂.F s k')}
    (hwφ : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫ φ s k' =
        φ (s + 1) k' ≫
          Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (hwψ : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫ ψ s k' =
        ψ (s + 1) k' ≫
          Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (h : φ = ψ) (s : ℤ) (k' : ω') :
    Filtration.inducedGradedMapOfMap φ hwφ s k' =
      Filtration.inducedGradedMapOfMap ψ hwψ s k' := by
  subst h
  rfl

/-- Explicit identity lifts induce the identity on associated graded pieces. -/
theorem Filtration.inducedGradedMapOfMap_id
    {ω' : Type w} {A : ω' → C} (F : Filtration A) (s : ℤ) (k' : ω')
    (hw : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F.F (s + 1) k') (F.F s k') (F.mono s k') ≫ 𝟙 _ =
        (𝟙 _ : Subobject.underlying.obj (F.F (s + 1) k') ⟶ _) ≫
          Subobject.ofLE (F.F (s + 1) k') (F.F s k') (F.mono s k')) :
    Filtration.inducedGradedMapOfMap (fun _ _ => 𝟙 _) hw s k' =
      𝟙 (F.associatedGraded s k') := by
  haveI := Classical.decEq ω'
  apply (cancel_epi (cokernel.π _)).mp
  dsimp only [Filtration.associatedGraded]
  simp only [Filtration.inducedGradedMapOfMap, cokernel.map,
    Category.id_comp, Category.comp_id, cokernel.π_desc]

/-- Explicit composite lifts induce the composite associated-graded map. -/
theorem Filtration.inducedGradedMapOfMap_comp
    {ω' : Type w} {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    (φ : ∀ (s : ℤ) (k' : ω'), Subobject.underlying.obj (F₁.F s k') ⟶
      Subobject.underlying.obj (F₂.F s k'))
    (ψ : ∀ (s : ℤ) (k' : ω'), Subobject.underlying.obj (F₂.F s k') ⟶
      Subobject.underlying.obj (F₃.F s k'))
    (hwφ : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫ φ s k' =
        φ (s + 1) k' ≫
          Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (hwψ : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k') ≫ ψ s k' =
        ψ (s + 1) k' ≫
          Subobject.ofLE (F₃.F (s + 1) k') (F₃.F s k') (F₃.mono s k'))
    (hwφψ : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫
          (φ s k' ≫ ψ s k') =
        (φ (s + 1) k' ≫ ψ (s + 1) k') ≫
          Subobject.ofLE (F₃.F (s + 1) k') (F₃.F s k') (F₃.mono s k'))
    (s : ℤ) (k' : ω') :
    Filtration.inducedGradedMapOfMap (fun s k' => φ s k' ≫ ψ s k') hwφψ s k' =
      Filtration.inducedGradedMapOfMap φ hwφ s k' ≫
        Filtration.inducedGradedMapOfMap ψ hwψ s k' := by
  haveI := Classical.decEq ω'
  apply (cancel_epi (cokernel.π _)).mp
  dsimp only [Filtration.associatedGraded]
  simp only [Filtration.inducedGradedMapOfMap, cokernel.map,
    Category.assoc, cokernel.π_desc_assoc, cokernel.π_desc]

omit [Abelian C] in
/-- Chosen filtration restrictions commute with level inclusions. -/
theorem Filtration.choose_compat
    {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
        Subobject.underlying.obj (F₂.F s k')),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (s : ℤ) (k' : ω') :
    Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫
        (hcompat s k').choose =
      (hcompat (s + 1) k').choose ≫
        Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k') := by
  apply (cancel_mono ((F₂.F s k').arrow)).mp
  simp only [Category.assoc, Subobject.ofLE_arrow]
  rw [(hcompat s k').choose_spec, (hcompat (s + 1) k').choose_spec,
    ← Category.assoc, Subobject.ofLE_arrow]

/-- The chosen-witness and explicit-witness associated-graded maps agree. -/
theorem Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap
    {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
        Subobject.underlying.obj (F₂.F s k')),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (s : ℤ) (k' : ω') :
    Filtration.inducedAssocGradedMap aMap hcompat s k' =
      Filtration.inducedGradedMapOfMap (fun s k' => (hcompat s k').choose)
        (Filtration.choose_compat aMap hcompat) s k' :=
  rfl

/-- The chosen identity restrictions induce the identity associated-graded map. -/
theorem Filtration.inducedAssocGradedMap_id
    {ω' : Type w} {A : ω' → C} (F : Filtration A) (s : ℤ) (k' : ω') :
    Filtration.inducedAssocGradedMap (fun k' => 𝟙 (A k')) F.fcId s k' =
      𝟙 (F.associatedGraded s k') := by
  rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap]
  have h : (fun s k' => (F.fcId s k').choose) =
      fun s k' => 𝟙 (Subobject.underlying.obj (F.F s k')) := by
    funext s k'
    apply (cancel_mono ((F.F s k').arrow)).mp
    rw [(F.fcId s k').choose_spec, Category.comp_id, Category.id_comp]
  rw [Filtration.inducedGradedMapOfMap_congr
    (Filtration.choose_compat (fun k' => 𝟙 (A k')) F.fcId)
    (fun _ _ => by rw [Category.comp_id, Category.id_comp]) h s k']
  exact Filtration.inducedGradedMapOfMap_id F s k' _

/-- Associated-graded maps respect composition of convergence morphisms. -/
theorem Filtration.inducedAssocGradedMap_comp
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (f : ConvergenceMorphism conv₁ conv₂) (g : ConvergenceMorphism conv₂ conv₃)
    (s : ℤ) (k' : ω') :
    Filtration.inducedAssocGradedMap (fun k' => f.aMap k' ≫ g.aMap k')
        (ConvergenceMorphismData.fcComp f g) s k' =
      Filtration.inducedAssocGradedMap f.aMap f.filtration_compat s k' ≫
        Filtration.inducedAssocGradedMap g.aMap g.filtration_compat s k' := by
  rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap
    (fun k' => f.aMap k' ≫ g.aMap k') (ConvergenceMorphismData.fcComp f g)]
  rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap f.aMap f.filtration_compat]
  rw [Filtration.inducedAssocGradedMap_eq_inducedGradedMapOfMap g.aMap g.filtration_compat]
  have h : (fun s k' => (ConvergenceMorphismData.fcComp f g s k').choose) =
      fun s k' => (f.filtration_compat s k').choose ≫
        (g.filtration_compat s k').choose := by
    funext s k'
    apply (cancel_mono ((F₃.F s k').arrow)).mp
    rw [Category.assoc _ _ ((F₃.F s k').arrow),
      (ConvergenceMorphismData.fcComp f g s k').choose_spec,
      (g.filtration_compat s k').choose_spec]
    conv_rhs => rw [← Category.assoc _ _ (g.aMap k'),
      (f.filtration_compat s k').choose_spec]
    exact (Category.assoc _ _ _).symm
  rw [Filtration.inducedGradedMapOfMap_congr
    (Filtration.choose_compat _ (ConvergenceMorphismData.fcComp f g))
    (fun s k' => by
      apply (cancel_mono ((F₃.F s k').arrow)).mp
      simp only [Category.assoc]
      rw [(g.filtration_compat s k').choose_spec,
        ← Category.assoc _ _ (g.aMap k'),
        (f.filtration_compat s k').choose_spec,
        ← Category.assoc _ _ (g.aMap k'),
        ← Category.assoc _ ((F₁.F s k').arrow) (f.aMap k'),
        Subobject.ofLE_arrow, Subobject.ofLE_arrow,
        (g.filtration_compat (s + 1) k').choose_spec,
        ← Category.assoc _ _ (g.aMap k'),
        (f.filtration_compat (s + 1) k').choose_spec]) h s k']
  exact Filtration.inducedGradedMapOfMap_comp _ _
    (Filtration.choose_compat f.aMap f.filtration_compat)
    (Filtration.choose_compat g.aMap g.filtration_compat) _ s k'

/-- Associated-graded maps commute with transport of grading indices. -/
theorem Filtration.inducedGradedMapOfMap_transportGraded
    {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (φ : ∀ (s : ℤ) (k' : ω'), Subobject.underlying.obj (F₁.F s k') ⟶
      Subobject.underlying.obj (F₂.F s k'))
    (hw : ∀ (s : ℤ) (k' : ω'),
      Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k') ≫ φ s k' =
        φ (s + 1) k' ≫
          Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    {r₁ r₂ : ℤ × ω'} (h : r₁ = r₂) :
    Filtration.inducedGradedMapOfMap φ hw r₁.1 r₁.2 ≫ F₂.transportGraded h =
      F₁.transportGraded h ≫
        Filtration.inducedGradedMapOfMap φ hw r₂.1 r₂.2 := by
  subst h
  simp only [Filtration.transportGraded_self, Category.comp_id, Category.id_comp]

/-- Compatibility of convergence isomorphisms is stable under composition. -/
theorem ConvergenceMorphism.iso_compat_comp
    {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {ω' : Type w} {X Y Z : ConvergingSS C ω ω'}
    (f : ConvergenceMorphism X.conv Y.conv) (g : ConvergenceMorphism Y.conv Z.conv)
    (k : ω) :
    (f.eMap k ≫ g.eMap k) ≫ (Z.conv.iso k).hom ≫
        Z.F.transportGraded ((congrFun (f.reindex_eq.trans g.reindex_eq) k).symm) =
      (X.conv.iso k).hom ≫
        Filtration.inducedAssocGradedMap (fun k' => f.aMap k' ≫ g.aMap k')
          (ConvergenceMorphismData.fcComp f g)
          (X.conv.reindex k).1 (X.conv.reindex k).2 := by
  have hsplit :
      Z.F.transportGraded ((congrFun (f.reindex_eq.trans g.reindex_eq) k).symm) =
        Z.F.transportGraded ((congrFun g.reindex_eq k).symm) ≫
          Z.F.transportGraded ((congrFun f.reindex_eq k).symm) := by
    rw [Filtration.transportGraded_trans]
  have hnat :
      Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
          (Y.conv.reindex k).1 (Y.conv.reindex k).2 ≫
          Z.F.transportGraded ((congrFun f.reindex_eq k).symm) =
        Y.F.transportGraded ((congrFun f.reindex_eq k).symm) ≫
          Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
            (X.conv.reindex k).1 (X.conv.reindex k).2 :=
    Filtration.inducedGradedMapOfMap_transportGraded
      (fun s k' => (g.filtration_compat s k').choose)
      (Filtration.choose_compat g.aMap g.filtration_compat)
      ((congrFun f.reindex_eq k).symm)
  rw [hsplit]
  simp only [Category.assoc]
  rw [← Category.assoc ((Z.conv.iso k).hom)
    (Z.F.transportGraded ((congrFun g.reindex_eq k).symm))
    (Z.F.transportGraded ((congrFun f.reindex_eq k).symm))]
  rw [← Category.assoc (g.eMap k)
    ((Z.conv.iso k).hom ≫ Z.F.transportGraded ((congrFun g.reindex_eq k).symm))
    (Z.F.transportGraded ((congrFun f.reindex_eq k).symm))]
  rw [g.iso_compat k]
  simp only [Category.assoc]
  rw [hnat]
  rw [← Category.assoc ((Y.conv.iso k).hom)
    (Y.F.transportGraded ((congrFun f.reindex_eq k).symm))
    (Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
      (X.conv.reindex k).1 (X.conv.reindex k).2)]
  rw [← Category.assoc (f.eMap k)
    ((Y.conv.iso k).hom ≫ Y.F.transportGraded ((congrFun f.reindex_eq k).symm))
    (Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
      (X.conv.reindex k).1 (X.conv.reindex k).2)]
  rw [f.iso_compat k]
  rw [Category.assoc ((X.conv.iso k).hom)
    (Filtration.inducedAssocGradedMap f.aMap f.filtration_compat
      (X.conv.reindex k).1 (X.conv.reindex k).2)
    (Filtration.inducedAssocGradedMap g.aMap g.filtration_compat
      (X.conv.reindex k).1 (X.conv.reindex k).2)]
  rw [← Filtration.inducedAssocGradedMap_comp f g
    (X.conv.reindex k).1 (X.conv.reindex k).2]

end KIP126.Core.SpectralSequence
