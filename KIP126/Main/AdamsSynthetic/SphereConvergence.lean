module

public import KIP126.Literature.Background.SphereConvergence

public import KIP126.Literature.Standard.ClassicalContext
public import KIP126.Literature.Standard.Foundation
public import KIP126.Def.ClassicalAdams.Convergence.BHS.Predicates
public import KIP126.Def.ClassicalAdams.SphereVanishing.Predicates

import KIP126.Def.ClassicalAdams.TowerLayer.Basic.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Coefficients.Basic.Proofs
import KIP126.Def.SpectralSequence.ModuleSubobject.Proofs
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.Types.Limits
import KIP126.Def.Algebra.InverseSequence.Finite.Proofs
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Finite.Sigma
import KIP126.Def.ClassicalAdams.Completion.Predicates
import KIP126.Def.ClassicalAdams.Tower.Proofs
import KIP126.Def.ClassicalAdams.Convergence.Tower.Data
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Data
import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finsupp.Fintype
import KIP126.Def.ClassicalAdams.Convergence.Tower.Predicates
import KIP126.Def.SpectralSequence.ModuleQuotient.Proofs
import Mathlib.LinearAlgebra.Isomorphisms
import KIP126.Def.StableHomotopy.Spectra.Comparison

import Mathlib.Algebra.Ring.GeomSum
import KIP126.Def.StableHomotopy.Context.Connecting.Proofs
import KIP126.Def.ClassicalAdams.TowerNaturality.Proofs
import KIP126.Def.StableHomotopy.Context.Mapping.Data
import KIP126.Def.StableHomotopy.Cohomology.Multiplication.Action.Proofs
import KIP126.Def.ClassicalAdams.MapFiltration.Predicates
import KIP126.Def.StableHomotopy.Cohomology.Coaction.Unit.Proofs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Continuity

public import KIP126.Def.StableHomotopy.FiniteType.Proofs

@[expose] public section

/-! The standard sphere Adams convergence assumption and supporting lemmas.
Completeness and strong convergence for the fixed 2-completed sphere are
explicitly assumed in `standardSphereApplicability`; filtration separation
is derived from that assumption below. The other lemmas prove the finite-kernel
criterion, prespectrum suspension cancellation and Moore comparisons. -/
section StandardSphereApplicabilitySupport


open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Algebra
universe u v
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [StableHomotopyCategory.{u,v} C]

private theorem cohomology_subsingleton_of_doubling (H : Mod2EilenbergMacLane (C := C))
    [MonoidalPreadditive C] (R : Mod2RingStructure H) (Z : C)
    (hd : IsIso (𝟙 Z + 𝟙 Z)) (n : ℤ) : Subsingleton (Mod2Cohomology H n Z) := by
  letI := hd
  have hz (x : Mod2Cohomology H n Z) : x = 0 := by
    apply (cancel_epi ((shiftFunctor C (-n)).map (𝟙 Z + 𝟙 Z))).mp
    simp only [Functor.map_add, (shiftFunctor C (-n)).map_id Z, Preadditive.add_comp,
      Category.id_comp, comp_zero]
    simpa only [two_nsmul] using mod2Cohomology_two_nsmul_zero H R n Z x
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

private theorem acyclic_of_fiber_doubling [HasFunctorialCofiber (C := C)]
    [HasProductsOfShape ℕ C] [MonoidalPreadditive C]
    (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
    (detect : ∀ Z : C, (∀ n : ℤ, Subsingleton (Mod2Cohomology H n Z)) → IsZero Z)
    (D : InverseSequence C)
    (hd : IsIso (𝟙 (fiber D.oneSubShift) + 𝟙 (fiber D.oneSubShift))) : D.IsAcyclic := by
  have hz := detect (fiber D.oneSubShift)
    (cohomology_subsingleton_of_doubling H R _ hd)
  exact (CategoryTheory.Pretriangulated.Triangle.isZero₁_iff_isIso₂
    (adamsFiberTriangle D.oneSubShift)
    (adamsFiberTriangle_distinguished D.oneSubShift)).mp hz

private theorem hom_delta_bijective [HasProductsOfShape ℕ C]
    (D : InverseSequence C) (hD : D.IsAcyclic) (B : C) :
    Function.Bijective (fun z : ∀ s, B ⟶ D.obj s =>
      fun s => z s - z (s+1) ≫ D.step s) := by
  letI : IsIso D.oneSubShift := hD
  have proj (z : ∀ s, B ⟶ D.obj s) (s : ℕ) :
      (Pi.lift z ≫ D.oneSubShift) ≫ Pi.π D.obj s = z s - z (s+1) ≫ D.step s := by
    simp [InverseSequence.oneSubShift, InverseSequence.shiftMap,
      Preadditive.comp_sub, Preadditive.sub_comp]
  constructor
  · intro z w h
    have he : Pi.lift z ≫ D.oneSubShift = Pi.lift w ≫ D.oneSubShift := by
      apply Pi.hom_ext
      intro s
      simpa only [proj] using congrFun h s
    have he' := (cancel_mono D.oneSubShift).mp he
    funext s
    simpa using congrArg (fun f => f ≫ Pi.π D.obj s) he'
  · intro y
    let z : ∀ s, B ⟶ D.obj s := fun s => Pi.lift y ≫ inv D.oneSubShift ≫ Pi.π D.obj s
    have hl : Pi.lift z = Pi.lift y ≫ inv D.oneSubShift := by
      apply Pi.hom_ext
      intro s
      simp [z]
    refine ⟨z, funext fun s => ?_⟩
    change z s - z (s+1) ≫ D.step s = y s
    rw [← proj z s, hl]
    simp

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Algebra



namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Inverse
universe u v w

private theorem finite_fiber_of_finite_ker
    {A : Type u} {B : Type v} [AddGroup A] [AddGroup B]
    (f : A →+ B) [Finite f.ker] (b : B) : Finite {a : A // f a = b} := by
  classical
  by_cases h : Nonempty {a : A // f a = b}
  · let a₀ := Classical.choice h
    let e : {a : A // f a = b} → f.ker := fun a =>
      ⟨a.val - a₀.val, by simp only [AddMonoidHom.mem_ker, map_sub, a.property, a₀.property, sub_self]⟩
    exact Finite.of_injective e (fun a a' h => Subtype.ext (sub_left_inj.mp (congrArg Subtype.val h)))
  · letI : IsEmpty {a : A // f a = b} := not_nonempty_iff.mp h
    infer_instance

private theorem finite_fiber_comp
    {A : Type u} {B : Type v} {C : Type w}
    (f : B → C) (g : A → B)
    (hf : ∀ c, Finite {b // f b = c}) (hg : ∀ b, Finite {a // g a = b})
    (c : C) : Finite {a // f (g a) = c} := by
  letI : Finite {b // f b = c} := hf c
  letI : ∀ b : {b // f b = c}, Finite {a // g a = b.val} := fun b => hg b.val
  let e : {a // f (g a) = c} → Σ b : {b // f b = c}, {a // g a = b.val} :=
    fun a => ⟨⟨g a.val, a.property⟩, ⟨a.val, rfl⟩⟩
  exact Finite.of_injective e (fun a a' h => Subtype.ext (congrArg (fun z => z.2.val) h))


private theorem finite_fiber_tower
    (G : ℕ → Type u) [∀ n, AddCommGroup (G n)]
    (p : ∀ a b, a ≤ b → G b →+ G a)
    (pid : ∀ a x, p a a (Nat.le_refl a) x = x)
    (pcomp : ∀ a b c (hab : a ≤ b) (hbc : b ≤ c) x,
      p a b hab (p b c hbc x) = p a c (hab.trans hbc) x)
    (hfinite : ∀ n, Finite (p n (n+1) (Nat.le_succ n)).ker)
    (a b : ℕ) (hab : a ≤ b) (x : G a) : Finite {y : G b // p a b hab y = x} := by
  induction b, hab using Nat.le_induction generalizing x with
  | base =>
    let he : {y : G a // p a a (Nat.le_refl a) y = x} → {y : G a // y = x} :=
      fun y => ⟨y.val, (pid a y.val).symm.trans y.property⟩
    exact Finite.of_injective he (by
      intro y y' h
      apply Subtype.ext
      exact congrArg (fun z : {y : G a // y = x} => z.val) h)
  | succ b hab ih =>
    letI := hfinite b
    have hf : ∀ z, Finite {y : G b // p a b hab y = z} := by
      intro z
      exact ih z
    have hg := finite_fiber_comp (p a b hab) (p b (b+1) (Nat.le_succ b)) hf
      (finite_fiber_of_finite_ker (p b (b+1) (Nat.le_succ b))) x
    exact Finite.of_injective
      (fun y : {y : G (b+1) // p a (b+1) (hab.trans (Nat.le_succ b)) y = x} =>
        (⟨y.val, (pcomp a b (b+1) hab (Nat.le_succ b) y.val).trans y.property⟩ :
          {y : G (b+1) // p a b hab (p b (b+1) (Nat.le_succ b) y) = x}))
      (by
        intro y y' h
        apply Subtype.ext
        exact congrArg (fun z : {y : G (b+1) // p a b hab (p b (b+1) (Nat.le_succ b) y) = x} => z.val) h)


/-- A zero inverse limit together with finite adjacent kernels separates all image filtrations. -/
private theorem separated_of_finite_ker
    (G : ℕ → Type u) [∀ n, AddCommGroup (G n)]
    (p : ∀ a b, a ≤ b → G b →+ G a)
    (pid : ∀ a x, p a a (Nat.le_refl a) x = x)
    (pcomp : ∀ a b c (hab : a ≤ b) (hbc : b ≤ c) x,
      p a b hab (p b c hbc x) = p a c (hab.trans hbc) x)
    (hfinite : ∀ n, Finite (p n (n+1) (Nat.le_succ n)).ker)
    (hzero : ∀ z : ∀ n, G n,
      (∀ n, p n (n+1) (Nat.le_succ n) (z (n+1)) = z n) → ∀ n, z n = 0)
    (a : ℕ) (x : G a)
    (hx : ∀ b (hab : a ≤ b), ∃ y, p a b hab y = x) : x = 0 := by
  classical
  let A (b : ℕ) (hab : a ≤ b) := {y : G b // p a b hab y = x}
  let step (b : ℕ) (hab : a ≤ b) : A (b+1) (Nat.le_succ_of_le hab) → A b hab :=
    fun y => ⟨p b (b+1) (Nat.le_succ b) y.val,
      (pcomp a b (b+1) hab (Nat.le_succ b) y.val).trans y.property⟩
  obtain ⟨u, hu⟩ := KIP126.Algebra.InverseSequence.exists_compatible_of_finite a A step
    (fun b hab => finite_fiber_tower G p pid pcomp hfinite a b hab x)
    (fun b hab => let ⟨y, hy⟩ := hx b hab; ⟨⟨y, hy⟩⟩)
  have hua : (u a (Nat.le_refl a)).val = x :=
    (pid a _).symm.trans (u a (Nat.le_refl a)).property
  let z (b : ℕ) : G b := if hab : a ≤ b then (u b hab).val else p b a (by omega) x
  have hcompat : ∀ b, p b (b+1) (Nat.le_succ b) (z (b+1)) = z b := by
    intro b
    by_cases hab : a ≤ b
    · have hab' : a ≤ b+1 := Nat.le_succ_of_le hab
      simp only [z, dif_pos hab, dif_pos hab']
      exact congrArg Subtype.val (hu b hab)
    · by_cases hab' : a ≤ b+1
      · have hba : b+1 = a := by omega
        subst a
        simp only [z, dif_pos hab', dif_neg hab]
        rw [hua]
      · simp only [z, dif_neg hab, dif_neg hab']
        exact pcomp b (b+1) a (Nat.le_succ b) (by omega) x
  have hza := hzero z hcompat a
  simpa only [z, dif_pos (Nat.le_refl a), hua] using hza

/-- Injectivity of the explicit difference operator kills compatible families. -/
private theorem compatible_zero_of_difference_injective
    (G : ℕ → Type u) [∀ n, AddCommGroup (G n)]
    (step : ∀ n, G (n+1) →+ G n)
    (hinj : Function.Injective (fun z : ∀ n, G n => fun n => z n - step n (z (n+1))))
    (z : ∀ n, G n) (hz : ∀ n, step n (z (n+1)) = z n) : ∀ n, z n = 0 := by
  have he : z = 0 := hinj (by funext n; simp only [hz, sub_self, Pi.zero_apply, map_zero])
  intro n
  exact congrFun he n


open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
open KIP126.Classical.Adams

set_option backward.isDefEq.respectTransparency false in
/-- Application of finite-kernel separation to the actual Adams tower at every starting stage. -/
private theorem adams_separated_of_finite_ker
    {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)]
    {H : C} (unit : 𝟙_ C ⟶ H) (X : C) (n : ℤ)
    (hfinite : ∀ s, Finite (LinearMap.ker
      (inducedMap (adamsTowerStep unit X s) n).toIntLinearMap))
    (hinj : Function.Injective (fun z : ∀ s, HomotopyGroup n (adamsTower unit X s) =>
      fun s => z s - z (s+1) ≫ adamsTowerStep unit X s))
    (a : ℕ) (x : HomotopyGroup n (adamsTower unit X a))
    (hx : ∀ b (hab : a ≤ b), x ∈ LinearMap.range
      (inducedMap (adamsTowerMap unit X a b hab) n).toIntLinearMap) : x = 0 := by
  apply separated_of_finite_ker (fun s => HomotopyGroup n (adamsTower unit X s))
    (fun a b hab => inducedMap (adamsTowerMap unit X a b hab) n)
    (fun a x => by simp only [adamsTowerMap_self, inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Category.comp_id])
    (fun a b c hab hbc x => by
      change (x ≫ adamsTowerMap unit X b c hbc) ≫ adamsTowerMap unit X a b hab = _
      rw [Category.assoc, adamsTowerMap_comp]
      rfl)
    ?_ ?_ a x hx
  · intro s
    rw [adamsTowerMap_succ unit X s s (Nat.le_refl s), adamsTowerMap_self, Category.comp_id]
    exact hfinite s
  · intro z hz
    apply compatible_zero_of_difference_injective _ (fun s => inducedMap (adamsTowerStep unit X s) n) hinj z
    intro s
    have h := hz s
    simpa only [adamsTowerMap_succ unit X s s (Nat.le_refl s), adamsTowerMap_self, Category.comp_id] using h


set_option backward.isDefEq.respectTransparency false in
/-- The elementwise separation theorem proves the required subobject field. -/
private theorem adams_filtration_separated
    {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)]
    {H : C} (unit : 𝟙_ C ⟶ H) (X : C)
    (hsep : ∀ (n : ℤ) (x : HomotopyGroup n X),
      (∀ s : ℕ, x ∈ LinearMap.range
        (inducedMap (adamsTowerMap unit X 0 s (Nat.zero_le s)) n).toIntLinearMap) → x = 0)
    (n : ℤ) (S : Subobject (towerAbutment X n))
    (hS : ∀ s : ℤ, S ≤ (adamsHomotopyFiltration unit X).F s n) : S = ⊥ := by
  apply (ModuleCat.subobjectModule (towerAbutment X n)).injective
  rw [OrderIso.map_bot]
  apply le_antisymm
  · intro x hx
    apply (Submodule.mem_bot ℤ).mpr
    apply hsep n x
    intro s
    have hs := (ModuleCat.subobjectModule (towerAbutment X n)).monotone (hS (s : ℤ))
    have hx' := hs hx
    simpa only [adamsHomotopyFiltration, OrderIso.apply_symm_apply,
      adamsHomotopyFiltrationSubmodule, adamsTowerToSpectrum, Int.toNat_natCast] using hx'
  · exact bot_le

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Inverse


open CategoryTheory CategoryTheory.MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams KIP126.Steenrod.Milnor

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Finiteness

private theorem word_finite (s : ℕ) (n : ℤ) : Finite (MilnorWord s n) := by
  classical
  have boundedWeight (n : ℕ) : Finite {d : ℕ →₀ ℕ // slotWeight d ≤ n} := by
    have hpos (j : ℕ) : 2 ^ (j + 1) - 1 ≠ 0 := by
      have h := (Nat.lt_two_pow_self (n := j + 1))
      omega
    let f : {d : ℕ →₀ ℕ // slotWeight d ≤ n} → (Fin (n+1) → Fin (n+1)) :=
      fun d j => ⟨d.val j.val, Nat.lt_succ_of_le
        ((Finsupp.le_weight (fun j => 2 ^ (j+1)-1) (hpos j) d.val).trans d.property)⟩
    apply Finite.of_injective f
    intro d e h
    apply Subtype.ext
    apply Finsupp.ext
    intro j
    by_cases hj : j < n + 1
    · exact congrArg Fin.val (congrFun h ⟨j,hj⟩)
    · have hz (a : {d : ℕ →₀ ℕ // slotWeight d ≤ n}) : a.val j = 0 := by
        by_contra hne
        have hw := (Finsupp.le_weight_of_ne_zero'
          (fun k : ℕ => 2 ^ (k+1)-1) hne).trans a.property
        have hp := (Nat.lt_two_pow_self (n := j+1))
        omega
      rw [hz d, hz e]
  let f : MilnorWord s n → (Fin s → {d : ℕ →₀ ℕ // slotWeight d ≤ n.toNat}) :=
    fun d i => ⟨d.val i, by
      have hle : (slotWeight (d.val i) : ℤ) ≤ wordDegree d.val := by
        exact Finset.single_le_sum (fun j _ => Int.natCast_nonneg _) (Finset.mem_univ i)
      have hdeg := d.property.1
      omega⟩
  letI := boundedWeight n.toNat
  apply Finite.of_injective f
  intro d e h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R) (B : Mod2ReducedMilnorBasis H R)
  [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

include R K B

private theorem sphere_tower_homology_finite (s : ℕ) (n : ℤ) :
    Finite (HomotopyGroup n (H.HF2 ⊗ adamsTower H.unit SphereSpectrum s)) := by
  classical
  letI := word_finite s (n + s)
  letI := Fintype.ofFinite (MilnorWord s (n + s))
  exact Finite.of_injective (sphereTowerHomologyWordEquiv H R K B s n)
    (sphereTowerHomologyWordEquiv H R K B s n).injective

private theorem sphere_e1_finite (s t : ℤ) :
    Finite (adamsE1 H.unit SphereSpectrum s t) := by
  by_cases hs : 0 ≤ s
  · obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le hs
    letI := sphere_tower_homology_finite H R K B s (t - s)
    exact Finite.of_injective (adamsE1HomologyEquiv H.unit SphereSpectrum s t)
      (adamsE1HomologyEquiv H.unit SphereSpectrum s t).injective
  · letI : Subsingleton (adamsE1 H.unit SphereSpectrum s t) :=
      ⟨fun x y => (adamsLayerAt_isZero_of_negative H.unit SphereSpectrum s (by omega)).eq_of_tgt x y⟩
    infer_instance

omit [MonoidalPreadditive C] H R K B [(tensorLeft H.HF2).CommShift ℤ]
  [(tensorLeft H.HF2).IsTriangulated] [HasFunctorialCofiber (C := C)] in
private theorem finite_kernel_of_cofiber (T : HoCofiberSequence (C := C)) (n : ℤ)
    [Finite (HomotopyGroup n T.Z)] :
    Finite (LinearMap.ker (inducedMap T.f (n - 1)).toIntLinearMap) := by
  classical
  let d : HomotopyGroup n T.Z → LinearMap.ker (inducedMap T.f (n - 1)).toIntLinearMap :=
    fun z => ⟨connectingHomomorphism T n z,
      (lesHomotopyExactH T n _).mpr ⟨z, rfl⟩⟩
  apply Finite.of_surjective d
  intro x
  obtain ⟨z, hz⟩ := (lesHomotopyExactH T n x.val).mp x.property
  exact ⟨z, Subtype.ext hz⟩

private theorem sphere_adjacent_kernel_finite (s : ℕ) (n : ℤ) :
    Finite (LinearMap.ker
      (inducedMap (adamsTowerStep H.unit SphereSpectrum s) n).toIntLinearMap) := by
  let f := adamsUnit H.unit (adamsTower H.unit SphereSpectrum s)
  let T := HoCofiberSequence.ofMorphism (adamsTowerStep H.unit SphereSpectrum s)
  letI := sphere_tower_homology_finite H R K B s (n + 1)
  letI : Finite (HomotopyGroup (n + 1) T.Z) := by
    change Finite (HomotopyGroup (n + 1) (HasFunctorialCofiber.cofib (fiberι f)))
    exact Finite.of_injective (fun z => z ≫ (cofiberFiberIso f).hom)
      (fun x y h => by
        have hh := congrArg (fun z => z ≫ (cofiberFiberIso f).inv) h
        simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh)
  have h := finite_kernel_of_cofiber T (n + 1)
  have hn : n + 1 - 1 = n := by omega
  rw [hn] at h
  exact h

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Finiteness


namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Algebra
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams
open KIP126.SpectralSequence
universe u v w
set_option backward.isDefEq.respectTransparency false

/-- The correction step in §9.1: solving the difference equation changes
compatible representatives into one representative of all quotient classes. -/
private theorem common_representative
    (G : ℕ → Type v) [∀ s, AddCommGroup (G s)]
    {A : Type w} [AddCommGroup A]
    (i : ∀ s, G (s+1) →+ G s) (p : ∀ s, G s →+ A)
    (hp : ∀ s y, p s (i s y) = p (s+1) y)
    (hdelta : Function.Surjective (fun z : ∀ s, G s => fun s => z s - i s (z (s+1))))
    (x : ℕ → A) (hx : ∀ s, ∃ y, p s y = x s - x (s+1)) :
    ∃ a : A, ∀ s, ∃ y, p s y = x s - a := by
  classical
  choose y hy using hx
  obtain ⟨z, hz⟩ := hdelta y
  have hz' (s : ℕ) : p s (z s) - p (s+1) (z (s+1)) = x s - x (s+1) := by
    have h := congrArg (p s) (congrFun hz s)
    simpa only [map_sub, hp, hy] using h
  have hw (s : ℕ) : x s - p s (z s) = x 0 - p 0 (z 0) := by
    induction s with
    | zero => rfl
    | succ s ih =>
      calc
        x (s+1) - p (s+1) (z (s+1)) = x s - p s (z s) := by
          rw [sub_eq_iff_eq_add.mp (hz' s)]
          abel
        _ = _ := ih
  refine ⟨x 0 - p 0 (z 0), fun s => ⟨z s, ?_⟩⟩
  rw [← hw s]
  abel

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]

private theorem quotientProjection_eq_zero_iff {H : C} (unit : 𝟙_ C ⟶ H) (X : C)
    (s n : ℤ) (x : towerAbutment X n) :
    (adamsHomotopyFiltration unit X).quotientProjection s n x = 0 ↔
      x ∈ adamsHomotopyFiltrationSubmodule unit X s n := by
  refine (cokernel_π_eq_zero_iff_mem_range
    ((adamsHomotopyFiltration unit X).F s n).arrow x).trans ?_
  change x ∈ (ModuleCat.subobjectModule (towerAbutment X n))
    ((ModuleCat.subobjectModule (towerAbutment X n)).symm (adamsHomotopyFiltrationSubmodule unit X s n)) ↔ _
  rw [OrderIso.apply_symm_apply]

/-- The prescribed cokernel cone is limiting, not just abstractly isomorphic
to some complete group. Only surjectivity of the difference and separation
at stage zero are needed for this step. -/
private theorem adams_complete_of_difference {H : C} (unit : 𝟙_ C ⟶ H) (X : C) (n : ℤ)
    (hdelta : Function.Surjective
      (fun z : ∀ s, HomotopyGroup n (adamsTower unit X s) =>
        fun s => z s - z (s+1) ≫ adamsTowerStep unit X s))
    (hsep : ∀ x : HomotopyGroup n X,
      (∀ s : ℕ, x ∈ adamsHomotopyFiltrationSubmodule unit X s n) → x = 0) :
    Nonempty (KIP126.Algebra.Filtration.CompletionWitness
      (adamsHomotopyFiltration unit X) n) := by
  classical
  let F := adamsHomotopyFiltration unit X
  let q (s : ℤ) := F.quotientProjection s n
  have hq (s : ℤ) : Function.Surjective (q s) := by
    apply (ModuleCat.epi_iff_surjective _).mp
    change Epi (cokernel.π _)
    infer_instance
  have hk (s : ℤ) (x : HomotopyGroup n X) :
      q s x = 0 ↔ x ∈ adamsHomotopyFiltrationSubmodule unit X s n :=
    quotientProjection_eq_zero_iff unit X s n x
  suffices ht : Nonempty (IsLimit ((forget (ModuleCat ℤ)).mapCone (F.quotientTowerCone n))) by
    exact ⟨⟨isLimitOfReflects (forget (ModuleCat ℤ)) (Classical.choice ht)⟩⟩
  rw [Types.isLimit_iff]
  intro c hc
  have hcn (s : ℕ) :
      F.quotientTransition (by omega : (s : ℤ) ≤ (s+1 : ℕ)) n (c (s+1 : ℕ)) = c s := by
    exact hc (homOfLE (show (s+1 : ℕ) ≤ (s : OrderDual ℤ) from by
      change (s : ℤ) ≤ (s+1 : ℕ); omega))
  choose x hx using fun s : ℕ => hq s (c s)
  change ℕ → HomotopyGroup n X at x
  have hdiff (s : ℕ) : ∃ y : HomotopyGroup n (adamsTower unit X s),
      inducedMap (adamsTowerMap unit X 0 s (Nat.zero_le s)) n y = x s - x (s+1) := by
    have hh : q s (x s - x (s+1)) = 0 := by
      rw [map_sub, hx, sub_eq_zero]
      calc
        c s = F.quotientTransition (by omega : (s : ℤ) ≤ (s+1 : ℕ)) n (q (s+1 : ℕ) (x (s+1))) := by
          rw [hx, hcn]
        _ = q s (x (s+1)) := by
          exact ConcreteCategory.congr_hom (F.quotientProjection_transition
            (by omega : (s : ℤ) ≤ (s+1 : ℕ)) n) _
    exact (hk s _).mp hh
  obtain ⟨a, ha⟩ := common_representative (A := HomotopyGroup n X)
    (fun s => HomotopyGroup n (adamsTower unit X s))
    (fun s => inducedMap (adamsTowerStep unit X s) n)
    (fun s => inducedMap (adamsTowerMap unit X 0 s (Nat.zero_le s)) n)
    (by
      intro s y
      change (y ≫ adamsTowerStep unit X s) ≫ adamsTowerMap unit X 0 s _ = _
      rw [Category.assoc, ← adamsTowerMap_succ]
      rfl) hdelta x hdiff
  have han (s : ℕ) : q s a = c s := by
    have hmem : x s - a ∈ adamsHomotopyFiltrationSubmodule unit X s n := ha s
    have he := (hk s _).mpr hmem
    rw [map_sub, hx, sub_eq_zero] at he
    exact he.symm
  have haall (s : ℤ) : q s a = c s := by
    let k := s.toNat
    have hsk : s ≤ (k : ℤ) := by dsimp [k]; omega
    have hcs : F.quotientTransition hsk n (c k) = c s :=
      hc (homOfLE (show (k : OrderDual ℤ) ≤ s from hsk))
    rw [← hcs, ← han k]
    exact (ConcreteCategory.congr_hom (F.quotientProjection_transition hsk n) a).symm
  refine ⟨a, haall, ?_⟩
  intro b hb
  change HomotopyGroup n X at b
  change ∀ s : ℤ, q s b = c s at hb
  change (b : HomotopyGroup n X) = a
  apply sub_eq_zero.mp
  apply hsep
  intro s
  apply (hk s _).mp
  rw [map_sub]
  change q s b - q s a = 0
  rw [hb, haall, sub_self]

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Algebra


open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
  KIP126.StableHomotopy KIP126.Classical.Adams KIP126.SpectralSequence

noncomputable section
namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Pages
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

private theorem augmentation_comp (n a b : ℤ) (h : a ≤ b)
    (x : HomotopyGroup n (adamsTowerAt unit X b)) :
    inducedMap (adamsTowerToSpectrum unit X a) n (adamsI unit X n a b h x) =
      inducedMap (adamsTowerToSpectrum unit X b) n x := by
  change (x ≫ adamsTowerMapAt unit X a b h) ≫ adamsTowerToSpectrum unit X a =
    x ≫ adamsTowerToSpectrum unit X b
  rw [Category.assoc]
  congr 1
  exact adamsTowerMap_comp unit X 0 a.toNat b.toNat (Nat.zero_le _) (by omega)

private theorem augmentation_injective_nonpos (n a : ℤ) (ha : a ≤ 0) :
    Function.Injective (inducedMap (adamsTowerToSpectrum unit X a) n) := by
  have hnat : a.toNat = 0 := Int.toNat_eq_zero.mpr ha
  haveI : IsIso (adamsTowerToSpectrum unit X a) := by
    have hh : ∀ (b : ℕ), b = 0 → IsIso (adamsTowerMap unit X 0 b (Nat.zero_le _)) := by
      intro b hb
      subst b
      rw [adamsTowerMap_self]
      infer_instance
    exact hh a.toNat hnat
  intro x y hxy
  exact (cancel_mono (adamsTowerToSpectrum unit X a)).mp hxy

private theorem boundary_top_iff (s t : ℤ) (x : adamsCycleAmbient unit X s t) :
    x ∈ adamsBoundarySubmodule unit X s t ⊤ ↔
      ∃ y : HomotopyGroup (t - s) (adamsTowerAt unit X s),
        inducedMap (adamsTowerToSpectrum unit X s) (t - s) y = 0 ∧
          adamsJ unit X s t y = x.val := by
  rw [mem_adamsBoundarySubmodule_top]
  constructor
  · rintro ⟨r, y, hy, hj⟩
    refine ⟨y, ?_, hj⟩
    have hz := congrArg (inducedMap
      (adamsTowerToSpectrum unit X (s - (r + 2 : ℕ) + 1)) (t - s)) hy
    simpa only [augmentation_comp, map_zero] using hz
  · rintro ⟨y, hy, hj⟩
    refine ⟨s.toNat, y, ?_, hj⟩
    change adamsI unit X (t - s) (s - (s.toNat + 2 : ℕ) + 1) s (by omega) y = 0
    apply augmentation_injective_nonpos unit X (t - s)
      (s - (s.toNat + 2 : ℕ) + 1) (by omega)
    rw [augmentation_comp, hy, map_zero]

private theorem cycle_top_iff
    (hsep : ∀ (n a : ℤ) (x : HomotopyGroup n (adamsTowerAt unit X a)),
      (∀ (b : ℤ) (h : a ≤ b), x ∈ LinearMap.range (adamsI unit X n a b h)) → x = 0)
    (s t : ℤ) (x : adamsCycleAmbient unit X s t) :
    x ∈ adamsCycleSubmodule unit X s t ⊤ ↔
      ∃ y : HomotopyGroup (t - s) (adamsTowerAt unit X s),
        adamsJ unit X s t y = x.val := by
  rw [mem_adamsCycleSubmodule_top]
  constructor
  · intro hx
    have hk : adamsK unit X s t x.val = 0 := by
      apply hsep (t - s - 1) (s + 1)
      intro b hb
      obtain ⟨y, hy⟩ := hx (b - s).toNat
      refine ⟨adamsI unit X (t - s - 1) b (s + ((b - s).toNat + 2 : ℕ))
        (by omega) y, ?_⟩
      rw [adamsI_comp]
      exact hy
    exact (les_homotopy_exact_g
      (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
      (t - s) x.val).mp hk
  · rintro ⟨y, hy⟩ r
    rw [← hy]
    exact adamsJ_mem_cycles unit X (r + 2) (by omega) s t y

private theorem boundary_image_iff (s t : ℤ)
    (x : HomotopyGroup (t - s) (adamsTowerAt unit X s)) :
    (∃ y : HomotopyGroup (t - s) (adamsTowerAt unit X s),
      inducedMap (adamsTowerToSpectrum unit X s) (t - s) y = 0 ∧
        adamsJ unit X s t y = adamsJ unit X s t x) ↔
      inducedMap (adamsTowerToSpectrum unit X s) (t - s) x ∈
        adamsHomotopyFiltrationSubmodule unit X (s + 1) (t - s) := by
  have exactness (a : HomotopyGroup (t - s) (adamsTowerAt unit X s)) :
      adamsJ unit X s t a = 0 ↔
        ∃ b, adamsI unit X (t - s) s (s + 1) (by omega) b = a :=
    les_homotopy_exact_f
      (HoCofiberSequence.ofMorphism (adamsTowerMapAt unit X s (s + 1) (by omega)))
      (t - s) a
  constructor
  · rintro ⟨y, hy, hj⟩
    obtain ⟨b, hb⟩ := (exactness (x - y)).mp (by rw [map_sub, hj, sub_self])
    refine ⟨b, ?_⟩
    have h := augmentation_comp unit X (t - s) s (s + 1) (by omega) b
    rw [hb, map_sub, hy, sub_zero] at h
    exact h.symm
  · rintro ⟨b, hb⟩
    refine ⟨x - adamsI unit X (t - s) s (s + 1) (by omega) b, ?_, ?_⟩
    · rw [map_sub, augmentation_comp]
      exact sub_eq_zero.mpr hb.symm
    · have hj := (exactness (adamsI unit X (t - s) s (s + 1) (by omega) b)).mpr
        ⟨b, rfl⟩
      rw [map_sub, hj, sub_zero]

private theorem integer_separated_of_natural
    (hsep : ∀ (n : ℤ) (a : ℕ) (x : HomotopyGroup n (adamsTower unit X a)),
      (∀ (b : ℕ) (h : a ≤ b), x ∈ LinearMap.range
        (inducedMap (adamsTowerMap unit X a b h) n).toIntLinearMap) → x = 0)
    (n a : ℤ) (x : HomotopyGroup n (adamsTowerAt unit X a))
    (hx : ∀ (b : ℤ) (h : a ≤ b), x ∈ LinearMap.range (adamsI unit X n a b h)) :
    x = 0 := by
  apply hsep n a.toNat x
  intro b hb
  have hh := hx (b : ℤ) (by omega)
  simpa only [adamsI, adamsTowerMapAt, Int.toNat_natCast] using hh

set_option maxHeartbeats 400000 in
private theorem associatedGraded_of_separated
    (hsep : ∀ (n a : ℤ) (x : HomotopyGroup n (adamsTowerAt unit X a)),
      (∀ (b : ℤ) (h : a ≤ b), x ∈ LinearMap.range (adamsI unit X n a b h)) → x = 0)
    (s t : ℤ) :
    Nonempty (((adamsTowerInternalSpectralSequence unit X).ssData (s, t)).eInfty ≅
      (adamsHomotopyFiltration unit X).associatedGraded s (t - s)) := by
  let Z := adamsCycleSubmodule unit X s t ⊤
  let B := adamsBoundarySubmodule unit X s t ⊤
  let F := adamsHomotopyFiltrationSubmodule unit X s (t - s)
  let F' := adamsHomotopyFiltrationSubmodule unit X (s + 1) (t - s)
  let j₀ : HomotopyGroup (t - s) (adamsTowerAt unit X s) →ₗ[ℤ]
      adamsCycleAmbient unit X s t :=
    (adamsJ unit X s t).codRestrict _ (adamsJ_mem_cycles unit X 2 (by omega) s t)
  let j : HomotopyGroup (t - s) (adamsTowerAt unit X s) →ₗ[ℤ] Z :=
    j₀.codRestrict _ (fun a => (mem_adamsCycleSubmodule_top unit X s t (j₀ a)).mpr
      (fun r => adamsJ_mem_cycles unit X (r + 2) (by omega) s t a))
  let p : HomotopyGroup (t - s) (adamsTowerAt unit X s) →ₗ[ℤ] F :=
    (inducedMap (adamsTowerToSpectrum unit X s) (t - s)).toIntLinearMap.rangeRestrict
  let qj : HomotopyGroup (t - s) (adamsTowerAt unit X s) →ₗ[ℤ]
      Z ⧸ B.comap Z.subtype := (B.comap Z.subtype).mkQ.comp j
  let qp : HomotopyGroup (t - s) (adamsTowerAt unit X s) →ₗ[ℤ]
      F ⧸ F'.comap F.subtype := (F'.comap F.subtype).mkQ.comp p
  have hj : Function.Surjective j := by
    intro z
    obtain ⟨a, ha⟩ := (cycle_top_iff unit X hsep s t z.val).mp z.property
    exact ⟨a, Subtype.ext (Subtype.ext ha)⟩
  have hp : Function.Surjective p := by
    rintro ⟨x, a, rfl⟩
    exact ⟨a, rfl⟩
  have hqj : Function.Surjective qj := (Submodule.mkQ_surjective _).comp hj
  have hqp : Function.Surjective qp := (Submodule.mkQ_surjective _).comp hp
  have hk : LinearMap.ker qj = LinearMap.ker qp := by
    ext a
    change (B.comap Z.subtype).mkQ (j a) = 0 ↔
      (F'.comap F.subtype).mkQ (p a) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change j₀ a ∈ B ↔ (p a).val ∈ F'
    exact (boundary_top_iff unit X s t (j₀ a)).trans
      (boundary_image_iff unit X s t a)
  let e := (qj.quotKerEquivOfSurjective hqj).symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (qp.quotKerEquivOfSurjective hqp))
  exact ⟨(submoduleCokernelIso (M := ModuleCat.of ℤ (adamsCycleAmbient unit X s t)) B Z
    (adamsBoundarySubmodule_le_cycle unit X s t ⊤)) ≪≫ e.toModuleIso ≪≫
      (submoduleCokernelIso (M := towerAbutment X (t - s)) F' F
        (adamsHomotopyFiltrationSubmodule_decreasing unit X s (t - s))).symm⟩

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Pages

end


open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.StableHomotopy.Spectra

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Local

private noncomputable def shiftSource (d : ℤ) : Prespectrum.{0} :=
  if 0 ≤ d then (Prespectrum.suspension^[d.toNat]) sourceHF2.spectrum
  else (Prespectrum.desuspension^[(-d).toNat]) sourceHF2.spectrum

private theorem source_shift_local (d : ℤ) : (shiftSource d).IsHF2Local := by
  intro A B f hf
  exact hf d

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} (S : SourceComparison completionModel H)

private theorem isZero_of_source_detector_vanishing (Z : C)
    (h : ∀ d : ℤ, Subsingleton
      (sourceLocalization.obj (S.equivalence.inverse.obj Z).spectrum ⟶ sourceHF2Shift d)) :
    IsZero Z := by
  let W := S.equivalence.inverse.obj Z
  let f : W ⟶ W := S.equivalence.inverse.map (0 : Z ⟶ Z)
  have hf : HF2Equivalences f := by
    intro d
    letI := h d
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨x, Subsingleton.elim _ _⟩⟩
  have hinj := (W.isLocal f hf).1
  have hidempotent : f ≫ f = f := by
    change S.equivalence.inverse.map (0 : Z ⟶ Z) ≫
      S.equivalence.inverse.map (0 : Z ⟶ Z) = S.equivalence.inverse.map (0 : Z ⟶ Z)
    rw [← Functor.map_comp, zero_comp]
  have hid : (𝟙 W) = f := hinj ((Category.comp_id f).trans hidempotent.symm)
  apply (IsZero.iff_id_eq_zero Z).mpr
  apply S.equivalence.inverse.map_injective
  exact (S.equivalence.inverse.map_id Z).trans hid

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Local

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Local

private noncomputable def localShift (d : ℤ) : CompletedSpectrum :=
  ⟨shiftSource d, source_shift_local d⟩

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} (S : SourceComparison completionModel H)

private theorem isZero_of_cohomology_vanishing_of_shift_comparison
    (hcmp : ∀ d : ℤ, Nonempty
      (S.equivalence.functor.obj (localShift d) ≅ (shiftFunctor C d).obj H.HF2))
    (Z : C) (h : ∀ d : ℤ, Subsingleton (Mod2Cohomology H d Z)) : IsZero Z := by
  classical
  apply isZero_of_source_detector_vanishing S Z
  intro d
  let e := Classical.choice (hcmp d)
  let a : S.equivalence.functor.obj (S.equivalence.inverse.obj Z) ≅ Z :=
    S.equivalence.counitIso.app Z
  let b : (shiftFunctor C (-d)).obj ((shiftFunctor C d).obj H.HF2) ≅ H.HF2 :=
    (shiftFunctorCompIsoId C d (-d) (by omega)).app H.HF2
  let f : (S.equivalence.inverse.obj Z ⟶ localShift d) → Mod2Cohomology H d Z :=
    fun z => (shiftFunctor C (-d)).map (a.inv ≫ S.equivalence.functor.map z ≫ e.hom) ≫ b.hom
  have hf : Function.Injective f := by
    intro x y hxy
    apply S.equivalence.functor.map_injective
    apply (cancel_epi a.inv).1
    apply (cancel_mono e.hom).1
    apply (shiftFunctor C (-d)).map_injective
    apply (cancel_mono b.hom).1
    simpa only [Category.assoc] using hxy
  letI := h d
  exact hf.subsingleton

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Local

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Local

private noncomputable def localReflectionIso (X : Prespectrum.{0}) (hX : X.IsHF2Local) :
    completedLocalization.obj X ≅ (⟨X, hX⟩ : CompletedSpectrum) := by
  let W : CompletedSpectrum := ⟨X, hX⟩
  let U := completedLocalization.obj X
  let u : W ⟶ U := sourceLocalization.map (completionModel.unit.app X)
  let r := Classical.choose ((completionModel.universal X W).2 (𝟙 _))
  have hr := Classical.choose_spec ((completionModel.universal X W).2 (𝟙 _))
  refine ⟨r, u, ?_, hr⟩
  apply (completionModel.universal X U).1
  change u ≫ (r ≫ u) = u ≫ 𝟙 U
  calc
    u ≫ (r ≫ u) = (u ≫ r) ≫ u := (Category.assoc _ _ _).symm
    _ = (𝟙 W) ≫ u := congrArg (fun f => f ≫ u) hr
    _ = u ≫ 𝟙 U := (Category.id_comp u).trans (Category.comp_id u).symm

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} (S : SourceComparison completionModel H)

private theorem isZero_of_cohomology_vanishing_of_completed_shift_comparison
    (hcmp : ∀ d : ℤ, Nonempty
      (S.equivalence.functor.obj (completedLocalization.obj (shiftSource d)) ≅
        (shiftFunctor C d).obj H.HF2))
    (Z : C) (h : ∀ d : ℤ, Subsingleton (Mod2Cohomology H d Z)) : IsZero Z := by
  apply isZero_of_cohomology_vanishing_of_shift_comparison S ?_ Z h
  intro d
  exact ⟨S.equivalence.functor.mapIso (localReflectionIso (shiftSource d) (source_shift_local d)).symm ≪≫
    Classical.choice (hcmp d)⟩

private theorem suspensionIter_good (n : ℕ) :
    ((Prespectrum.suspension^[n]) sourceHF2.spectrum).IsWellBased := by
  have hg : ∀ n : ℕ, ∀ k : ℕ,
      (((Prespectrum.suspension^[n]) sourceHF2.spectrum).level k).IsGood := by
    intro n
    induction n with
    | zero => exact sourceHF2.good
    | succ n ih =>
      intro k
      rw [Function.iterate_succ_apply']
      exact BasedSpace.good_suspension (ih k)
  exact fun k => (hg n k).2.1

private noncomputable def completed_positive_shift_comparison : ∀ n : ℕ,
    S.equivalence.functor.obj
      (completedLocalization.obj ((Prespectrum.suspension^[n]) sourceHF2.spectrum)) ≅
        (shiftFunctor C (n : ℤ)).obj H.HF2
  | 0 => S.hf2Iso ≪≫ (shiftFunctorZero C ℤ).symm.app H.HF2
  | n + 1 =>
    eqToIso (by simp only [Function.iterate_succ_apply', completedLocalization]) ≪≫
      S.suspension ((Prespectrum.suspension^[n]) sourceHF2.spectrum) (suspensionIter_good n) ≪≫
      (shiftFunctor C (1 : ℤ)).mapIso (completed_positive_shift_comparison n) ≪≫
      ((shiftFunctorAdd' C (n : ℤ) (1 : ℤ) (↑(n + 1)) (by omega)).app H.HF2).symm

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Local

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Local
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} (S : SourceComparison completionModel H)

private theorem isZero_of_cohomology_vanishing_of_negative_shift_comparison
    (hneg : ∀ n : ℕ, Nonempty
      (S.equivalence.functor.obj
        (completedLocalization.obj ((Prespectrum.desuspension^[n]) sourceHF2.spectrum)) ≅
        (shiftFunctor C (-(n : ℤ))).obj H.HF2))
    (Z : C) (h : ∀ d : ℤ, Subsingleton (Mod2Cohomology H d Z)) : IsZero Z := by
  apply isZero_of_cohomology_vanishing_of_completed_shift_comparison S ?_ Z h
  intro d
  by_cases hd : 0 ≤ d
  · simp only [shiftSource, if_pos hd]
    exact ⟨completed_positive_shift_comparison S d.toNat ≪≫
      eqToIso (by rw [Int.toNat_of_nonneg hd])⟩
  · simp only [shiftSource, if_neg hd]
    obtain ⟨e⟩ := hneg (-d).toNat
    have hi : -(((-d).toNat : ℕ) : ℤ) = d := by omega
    exact ⟨e ≪≫ eqToIso (by rw [hi])⟩

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Local

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Convergence
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams
open KIP126.AdamsSynthetic.Standard.SphereConvergence.Algebra KIP126.AdamsSynthetic.Standard.SphereConvergence.Inverse KIP126.AdamsSynthetic.Standard.SphereConvergence.Pages
universe u v
set_option backward.isDefEq.respectTransparency false

private theorem strong_of_acyclic_and_finite
    {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]
    {H : C} (unit : 𝟙_ C ⟶ H) (X : C)
    (hacyclic : IsENilpotentComplete unit X)
    (hfinite : ∀ (n : ℤ) (s : ℕ), Finite (LinearMap.ker
      (inducedMap (adamsTowerStep unit X s) n).toIntLinearMap)) :
    IsAdamsTowerStronglyConvergent unit X := by
  have hdelta (n : ℤ) := hom_delta_bijective (adamsResidualSequence unit X) hacyclic (Sphere n)
  have hsep (n : ℤ) := adams_separated_of_finite_ker unit X n (hfinite n) (hdelta n).1
  have hzero (n : ℤ) (x : HomotopyGroup n X)
      (hx : ∀ s : ℕ, x ∈ LinearMap.range
        (inducedMap (adamsTowerMap unit X 0 s (Nat.zero_le s)) n).toIntLinearMap) : x = 0 :=
    hsep n 0 x (fun s _ => hx s)
  refine ⟨?_, adams_filtration_separated unit X hzero, ?_⟩
  · intro n
    apply adams_complete_of_difference unit X n (hdelta n).2
    intro x hx
    apply hzero n x
    intro s
    simpa only [adamsHomotopyFiltrationSubmodule, adamsTowerToSpectrum,
      Int.toNat_natCast] using hx s
  · exact associatedGraded_of_separated unit X (integer_separated_of_natural unit X hsep)

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Convergence


/-! The following lemmas establish the remaining Milnor algebra identities and the
source homotopy detector.  The nilpotence lemmas provide the finite Postnikov
steps of §§5–6; constructing their actual source Postnikov witnesses remains
explicit below.  No homotopy-limit/cofiber commutation is assumed. -/

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits KIP126.StableHomotopy KIP126.Classical.Adams
open scoped BigOperators

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Milnor
universe u v
set_option backward.isDefEq.respectTransparency false

private theorem doubling_kernel_cokernel
    {B : Type u} [AddCommGroup B] (f : B →+ B)
    (hqsurj : ∀ b, ∃ x y, f x + (y + y) = b)
    (hqinj : ∀ x y, f x = y + y → ∃ z, x = z + z)
    (htsurj : ∀ b, b + b = 0 → ∃ x, x + x = 0 ∧ f x = b)
    (htinj : ∀ x, x + x = 0 → f x = 0 → x = 0) :
    (∀ x, f x = 0 → x + x = 0 → x = 0) ∧
    (∀ x, f x = 0 → ∃ y, f y = 0 ∧ y + y = x) ∧
    (∀ x, ∃ y z, y + y + f z = x) ∧
    (∀ x y, x + x = f y → ∃ z, f z = x) := by
  refine ⟨fun x hf hx => htinj x hx hf, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy⟩ := hqinj x 0 (by simpa using hx)
    have hfy : f y + f y = 0 := by rw [← map_add, ← hy, hx]
    obtain ⟨z, hz, hfz⟩ := htsurj (f y) hfy
    refine ⟨y - z, by simp [hfz], ?_⟩
    rw [hy]
    calc
      (y - z) + (y - z) = (y + y) - (z + z) := by abel
      _ = y + y := by rw [hz, sub_zero]
  · intro x
    obtain ⟨z, y, h⟩ := hqsurj x
    exact ⟨y, z, by simpa only [add_comm (f z)] using h⟩
  · intro x y h
    obtain ⟨z, hz⟩ := hqinj y x h.symm
    have ht : (x - f z) + (x - f z) = 0 := by
      rw [hz, map_add] at h
      calc
        (x - f z) + (x - f z) = (x + x) - (f z + f z) := by abel
        _ = 0 := sub_eq_zero.mpr h
    obtain ⟨w, _, hw⟩ := htsurj (x - f z) ht
    refine ⟨z + w, ?_⟩
    rw [map_add, hw]
    abel

private theorem shift_power_doubling_conditions
    {B : Type u} [AddCommGroup B] (sigma : Module.End ℤ B) (m : ℕ)
    (heven : ∀ x, ∃ y, (sigma ^ m) x = y + y)
    (htors : ∀ x, x + x = 0 → (sigma ^ m) x = 0) :
    (∀ b, ∃ x y, (1 - sigma) x + (y + y) = b) ∧
    (∀ x y, (1 - sigma) x = y + y → ∃ z, x = z + z) ∧
    (∀ b, b + b = 0 → ∃ x, x + x = 0 ∧ (1 - sigma) x = b) ∧
    (∀ x, x + x = 0 → (1 - sigma) x = 0 → x = 0) := by
  let S : Module.End ℤ B := ∑ i ∈ Finset.range m, sigma ^ i
  have hleft (x : B) : S ((1 - sigma) x) = x - (sigma ^ m) x := by
    have h := congrArg (fun f : Module.End ℤ B => f x) (geom_sum_mul_neg sigma m)
    exact h
  have hright (x : B) : (1 - sigma) (S x) = x - (sigma ^ m) x := by
    have h := congrArg (fun f : Module.End ℤ B => f x) (mul_neg_geom_sum sigma m)
    exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b
    obtain ⟨y, hy⟩ := heven b
    exact ⟨S b, y, by rw [hright, hy, sub_add_cancel]⟩
  · intro x y h
    obtain ⟨z, hz⟩ := heven x
    refine ⟨S y + z, ?_⟩
    have hh := hleft x
    rw [h, map_add, hz] at hh
    have hh' : x = (S y + S y) + (z + z) := (sub_eq_iff_eq_add).mp hh.symm
    rw [hh']
    abel
  · intro b hb
    refine ⟨S b, ?_, ?_⟩
    · rw [← map_add, hb, map_zero]
    · rw [hright, htors b hb, sub_zero]
  · intro x hx hd
    have hh := hleft x
    rw [hd, map_zero, htors x hx, sub_zero] at hh
    exact hh.symm

private theorem doubling_middle_of_exact
    {A B K C D : Type u} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup K] [AddCommGroup C] [AddCommGroup D]
    (f : A →+ B) (g : B →+ K) (i : K →+ C) (j : C →+ D)
    (hfg : ∀ b, g b = 0 ↔ ∃ a, f a = b)
    (hgi : ∀ z, i z = 0 ↔ ∃ b, g b = z)
    (hij : ∀ c, j c = 0 ↔ ∃ z, i z = c)
    (hkinj : ∀ c, j c = 0 → c + c = 0 → c = 0)
    (hksurj : ∀ c, j c = 0 → ∃ d, j d = 0 ∧ d + d = c)
    (hcsurj : ∀ b, ∃ c a, c + c + f a = b)
    (hcinj : ∀ b a, b + b = f a → ∃ c, f c = b) :
    Function.Bijective (fun z : K => z + z) := by
  have kill : ∀ z : K, z + z = 0 → z = 0 := by
    intro z hz
    have hiz : i z = 0 := hkinj (i z) ((hij _).mpr ⟨z, rfl⟩)
      (by rw [← map_add, hz, map_zero])
    obtain ⟨b, hb⟩ := (hgi z).mp hiz
    obtain ⟨a, ha⟩ := (hfg (b+b)).mp (by rw [map_add, hb, hz])
    obtain ⟨c, hc⟩ := hcinj b a ha.symm
    rw [← hb]
    exact (hfg b).mpr ⟨c, hc⟩
  constructor
  · intro x y hxy
    have hz : (x-y) + (x-y) = 0 := by
      have h : (x+x) - (y+y) = 0 := sub_eq_zero.mpr hxy
      calc
        (x-y) + (x-y) = (x+x) - (y+y) := by abel
        _ = 0 := h
    exact sub_eq_zero.mp (kill (x-y) hz)
  · intro z
    obtain ⟨c, hc, hd⟩ := hksurj (i z) ((hij _).mpr ⟨z, rfl⟩)
    obtain ⟨w, hw⟩ := (hij c).mp hc
    have hz : i (z - (w+w)) = 0 := by rw [map_sub, map_add, hw, hd, sub_self]
    obtain ⟨b, hb⟩ := (hgi _).mp hz
    obtain ⟨b', a, ha⟩ := hcsurj b
    have hfa : g (f a) = 0 := (hfg _).mpr ⟨a, rfl⟩
    refine ⟨w + g b', ?_⟩
    have hgb : g b = g b' + g b' := by rw [← ha, map_add, map_add, hfa, add_zero]
    rw [hgb] at hb
    calc
      (w + g b') + (w + g b') = (g b' + g b') + (w + w) := by abel
      _ = z := eq_sub_iff_add_eq.mp hb


private theorem doubling_cofiber_bijective_of_shift_power
    {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] (P : C) (sigma : P ⟶ P)
    (h : ∀ n : ℤ, ∃ m : ℕ,
      (∀ x : HomotopyGroup n P, ∃ y,
        (((inducedMap sigma n).toIntLinearMap) ^ m) x = y + y) ∧
      (∀ x : HomotopyGroup n P, x + x = 0 →
        (((inducedMap sigma n).toIntLinearMap) ^ m) x = 0))
    (n : ℤ) : Function.Bijective
      (fun z : HomotopyGroup n (HasFunctorialCofiber.cofib (𝟙 P - sigma)) => z + z) := by
  let f := 𝟙 P - sigma
  let T := HoCofiberSequence.ofMorphism f
  have conditions (k : ℤ) :
      (∀ x, inducedMap f k x = 0 → x + x = 0 → x = 0) ∧
      (∀ x, inducedMap f k x = 0 → ∃ y, inducedMap f k y = 0 ∧ y + y = x) ∧
      (∀ x, ∃ y z, y + y + inducedMap f k z = x) ∧
      (∀ x y, x + x = inducedMap f k y → ∃ z, inducedMap f k z = x) := by
    obtain ⟨m, he, ht⟩ := h k
    obtain ⟨hqs, hqi, hts, hti⟩ :=
      shift_power_doubling_conditions (inducedMap sigma k).toIntLinearMap m he ht
    have heq : (inducedMap f k) = (1 - (inducedMap sigma k).toIntLinearMap).toAddMonoidHom := by
      ext x
      simp [f, inducedMap, Preadditive.comp_sub]
    rw [heq]
    exact doubling_kernel_cokernel (1 - (inducedMap sigma k).toIntLinearMap).toAddMonoidHom hqs hqi hts hti
  obtain ⟨hki, hks, _, _⟩ := conditions (n - 1)
  obtain ⟨_, _, hcs, hci⟩ := conditions n
  exact doubling_middle_of_exact (inducedMap T.f n) (inducedMap T.g n)
    (connectingHomomorphism T n) (inducedMap T.f (n-1))
    (les_homotopy_exact_f T n) (les_homotopy_exact_g T n)
    (lesHomotopyExactH T n) hki hks hcs hci


private theorem adams_shift_pow_projection
    {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]
    {H : C} (unit : 𝟙_ C ⟶ H) (X : C) (n : ℤ) (m : ℕ)
    (x : HomotopyGroup n (∏ᶜ (adamsResidualSequence unit X).obj)) (s : ℕ) :
    (((inducedMap (adamsResidualSequence unit X).shiftMap n).toIntLinearMap)^m) x ≫
      Pi.π (adamsResidualSequence unit X).obj s =
    x ≫ Pi.π (adamsResidualSequence unit X).obj (s+m) ≫
      adamsTowerMap unit X s (s+m) (Nat.le_add_right s m) := by
  dsimp only [adamsResidualSequence] at *
  induction m generalizing x with
  | zero => simp [Module.End.one_apply]
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    change (x ≫ (adamsResidualSequence unit X).shiftMap) ≫
        Pi.π _ (s+m) ≫ adamsTowerMap unit X s (s+m) _ = _
    simp only [Category.assoc, InverseSequence.shiftMap, Pi.lift_π_assoc]
    change x ≫ Pi.π _ ((s+m)+1) ≫
        adamsTowerStep unit X (s+m) ≫ adamsTowerMap unit X s (s+m) _ = _
    rw [← adamsTowerMap_succ]
    rfl

private theorem adams_shift_power_even
    {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]
    {H : C} (unit : 𝟙_ C ⟶ H) (X : C) (n : ℤ) (m : ℕ)
    (he : ∀ (s : ℕ) (x : HomotopyGroup n (adamsTower unit X (s+m))),
      ∃ y, inducedMap (adamsTowerMap unit X s (s+m) (Nat.le_add_right s m)) n x = y+y)
    (x : HomotopyGroup n (∏ᶜ (adamsResidualSequence unit X).obj)) :
    ∃ y, (((inducedMap (adamsResidualSequence unit X).shiftMap n).toIntLinearMap)^m) x = y+y := by
  classical
  let y (s : ℕ) := (he s (x ≫ Pi.π (adamsResidualSequence unit X).obj (s+m))).choose
  refine ⟨Pi.lift y, ?_⟩
  apply Pi.hom_ext
  intro s
  rw [adams_shift_pow_projection, Preadditive.add_comp, Pi.lift_π]
  dsimp only [y]
  simpa only [inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Category.assoc] using
    (he s (x ≫ Pi.π (adamsResidualSequence unit X).obj (s+m))).choose_spec

private theorem adams_shift_power_torsion
    {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]
    {H : C} (unit : 𝟙_ C ⟶ H) (X : C) (n : ℤ) (m : ℕ)
    (ht : ∀ (s : ℕ) (x : HomotopyGroup n (adamsTower unit X (s+m))), x+x = 0 →
      inducedMap (adamsTowerMap unit X s (s+m) (Nat.le_add_right s m)) n x = 0)
    (x : HomotopyGroup n (∏ᶜ (adamsResidualSequence unit X).obj)) (hx : x+x = 0) :
    (((inducedMap (adamsResidualSequence unit X).shiftMap n).toIntLinearMap)^m) x = 0 := by
  apply Pi.hom_ext
  intro s
  rw [adams_shift_pow_projection, zero_comp]
  have hh := ht s (x ≫ Pi.π (adamsResidualSequence unit X).obj (s+m))
    (by rw [← Preadditive.add_comp, hx, zero_comp])
  simpa only [inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Category.assoc] using hh

private theorem adams_shift_power_of_eventual_mod_two
    {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]
    {H : C} (unit : 𝟙_ C ⟶ H) (X : C) (n : ℤ)
    (he : ∃ m : ℕ, ∀ (s : ℕ) (x : HomotopyGroup n (adamsTower unit X (s+m))),
      ∃ y, inducedMap (adamsTowerMap unit X s (s+m) (Nat.le_add_right s m)) n x = y+y)
    (ht : ∃ m : ℕ, ∀ (s : ℕ) (x : HomotopyGroup n (adamsTower unit X (s+m))), x+x = 0 →
      inducedMap (adamsTowerMap unit X s (s+m) (Nat.le_add_right s m)) n x = 0) :
    ∃ m : ℕ,
      (∀ x : HomotopyGroup n (∏ᶜ (adamsResidualSequence unit X).obj), ∃ y,
        (((inducedMap (adamsResidualSequence unit X).shiftMap n).toIntLinearMap)^m) x = y+y) ∧
      (∀ x : HomotopyGroup n (∏ᶜ (adamsResidualSequence unit X).obj), x+x = 0 →
        (((inducedMap (adamsResidualSequence unit X).shiftMap n).toIntLinearMap)^m) x = 0) := by
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := ht
  refine ⟨a+b, ?_, ?_⟩
  · intro x
    rw [pow_add, Module.End.mul_apply]
    exact adams_shift_power_even unit X n a ha _
  · intro x hx
    rw [pow_add, Module.End.mul_apply, adams_shift_power_torsion unit X n b hb x hx, map_zero]

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Milnor

open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.StableHomotopy.Spectra

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Detection

set_option backward.isDefEq.respectTransparency false

private noncomputable def pointSpectrum : Prespectrum.{0} where
  level _ := { space := TopCat.of PUnit, point := PUnit.unit }
  bond _ := ContinuousMap.const _ PUnit.unit
  bond_point _ _ := rfl
  bond_zero _ _ := rfl
  bond_one _ _ := rfl

private noncomputable def toPoint (X : Prespectrum.{0}) : X ⟶ pointSpectrum where
  level _ := ContinuousMap.const _ PUnit.unit
  point _ := rfl
  bond _ _ _ := rfl

private noncomputable def fromPoint (X : Prespectrum.{0}) : pointSpectrum ⟶ X where
  level n := ContinuousMap.const _ (X.level n).point
  point _ := rfl
  bond n _ t := (X.bond_point n t).symm

private theorem point_source_isZero : IsZero (sourceLocalization.obj pointSpectrum) := by
  let K : SourceCategory.{0} ⥤ SourceCategory.{0} :=
    (Functor.const SourceCategory.{0}).obj (sourceLocalization.obj pointSpectrum)
  let τ₀ : sourceLocalization ⋙ K ⟶ sourceLocalization ⋙ 𝟭 _ :=
    { app X := sourceLocalization.map (fromPoint X)
      naturality := by
        intro X Y f
        change (𝟙 (sourceLocalization.obj pointSpectrum)) ≫ sourceLocalization.map (fromPoint Y) =
          sourceLocalization.map (fromPoint X) ≫ sourceLocalization.map f
        rw [Category.id_comp, ← Functor.map_comp]
        congr 1
        apply Prespectrum.Hom.ext
        funext n
        apply ContinuousMap.ext
        intro x
        exact (f.point n).symm }
  let σ₀ : sourceLocalization ⋙ 𝟭 _ ⟶ sourceLocalization ⋙ K :=
    { app X := sourceLocalization.map (toPoint X)
      naturality := by
        intro X Y f
        change sourceLocalization.map f ≫ sourceLocalization.map (toPoint Y) =
          sourceLocalization.map (toPoint X) ≫ (𝟙 (sourceLocalization.obj pointSpectrum))
        rw [Category.comp_id, ← Functor.map_comp]
        congr 1 }
  let τ := Localization.Construction.natTransExtension τ₀
  let σ := Localization.Construction.natTransExtension σ₀
  have hτ : τ.app (sourceLocalization.obj pointSpectrum) = 𝟙 (sourceLocalization.obj pointSpectrum) := by
    rw [Localization.Construction.natTransExtension_app]
    change sourceLocalization.map (fromPoint pointSpectrum) = 𝟙 (sourceLocalization.obj pointSpectrum)
    rw [← sourceLocalization.map_id pointSpectrum]
    congr 1
  have hσ : σ.app (sourceLocalization.obj pointSpectrum) = 𝟙 (sourceLocalization.obj pointSpectrum) := by
    rw [Localization.Construction.natTransExtension_app]
    change sourceLocalization.map (toPoint pointSpectrum) = 𝟙 (sourceLocalization.obj pointSpectrum)
    rw [← sourceLocalization.map_id pointSpectrum]
    congr 1
  refine ⟨?_, ?_⟩
  · intro Y
    refine ⟨⟨⟨τ.app Y⟩, ?_⟩⟩
    intro f
    have h := τ.naturality f
    change (𝟙 _) ≫ τ.app Y = τ.app (sourceLocalization.obj pointSpectrum) ≫ f at h
    exact (Category.id_comp f).symm.trans ((congrArg (fun z => z ≫ f) hτ).symm.trans
      (h.symm.trans (Category.id_comp _)))
  · intro Y
    refine ⟨⟨⟨σ.app Y⟩, ?_⟩⟩
    intro f
    have h := σ.naturality f
    change f ≫ σ.app (sourceLocalization.obj pointSpectrum) = σ.app Y ≫ (𝟙 _) at h
    exact (Category.comp_id f).symm.trans ((congrArg (fun z => f ≫ z) hσ).symm.trans (h.trans (Category.comp_id _)))

private theorem source_isZero_of_stableHomotopy (X : Prespectrum.{0})
    (hX : ∀ d : ℤ, Subsingleton (Prespectrum.StableHomotopy X d)) :
    IsZero (sourceLocalization.obj X) := by
  let f : X ⟶ X := toPoint X ≫ fromPoint X
  have hf : Prespectrum.stableEquivalences f := by
    intro d
    letI := hX d
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨y, Subsingleton.elim _ _⟩⟩
  let e := Localization.Construction.wIso f hf
  let i : sourceLocalization.obj X ≅ sourceLocalization.obj pointSpectrum :=
    { hom := sourceLocalization.map (toPoint X)
      inv := sourceLocalization.map (fromPoint X) ≫ e.inv
      hom_inv_id := by
        rw [← Category.assoc, ← Functor.map_comp]
        exact e.hom_inv_id
      inv_hom_id := point_source_isZero.eq_of_src _ _ }
  exact point_source_isZero.of_iso i

universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : Mod2EilenbergMacLane (C := C)}

private theorem homotopy_detects_zero (S : SourceComparison completionModel H) (Z : C)
    (hZ : ∀ d : ℤ, Subsingleton (HomotopyGroup d Z)) : IsZero Z := by
  let W := S.equivalence.inverse.obj Z
  let e : S.equivalence.functor.obj (completedLocalization.obj W.spectrum) ≅ Z :=
    S.equivalence.functor.mapIso
      (KIP126.AdamsSynthetic.Standard.SphereConvergence.Local.localReflectionIso W.spectrum W.isLocal) ≪≫
      S.equivalence.counitIso.app Z
  have h : ∀ d : ℤ, Subsingleton
      (Prespectrum.StableHomotopy (completionModel.replacement.obj W.spectrum) d) := by
    intro d
    letI := hZ d
    have hinj : Function.Injective (fun x : HomotopyGroup d
        (S.equivalence.functor.obj (completedLocalization.obj W.spectrum)) => x ≫ e.hom) :=
      fun x y he => (cancel_mono e.hom).1 he
    have hs := hinj.subsingleton
    letI : Subsingleton (HomotopyGroup d
        (S.equivalence.functor.obj (completionModel.localization.obj W.spectrum))) := by
      simpa only [completedLocalization] using hs
    exact (S.homotopy W.spectrum d).symm.injective.subsingleton
  have hz := source_isZero_of_stableHomotopy (completionModel.replacement.obj W.spectrum) h
  have hz' : IsZero (completedLocalization.obj W.spectrum) :=
    ⟨fun X => hz.unique_to _, fun X => hz.unique_from _⟩
  apply (IsZero.iff_id_eq_zero Z).mpr
  apply S.equivalence.inverse.map_injective
  have hw : IsZero W := hz'.of_iso
    (KIP126.AdamsSynthetic.Standard.SphereConvergence.Local.localReflectionIso W.spectrum W.isLocal).symm
  exact (S.equivalence.inverse.map_id Z).trans (hw.eq_of_src _ _)

private theorem homotopy_detects_iso (S : SourceComparison completionModel H) {X Y : C} (f : X ⟶ Y)
    (hf : ∀ d : ℤ, Function.Bijective (inducedMap f d)) : IsIso f := by
  let T := HoCofiberSequence.ofMorphism f
  have hc : IsZero (HasFunctorialCofiber.cofib f) := by
    apply homotopy_detects_zero S
    intro d
    apply subsingleton_of_forall_eq 0
    intro z
    have hz : connectingHomomorphism T d z = 0 := by
      apply (hf (d - 1)).1
      rw [map_zero]
      exact (lesHomotopyExactH T d _).mpr ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := (les_homotopy_exact_g T d z).mp hz
    obtain ⟨x, hx⟩ := (hf d).2 y
    rw [← hy, ← hx]
    change (x ≫ f) ≫ HasFunctorialCofiber.cofibι f = 0
    change (x ≫ T.f) ≫ T.g = 0
    rw [Category.assoc, T.fg_zero, comp_zero]
  exact (CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    (HasFunctorialCofiber.cofib_distinguished f)).mp hc

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Detection


namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Milnor
open KIP126.StableHomotopy.Cohomology KIP126.StableHomotopy.Spectra
universe u v
set_option backward.isDefEq.respectTransparency false
private theorem doubling_fiber_isIso_of_shift_power
    {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] {H : Mod2EilenbergMacLane (C := C)}
    (S : SourceComparison completionModel H) (P : C) (sigma : P ⟶ P)
    (h : ∀ n : ℤ, ∃ m : ℕ,
      (∀ x : HomotopyGroup n P, ∃ y,
        (((inducedMap sigma n).toIntLinearMap) ^ m) x = y + y) ∧
      (∀ x : HomotopyGroup n P, x + x = 0 →
        (((inducedMap sigma n).toIntLinearMap) ^ m) x = 0)) :
    IsIso (𝟙 (fiber (𝟙 P - sigma)) + 𝟙 (fiber (𝟙 P - sigma))) := by
  let Z := HasFunctorialCofiber.cofib (𝟙 P - sigma)
  haveI : IsIso (𝟙 Z + 𝟙 Z) := by
    apply Detection.homotopy_detects_iso S
    intro n
    have hb := doubling_cofiber_bijective_of_shift_power P sigma h n
    simpa only [inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Preadditive.comp_add, Category.comp_id] using hb
  have hmap : IsIso ((shiftFunctor C (-1 : ℤ)).map (𝟙 Z + 𝟙 Z)) := by infer_instance
  simpa only [Functor.map_add, (shiftFunctor C (-1 : ℤ)).map_id Z, fiber, Z] using hmap
end KIP126.AdamsSynthetic.Standard.SphereConvergence.Milnor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.ModTwo
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
variable [HasFunctorialCofiber (C := C)]

/-- A zero Moore comparison forces every image to be divisible by two.
Only the actual cofiber inclusion square is used; the comparison is not
required to equal the independently selected cofiber-map filler. -/
private theorem image_even_of_moore_square_zero {X Y : C} (f : X ⟶ Y)
    (c : HasFunctorialCofiber.cofib (𝟙 X + 𝟙 X) ⟶
      HasFunctorialCofiber.cofib (𝟙 Y + 𝟙 Y))
    (hι : f ≫ HasFunctorialCofiber.cofibι (𝟙 Y + 𝟙 Y) =
      HasFunctorialCofiber.cofibι (𝟙 X + 𝟙 X) ≫ c)
    (n : ℤ) (hzero : ∀ z, inducedMap c n z = 0)
    (x : HomotopyGroup n X) :
    ∃ y : HomotopyGroup n Y, inducedMap f n x = y + y := by
  have hz : inducedMap (HasFunctorialCofiber.cofibι (𝟙 Y + 𝟙 Y)) n
      (inducedMap f n x) = 0 := by
    change (x ≫ f) ≫ HasFunctorialCofiber.cofibι (𝟙 Y + 𝟙 Y) = 0
    rw [Category.assoc, hι, ← Category.assoc]
    exact hzero (x ≫ HasFunctorialCofiber.cofibι (𝟙 X + 𝟙 X))
  obtain ⟨y, hy⟩ := (les_homotopy_exact_f (HoCofiberSequence.ofMorphism (𝟙 Y + 𝟙 Y))
    n (inducedMap f n x)).mp hz
  change HomotopyGroup n Y at y
  refine ⟨y, ?_⟩
  change x ≫ f = y + y
  change y ≫ (𝟙 Y + 𝟙 Y) = x ≫ f at hy
  simpa only [Preadditive.comp_add, Category.comp_id] using hy.symm

/-- A zero Moore comparison kills two-torsion one homotopy degree lower.
The actual boundary square gives the connecting-map naturality; no
functoriality of a chosen cofiber-map operation is assumed. -/
private theorem torsion_zero_of_moore_square_zero {X Y : C} (f : X ⟶ Y)
    (c : HasFunctorialCofiber.cofib (𝟙 X + 𝟙 X) ⟶
      HasFunctorialCofiber.cofib (𝟙 Y + 𝟙 Y))
    (hδ : c ≫ HasFunctorialCofiber.cofibδ (𝟙 Y + 𝟙 Y) =
      HasFunctorialCofiber.cofibδ (𝟙 X + 𝟙 X) ≫ f⟦(1 : ℤ)⟧')
    (m n : ℤ) (hmn : m - 1 = n)
    (hzero : ∀ z, inducedMap c m z = 0)
    (x : HomotopyGroup n X) (hx : x + x = 0) : inducedMap f n x = 0 := by
  subst n
  have hx' : inducedMap (𝟙 X + 𝟙 X) (m-1) x = 0 := by
    simpa only [inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Preadditive.comp_add, Category.comp_id] using hx
  obtain ⟨z, hz⟩ := (lesHomotopyExactH (HoCofiberSequence.ofMorphism (𝟙 X + 𝟙 X)) m x).mp hx'
  have hnat := connectingHomomorphism_naturality
    (HoCofiberSequence.ofMorphism (𝟙 X + 𝟙 X))
    (HoCofiberSequence.ofMorphism (𝟙 Y + 𝟙 Y)) f c hδ m z
  exact (congrArg (inducedMap f (m-1)) hz).symm.trans
    (hnat.symm.trans ((congrArg
      (connectingHomomorphism (HoCofiberSequence.ofMorphism (𝟙 Y + 𝟙 Y)) m)
      (hzero z)).trans (map_zero _)))

/-- Degreewise Moore comparisons yield exactly the two group-theoretic
pro-zero conditions for the actual tower, with the correct degree shift.
The maps `c` are existential comparison witnesses for the actual long
transition; they need not be the independently selected `cofibMap`. -/
private theorem adams_even_torsion_of_moore_proZero {H : C} (unit : 𝟙_ C ⟶ H) (X : C)
    (hzero : ∀ n : ℤ, ∃ m : ℕ, 0 < m ∧ ∀ s : ℕ,
      ∃ c : HasFunctorialCofiber.cofib
          (𝟙 (adamsTower unit X (s+m)) + 𝟙 (adamsTower unit X (s+m))) ⟶
        HasFunctorialCofiber.cofib (𝟙 (adamsTower unit X s) + 𝟙 (adamsTower unit X s)),
      (adamsTowerMap unit X s (s+m) (Nat.le_add_right s m)) ≫
          HasFunctorialCofiber.cofibι (𝟙 (adamsTower unit X s) + 𝟙 (adamsTower unit X s)) =
        HasFunctorialCofiber.cofibι
          (𝟙 (adamsTower unit X (s+m)) + 𝟙 (adamsTower unit X (s+m))) ≫ c ∧
      c ≫ HasFunctorialCofiber.cofibδ
          (𝟙 (adamsTower unit X s) + 𝟙 (adamsTower unit X s)) =
        HasFunctorialCofiber.cofibδ
          (𝟙 (adamsTower unit X (s+m)) + 𝟙 (adamsTower unit X (s+m))) ≫
          (adamsTowerMap unit X s (s+m) (Nat.le_add_right s m))⟦(1 : ℤ)⟧' ∧
      ∀ z, inducedMap c n z = 0) :
    (∀ n : ℤ, ∃ m : ℕ, 0 < m ∧ ∀ s : ℕ,
      ∀ x : HomotopyGroup n (adamsTower unit X (s+m)),
      ∃ y : HomotopyGroup n (adamsTower unit X s),
        inducedMap (adamsTowerMap unit X s (s+m) (Nat.le_add_right s m)) n x = y+y) ∧
    (∀ n : ℤ, ∃ m : ℕ, 0 < m ∧ ∀ s : ℕ,
      ∀ x : HomotopyGroup n (adamsTower unit X (s+m)), x+x=0 →
        inducedMap (adamsTowerMap unit X s (s+m) (Nat.le_add_right s m)) n x = 0) := by
  constructor
  · intro n
    obtain ⟨m, hm, hz⟩ := hzero n
    refine ⟨m, hm, fun s => ?_⟩
    obtain ⟨c, hι, _, hc⟩ := hz s
    exact image_even_of_moore_square_zero _ c hι n hc
  · intro n
    obtain ⟨m, hm, hz⟩ := hzero (n+1)
    refine ⟨m, hm, fun s => ?_⟩
    obtain ⟨c, _, hδ, hc⟩ := hz s
    exact torsion_zero_of_moore_square_zero _ c hδ (n+1) n (by omega) hc

end KIP126.AdamsSynthetic.Standard.SphereConvergence.ModTwo

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Milnor
open KIP126.StableHomotopy.Cohomology KIP126.StableHomotopy.Spectra
universe u v
set_option backward.isDefEq.respectTransparency false
private theorem adams_fiber_doubling_of_moore_proZero
    {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]
    {H : Mod2EilenbergMacLane (C := C)} (S : SourceComparison completionModel H) (X : C)
    (hzero : ∀ n : ℤ, ∃ m : ℕ, 0 < m ∧ ∀ s : ℕ,
      ∃ c : HasFunctorialCofiber.cofib
          (𝟙 (adamsTower H.unit X (s+m)) + 𝟙 (adamsTower H.unit X (s+m))) ⟶
        HasFunctorialCofiber.cofib (𝟙 (adamsTower H.unit X s) + 𝟙 (adamsTower H.unit X s)),
      (adamsTowerMap H.unit X s (s+m) (Nat.le_add_right s m)) ≫
          HasFunctorialCofiber.cofibι (𝟙 (adamsTower H.unit X s) + 𝟙 (adamsTower H.unit X s)) =
        HasFunctorialCofiber.cofibι
          (𝟙 (adamsTower H.unit X (s+m)) + 𝟙 (adamsTower H.unit X (s+m))) ≫ c ∧
      c ≫ HasFunctorialCofiber.cofibδ
          (𝟙 (adamsTower H.unit X s) + 𝟙 (adamsTower H.unit X s)) =
        HasFunctorialCofiber.cofibδ
          (𝟙 (adamsTower H.unit X (s+m)) + 𝟙 (adamsTower H.unit X (s+m))) ≫
          (adamsTowerMap H.unit X s (s+m) (Nat.le_add_right s m))⟦(1 : ℤ)⟧' ∧
      ∀ z, inducedMap c n z = 0) :
    IsIso (𝟙 (fiber (adamsResidualSequence H.unit X).oneSubShift) +
      𝟙 (fiber (adamsResidualSequence H.unit X).oneSubShift)) := by
  obtain ⟨he, ht⟩ := ModTwo.adams_even_torsion_of_moore_proZero H.unit X hzero
  apply doubling_fiber_isIso_of_shift_power S (∏ᶜ (adamsResidualSequence H.unit X).obj)
    (adamsResidualSequence H.unit X).shiftMap
  intro n
  obtain ⟨a, _, ha⟩ := he n
  obtain ⟨b, _, hb⟩ := ht n
  exact adams_shift_power_of_eventual_mod_two H.unit X n ⟨a, ha⟩ ⟨b, hb⟩
end KIP126.AdamsSynthetic.Standard.SphereConvergence.Milnor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Nilpotence
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
variable [HasFunctorialCofiber (C := C)]

/-- A unital action kills one step of every actual Adams tower. -/
private theorem module_length_one {H N : C} (unit : 𝟙_ C ⟶ H)
    (act : H ⊗ N ⟶ N) (hact : adamsUnit unit N ≫ act = 𝟙 N)
    (X : C) (s : ℕ) (f : adamsTower unit X s ⟶ N) :
    adamsTowerMap unit X s (s + 1) (Nat.le_succ s) ≫ f = 0 := by
  rw [adamsTowerMap_succ unit X s s le_rfl, adamsTowerMap_self, Category.comp_id]
  calc
    adamsTowerStep unit X s ≫ f =
      adamsTowerStep unit X s ≫ f ≫ adamsUnit unit N ≫ act := by rw [hact]; simp
    _ = adamsTowerStep unit X s ≫ adamsUnit unit (adamsTower unit X s) ≫
        (H ◁ f) ≫ act := by rw [← Category.assoc f, adamsUnit_naturality]; simp only [Category.assoc]
    _ = 0 := by rw [← Category.assoc, ← Category.assoc, adamsTowerStep, fiberι_comp_eq_zero]; simp

/-- The universal tower-annihilation length adds across a distinguished triangle. -/
private theorem extension_length_add {H : C} (unit : 𝟙_ C ⟶ H)
    (T : Triangle C) (hT : T ∈ distTriang C) (a b : ℕ)
    (ha : ∀ (X : C) (s : ℕ) (f : adamsTower unit X s ⟶ T.obj₁),
      adamsTowerMap unit X s (s + a) (Nat.le_add_right s a) ≫ f = 0)
    (hb : ∀ (X : C) (s : ℕ) (f : adamsTower unit X s ⟶ T.obj₃),
      adamsTowerMap unit X s (s + b) (Nat.le_add_right s b) ≫ f = 0)
    (X : C) (s : ℕ) (f : adamsTower unit X s ⟶ T.obj₂) :
    adamsTowerMap unit X s (s + (a + b)) (Nat.le_add_right s (a+b)) ≫ f = 0 := by
  have hf : (adamsTowerMap unit X s (s+b) (Nat.le_add_right s b) ≫ f) ≫ T.mor₂ = 0 := by
    simpa only [Category.assoc] using hb X s (f ≫ T.mor₂)
  obtain ⟨g, hg⟩ := T.coyoneda_exact₂ hT _ hf
  have hkill := ha X (s+b) g
  have he : (s+b)+a = s+(a+b) := by omega
  have hh : adamsTowerMap unit X s ((s+b)+a) (by omega) ≫ f = 0 := by
    rw [← adamsTowerMap_comp unit X s (s+b) ((s+b)+a)
      (Nat.le_add_right s b) (Nat.le_add_right (s+b) a), Category.assoc, hg,
      ← Category.assoc, hkill, zero_comp]
  exact (Eq.ndrec (motive := fun k => ∀ hk : s ≤ k,
    adamsTowerMap unit X s k hk ≫ f = 0) (fun _ => hh) he) _

/-- Exactness gives exponent four, not exponent two, on a Moore cofiber. -/
private theorem doubling_cofiber_four_nsmul (X : C) (n : ℤ)
    (z : HomotopyGroup n (HasFunctorialCofiber.cofib (𝟙 X + 𝟙 X))) :
    (4 : ℕ) • z = 0 := by
  let T := HoCofiberSequence.ofMorphism (𝟙 X + 𝟙 X)
  have hδ : (z + z) ≫ T.h = 0 := by
    have hz := congrArg (fun f => z ≫ f) T.hf_shift_zero
    simpa [T, HoCofiberSequence.ofMorphism, Functor.map_add, Preadditive.comp_add,
      Preadditive.add_comp] using hz
  obtain ⟨y, hy⟩ := (Triangle.mk T.f T.g T.h).coyoneda_exact₃ T.distinguished (z+z) hδ
  have hyzero : (y+y) ≫ T.g = 0 := by
    have hh := congrArg (fun f => y ≫ f) T.fg_zero
    simpa [T, HoCofiberSequence.ofMorphism, Preadditive.comp_add,
      Preadditive.add_comp] using hh
  change z+z = y ≫ HasFunctorialCofiber.cofibι (𝟙 X + 𝟙 X) at hy
  change (y+y) ≫ HasFunctorialCofiber.cofibι (𝟙 X + 𝟙 X) = 0 at hyzero
  have he : (z+z)+(z+z) = 0 := by rw [hy]; simpa only [Preadditive.add_comp] using hyzero
  simpa only [show (4 : ℕ) = 2*2 by decide, mul_nsmul, two_nsmul] using he

/-- A homotopy-detecting truncation transfers universal length to actual tower maps. -/
private theorem length_detected_on_homotopy {H N : C} (unit : 𝟙_ C ⟶ H)
    (m : ℕ)
    (hN : ∀ (X : C) (s : ℕ) (f : adamsTower unit X s ⟶ N),
      adamsTowerMap unit X s (s + m) (Nat.le_add_right s m) ≫ f = 0)
    (X : C) (s : ℕ) (n : ℤ) (p : adamsTower unit X s ⟶ N)
    (hp : Function.Injective (inducedMap p n)) :
    ∀ x : HomotopyGroup n (adamsTower unit X (s+m)),
      inducedMap (adamsTowerMap unit X s (s+m) (Nat.le_add_right s m)) n x = 0 := by
  intro x
  apply hp
  change (x ≫ adamsTowerMap unit X s (s+m) _) ≫ p = (0 : HomotopyGroup n _) ≫ p
  rw [Category.assoc, hN, comp_zero, zero_comp]

/-- All finite extension lengths in a Postnikov diagram add, before any source recognition. -/
private theorem finite_extension_length {H : C} (unit : 𝟙_ C ⟶ H)
    (P L : ℕ → C) (i : ∀ k, L k ⟶ P (k+1)) (q : ∀ k, P (k+1) ⟶ P k)
    (δ : ∀ k, P k ⟶ (L k)⟦(1 : ℤ)⟧)
    (hdist : ∀ k, Triangle.mk (i k) (q k) (δ k) ∈ distTriang C)
    (hzero : IsZero (P 0))
    (hL : ∀ (k : ℕ) (X : C) (s : ℕ) (f : adamsTower unit X s ⟶ L k),
      adamsTowerMap unit X s (s+2) (Nat.le_add_right s 2) ≫ f = 0)
    (k : ℕ) (X : C) (s : ℕ) (f : adamsTower unit X s ⟶ P k) :
    adamsTowerMap unit X s (s + 2*k) (Nat.le_add_right s (2*k)) ≫ f = 0 := by
  induction k generalizing X s with
  | zero => exact hzero.eq_of_tgt _ _
  | succ k ih =>
    have hh := extension_length_add unit (Triangle.mk (i k) (q k) (δ k)) (hdist k)
      2 (2*k) (hL k) (fun X s f => ih X s f) X s f
    have he : s+(2+2*k) = s+2*(k+1) := by omega
    exact (Eq.ndrec (motive := fun t => ∀ ht : s ≤ t,
      adamsTowerMap unit X s t ht ≫ f = 0) (fun _ => hh) he) _

/-- The specified HF₂ object itself has universal Adams length one. -/
private theorem hf2_length_one (H : Mod2EilenbergMacLane (C := C))
    (R : Mod2RingStructure H)
    (X : C) (s : ℕ) (f : adamsTower H.unit X s ⟶ H.HF2) :
    adamsTowerMap H.unit X s (s+1) (Nat.le_succ s) ≫ f = 0 := by
  apply module_length_one H.unit R.monoid.mul _ X s f
  letI := R.monoid
  dsimp [adamsUnit]
  rw [Category.assoc, ← R.one_eq, MonObj.one_mul, Iso.inv_hom_id]

/-- The actual Moore cofiber preserves negative homotopy vanishing. -/
private theorem doubling_cofiber_connective (X : C)
    (hX : ∀ n : ℤ, n < 0 → Subsingleton (HomotopyGroup n X)) :
    ∀ n : ℤ, n < 0 →
      Subsingleton (HomotopyGroup n (HasFunctorialCofiber.cofib (𝟙 X + 𝟙 X))) := by
  intro n hn
  let T := HoCofiberSequence.ofMorphism (𝟙 X + 𝟙 X)
  have hz (z : HomotopyGroup n T.Z) : z = 0 := by
    letI : Subsingleton (HomotopyGroup n T.Y) := hX n hn
    letI : Subsingleton (HomotopyGroup (n-1) T.X) := hX (n-1) (by omega)
    have hδ : connectingHomomorphism T n z = 0 := Subsingleton.elim _ _
    obtain ⟨y, hy⟩ := (les_homotopy_exact_g T n z).mp hδ
    have hy0 : y = 0 := Subsingleton.elim _ _
    simpa only [hy0, map_zero] using hy.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Nilpotence

open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.StableHomotopy.Spectra
open scoped unitInterval

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.Local
set_option backward.isDefEq.respectTransparency false

private theorem desuspension_wellBased {X : Prespectrum.{0}} (hX : X.IsWellBased) :
    X.desuspension.IsWellBased := by
  intro n
  cases n with
  | zero =>
    change BasedSpace.IsWellBased { space := TopCat.of PUnit, point := PUnit.unit }
    constructor
    · change IsClosed ({PUnit.unit} : Set PUnit)
      exact isClosed_discrete _
    · intro Y f p hp
      refine ⟨p.comp ⟨Prod.snd, continuous_snd⟩, ?_, ?_⟩
      · intro x
        exact hp.trans (congrArg f (show PUnit.unit = x from Subsingleton.elim _ _))
      · intro t
        rfl
  | succ n => exact hX n

private theorem desuspensionIter_wellBased (n : ℕ) :
    ((Prespectrum.desuspension^[n]) sourceHF2.spectrum).IsWellBased := by
  induction n with
  | zero => exact fun k => (sourceHF2.good k).2.1
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact desuspension_wellBased ih

/-- Reflection sends an actual isomorphism in the ordinary stable source to
an isomorphism between the same specified completion objects. -/
private noncomputable def completionIsoOfSourceIso {X Y : Prespectrum.{0}}
    (e : sourceLocalization.obj X ≅ sourceLocalization.obj Y) :
    completedLocalization.obj X ≅ completedLocalization.obj Y := by
  let X' := completedLocalization.obj X
  let Y' := completedLocalization.obj Y
  let uX := sourceLocalization.map (completionModel.unit.app X)
  let uY := sourceLocalization.map (completionModel.unit.app Y)
  let f := Classical.choose ((completionModel.universal X Y').2 (e.hom ≫ uY))
  have hf := Classical.choose_spec ((completionModel.universal X Y').2 (e.hom ≫ uY))
  let g := Classical.choose ((completionModel.universal Y X').2 (e.inv ≫ uX))
  have hg := Classical.choose_spec ((completionModel.universal Y X').2 (e.inv ≫ uX))
  change uX ≫ f = e.hom ≫ uY at hf
  change uY ≫ g = e.inv ≫ uX at hg
  refine ⟨f, g, ?_, ?_⟩
  · apply (completionModel.universal X X').1
    change uX ≫ (f ≫ g) = uX ≫ 𝟙 (sourceLocalization.obj (completionModel.replacement.obj X))
    rw [← Category.assoc, hf, Category.assoc, hg]
    simp
  · apply (completionModel.universal Y Y').1
    change uY ≫ (g ≫ f) = uY ≫ 𝟙 (sourceLocalization.obj (completionModel.replacement.obj Y))
    rw [← Category.assoc, hg, Category.assoc, hf]
    simp

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} (S : SourceComparison completionModel H)

/-- An ordinary stable-source cancellation, followed by the fixed reflection
and the same suspension comparison, recognizes one negative shift. -/
private noncomputable def completed_desuspension_comparison (X : Prespectrum.{0})
    (hX : X.IsWellBased)
    (e : sourceLocalization.obj X.desuspension.suspension ≅ sourceLocalization.obj X) :
    S.equivalence.functor.obj (completedLocalization.obj X.desuspension) ≅
      (shiftFunctor C (-1 : ℤ)).obj
        (S.equivalence.functor.obj (completedLocalization.obj X)) :=
  ((shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).app _).symm ≪≫
    (shiftFunctor C (-1 : ℤ)).mapIso
      ((S.suspension X.desuspension (desuspension_wellBased hX)).symm ≪≫
        S.equivalence.functor.mapIso (completionIsoOfSourceIso e))

private noncomputable def completed_negative_shift_comparison
    (hcancel : ∀ n : ℕ, Nonempty
      (sourceLocalization.obj (((Prespectrum.desuspension^[n]) sourceHF2.spectrum).desuspension.suspension) ≅
        sourceLocalization.obj ((Prespectrum.desuspension^[n]) sourceHF2.spectrum))) :
    ∀ n : ℕ,
      S.equivalence.functor.obj
        (completedLocalization.obj ((Prespectrum.desuspension^[n]) sourceHF2.spectrum)) ≅
          (shiftFunctor C (-(n : ℤ))).obj H.HF2
  | 0 => S.hf2Iso ≪≫ (shiftFunctorZero C ℤ).symm.app H.HF2
  | n + 1 =>
    eqToIso (by rw [Function.iterate_succ_apply']) ≪≫
      completed_desuspension_comparison S ((Prespectrum.desuspension^[n]) sourceHF2.spectrum)
        (desuspensionIter_wellBased n) (Classical.choice (hcancel n)) ≪≫
      (shiftFunctor C (-1 : ℤ)).mapIso (completed_negative_shift_comparison hcancel n) ≪≫
      ((shiftFunctorAdd' C (-(n : ℤ)) (-1 : ℤ) (-((n + 1 : ℕ) : ℤ)) (by omega)).app H.HF2).symm

end KIP126.AdamsSynthetic.Standard.SphereConvergence.Local


open CategoryTheory Topology
open scoped unitInterval
namespace KIP126.StableHomotopy.Spectra.Prespectrum
universe u
private theorem applicabilityStabilizeLoopHomotopic (P : Prespectrum.{u}) (n r : ℕ)
    (p q : GenLoop (Fin r) (P.level n) (P.level n).point) (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (stabilizeLoop P n r p) (stabilizeLoop P n r q) := by
  obtain ⟨H⟩ := h
  refine ⟨{ toFun := fun t => P.bond n (H (t.1,fun i => t.2 i.succ),t.2 0)
            continuous_toFun := (P.bond n).continuous.comp
              ((H.continuous.comp (continuous_fst.prodMk
                (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd))).prodMk
                  ((continuous_apply 0).comp continuous_snd))
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    change P.bond n (H (0,_),_) = _
    rw [H.apply_zero]
    rfl
  · intro t
    change P.bond n (H (1,_),_) = _
    rw [H.apply_one]
    rfl
  · intro s t ht
    obtain ⟨i,hi⟩ := ht
    induction i using Fin.cases with
    | zero =>
      rcases hi with h | h
      · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
        rw [h,P.bond_zero,P.bond_zero]
      · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
        rw [h,P.bond_one,P.bond_one]
    | succ j =>
      change P.bond n (H (s,_),_) = P.bond n (p _,_)
      rw [H.eq_fst s ⟨j,hi⟩]
      rfl


/-- Deleting the first level is cofinal and shifts the displayed stable
integer degree by minus one. The equivalence is natural in every spectrum map. -/
private theorem stable_tail_shift :
    ∃ e : ∀ (X : Prespectrum.{0}) (d : ℤ),
      StableHomotopy X.tail d ≃ StableHomotopy X (d-1),
      ∀ {X Y} (f : X ⟶ Y) (d : ℤ) (a : StableHomotopy X.tail d),
        e Y d (stableHomotopyMap (tailMap f) d a)=
          stableHomotopyMap f (d-1) (e X d a) := by
  let L (X : Prespectrum.{0}) (d : ℤ) (a : Representative X.tail d) :
      Representative X (d-1) :=
    ⟨a.stage+1,a.dimension,by have := a.degree; omega,a.loop⟩
  let R (X : Prespectrum.{0}) (d : ℤ) (a : Representative X (d-1)) :
      Representative X.tail d :=
    ⟨a.stage,a.dimension+1,by have := a.degree; omega,
      stabilizeLoop X a.stage a.dimension a.loop⟩
  have hL (X : Prespectrum.{0}) (d : ℤ) (a b : Representative X.tail d)
      (h : StableRelation X.tail d a b) :
      Quot.mk (StableRelation X (d-1)) (L X d a)=Quot.mk _ (L X d b) := by
    cases h with
    | homotopy p hp => exact Quot.sound (StableRelation.homotopy (L X d a) p hp)
    | stabilization => exact Quot.sound (StableRelation.stabilization (L X d a))
  have hR (X : Prespectrum.{0}) (d : ℤ) (a b : Representative X (d-1))
      (h : StableRelation X (d-1) a b) :
      Quot.mk (StableRelation X.tail d) (R X d a)=Quot.mk _ (R X d b) := by
    cases h with
    | homotopy p hp =>
      exact Quot.sound (StableRelation.homotopy (R X d a)
        (stabilizeLoop X a.stage a.dimension p) (applicabilityStabilizeLoopHomotopic X _ _ _ _ hp))
    | stabilization => exact Quot.sound (StableRelation.stabilization (R X d a))
  let e (X : Prespectrum.{0}) (d : ℤ) : StableHomotopy X.tail d ≃ StableHomotopy X (d-1) :=
    { toFun := Quot.lift (fun a => Quot.mk _ (L X d a)) (hL X d)
      invFun := Quot.lift (fun a => Quot.mk _ (R X d a)) (hR X d)
      left_inv := by
        intro a
        refine Quot.inductionOn a ?_
        intro a
        exact (Quot.sound (StableRelation.stabilization a)).symm
      right_inv := by
        intro a
        refine Quot.inductionOn a ?_
        intro a
        exact (Quot.sound (StableRelation.stabilization a)).symm }
  refine ⟨e,?_⟩
  intro X Y f d a
  refine Quot.inductionOn a ?_
  intro a
  rfl

private theorem stableEquivalences_tail_iff {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    stableEquivalences (tailMap f) ↔ stableEquivalences f := by
  obtain ⟨e,he⟩ := stable_tail_shift
  have equiv_transport (d : ℤ) : Function.Bijective (stableHomotopyMap (tailMap f) d) ↔
      Function.Bijective (stableHomotopyMap f (d-1)) := by
    constructor
    · intro h
      constructor
      · intro a b hab
        obtain ⟨a,rfl⟩ := (e X d).surjective a
        obtain ⟨b,rfl⟩ := (e X d).surjective b
        apply congrArg (e X d)
        apply h.1
        apply (e Y d).injective
        simpa only [he] using hab
      · intro b
        obtain ⟨b,rfl⟩ := (e Y d).surjective b
        obtain ⟨a,rfl⟩ := h.2 b
        exact ⟨e X d a,(he f d a).symm⟩
    · intro h
      constructor
      · intro a b hab
        apply (e X d).injective
        apply h.1
        exact (he f d a).symm.trans ((congrArg (e Y d) hab).trans (he f d b))
      · intro b
        obtain ⟨a,ha⟩ := h.2 (e Y d b)
        obtain ⟨a,rfl⟩ := (e X d).surjective a
        refine ⟨a,(e Y d).injective ?_⟩
        exact (he f d a).trans ha
  constructor
  · intro h d
    have hd : d+1-1=d := by omega
    exact cast (congrArg (fun z : ℤ => Function.Bijective (stableHomotopyMap f z)) hd)
      ((equiv_transport (d+1)).mp (h (d+1)))
  · intro h d
    exact (equiv_transport d).mpr (h (d-1))


private def applicabilityDesuspensionMap {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    X.desuspension ⟶ Y.desuspension where
  level
    | 0 => ContinuousMap.id _
    | n + 1 => f.level n
  point n := by cases n with
    | zero => rfl
    | succ n => exact f.point n
  bond n x t := by cases n with
    | zero => exact f.point 0
    | succ n => exact f.bond n x t

private def suspensionDesuspensionIso (X : Prespectrum.{0}) :
    X.desuspension.suspension ≅ X.suspension.desuspension where
  hom :=
    { level := fun n => match n with
        | 0 => ContinuousMap.const _ PUnit.unit
        | _ + 1 => ContinuousMap.id _
      point := by intro n; cases n <;> rfl
      bond := by
        intro n x t
        cases n with
        | zero =>
          refine Quot.inductionOn x ?_
          rintro ⟨x,s⟩
          exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)
        | succ n => rfl }
  inv :=
    { level := fun n => match n with
        | 0 => ContinuousMap.const _ (X.desuspension.suspension.level 0).point
        | _ + 1 => ContinuousMap.id _
      point := by intro n; cases n <;> rfl
      bond := by
        intro n x t
        cases n with
        | zero =>
          exact (BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)).symm
        | succ n => rfl }
  hom_inv_id := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    cases n with
    | zero =>
      refine Quot.inductionOn x ?_
      rintro ⟨x,t⟩
      letI : Subsingleton (X.desuspension.level 0) := inferInstanceAs (Subsingleton PUnit)
      exact (BasedSpace.suspensionProjection_collapsed _ _ (Or.inl (show x = PUnit.unit from Subsingleton.elim _ _))).symm
    | succ n => rfl
  inv_hom_id := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    cases n with
    | zero => exact (show (PUnit.unit : PUnit) = x from Subsingleton.elim _ _)
    | succ n => rfl

private theorem desuspensionMap_stable {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (hf : stableEquivalences f) : stableEquivalences (applicabilityDesuspensionMap f) := by
  apply (stableEquivalences_tail_iff _).mp
  exact hf

private def applicabilityDesuspensionFunctor : Prespectrum.{0} ⥤ Prespectrum.{0} where
  obj := desuspension
  map := applicabilityDesuspensionMap
  map_id X := by
    apply Hom.ext
    funext n
    cases n <;> rfl
  map_comp f g := by
    apply Hom.ext
    funext n
    cases n <;> rfl

private theorem desuspensionFunctor_inverts :
    stableEquivalences.IsInvertedBy (applicabilityDesuspensionFunctor ⋙ sourceLocalization) := by
  intro X Y f hf
  exact stableEquivalences.Q_inverts _ (desuspensionMap_stable f hf)

private noncomputable def sourceDesuspension : SourceCategory.{0} ⥤ SourceCategory.{0} :=
  Localization.lift (applicabilityDesuspensionFunctor ⋙ sourceLocalization)
    desuspensionFunctor_inverts sourceLocalization

private noncomputable def sourceDesuspensionObjIso (X : Prespectrum.{0}) :
    sourceDesuspension.obj (sourceLocalization.obj X) ≅ sourceLocalization.obj X.desuspension :=
  (Localization.fac (applicabilityDesuspensionFunctor ⋙ sourceLocalization)
    desuspensionFunctor_inverts sourceLocalization).app X

private noncomputable def sourceDesuspensionMapIso {X Y : Prespectrum.{0}}
    (e : sourceLocalization.obj X ≅ sourceLocalization.obj Y) :
    sourceLocalization.obj X.desuspension ≅ sourceLocalization.obj Y.desuspension :=
  (sourceDesuspensionObjIso X).symm ≪≫ sourceDesuspension.mapIso e ≪≫
    sourceDesuspensionObjIso Y

/-- It suffices to cancel suspension and padding once, on the original
HF₂ source: all iterated-padding instances then follow functorially. -/
private noncomputable def sourceCancellationIter (X : Prespectrum.{0})
    (e : sourceLocalization.obj X.desuspension.suspension ≅ sourceLocalization.obj X) :
    ∀ n : ℕ, sourceLocalization.obj
        (((desuspension^[n]) X).desuspension.suspension) ≅
      sourceLocalization.obj ((desuspension^[n]) X)
  | 0 => e
  | n + 1 =>
    eqToIso (by rw [Function.iterate_succ_apply']) ≪≫
      sourceLocalization.mapIso
        (suspensionDesuspensionIso (((desuspension^[n]) X).desuspension)) ≪≫
      sourceDesuspensionMapIso (sourceCancellationIter X e n) ≪≫
      eqToIso (by rw [Function.iterate_succ_apply'])

end KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.MooreGhost
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
/-- Consecutive maps through the third vertex vanish when the first is killed
by the boundary and the second kills the inclusion. -/
private theorem triangle_ghost_composite_zero (T : Triangle C) (hT : T ∈ distTriang C)
    {A B : C} (c₁ : A ⟶ T.obj₃) (c₂ : T.obj₃ ⟶ B)
    (h₁ : c₁ ≫ T.mor₃ = 0) (h₂ : T.mor₂ ≫ c₂ = 0) : c₁ ≫ c₂ = 0 := by
  obtain ⟨a, ha⟩ := T.coyoneda_exact₃ hT c₁ h₁
  rw [ha, Category.assoc, h₂, comp_zero]

variable [HasFunctorialCofiber (C := C)]

/-- Two Moore comparisons over maps annihilated by the same exact functor
have composite annihilated by that functor. No tensor-variable shift
coherence and no chosen-cofiber-map composition law are needed. -/
private theorem moore_composite_map_zero
    (F : C ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
    {X Y Z : C} (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z)
    (c₁ : HasFunctorialCofiber.cofib (𝟙 X + 𝟙 X) ⟶
      HasFunctorialCofiber.cofib (𝟙 Y + 𝟙 Y))
    (c₂ : HasFunctorialCofiber.cofib (𝟙 Y + 𝟙 Y) ⟶
      HasFunctorialCofiber.cofib (𝟙 Z + 𝟙 Z))
    (hδ₁ : c₁ ≫ HasFunctorialCofiber.cofibδ (𝟙 Y + 𝟙 Y) =
      HasFunctorialCofiber.cofibδ (𝟙 X + 𝟙 X) ≫ f₁⟦(1 : ℤ)⟧')
    (hι₂ : f₂ ≫ HasFunctorialCofiber.cofibι (𝟙 Z + 𝟙 Z) =
      HasFunctorialCofiber.cofibι (𝟙 Y + 𝟙 Y) ≫ c₂)
    (h₁ : F.map f₁ = 0) (h₂ : F.map f₂ = 0) :
    F.map (c₁ ≫ c₂) = 0 := by
  let T := (HoCofiberSequence.ofMorphism (𝟙 Y + 𝟙 Y)).map F
  have hδ : F.map c₁ ≫ T.h = 0 := by
    change F.map c₁ ≫ (F.map (HasFunctorialCofiber.cofibδ (𝟙 Y + 𝟙 Y)) ≫
      (F.commShiftIso (1 : ℤ)).hom.app Y) = 0
    rw [← Category.assoc, ← Functor.map_comp, hδ₁, Functor.map_comp, Category.assoc,
      F.commShiftIso_hom_naturality, h₁, Functor.map_zero, comp_zero, comp_zero]
  have hι : T.g ≫ F.map c₂ = 0 := by
    change F.map (HasFunctorialCofiber.cofibι (𝟙 Y + 𝟙 Y)) ≫ F.map c₂ = 0
    rw [← Functor.map_comp, ← hι₂, Functor.map_comp, h₂, zero_comp]
  rw [Functor.map_comp]
  exact triangle_ghost_composite_zero (Triangle.mk T.f T.g T.h) T.distinguished _ _ hδ hι

/-- The specified one-step Moore comparison over an actual Adams tower map. -/
private noncomputable def mooreStep {H : C} (unit : 𝟙_ C ⟶ H) (X : C) (s : ℕ) :
    HasFunctorialCofiber.cofib
        (𝟙 (adamsTower unit X (s+1)) + 𝟙 (adamsTower unit X (s+1))) ⟶
      HasFunctorialCofiber.cofib
        (𝟙 (adamsTower unit X s) + 𝟙 (adamsTower unit X s)) :=
  HasFunctorialCofiber.cofibMap _ _ (adamsTowerStep unit X s) (adamsTowerStep unit X s)
    (by simp only [Preadditive.comp_add, Preadditive.add_comp, Category.id_comp, Category.comp_id])

/-- Pair actual Moore successor maps into an H-smash-zero chain. Its composite
covers the actual length `2*k` Adams transition in both triangle squares. -/
private theorem moorePairChain_exists
    (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
    [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
    (X : C) (s k a : ℕ) (ha : a = s+2*k) :
    ∃ chain : FiniteMorphismChain
      (HasFunctorialCofiber.cofib (𝟙 (adamsTower H.unit X a) + 𝟙 (adamsTower H.unit X a)))
      (HasFunctorialCofiber.cofib (𝟙 (adamsTower H.unit X s) + 𝟙 (adamsTower H.unit X s))) k,
    chain.All (fun {_ _} f => H.HF2 ◁ f = 0) ∧
    adamsTowerMap H.unit X s a (by omega) ≫
        HasFunctorialCofiber.cofibι (𝟙 (adamsTower H.unit X s) + 𝟙 (adamsTower H.unit X s)) =
      HasFunctorialCofiber.cofibι (𝟙 (adamsTower H.unit X a) + 𝟙 (adamsTower H.unit X a)) ≫ chain.composite ∧
    chain.composite ≫
        HasFunctorialCofiber.cofibδ (𝟙 (adamsTower H.unit X s) + 𝟙 (adamsTower H.unit X s)) =
      HasFunctorialCofiber.cofibδ (𝟙 (adamsTower H.unit X a) + 𝟙 (adamsTower H.unit X a)) ≫
        (adamsTowerMap H.unit X s a (by omega))⟦(1 : ℤ)⟧' := by
  have hι (b : ℕ) : adamsTowerStep H.unit X b ≫
      HasFunctorialCofiber.cofibι (𝟙 (adamsTower H.unit X b) + 𝟙 (adamsTower H.unit X b)) =
    HasFunctorialCofiber.cofibι (𝟙 (adamsTower H.unit X (b+1)) + 𝟙 (adamsTower H.unit X (b+1))) ≫
      mooreStep H.unit X b := HasFunctorialCofiber.cofibMap_ι _ _ _ _ _
  have hδ (b : ℕ) : mooreStep H.unit X b ≫
      HasFunctorialCofiber.cofibδ (𝟙 (adamsTower H.unit X b) + 𝟙 (adamsTower H.unit X b)) =
    HasFunctorialCofiber.cofibδ (𝟙 (adamsTower H.unit X (b+1)) + 𝟙 (adamsTower H.unit X (b+1))) ≫
      (adamsTowerStep H.unit X b)⟦(1 : ℤ)⟧' := HasFunctorialCofiber.cofibMap_δ _ _ _ _ _
  induction k generalizing a with
  | zero =>
    have hae : a = s := by omega
    subst a
    refine ⟨.nil _, trivial, ?_, ?_⟩ <;> simp [FiniteMorphismChain.composite]
  | succ k ih =>
    have hae : a = (s+2*k+1)+1 := by omega
    subst hae
    obtain ⟨tail, ht, hti, htd⟩ := ih (s+2*k) rfl
    let pair := mooreStep H.unit X (s+2*k+1) ≫ mooreStep H.unit X (s+2*k)
    have hp : H.HF2 ◁ pair = 0 :=
      moore_composite_map_zero (tensorLeft H.HF2)
        (adamsTowerStep H.unit X (s+2*k+1)) (adamsTowerStep H.unit X (s+2*k))
        (mooreStep H.unit X (s+2*k+1)) (mooreStep H.unit X (s+2*k))
        (hδ (s+2*k+1)) (hι (s+2*k))
        (mod2_adamsTowerStep_eq_zero H R X (s+2*k+1))
        (mod2_adamsTowerStep_eq_zero H R X (s+2*k))
    refine ⟨.cons pair tail, ⟨hp, ht⟩, ?_, ?_⟩
    · change adamsTowerMap H.unit X s ((s+2*k+1)+1) _ ≫ _ = _ ≫ (pair ≫ tail.composite)
      rw [adamsTowerMap_succ H.unit X s (s+2*k+1) (by omega),
        adamsTowerMap_succ H.unit X s (s+2*k) (by omega)]
      simp only [Category.assoc]
      rw [hti, ← Category.assoc (adamsTowerStep H.unit X (s+2*k)), hι,
        Category.assoc, ← Category.assoc (adamsTowerStep H.unit X (s+2*k+1)), hι]
      simp only [pair, Category.assoc]
    · change (pair ≫ tail.composite) ≫ _ = _ ≫ (adamsTowerMap H.unit X s ((s+2*k+1)+1) _)⟦(1 : ℤ)⟧'
      rw [Category.assoc, htd]
      dsimp only [pair]
      rw [Category.assoc, ← Category.assoc (mooreStep H.unit X (s+2*k)), hδ,
        Category.assoc, ← Category.assoc (mooreStep H.unit X (s+2*k+1)), hδ]
      rw [adamsTowerMap_succ H.unit X s (s+2*k+1) (by omega),
        adamsTowerMap_succ H.unit X s (s+2*k) (by omega)]
      simp only [Functor.map_comp, Category.assoc]

end KIP126.AdamsSynthetic.Standard.SphereConvergence.MooreGhost

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.MooreConstruction
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
variable [HasFunctorialCofiber (C := C)]

/-- A chain of actual H-smash-zero maps factors through the specified Adams tower. -/
private theorem ghost_chain_lift {H : C} (unit : 𝟙_ C ⟶ H)
    {X Y : C} {k : ℕ} (chain : FiniteMorphismChain X Y k)
    (hchain : chain.All (fun {_ _} f => H ◁ f = 0)) :
    ∃ lift : X ⟶ adamsTower unit Y k,
      lift ≫ adamsTowerMap unit Y 0 k (Nat.zero_le k) = chain.composite := by
  induction chain with
  | nil Y => exact ⟨𝟙 Y, by simp [FiniteMorphismChain.composite]⟩
  | @cons X Y Z k f tail ih =>
    obtain ⟨lift, hlift⟩ := ih hchain.2
    have hzero : (f ≫ lift) ≫ adamsUnit unit (adamsTower unit Z k) = 0 := by
      rw [Category.assoc, adamsUnit_naturality, ← Category.assoc,
        adamsUnit_naturality, hchain.1, comp_zero, zero_comp]
    obtain ⟨g, hg⟩ := (adamsFiberTriangle (adamsUnit unit (adamsTower unit Z k))).coyoneda_exact₂
      (adamsFiberTriangle_distinguished _) (f ≫ lift) hzero
    refine ⟨-g, ?_⟩
    rw [adamsTowerMap_succ unit Z 0 k (Nat.zero_le k), ← Category.assoc]
    change ((-g) ≫ fiberι (adamsUnit unit (adamsTower unit Z k))) ≫ _ = _
    rw [adamsFiberTriangle_mor₁, Preadditive.comp_neg] at hg
    rw [Preadditive.neg_comp, ← hg, Category.assoc, hlift]
    rfl

/-- A homotopy-detecting map into a finite Adams-length target kills a chain
of that many H-smash-zero maps. The detector is an actual map, not an
abstract identification of homotopy groups. -/
private theorem ghost_chain_homotopy_zero {H : C} (unit : 𝟙_ C ⟶ H)
    {X Y N : C} {k : ℕ} (chain : FiniteMorphismChain X Y k)
    (hchain : chain.All (fun {_ _} f => H ◁ f = 0)) (p : Y ⟶ N) (n : ℤ)
    (hp : Function.Injective (inducedMap p n))
    (hN : ∀ (V : C) (s : ℕ) (f : adamsTower unit V s ⟶ N),
      adamsTowerMap unit V s (s+k) (Nat.le_add_right s k) ≫ f = 0) :
    ∀ z, inducedMap chain.composite n z = 0 := by
  obtain ⟨lift, hlift⟩ := ghost_chain_lift unit chain hchain
  intro z
  apply hp
  change (z ≫ chain.composite) ≫ p = (0 : HomotopyGroup n Y) ≫ p
  have hz : adamsTowerMap unit Y 0 k (Nat.zero_le k) ≫ p = 0 := by
    have hh := hN Y 0 p
    exact (Eq.ndrec (motive := fun t => ∀ ht : 0 ≤ t,
      adamsTowerMap unit Y 0 t ht ≫ p = 0) (fun _ => hh) (Nat.zero_add k)) _
  rw [← hlift, Category.assoc, Category.assoc, hz, comp_zero, comp_zero, zero_comp]


end KIP126.AdamsSynthetic.Standard.SphereConvergence.MooreConstruction

open CategoryTheory Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false
namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof
open KIP126.StableHomotopy.Spectra

private noncomputable def mappingPathSpace {A B : BasedSpace.{0}} (f : A ⟶ B) : BasedSpace.{0} where
  space := TopCat.of {z : A × C(I,B) // z.2 0 = f.map z.1}
  point := ⟨(A.point, ContinuousMap.const _ B.point), f.point.symm⟩

private noncomputable def mappingPathProjection {A B : BasedSpace.{0}} (f : A ⟶ B) :
    mappingPathSpace f ⟶ A where
  map := ⟨fun z => z.val.1, continuous_subtype_val.fst⟩
  point := rfl

private noncomputable def mappingPathEndpoint {A B : BasedSpace.{0}} (f : A ⟶ B) :
    mappingPathSpace f ⟶ B where
  map := ⟨fun z => z.val.2 1, (continuous_eval_const 1).comp
    continuous_subtype_val.snd⟩
  point := rfl

private noncomputable def mappingPathSection {A B : BasedSpace.{0}} (f : A ⟶ B) :
    A ⟶ mappingPathSpace f where
  map :=
    ⟨fun a => ⟨(a, ContinuousMap.const _ (f.map a)), rfl⟩,
      (continuous_id.prodMk
        (ContinuousMap.curry (⟨fun z : A × I => f.map z.1,
          f.map.continuous.comp continuous_fst⟩ : C(A × I,B))).continuous).subtype_mk _⟩
  point := by
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    apply ContinuousMap.ext
    intro t
    exact f.point

private theorem mappingPathSection_projection {A B : BasedSpace.{0}} (f : A ⟶ B) :
    mappingPathSection f ≫ mappingPathProjection f = 𝟙 A := by
  rfl

/-- The actual path-space projection is a based deformation retract, so the
left leg of a strictification roof will be a levelwise weak equivalence. -/
private theorem mappingPath_deformation {A B : BasedSpace.{0}} (f : A ⟶ B) :
    Nonempty ((mappingPathSection f).map.comp (mappingPathProjection f).map |>.HomotopyRel
      (ContinuousMap.id (mappingPathSpace f)) {(mappingPathSpace f).point}) := by
  let R := mappingPathSpace f
  let mulI (u t : I) : I := ⟨(u : ℝ) * (t : ℝ), by
    constructor
    · exact mul_nonneg u.property.1 t.property.1
    · nlinarith [u.property.1, u.property.2, t.property.1, t.property.2]⟩
  have hc : Continuous (fun p : I × I => mulI p.1 p.2) :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  have h0 (t : I) : mulI 0 t = 0 := by apply Subtype.ext; simp [mulI]
  have h1 (t : I) : mulI 1 t = t := by apply Subtype.ext; simp [mulI]
  have hz (u : I) : mulI u 0 = 0 := by apply Subtype.ext; simp [mulI]
  let raw : C((I × R) × I,B) :=
    ⟨fun p => p.1.2.val.2 (mulI p.1.1 p.2),
      continuous_eval.comp
        ((continuous_fst.snd.subtype_val.snd).prodMk
          (hc.comp (continuous_fst.fst.prodMk continuous_snd)))⟩
  let g : C(I × R,C(I,B)) := raw.curry
  have hg (p : I × R) : (g p) 0 = f.map p.2.val.1 := by
    change p.2.val.2 (mulI p.1 0) = _
    rw [hz]
    exact p.2.property
  refine ⟨{ toFun := fun p => ⟨(p.2.val.1, g p), hg p⟩
            continuous_toFun :=
              (continuous_snd.subtype_val.fst.prodMk g.continuous).subtype_mk _
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro r
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    apply ContinuousMap.ext
    intro t
    change r.val.2 (mulI 0 t) = f.map r.val.1
    rw [h0]
    exact r.property
  · intro r
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    apply ContinuousMap.ext
    intro t
    change r.val.2 (mulI 1 t) = r.val.2 t
    rw [h1]
  · intro u r hr
    have hr' : r = R.point := hr
    subst r
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    apply ContinuousMap.ext
    intro t
    exact f.point.symm

/-- On the same mapping-path object, the candidate level map and endpoint
map are connected by the displayed path, with the basepoint fixed. -/
private theorem mappingPath_endpoint_homotopy {A B : BasedSpace.{0}} (f : A ⟶ B) :
    Nonempty ((f.map.comp (mappingPathProjection f).map).HomotopyRel
      (mappingPathEndpoint f).map {(mappingPathSpace f).point}) := by
  refine ⟨{ toFun := fun p => p.2.val.2 p.1
            continuous_toFun := continuous_eval.comp
              (continuous_snd.subtype_val.snd.prodMk continuous_fst)
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro r
    exact r.property
  · intro r
    rfl
  · intro t r hr
    subst r
    exact f.point.symm

end KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof
open KIP126.StableHomotopy.Spectra

private noncomputable def bondSquareLeft (P Q : Prespectrum.{0})
    (f : ∀ n, P.level n ⟶ Q.level n) (n : ℕ) : C(P.level n × I, Q.level (n+1)) :=
  (f (n+1)).map.comp (P.bond n)

private noncomputable def bondSquareRight (P Q : Prespectrum.{0})
    (f : ∀ n, P.level n ⟶ Q.level n) (n : ℕ) : C(P.level n × I, Q.level (n+1)) :=
  (Q.bond n).comp ((f n).map.prodMap (ContinuousMap.id I))

private noncomputable def roofBondFirst (P Q : Prespectrum.{0})
    (f : ∀ n, P.level n ⟶ Q.level n)
    (H : ∀ n, (bondSquareLeft P Q f n).Homotopy (bondSquareRight P Q f n)) (n : ℕ) :=
  (H n).compContinuousMap
    ((mappingPathProjection (f n)).map.prodMap (ContinuousMap.id I))

private noncomputable def roofBondSecond (P Q : Prespectrum.{0})
    (f : ∀ n, P.level n ⟶ Q.level n) (n : ℕ) :
    ((bondSquareRight P Q f n).comp
      ((mappingPathProjection (f n)).map.prodMap (ContinuousMap.id I))).Homotopy
      ((Q.bond n).comp ((mappingPathEndpoint (f n)).map.prodMap (ContinuousMap.id I))) where
  toFun p := Q.bond n (p.2.1.val.2 p.1, p.2.2)
  continuous_toFun := (Q.bond n).continuous.comp
    ((continuous_eval.comp (continuous_snd.fst.subtype_val.snd.prodMk continuous_fst)).prodMk
      continuous_snd.snd)
  map_zero_left r := by
    change Q.bond n (r.1.val.2 0, r.2) = Q.bond n ((f n).map r.1.val.1, r.2)
    rw [r.1.property]
  map_one_left r := rfl

private noncomputable def roofBondHomotopy (P Q : Prespectrum.{0})
    (f : ∀ n, P.level n ⟶ Q.level n)
    (H : ∀ n, (bondSquareLeft P Q f n).Homotopy (bondSquareRight P Q f n)) (n : ℕ) :=
  (roofBondFirst P Q f H n).trans (roofBondSecond P Q f n)

private noncomputable def roofBond (P Q : Prespectrum.{0})
    (f : ∀ n, P.level n ⟶ Q.level n)
    (H : ∀ n, (bondSquareLeft P Q f n).Homotopy (bondSquareRight P Q f n)) (n : ℕ) :
    C(mappingPathSpace (f n) × I, mappingPathSpace (f (n+1))) := by
  let G := roofBondHomotopy P Q f H n
  let paths : C(mappingPathSpace (f n) × I, C(I,Q.level (n+1))) :=
    (G.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry
  refine ⟨fun r => ⟨(P.bond n (r.1.val.1,r.2), paths r), ?_⟩, ?_⟩
  · change G (0,r) = (f (n+1)).map (P.bond n (r.1.val.1,r.2))
    exact G.map_zero_left r
  · exact (((P.bond n).continuous.comp
      ((continuous_fst.subtype_val.fst).prodMk continuous_snd)).prodMk
        paths.continuous).subtype_mk _

private theorem roofBond_path_apply (P Q : Prespectrum.{0})
    (f : ∀ n, P.level n ⟶ Q.level n)
    (H : ∀ n, (bondSquareLeft P Q f n).Homotopy (bondSquareRight P Q f n))
    (n : ℕ) (r : mappingPathSpace (f n)) (t u : I) :
    (roofBond P Q f H n (r,t)).val.2 u = roofBondHomotopy P Q f H n (u,(r,t)) := rfl

private noncomputable def roofPrespectrum (P Q : Prespectrum.{0})
    (f : ∀ n, P.level n ⟶ Q.level n)
    (H : ∀ n, (bondSquareLeft P Q f n).Homotopy (bondSquareRight P Q f n))
    (Hpoint : ∀ n u t, H n (u,((P.level n).point,t)) = (Q.level (n+1)).point)
    (Hzero : ∀ n u x, H n (u,(x,0)) = (Q.level (n+1)).point)
    (Hone : ∀ n u x, H n (u,(x,1)) = (Q.level (n+1)).point) : Prespectrum.{0} where
  level n := mappingPathSpace (f n)
  bond := roofBond P Q f H
  bond_point n t := by
    apply Subtype.ext
    refine Prod.ext (P.bond_point n t) ?_
    apply ContinuousMap.ext
    intro u
    rw [roofBond_path_apply]
    unfold roofBondHomotopy
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact Hpoint n _ t
    · exact Q.bond_point n t
  bond_zero n r := by
    apply Subtype.ext
    refine Prod.ext (P.bond_zero n r.val.1) ?_
    apply ContinuousMap.ext
    intro u
    rw [roofBond_path_apply]
    unfold roofBondHomotopy
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact Hzero n _ r.val.1
    · exact Q.bond_zero n _
  bond_one n r := by
    apply Subtype.ext
    refine Prod.ext (P.bond_one n r.val.1) ?_
    apply ContinuousMap.ext
    intro u
    rw [roofBond_path_apply]
    unfold roofBondHomotopy
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact Hone n _ r.val.1
    · exact Q.bond_one n _

private noncomputable def roofProjection (P Q : Prespectrum.{0})
    (f : ∀ n, P.level n ⟶ Q.level n)
    (H : ∀ n, (bondSquareLeft P Q f n).Homotopy (bondSquareRight P Q f n))
    (Hpoint : ∀ n u t, H n (u,((P.level n).point,t)) = (Q.level (n+1)).point)
    (Hzero : ∀ n u x, H n (u,(x,0)) = (Q.level (n+1)).point)
    (Hone : ∀ n u x, H n (u,(x,1)) = (Q.level (n+1)).point) :
    roofPrespectrum P Q f H Hpoint Hzero Hone ⟶ P where
  level n := (mappingPathProjection (f n)).map
  point _ := rfl
  bond _ _ _ := rfl

private noncomputable def roofEndpoint (P Q : Prespectrum.{0})
    (f : ∀ n, P.level n ⟶ Q.level n)
    (H : ∀ n, (bondSquareLeft P Q f n).Homotopy (bondSquareRight P Q f n))
    (Hpoint : ∀ n u t, H n (u,((P.level n).point,t)) = (Q.level (n+1)).point)
    (Hzero : ∀ n u x, H n (u,(x,0)) = (Q.level (n+1)).point)
    (Hone : ∀ n u x, H n (u,(x,1)) = (Q.level (n+1)).point) :
    roofPrespectrum P Q f H Hpoint Hzero Hone ⟶ Q where
  level n := (mappingPathEndpoint (f n)).map
  point n := rfl
  bond n r t := by
    change (roofBond P Q f H n (r,t)).val.2 1 = _
    rw [roofBond_path_apply]
    exact (roofBondHomotopy P Q f H n).map_one_left (r,t)

end KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof
open KIP126.StableHomotopy.Spectra KIP126.StableHomotopy.Spectra.Prespectrum
private theorem stableEquivalence_of_levelwise_loops {X Y : Prespectrum.{0}} (f : X ⟶ Y)
    (hinj : ∀ n r (p q : GenLoop (Fin r) (X.level n) (X.level n).point),
      GenLoop.Homotopic
        (⟨(f.level n).comp p.val,fun t ht => (congrArg (f.level n) (p.property t ht)).trans (f.point n)⟩ :
          GenLoop (Fin r) (Y.level n) (Y.level n).point)
        ⟨(f.level n).comp q.val,fun t ht => (congrArg (f.level n) (q.property t ht)).trans (f.point n)⟩ →
      GenLoop.Homotopic p q)
    (hsurj : ∀ n r (p : GenLoop (Fin r) (Y.level n) (Y.level n).point),
      ∃ q : GenLoop (Fin r) (X.level n) (X.level n).point,
        GenLoop.Homotopic
          (⟨(f.level n).comp q.val,fun t ht => (congrArg (f.level n) (q.property t ht)).trans (f.point n)⟩ :
            GenLoop (Fin r) (Y.level n) (Y.level n).point) p) :
    stableEquivalences f := by
  have applicabilityStabilizeLoopHomotopic (P : Prespectrum.{0}) (n r : ℕ)
      (p q : GenLoop (Fin r) (P.level n) (P.level n).point) (h : GenLoop.Homotopic p q) :
      GenLoop.Homotopic (stabilizeLoop P n r p) (stabilizeLoop P n r q) := by
    obtain ⟨H⟩ := h
    refine ⟨{ toFun := fun t => P.bond n (H (t.1,fun i => t.2 i.succ),t.2 0)
              continuous_toFun := (P.bond n).continuous.comp
                ((H.continuous.comp (continuous_fst.prodMk
                  (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd))).prodMk
                    ((continuous_apply 0).comp continuous_snd))
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro t
      change P.bond n (H (0,_),_) = _
      rw [H.apply_zero]
      rfl
    · intro t
      change P.bond n (H (1,_),_) = _
      rw [H.apply_one]
      rfl
    · intro s t ht
      obtain ⟨i,hi⟩ := ht
      induction i using Fin.cases with
      | zero =>
        rcases hi with h | h
        · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
          rw [h,P.bond_zero,P.bond_zero]
        · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
          rw [h,P.bond_one,P.bond_one]
      | succ j =>
        change P.bond n (H (s,_),_) = P.bond n (p _,_)
        rw [H.eq_fst s ⟨j,hi⟩]
        rfl

  classical
  let F (n r : ℕ) (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
      GenLoop (Fin r) (Y.level n) (Y.level n).point :=
    ⟨(f.level n).comp p.val,fun t ht => (congrArg (f.level n) (p.property t ht)).trans (f.point n)⟩
  choose L hL using hsurj
  have hnext (n r : ℕ) (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
      F (n+1) (r+1) (stabilizeLoop X n r p)=stabilizeLoop Y n r (F n r p) := by
    apply GenLoop.ext
    intro t
    exact f.bond n _ _
  intro d
  let R (a : Representative Y d) : Representative X d :=
    ⟨a.stage,a.dimension,a.degree,L a.stage a.dimension a.loop⟩
  have respects : ∀ a b, StableRelation Y d a b → Quot.mk (StableRelation X d) (R a)=Quot.mk _ (R b) := by
    intro a b hab
    cases hab with
    | homotopy p hp =>
      apply Quot.sound
      apply StableRelation.homotopy (R a)
      apply hinj
      exact (hL a.stage a.dimension a.loop).trans (hp.trans (hL a.stage a.dimension p).symm)
    | stabilization =>
      apply (Quot.sound (StableRelation.stabilization (R a))).trans
      have hh : GenLoop.Homotopic (stabilizeLoop X a.stage a.dimension (L _ _ a.loop))
          (L _ _ (stabilizeLoop Y a.stage a.dimension a.loop)) := by
        apply hinj
        change GenLoop.Homotopic (F _ _ (stabilizeLoop X _ _ (L _ _ a.loop))) _
        rw [hnext]
        exact (applicabilityStabilizeLoopHomotopic Y _ _ _ _ (hL _ _ a.loop)).trans
          (hL _ _ (stabilizeLoop Y _ _ a.loop)).symm
      exact Quot.sound (StableRelation.homotopy (R a).next _ hh)
  let G : StableHomotopy Y d → StableHomotopy X d := Quot.lift (fun a => Quot.mk _ (R a)) respects
  have hGF : Function.LeftInverse G (stableHomotopyMap f d) := by
    intro a
    refine Quot.inductionOn a ?_
    intro a
    change Quot.mk _ (R (a.map f))=Quot.mk _ a
    have h : GenLoop.Homotopic (L a.stage a.dimension (F _ _ a.loop)) a.loop :=
      hinj _ _ _ _ (hL _ _ (F _ _ a.loop))
    exact Quot.sound (StableRelation.homotopy (R (a.map f)) _ h)
  have hFG : Function.RightInverse G (stableHomotopyMap f d) := by
    intro a
    refine Quot.inductionOn a ?_
    intro a
    change Quot.mk _ ((R a).map f)=Quot.mk _ a
    exact Quot.sound (StableRelation.homotopy ((R a).map f) _ (hL _ _ a.loop))
  exact ⟨hGF.injective,hFG.surjective⟩

private noncomputable def basedLoopMap {A B : BasedSpace.{0}} (f : A ⟶ B) {r : ℕ}
    (p : GenLoop (Fin r) A A.point) : GenLoop (Fin r) B B.point :=
  ⟨f.map.comp p.val, fun t ht => (congrArg f.map (p.property t ht)).trans f.point⟩

private theorem basedLoopMap_homotopy {A B : BasedSpace.{0}} {f g : A ⟶ B}
    (H : f.map.HomotopyRel g.map {A.point}) {r : ℕ}
    (p : GenLoop (Fin r) A A.point) :
    GenLoop.Homotopic (basedLoopMap f p) (basedLoopMap g p) := by
  refine ⟨{ toFun := fun z => H (z.1,p z.2)
            continuous_toFun := H.continuous.comp (continuous_fst.prodMk
              (p.val.continuous.comp continuous_snd))
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    exact H.apply_zero _
  · intro t
    exact H.apply_one _
  · intro u t ht
    exact H.eq_fst u (p.property t ht)

private theorem mappingPathProjection_loops
    {A B : BasedSpace.{0}} (f : A ⟶ B) (r : ℕ) :
    (∀ p q : GenLoop (Fin r) (mappingPathSpace f) (mappingPathSpace f).point,
      GenLoop.Homotopic (basedLoopMap (mappingPathProjection f) p)
        (basedLoopMap (mappingPathProjection f) q) → GenLoop.Homotopic p q) ∧
    (∀ p : GenLoop (Fin r) A A.point,
      ∃ q : GenLoop (Fin r) (mappingPathSpace f) (mappingPathSpace f).point,
        GenLoop.Homotopic (basedLoopMap (mappingPathProjection f) q) p) := by
  obtain ⟨D⟩ := mappingPath_deformation f
  constructor
  · intro p q hpq
    have hp := basedLoopMap_homotopy
      (f := mappingPathProjection f ≫ mappingPathSection f) (g := 𝟙 _) D p
    have hq := basedLoopMap_homotopy
      (f := mappingPathProjection f ≫ mappingPathSection f) (g := 𝟙 _) D q
    have hmid := hpq.comp_continuousMap (mappingPathSection f).map
    exact hp.symm.trans (hmid.trans hq)
  · intro p
    refine ⟨basedLoopMap (mappingPathSection f) p, ?_⟩
    exact GenLoop.Homotopic.refl p

private theorem roofProjection_stableEquivalence (P Q : Prespectrum.{0})
    (f : ∀ n, P.level n ⟶ Q.level n)
    (H : ∀ n, (bondSquareLeft P Q f n).Homotopy (bondSquareRight P Q f n))
    (Hpoint : ∀ n u t, H n (u,((P.level n).point,t)) = (Q.level (n+1)).point)
    (Hzero : ∀ n u x, H n (u,(x,0)) = (Q.level (n+1)).point)
    (Hone : ∀ n u x, H n (u,(x,1)) = (Q.level (n+1)).point) :
    Prespectrum.stableEquivalences (roofProjection P Q f H Hpoint Hzero Hone) := by
  apply stableEquivalence_of_levelwise_loops
  · intro n r p q hpq
    exact (mappingPathProjection_loops (f n) r).1 p q hpq
  · intro n r p
    exact (mappingPathProjection_loops (f n) r).2 p

end KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof
open KIP126.StableHomotopy.Spectra KIP126.StableHomotopy.Spectra.Prespectrum

/-- The endpoint agrees on actual stable representatives with the specified
level map after projection, even though those level maps are only homotopy
compatible with the bonds. -/
private theorem roofEndpoint_loop_formula (P Q : Prespectrum.{0})
    (f : ∀ n, P.level n ⟶ Q.level n)
    (H : ∀ n, (bondSquareLeft P Q f n).Homotopy (bondSquareRight P Q f n))
    (Hpoint : ∀ n u t, H n (u,((P.level n).point,t)) = (Q.level (n+1)).point)
    (Hzero : ∀ n u x, H n (u,(x,0)) = (Q.level (n+1)).point)
    (Hone : ∀ n u x, H n (u,(x,1)) = (Q.level (n+1)).point)
    (d : ℤ) (a : Representative (roofPrespectrum P Q f H Hpoint Hzero Hone) d) :
    stableHomotopyMap (roofEndpoint P Q f H Hpoint Hzero Hone) d (Quot.mk _ a) =
      loopClass Q d a.stage a.dimension a.degree
        (basedLoopMap (f a.stage) (basedLoopMap (mappingPathProjection (f a.stage)) a.loop)) := by
  obtain ⟨D⟩ := mappingPath_endpoint_homotopy (f a.stage)
  have h := basedLoopMap_homotopy
    (f := mappingPathProjection (f a.stage) ≫ f a.stage)
    (g := mappingPathEndpoint (f a.stage)) D a.loop
  exact Quot.sound (StableRelation.homotopy
    (a.map (roofEndpoint P Q f H Hpoint Hzero Hone)) _ h.symm)

end KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof

open Filter
namespace KIP126.StableHomotopy.Spectra

private theorem cube_three_cycle_homotopy :
    ∃ H : C(I × (Fin 3 → I),Fin 3 → I),
      (∀ z, H (0,z)=z) ∧ (∀ z, H (1,z)=![z 1,z 2,z 0]) ∧
      ∀ t z, z ∈ Cube.boundary (Fin 3) → H (t,z) ∈ Cube.boundary (Fin 3) := by
  let P (v : Fin 3 → ℝ) : Fin 3 → ℝ := ![v 1,v 2,v 0]
  have hPc : Continuous P := by
    apply continuous_pi
    intro i
    fin_cases i <;> exact continuous_apply _
  have hPn (v : Fin 3 → ℝ) : ‖P v‖=‖v‖ := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      fin_cases i <;> exact norm_le_pi_norm v _
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      fin_cases i
      · exact norm_le_pi_norm (P v) 2
      · exact norm_le_pi_norm (P v) 0
      · exact norm_le_pi_norm (P v) 1
  let L (t : I) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
    (1-(t:ℝ)) • v + (t:ℝ) • P v
  have hLc : Continuous (fun z : I × (Fin 3 → ℝ) => L z.1 z.2) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul continuous_snd |>.add
      ((continuous_subtype_val.comp continuous_fst).smul (hPc.comp continuous_snd))
  have hLzero (t : I) (v : Fin 3 → ℝ) (h : L t v=0) : v=0 := by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    change (1-(t:ℝ))*v 0+(t:ℝ)*v 1=0 at h0
    change (1-(t:ℝ))*v 1+(t:ℝ)*v 2=0 at h1
    change (1-(t:ℝ))*v 2+(t:ℝ)*v 0=0 at h2
    have hD : 0 < (1-(t:ℝ))^3+(t:ℝ)^3 := by
      nlinarith [sq_nonneg ((t:ℝ)-1/2)]
    have hv0 : ((1-(t:ℝ))^3+(t:ℝ)^3)*v 0=0 := by
      linear_combination (1-(t:ℝ))^2*h0 - ((1-(t:ℝ))*(t:ℝ))*h1 + (t:ℝ)^2*h2
    have hv1 : ((1-(t:ℝ))^3+(t:ℝ)^3)*v 1=0 := by
      linear_combination (1-(t:ℝ))^2*h1 - ((1-(t:ℝ))*(t:ℝ))*h2 + (t:ℝ)^2*h0
    have hv2 : ((1-(t:ℝ))^3+(t:ℝ)^3)*v 2=0 := by
      linear_combination (1-(t:ℝ))^2*h2 - ((1-(t:ℝ))*(t:ℝ))*h0 + (t:ℝ)^2*h1
    funext i
    fin_cases i
    · exact (mul_eq_zero.mp hv0).resolve_left hD.ne'
    · exact (mul_eq_zero.mp hv1).resolve_left hD.ne'
    · exact (mul_eq_zero.mp hv2).resolve_left hD.ne'
  let N (t : I) (v : Fin 3 → ℝ) : Fin 3 → ℝ := (‖v‖/‖L t v‖) • L t v
  have hNzero (t : I) : N t 0=0 := by simp [N]
  have hNnorm (t : I) (v : Fin 3 → ℝ) : ‖N t v‖=‖v‖ := by
    by_cases hv : v=0
    · simp [hv,hNzero]
    have hLn : ‖L t v‖ ≠ 0 := norm_ne_zero_iff.mpr (fun h => hv (hLzero t v h))
    change ‖(‖v‖/‖L t v‖) • L t v‖=‖v‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)),
      div_mul_cancel₀ _ hLn]
  have hNc : Continuous (fun z : I × (Fin 3 → ℝ) => N z.1 z.2) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z.2=0
    · change Tendsto (fun z : I × (Fin 3 → ℝ) => N z.1 z.2) (𝓝 z) (𝓝 (N z.1 z.2))
      rw [hz,hNzero]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp only [hNnorm]
      have hh : Tendsto (fun z : I × (Fin 3 → ℝ) => ‖z.2‖) (𝓝 z) (𝓝 ‖z.2‖) :=
        continuous_snd.norm.continuousAt
      rw [hz,norm_zero] at hh
      exact hh
    · exact ((continuous_snd.norm.continuousAt).div hLc.norm.continuousAt
        (norm_ne_zero_iff.mpr (fun h => hz (hLzero z.1 z.2 h)))).smul hLc.continuousAt
  have hN0 (v : Fin 3 → ℝ) : N 0 v=v := by
    by_cases hv : v=0
    · simp [hv,hNzero]
    simp [N,L,div_self (norm_ne_zero_iff.mpr hv)]
  have hN1 (v : Fin 3 → ℝ) : N 1 v=P v := by
    by_cases hv : v=0
    · rw [hv,hNzero]
      funext i
      fin_cases i <;> rfl
    simp [N,L,hPn,div_self (norm_ne_zero_iff.mpr hv)]
  let c (z : Fin 3 → I) : Fin 3 → ℝ := fun i => (z i:ℝ)-1/2
  have hc : Continuous c := continuous_pi fun i =>
    ((continuous_subtype_val.comp (continuous_apply i)).sub continuous_const)
  have hcn (z : Fin 3 → I) : ‖c z‖ ≤ 1/2 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    change |(z i:ℝ)-1/2| ≤ 1/2
    rw [abs_le]
    constructor <;> linarith [(z i).2.1,(z i).2.2]
  have hbound (t : I) (z : Fin 3 → I) (i : Fin 3) :
      N t (c z) i+1/2 ∈ Set.Icc (0:ℝ) 1 := by
    have hi : |N t (c z) i| ≤ 1/2 :=
      (norm_le_pi_norm (N t (c z)) i).trans ((hNnorm t (c z)).le.trans (hcn z))
    rw [abs_le] at hi
    constructor <;> linarith
  let H : C(I × (Fin 3 → I),Fin 3 → I) :=
    ⟨fun p i => ⟨N p.1 (c p.2) i+1/2,hbound p.1 p.2 i⟩,by
      apply continuous_pi
      intro i
      exact (((continuous_apply i).comp (hNc.comp
        (continuous_fst.prodMk (hc.comp continuous_snd)))).add continuous_const).subtype_mk _⟩
  refine ⟨H,?_,?_,?_⟩
  · intro z
    funext i
    apply Subtype.ext
    change N 0 (c z) i+1/2=(z i:ℝ)
    rw [hN0]
    dsimp [c]
    ring
  · intro z
    funext i
    apply Subtype.ext
    change N 1 (c z) i+1/2=(![z 1,z 2,z 0] i:ℝ)
    rw [hN1]
    fin_cases i <;> simp [P,c]
  · intro t z hz
    have hn : ‖c z‖=1/2 := by
      apply le_antisymm (hcn z)
      obtain ⟨i,hi⟩ := hz
      have hle := norm_le_pi_norm (c z) i
      rcases hi with hi | hi <;> norm_num [c,hi] at hle ⊢ <;> exact hle
    by_contra hh
    have hstrict : ∀ i : Fin 3, ‖N t (c z) i‖ < 1/2 := by
      intro i
      have hi₀ : H (t,z) i ≠ 0 := fun h => hh ⟨i,Or.inl h⟩
      have hi₁ : H (t,z) i ≠ 1 := fun h => hh ⟨i,Or.inr h⟩
      have hb := hbound t z i
      have h0 : N t (c z) i+1/2 ≠ 0 := fun h => hi₀ (Subtype.ext h)
      have h1 : N t (c z) i+1/2 ≠ 1 := fun h => hi₁ (Subtype.ext h)
      rw [Real.norm_eq_abs,abs_lt]
      constructor <;> grind
    have hlt : ‖N t (c z)‖ < 1/2 := (pi_norm_lt_iff (by norm_num)).mpr hstrict
    rw [hNnorm,hn] at hlt
    exact (lt_irrefl _ hlt)


private theorem triple_suspension_cycle_homotopic (A : BasedSpace.{0}) :
    ((Prespectrum.suspensionSpectrumSuspensionIso A).hom.level 2).HomotopicRel
      (ContinuousMap.id A.suspension.suspension.suspension)
      {A.suspension.suspension.suspension.point} := by
  obtain ⟨H,hH0,hH1,hHb⟩ := cube_three_cycle_homotopy
  let K : C(I × (Fin 3 → I),Fin 3 → I) :=
    ⟨fun p => H (p.1,H p),H.continuous.comp (continuous_fst.prodMk H.continuous)⟩
  have hK0 (z : Fin 3 → I) : K (0,z)=z := by
    change H (0,H (0,z))=z
    rw [hH0,hH0]
  have hK1 (z : Fin 3 → I) : K (1,z)=![z 2,z 0,z 1] := by
    change H (1,H (1,z))=![z 2,z 0,z 1]
    rw [hH1,hH1]
    rfl
  have hKb (t : I) (z : Fin 3 → I) (hz : z ∈ Cube.boundary (Fin 3)) :
      K (t,z) ∈ Cube.boundary (Fin 3) := hHb t _ (hHb t z hz)
  let B := A.suspension.suspension.suspension
  let val (a : A) (z : Fin 3 → I) : B :=
    BasedSpace.suspensionProjection A.suspension.suspension
      (BasedSpace.suspensionProjection A.suspension
        (BasedSpace.suspensionProjection A (a,z 2),z 1),z 0)
  have hval : Continuous (fun p : A × (Fin 3 → I) => val p.1 p.2) :=
    (BasedSpace.suspensionProjection A.suspension.suspension).continuous.comp
      (((BasedSpace.suspensionProjection A.suspension).continuous.comp
        (((BasedSpace.suspensionProjection A).continuous.comp
          (continuous_fst.prodMk ((continuous_apply 2).comp continuous_snd))).prodMk
            ((continuous_apply 1).comp continuous_snd))).prodMk
              ((continuous_apply 0).comp continuous_snd))
  have hvalp (z : Fin 3 → I) : val A.point z=B.point := by
    change BasedSpace.suspensionProjection _ (BasedSpace.suspensionProjection _
      (BasedSpace.suspensionProjection A (A.point,z 2),z 1),z 0)=_
    rw [BasedSpace.suspensionProjection_collapsed A _ (Or.inl rfl),
      BasedSpace.suspensionProjection_collapsed A.suspension _ (Or.inl rfl),
      BasedSpace.suspensionProjection_collapsed A.suspension.suspension _ (Or.inl rfl)]
  have hvalb (a : A) (z : Fin 3 → I) (hz : z ∈ Cube.boundary (Fin 3)) : val a z=B.point := by
    obtain ⟨i,hi⟩ := hz
    fin_cases i
    · exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inr hi)
    · have h := BasedSpace.suspensionProjection_collapsed A.suspension
        (BasedSpace.suspensionProjection A (a,z 2),z 1) (Or.inr hi)
      change BasedSpace.suspensionProjection _ (_,z 0)=_
      rw [h]
      exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)
    · have h := BasedSpace.suspensionProjection_collapsed A (a,z 2) (Or.inr hi)
      change BasedSpace.suspensionProjection _ (BasedSpace.suspensionProjection _ (_,z 1),z 0)=_
      rw [h,BasedSpace.suspensionProjection_collapsed A.suspension _ (Or.inl rfl)]
      exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)
  have lift_family (U : BasedSpace.{0}) (J : Type) [TopologicalSpace J] [LocallyCompactSpace J]
      (f : C((U × I) × J,B))
      (hf : ∀ p k, BasedSpace.SuspensionCollapsed U p → f (p,k)=B.point) :
      ∃ F : C(U.suspension × J,B),
        (∀ a s k, F (BasedSpace.suspensionProjection U (a,s),k)=f ((a,s),k)) ∧
        (∀ k, F (U.suspension.point,k)=B.point) := by
    have hr (k : J) : ∀ a b, BasedSpace.SuspensionRelation U a b → f (a,k)=f (b,k) :=
      fun a b h => (hf a k h.1).trans (hf b k h.2).symm
    let F : C(U.suspension × J,B) :=
      ⟨fun p => Quot.lift (fun a => f (a,p.2)) (hr p.2) p.1,by
        apply isQuotientMap_quot_mk.continuous_lift_prod_left
        exact f.continuous⟩
    exact ⟨F,fun _ _ _ => rfl,fun k => hf (U.point,0) k (Or.inl rfl)⟩
  let f₀ : C((A × I) × ((I × I) × I),B) :=
    ⟨fun p => val p.1.1 (K (p.2.2,![p.2.1.2,p.2.1.1,p.1.2])),by
      refine hval.comp (f := fun p : (A × I) × ((I × I) × I) =>
        (p.1.1,K (p.2.2,![p.2.1.2,p.2.1.1,p.1.2]))) ?_
      apply Continuous.prodMk continuous_fst.fst
      apply K.continuous.comp
      apply Continuous.prodMk continuous_snd.snd
      apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_snd.fst.snd
      · exact continuous_snd.fst.fst
      · exact continuous_fst.snd⟩
  have hf₀ (p : A × I) (k : (I × I) × I) (hp : BasedSpace.SuspensionCollapsed A p) :
      f₀ (p,k)=B.point := by
    rcases p with ⟨a,s⟩
    rcases hp with h | h | h
    · change a=A.point at h
      change val a (K (k.2,![k.1.2,k.1.1,s]))=B.point
      rw [h]
      exact hvalp _
    · exact hvalb a _ (hKb _ _ ⟨2,Or.inl h⟩)
    · exact hvalb a _ (hKb _ _ ⟨2,Or.inr h⟩)
  obtain ⟨F₁,hF₁,hF₁p⟩ := lift_family A ((I × I) × I) f₀ hf₀
  let f₁ : C((A.suspension × I) × (I × I),B) :=
    ⟨fun p => F₁ (p.1.1,((p.1.2,p.2.1),p.2.2)),F₁.continuous.comp
      (continuous_fst.fst.prodMk ((continuous_fst.snd.prodMk continuous_snd.fst).prodMk continuous_snd.snd))⟩
  have hf₁ (p : A.suspension × I) (k : I × I)
      (hp : BasedSpace.SuspensionCollapsed A.suspension p) : f₁ (p,k)=B.point := by
    rcases p with ⟨q,s⟩
    rcases hp with h | h | h
    · change q=A.suspension.point at h
      change F₁ (q,((s,k.1),k.2))=B.point
      rw [h]
      exact hF₁p _
    · refine Quot.inductionOn q ?_
      rintro ⟨a,r⟩
      change F₁ (BasedSpace.suspensionProjection A (a,r),((s,k.1),k.2))=B.point
      rw [hF₁]
      exact hvalb a _ (hKb _ _ ⟨1,Or.inl h⟩)
    · refine Quot.inductionOn q ?_
      rintro ⟨a,r⟩
      change F₁ (BasedSpace.suspensionProjection A (a,r),((s,k.1),k.2))=B.point
      rw [hF₁]
      exact hvalb a _ (hKb _ _ ⟨1,Or.inr h⟩)
  obtain ⟨F₂,hF₂,hF₂p⟩ := lift_family A.suspension (I × I) f₁ hf₁
  let f₂ : C((A.suspension.suspension × I) × I,B) :=
    ⟨fun p => F₂ (p.1.1,(p.1.2,p.2)),F₂.continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))⟩
  have hf₂ (p : A.suspension.suspension × I) (k : I)
      (hp : BasedSpace.SuspensionCollapsed A.suspension.suspension p) : f₂ (p,k)=B.point := by
    rcases p with ⟨q,s⟩
    rcases hp with h | h | h
    · change q=A.suspension.suspension.point at h
      change F₂ (q,(s,k))=B.point
      rw [h]
      exact hF₂p _
    · refine Quot.inductionOn q ?_
      rintro ⟨q,r⟩
      refine Quot.inductionOn q ?_
      rintro ⟨a,u⟩
      change F₂ (BasedSpace.suspensionProjection A.suspension
        (BasedSpace.suspensionProjection A (a,u),r),(s,k))=B.point
      rw [hF₂]
      change F₁ (BasedSpace.suspensionProjection A (a,u),((r,s),k))=B.point
      rw [hF₁]
      exact hvalb a _ (hKb _ _ ⟨0,Or.inl h⟩)
    · refine Quot.inductionOn q ?_
      rintro ⟨q,r⟩
      refine Quot.inductionOn q ?_
      rintro ⟨a,u⟩
      change F₂ (BasedSpace.suspensionProjection A.suspension
        (BasedSpace.suspensionProjection A (a,u),r),(s,k))=B.point
      rw [hF₂]
      change F₁ (BasedSpace.suspensionProjection A (a,u),((r,s),k))=B.point
      rw [hF₁]
      exact hvalb a _ (hKb _ _ ⟨0,Or.inr h⟩)
  obtain ⟨F₃,hF₃,hF₃p⟩ := lift_family A.suspension.suspension I f₂ hf₂
  have hF (a : A) (s r u t : I) :
      F₃ (val a ![u,r,s],t)=val a (K (t,![u,r,s])) := by
    change F₃ (BasedSpace.suspensionProjection A.suspension.suspension
      (BasedSpace.suspensionProjection A.suspension (BasedSpace.suspensionProjection A (a,s),r),u),t)=_
    rw [hF₃]
    change F₂ (BasedSpace.suspensionProjection A.suspension (BasedSpace.suspensionProjection A (a,s),r),(u,t))=_
    rw [hF₂]
    change F₁ (BasedSpace.suspensionProjection A (a,s),((r,u),t))=_
    rw [hF₁]
    rfl
  apply ContinuousMap.HomotopicRel.symm
  refine ⟨{ toFun := fun p => F₃ (p.2,p.1)
            continuous_toFun := F₃.continuous.comp continuous_swap
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro q
    refine Quot.inductionOn q ?_
    rintro ⟨q,u⟩
    refine Quot.inductionOn q ?_
    rintro ⟨q,r⟩
    refine Quot.inductionOn q ?_
    rintro ⟨a,s⟩
    change F₃ (val a ![u,r,s],0)=val a ![u,r,s]
    rw [hF,hK0]
  · intro q
    refine Quot.inductionOn q ?_
    rintro ⟨q,u⟩
    refine Quot.inductionOn q ?_
    rintro ⟨q,r⟩
    refine Quot.inductionOn q ?_
    rintro ⟨a,s⟩
    change F₃ (val a ![u,r,s],1)=
      (Prespectrum.suspensionSpectrumSuspensionIso A).hom.level 2 (val a ![u,r,s])
    rw [hF,hK1]
    exact ((Prespectrum.suspensionSpectrumSuspensionIso_exists A).choose_spec 2 a s ![u,r]).symm
  · intro t q hq
    obtain rfl := Set.mem_singleton_iff.mp hq
    exact hF₃p t


/-- Suspending cubical representatives respects two actual spectrum
stabilizations up to based homotopy. The three new coordinates form the cycle
proved above, rather than a silently omitted transposition. -/
private theorem suspension_loop_two_stabilizations (P : Prespectrum.{0}) (n r : ℕ)
    (p : GenLoop (Fin r) (P.level n) (P.level n).point) :
    GenLoop.Homotopic
      (Prespectrum.stabilizeLoop (Prespectrum.suspensionSpectrum (P.level (n+2))) 0 (r+2)
        (Prespectrum.stabilizeLoop P (n+1) (r+1) (Prespectrum.stabilizeLoop P n r p)))
      (Prespectrum.stabilizeLoop P.suspension (n+1) (r+2)
        (Prespectrum.stabilizeLoop P.suspension n (r+1)
          (Prespectrum.stabilizeLoop (Prespectrum.suspensionSpectrum (P.level n)) 0 r p))) := by
  let beta (n : ℕ) : (P.level n).suspension ⟶ P.level (n+1) := by
    have hc (a : P.level n × I) (ha : BasedSpace.SuspensionCollapsed (P.level n) a) :
        P.bond n a=(P.level (n+1)).point := by
      rcases a with ⟨x,t⟩
      rcases ha with h | h | h
      · change x=(P.level n).point at h
        rw [h,P.bond_point]
      · change t=0 at h
        rw [h,P.bond_zero]
      · change t=1 at h
        rw [h,P.bond_one]
    have hr : ∀ a b, BasedSpace.SuspensionRelation (P.level n) a b → P.bond n a=P.bond n b :=
      fun a b h => (hc a h.1).trans (hc b h.2).symm
    exact ⟨⟨Quot.lift (P.bond n) hr,continuous_quot_lift hr (P.bond n).continuous⟩,
      P.bond_point n 0⟩
  let G : (P.level n).suspension.suspension.suspension ⟶ (P.level (n+2)).suspension :=
    BasedSpace.suspendMap (BasedSpace.suspendMap (beta n) ≫ beta (n+1))
  let j : GenLoop (Fin (r+3)) (P.level n).suspension.suspension.suspension
      (P.level n).suspension.suspension.suspension.point :=
    Prespectrum.stabilizeLoop (Prespectrum.suspensionSpectrum ((P.level n).suspension.suspension)) 0 (r+2)
      (Prespectrum.stabilizeLoop (Prespectrum.suspensionSpectrum ((P.level n).suspension)) 0 (r+1)
        (Prespectrum.stabilizeLoop (Prespectrum.suspensionSpectrum (P.level n)) 0 r p))
  obtain ⟨H⟩ := (triple_suspension_cycle_homotopic (P.level n)).symm
  refine ⟨{ toFun := fun z => G.map (H (z.1,j.val z.2))
            continuous_toFun := G.map.continuous.comp (H.continuous.comp
              (continuous_fst.prodMk (j.val.continuous.comp continuous_snd)))
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro z
    rw [H.apply_zero]
    rfl
  · intro z
    rw [H.apply_one]
    have h := (Prespectrum.suspensionSpectrumSuspensionIso_exists (P.level n)).choose_spec 2
      (p (fun i => z i.succ.succ.succ)) (z 2) ![z 0,z 1]
    change G.map ((Prespectrum.suspensionSpectrumSuspensionIso (P.level n)).hom.level 2 (j.val z))=_
    have hj : j.val z=BasedSpace.iteratedPoint (P.level n).suspension 2
        (BasedSpace.suspensionProjection _ (p (fun i => z i.succ.succ.succ),z 2)) ![z 0,z 1] := rfl
    rw [hj]
    exact congrArg G.map h
  · intro t z hz
    change G.map (H (t,j.val z))=_
    rw [j.property z hz,H.eq_fst t (Set.mem_singleton _)]
    exact G.point.trans (by
      symm
      exact (Prespectrum.stabilizeLoop (Prespectrum.suspensionSpectrum (P.level (n+2))) 0 (r+2)
        (Prespectrum.stabilizeLoop P (n+1) (r+1) (Prespectrum.stabilizeLoop P n r p))).property z hz)


open Prespectrum
private theorem stable_suspension_natural_map :
    ∃ S : ∀ (P : Prespectrum.{0}) (d : ℤ), StableHomotopy P (d-1) → StableHomotopy P.suspension d,
      (∀ P d (a : Representative P (d-1)), a.stage%2=0 →
        S P d (Quot.mk _ a)=Quot.mk _
          (⟨a.stage,a.dimension+1,by have := a.degree; omega,
            stabilizeLoop (suspensionSpectrum (P.level a.stage)) 0 a.dimension a.loop⟩ :
              Representative P.suspension d)) ∧
      (∀ {P Q} (f : P ⟶ Q) d a,
        S Q d (stableHomotopyMap f (d-1) a)=stableHomotopyMap (suspensionMap f) d (S P d a)) := by
  let E (P : Prespectrum.{0}) (d : ℤ) (a : Representative P (d-1)) : Representative P.suspension d :=
    ⟨a.stage,a.dimension+1,by have := a.degree; omega,
      stabilizeLoop (suspensionSpectrum (P.level a.stage)) 0 a.dimension a.loop⟩
  have hEhom (P : Prespectrum.{0}) (d : ℤ) (a : Representative P (d-1))
      (p : GenLoop (Fin a.dimension) (P.level a.stage) (P.level a.stage).point)
      (hp : GenLoop.Homotopic a.loop p) :
      Quot.mk (StableRelation P.suspension d) (E P d a)=Quot.mk _ (E P d {a with loop:=p}) :=
    Quot.sound (StableRelation.homotopy (E P d a) _
      (applicabilityStabilizeLoopHomotopic (suspensionSpectrum (P.level a.stage)) 0 a.dimension _ _ hp))
  have hE2 (P : Prespectrum.{0}) (d : ℤ) (a : Representative P (d-1)) :
      Quot.mk (StableRelation P.suspension d) (E P d a.next.next)=Quot.mk _ (E P d a).next.next :=
    Quot.sound (StableRelation.homotopy (E P d a.next.next) _
      (suspension_loop_two_stabilizations P a.stage a.dimension a.loop))
  let phi (P : Prespectrum.{0}) (d : ℤ) (a : Representative P (d-1)) : StableHomotopy P.suspension d :=
    if a.stage%2=0 then Quot.mk _ (E P d a) else Quot.mk _ (E P d a.next)
  have hphi (P : Prespectrum.{0}) (d : ℤ) (a b : Representative P (d-1))
      (h : StableRelation P (d-1) a b) : phi P d a=phi P d b := by
    cases h with
    | homotopy p hp =>
      by_cases ha : a.stage%2=0
      · dsimp only [phi]
        rw [if_pos ha,if_pos ha]
        exact hEhom P d a p hp
      · dsimp only [phi]
        rw [if_neg ha,if_neg ha]
        exact hEhom P d a.next _ (applicabilityStabilizeLoopHomotopic P _ _ _ _ hp)
    | stabilization =>
      by_cases ha : a.stage%2=0
      · have hn : a.next.stage%2≠0 := by change (a.stage+1)%2≠0; omega
        dsimp only [phi]
        rw [if_pos ha,if_neg hn,hE2]
        exact (Quot.sound (StableRelation.stabilization (E P d a))).trans
          (Quot.sound (StableRelation.stabilization (E P d a).next))
      · have hn : a.next.stage%2=0 := by change (a.stage+1)%2=0; omega
        dsimp only [phi]
        rw [if_neg ha,if_pos hn]
  let S (P : Prespectrum.{0}) (d : ℤ) : StableHomotopy P (d-1) → StableHomotopy P.suspension d :=
    Quot.lift (phi P d) (hphi P d)
  have hEmap {P Q : Prespectrum.{0}} (f : P ⟶ Q) (d : ℤ) (a : Representative P (d-1)) :
      E Q d (a.map f)=(E P d a).map (suspensionMap f) := by
    cases a
    rfl
  have hnext {P Q : Prespectrum.{0}} (f : P ⟶ Q) (d : ℤ) (a : Representative P (d-1)) :
      (a.map f).next=a.next.map f := by
    unfold Representative.next Representative.map
    congr 1
    apply GenLoop.ext
    intro t
    exact (f.bond _ _ _).symm
  refine ⟨S,fun P d a ha => if_pos ha,?_⟩
  intro P Q f d a
  refine Quot.inductionOn a ?_
  intro a
  change phi Q d (a.map f)=stableHomotopyMap (suspensionMap f) d (phi P d a)
  by_cases ha : a.stage%2=0
  · dsimp only [phi]
    rw [if_pos (show (a.map f).stage%2=0 from ha),if_pos ha,hEmap]
    rfl
  · dsimp only [phi]
    rw [if_neg (show (a.map f).stage%2≠0 from ha),if_neg ha,hnext,hEmap]
    rfl


private noncomputable def sourceBondAdjoint (P : Prespectrum.{0}) (n : ℕ) : (P.level n).suspension ⟶ P.level (n+1) := by
  have hc (a : P.level n × I) (ha : BasedSpace.SuspensionCollapsed (P.level n) a) :
      P.bond n a=(P.level (n+1)).point := by
    rcases a with ⟨x,t⟩
    rcases ha with h | h | h
    · change x=(P.level n).point at h
      rw [h,P.bond_point]
    · change t=0 at h
      rw [h,P.bond_zero]
    · change t=1 at h
      rw [h,P.bond_one]
  have hr : ∀ a b, BasedSpace.SuspensionRelation (P.level n) a b → P.bond n a=P.bond n b :=
    fun a b h => (hc a h.1).trans (hc b h.2).symm
  exact ⟨⟨Quot.lift (P.bond n) hr,continuous_quot_lift hr (P.bond n).continuous⟩,
    P.bond_point n 0⟩

private theorem stable_suspension_equivalence_formula :
    ∃ e : ∀ (P : Prespectrum.{0}) (d : ℤ), StableHomotopy P (d-1) ≃ StableHomotopy P.suspension d,
      (∀ {P Q} (f : P ⟶ Q) d a,
        e Q d (stableHomotopyMap f (d-1) a)=stableHomotopyMap (suspensionMap f) d (e P d a)) ∧
      ∀ P d (a : Representative P.suspension d), a.stage % 2 = 0 →
        (e P d).symm (Quot.mk _ a) =
          loopClass P (d-1) (a.stage+1) a.dimension (by have := a.degree; omega)
            (KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof.basedLoopMap
              (sourceBondAdjoint P a.stage) a.loop) := by
  obtain ⟨S,hSeven,hSnat⟩ := stable_suspension_natural_map
  let beta := sourceBondAdjoint
  let M {A B : BasedSpace.{0}} (f : A ⟶ B) (r : ℕ)
      (q : GenLoop (Fin r) A A.point) : GenLoop (Fin r) B B.point :=
    ⟨f.map.comp q.val,fun z hz => (congrArg f.map (q.property z hz)).trans f.point⟩
  have hbeta2 (P : Prespectrum.{0}) (n r : ℕ)
      (q : GenLoop (Fin r) (P.level n).suspension (P.level n).suspension.point) :
      GenLoop.Homotopic
        (M (beta P (n+2)) (r+2)
          (stabilizeLoop P.suspension (n+1) (r+1) (stabilizeLoop P.suspension n r q)))
        (stabilizeLoop P (n+2) (r+1) (stabilizeLoop P (n+1) r (M (beta P n) r q))) := by
    let G : (P.level n).suspension.suspension.suspension ⟶ P.level (n+3) :=
      BasedSpace.suspendMap (BasedSpace.suspendMap (beta P n) ≫ beta P (n+1)) ≫ beta P (n+2)
    let j : GenLoop (Fin (r+2)) (P.level n).suspension.suspension.suspension
        (P.level n).suspension.suspension.suspension.point :=
      stabilizeLoop (suspensionSpectrum ((P.level n).suspension.suspension)) 0 (r+1)
        (stabilizeLoop (suspensionSpectrum ((P.level n).suspension)) 0 r q)
    obtain ⟨H⟩ := triple_suspension_cycle_homotopic (P.level n)
    refine ⟨{ toFun := fun z => G.map (H (z.1,j.val z.2))
              continuous_toFun := G.map.continuous.comp (H.continuous.comp
                (continuous_fst.prodMk (j.val.continuous.comp continuous_snd)))
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro z
      rw [H.apply_zero]
      change G.map ((suspensionSpectrumSuspensionIso (P.level n)).hom.level 2
        (BasedSpace.suspensionProjection _
          (BasedSpace.suspensionProjection _ (q.val (fun i => z i.succ.succ),z 1),z 0)))=
        (beta P (n+2)).map (P.suspension.bond (n+1)
          (P.suspension.bond n (q.val (fun i => z i.succ.succ),z 1),z 0))
      generalize hq : q.val (fun i => z i.succ.succ)=a
      refine Quot.inductionOn a ?_
      rintro ⟨a,s⟩
      have h := (suspensionSpectrumSuspensionIso_exists (P.level n)).choose_spec 2 a s ![z 0,z 1]
      exact congrArg G.map h
    · intro z
      rw [H.apply_one]
      rfl
    · intro t z hz
      change G.map (H (t,j.val z))=_
      rw [j.property z hz,H.eq_fst t (Set.mem_singleton _)]
      have hp := (suspensionSpectrumSuspensionIso (P.level n)).hom.point 2
      change G.map ((suspensionSpectrumSuspensionIso (P.level n)).hom.level 2
        (P.level n).suspension.suspension.suspension.point)=_
      exact (congrArg G.map hp).trans (G.point.trans
        ((M (beta P (n+2)) (r+2)
          (stabilizeLoop P.suspension (n+1) (r+1) (stabilizeLoop P.suspension n r q))).property z hz).symm)
  have hEbeta (P : Prespectrum.{0}) (n r : ℕ)
      (q : GenLoop (Fin r) (P.level n).suspension (P.level n).suspension.point) :
      GenLoop.Homotopic
        (stabilizeLoop (suspensionSpectrum (P.level (n+2))) 0 (r+1)
          (stabilizeLoop P (n+1) r (M (beta P n) r q)))
        (stabilizeLoop P.suspension (n+1) (r+1) (stabilizeLoop P.suspension n r q)) := by
    let G : (P.level n).suspension.suspension.suspension ⟶ (P.level (n+2)).suspension :=
      BasedSpace.suspendMap (BasedSpace.suspendMap (beta P n) ≫ beta P (n+1))
    let j : GenLoop (Fin (r+2)) (P.level n).suspension.suspension.suspension
        (P.level n).suspension.suspension.suspension.point :=
      stabilizeLoop (suspensionSpectrum ((P.level n).suspension.suspension)) 0 (r+1)
        (stabilizeLoop (suspensionSpectrum ((P.level n).suspension)) 0 r q)
    obtain ⟨H⟩ := (triple_suspension_cycle_homotopic (P.level n)).symm
    refine ⟨{ toFun := fun z => G.map (H (z.1,j.val z.2))
              continuous_toFun := G.map.continuous.comp (H.continuous.comp
                (continuous_fst.prodMk (j.val.continuous.comp continuous_snd)))
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro z
      rw [H.apply_zero]
      rfl
    · intro z
      rw [H.apply_one]
      change G.map ((suspensionSpectrumSuspensionIso (P.level n)).hom.level 2
        (BasedSpace.suspensionProjection _
          (BasedSpace.suspensionProjection _ (q.val (fun i => z i.succ.succ),z 1),z 0)))=
        P.suspension.bond (n+1) (P.suspension.bond n (q.val (fun i => z i.succ.succ),z 1),z 0)
      generalize hq : q.val (fun i => z i.succ.succ)=a
      refine Quot.inductionOn a ?_
      rintro ⟨a,s⟩
      have h := (suspensionSpectrumSuspensionIso_exists (P.level n)).choose_spec 2 a s ![z 0,z 1]
      exact congrArg G.map h
    · intro t z hz
      change G.map (H (t,j.val z))=_
      rw [j.property z hz,H.eq_fst t (Set.mem_singleton _)]
      exact G.point.trans (by
        symm
        exact (stabilizeLoop (suspensionSpectrum (P.level (n+2))) 0 (r+1)
          (stabilizeLoop P (n+1) r (M (beta P n) r q))).property z hz)
  let R (P : Prespectrum.{0}) (d : ℤ) (a : Representative P.suspension d) : Representative P (d-1) :=
    ⟨a.stage+1,a.dimension,by have := a.degree; omega,M (beta P a.stage) a.dimension a.loop⟩
  have hRhom (P : Prespectrum.{0}) (d : ℤ) (a : Representative P.suspension d)
      (p : GenLoop (Fin a.dimension) (P.suspension.level a.stage) (P.suspension.level a.stage).point)
      (hp : GenLoop.Homotopic a.loop p) :
      Quot.mk (StableRelation P (d-1)) (R P d a)=Quot.mk _ (R P d {a with loop:=p}) :=
    Quot.sound (StableRelation.homotopy (R P d a) _ (hp.comp_continuousMap (beta P a.stage).map))
  have hR2 (P : Prespectrum.{0}) (d : ℤ) (a : Representative P.suspension d) :
      Quot.mk (StableRelation P (d-1)) (R P d a.next.next)=Quot.mk _ (R P d a).next.next :=
    Quot.sound (StableRelation.homotopy (R P d a.next.next) _
      (hbeta2 P a.stage a.dimension a.loop))
  let phi (P : Prespectrum.{0}) (d : ℤ) (a : Representative P.suspension d) : StableHomotopy P (d-1) :=
    if a.stage%2=0 then Quot.mk _ (R P d a) else Quot.mk _ (R P d a.next)
  have hphi (P : Prespectrum.{0}) (d : ℤ) (a b : Representative P.suspension d)
      (h : StableRelation P.suspension d a b) : phi P d a=phi P d b := by
    cases h with
    | homotopy p hp =>
      by_cases ha : a.stage%2=0
      · dsimp only [phi]
        rw [if_pos ha,if_pos ha]
        exact hRhom P d a p hp
      · dsimp only [phi]
        rw [if_neg ha,if_neg ha]
        exact hRhom P d a.next _ (applicabilityStabilizeLoopHomotopic P.suspension _ _ _ _ hp)
    | stabilization =>
      by_cases ha : a.stage%2=0
      · have hn : a.next.stage%2≠0 := by change (a.stage+1)%2≠0; omega
        dsimp only [phi]
        rw [if_pos ha,if_neg hn,hR2]
        exact (Quot.sound (StableRelation.stabilization (R P d a))).trans
          (Quot.sound (StableRelation.stabilization (R P d a).next))
      · have hn : a.next.stage%2=0 := by change (a.stage+1)%2=0; omega
        dsimp only [phi]
        rw [if_neg ha,if_pos hn]
  let B (P : Prespectrum.{0}) (d : ℤ) : StableHomotopy P.suspension d → StableHomotopy P (d-1) :=
    Quot.lift (phi P d) (hphi P d)
  have even_rep (P : Prespectrum.{0}) (d : ℤ) (x : StableHomotopy P d) :
      ∃ a : Representative P d, a.stage%2=0 ∧ Quot.mk _ a=x := by
    refine Quot.inductionOn x ?_
    intro a
    by_cases ha : a.stage%2=0
    · exact ⟨a,ha,rfl⟩
    · refine ⟨a.next,?_,(Quot.sound (StableRelation.stabilization a)).symm⟩
      change (a.stage+1)%2=0
      omega
  have hBS (P : Prespectrum.{0}) (d : ℤ) : Function.LeftInverse (B P d) (S P d) := by
    intro a
    obtain ⟨a,ha,rfl⟩ := even_rep P (d-1) a
    rw [hSeven P d a ha]
    change phi P d ⟨a.stage,a.dimension+1,_,
      stabilizeLoop (suspensionSpectrum (P.level a.stage)) 0 a.dimension a.loop⟩=Quot.mk _ a
    dsimp only [phi]
    rw [if_pos ha]
    exact (Quot.sound (StableRelation.stabilization a)).symm
  have hSB (P : Prespectrum.{0}) (d : ℤ) : Function.RightInverse (B P d) (S P d) := by
    intro a
    obtain ⟨a,ha,rfl⟩ := even_rep P.suspension d a
    change S P d (phi P d a)=Quot.mk _ a
    dsimp only [phi]
    rw [if_pos ha]
    rw [Quot.sound (StableRelation.stabilization (R P d a))]
    have hn : (R P d a).next.stage%2=0 := by change (a.stage+1+1)%2=0; omega
    rw [hSeven P d (R P d a).next hn]
    have hh := Quot.sound (StableRelation.homotopy
      (⟨a.stage+2,a.dimension+2,by have := a.degree; omega,
        stabilizeLoop (suspensionSpectrum (P.level (a.stage+2))) 0 (a.dimension+1)
          (stabilizeLoop P (a.stage+1) a.dimension (M (beta P a.stage) a.dimension a.loop))⟩ :
        Representative P.suspension d) _ (hEbeta P a.stage a.dimension a.loop))
    exact hh.trans ((Quot.sound (StableRelation.stabilization a.next)).symm.trans
      (Quot.sound (StableRelation.stabilization a)).symm)
  exact ⟨fun P d => ⟨S P d,B P d,hBS P d,hSB P d⟩,hSnat,fun P d a ha => if_pos ha⟩


end KIP126.StableHomotopy.Spectra

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof
open KIP126.StableHomotopy.Spectra KIP126.StableHomotopy.Spectra.Prespectrum

private theorem stable_even_representative (P : Prespectrum.{0}) (d : ℤ)
    (x : StableHomotopy P d) :
    ∃ a : Representative P d, a.stage % 2 = 0 ∧ Quot.mk _ a = x := by
  refine Quot.inductionOn x ?_
  intro a
  by_cases ha : a.stage % 2 = 0
  · exact ⟨a, ha, rfl⟩
  · refine ⟨a.next, ?_, (Quot.sound (StableRelation.stabilization a)).symm⟩
    change (a.stage+1)%2=0
    omega

private theorem roofEndpoint_stableEquivalence_of_even_formula (P Q : Prespectrum.{0})
    (f : ∀ n, P.level n ⟶ Q.level n)
    (H : ∀ n, (bondSquareLeft P Q f n).Homotopy (bondSquareRight P Q f n))
    (Hpoint : ∀ n u t, H n (u,((P.level n).point,t)) = (Q.level (n+1)).point)
    (Hzero : ∀ n u x, H n (u,(x,0)) = (Q.level (n+1)).point)
    (Hone : ∀ n u x, H n (u,(x,1)) = (Q.level (n+1)).point)
    (e : ∀ d : ℤ, StableHomotopy P d ≃ StableHomotopy Q d)
    (he : ∀ (d : ℤ) (a : Representative P d), a.stage % 2 = 0 →
      e d (Quot.mk _ a) = loopClass Q d a.stage a.dimension a.degree
        (basedLoopMap (f a.stage) a.loop)) :
    stableEquivalences (roofEndpoint P Q f H Hpoint Hzero Hone) := by
  intro d
  have hh : stableHomotopyMap (roofEndpoint P Q f H Hpoint Hzero Hone) d =
      e d ∘ stableHomotopyMap (roofProjection P Q f H Hpoint Hzero Hone) d := by
    funext z
    obtain ⟨a, ha, rfl⟩ := stable_even_representative _ d z
    rw [roofEndpoint_loop_formula]
    exact (he d (a.map (roofProjection P Q f H Hpoint Hzero Hone)) ha).symm
  rw [hh]
  exact (e d).bijective.comp
    (roofProjection_stableEquivalence P Q f H Hpoint Hzero Hone d)

end KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof

namespace KIP126.StableHomotopy.Spectra.Prespectrum
private theorem stable_tail_shift_formula :
    ∃ e : ∀ (X : Prespectrum.{0}) (d : ℤ),
      StableHomotopy X.tail d ≃ StableHomotopy X (d-1),
      (∀ {X Y} (f : X ⟶ Y) (d : ℤ) (a : StableHomotopy X.tail d),
        e Y d (stableHomotopyMap (tailMap f) d a)=
          stableHomotopyMap f (d-1) (e X d a)) ∧
      (∀ (X : Prespectrum.{0}) (d : ℤ) (a : Representative X.tail d),
        e X d (Quot.mk _ a)=Quot.mk _
          (⟨a.stage+1,a.dimension,by have := a.degree; omega,a.loop⟩ :
            Representative X (d-1))) := by
  let L (X : Prespectrum.{0}) (d : ℤ) (a : Representative X.tail d) :
      Representative X (d-1) :=
    ⟨a.stage+1,a.dimension,by have := a.degree; omega,a.loop⟩
  let R (X : Prespectrum.{0}) (d : ℤ) (a : Representative X (d-1)) :
      Representative X.tail d :=
    ⟨a.stage,a.dimension+1,by have := a.degree; omega,
      stabilizeLoop X a.stage a.dimension a.loop⟩
  have hL (X : Prespectrum.{0}) (d : ℤ) (a b : Representative X.tail d)
      (h : StableRelation X.tail d a b) :
      Quot.mk (StableRelation X (d-1)) (L X d a)=Quot.mk _ (L X d b) := by
    cases h with
    | homotopy p hp => exact Quot.sound (StableRelation.homotopy (L X d a) p hp)
    | stabilization => exact Quot.sound (StableRelation.stabilization (L X d a))
  have hR (X : Prespectrum.{0}) (d : ℤ) (a b : Representative X (d-1))
      (h : StableRelation X (d-1) a b) :
      Quot.mk (StableRelation X.tail d) (R X d a)=Quot.mk _ (R X d b) := by
    cases h with
    | homotopy p hp =>
      exact Quot.sound (StableRelation.homotopy (R X d a)
        (stabilizeLoop X a.stage a.dimension p) (KIP126.StableHomotopy.Spectra.Prespectrum.applicabilityStabilizeLoopHomotopic X _ _ _ _ hp))
    | stabilization => exact Quot.sound (StableRelation.stabilization (R X d a))
  let e (X : Prespectrum.{0}) (d : ℤ) : StableHomotopy X.tail d ≃ StableHomotopy X (d-1) :=
    { toFun := Quot.lift (fun a => Quot.mk _ (L X d a)) (hL X d)
      invFun := Quot.lift (fun a => Quot.mk _ (R X d a)) (hR X d)
      left_inv := by
        intro a
        refine Quot.inductionOn a ?_
        intro a
        exact (Quot.sound (StableRelation.stabilization a)).symm
      right_inv := by
        intro a
        refine Quot.inductionOn a ?_
        intro a
        exact (Quot.sound (StableRelation.stabilization a)).symm }
  refine ⟨e,?_,?_⟩
  · intro X Y f d a
    refine Quot.inductionOn a ?_
    intro a
    rfl
  · intro X d a
    rfl



end KIP126.StableHomotopy.Spectra.Prespectrum

namespace KIP126.StableHomotopy.Spectra
open Prespectrum
open KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof
private theorem stable_cancellation_equivalence_formula :
    ∃ e : ∀ (X : Prespectrum.{0}) (d : ℤ),
      StableHomotopy X.desuspension.suspension d ≃ StableHomotopy X d,
      ∀ X d (a : Representative X.desuspension.suspension d), a.stage % 2 = 0 →
        e X d (Quot.mk _ a) = loopClass X d a.stage a.dimension a.degree
          (basedLoopMap (sourceBondAdjoint X.desuspension a.stage) a.loop) := by
  obtain ⟨S, _, hS⟩ := stable_suspension_equivalence_formula
  obtain ⟨T, _, hT⟩ := stable_tail_shift_formula
  let e (X : Prespectrum.{0}) (d : ℤ) :
      StableHomotopy X.desuspension.suspension d ≃ StableHomotopy X d :=
    (S X.desuspension d).symm.trans (T X.desuspension d).symm
  refine ⟨e, ?_⟩
  intro X d a ha
  change (T X.desuspension d).symm ((S X.desuspension d).symm (Quot.mk _ a)) = _
  rw [hS X.desuspension d a ha]
  apply (T X.desuspension d).injective
  rw [Equiv.apply_symm_apply]
  exact (hT X.desuspension d
    ⟨a.stage,a.dimension,a.degree,basedLoopMap (sourceBondAdjoint X.desuspension a.stage) a.loop⟩).symm
end KIP126.StableHomotopy.Spectra

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRotation

private theorem cube_quarter_turn_homotopy :
    ∃ H : C(I × (Fin 2 → I),Fin 2 → I),
      (∀ z, H (0,z)=z) ∧ (∀ z, H (1,z)=![unitInterval.symm (z 1),z 0]) ∧
      ∀ t z, z ∈ Cube.boundary (Fin 2) → H (t,z) ∈ Cube.boundary (Fin 2) := by
  let P (v : Fin 2 → ℝ) : Fin 2 → ℝ := ![-v 1,v 0]
  have hPc : Continuous P := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply 1).neg
    · exact continuous_apply 0
  have hPn (v : Fin 2 → ℝ) : ‖P v‖ = ‖v‖ := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      fin_cases i
      · simpa [P] using norm_le_pi_norm v 1
      · exact norm_le_pi_norm v 0
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      fin_cases i
      · exact norm_le_pi_norm (P v) 1
      · simpa [P] using norm_le_pi_norm (P v) 0
  let L (t : I) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
    (1-(t:ℝ)) • v + (t:ℝ) • P v
  have hLc : Continuous (fun z : I × (Fin 2 → ℝ) => L z.1 z.2) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul continuous_snd |>.add
      ((continuous_subtype_val.comp continuous_fst).smul (hPc.comp continuous_snd))
  have hLzero (t : I) (v : Fin 2 → ℝ) (h : L t v = 0) : v = 0 := by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    change (1-(t:ℝ))*v 0 + (t:ℝ)*(-v 1) = 0 at h0
    change (1-(t:ℝ))*v 1 + (t:ℝ)*v 0 = 0 at h1
    have hD : 0 < (1-(t:ℝ))^2 + (t:ℝ)^2 := by
      nlinarith [sq_nonneg ((t:ℝ)-1/2)]
    have hv0 : ((1-(t:ℝ))^2 + (t:ℝ)^2)*v 0 = 0 := by
      linear_combination (1-(t:ℝ))*h0 + (t:ℝ)*h1
    have hv1 : ((1-(t:ℝ))^2 + (t:ℝ)^2)*v 1 = 0 := by
      linear_combination (1-(t:ℝ))*h1 - (t:ℝ)*h0
    funext i
    fin_cases i
    · exact (mul_eq_zero.mp hv0).resolve_left hD.ne'
    · exact (mul_eq_zero.mp hv1).resolve_left hD.ne'
  let N (t : I) (v : Fin 2 → ℝ) : Fin 2 → ℝ := (‖v‖/‖L t v‖) • L t v
  have hNzero (t : I) : N t 0=0 := by simp [N]
  have hNnorm (t : I) (v : Fin 2 → ℝ) : ‖N t v‖=‖v‖ := by
    by_cases hv : v=0
    · simp [hv,hNzero]
    have hLn : ‖L t v‖ ≠ 0 := norm_ne_zero_iff.mpr (fun h => hv (hLzero t v h))
    change ‖(‖v‖/‖L t v‖) • L t v‖=‖v‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)),
      div_mul_cancel₀ _ hLn]
  have hNc : Continuous (fun z : I × (Fin 2 → ℝ) => N z.1 z.2) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z.2=0
    · change Tendsto (fun z : I × (Fin 2 → ℝ) => N z.1 z.2) (𝓝 z) (𝓝 (N z.1 z.2))
      rw [hz,hNzero]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp only [hNnorm]
      have hh : Tendsto (fun z : I × (Fin 2 → ℝ) => ‖z.2‖) (𝓝 z) (𝓝 ‖z.2‖) :=
        continuous_snd.norm.continuousAt
      rw [hz,norm_zero] at hh
      exact hh
    · exact ((continuous_snd.norm.continuousAt).div hLc.norm.continuousAt
        (norm_ne_zero_iff.mpr (fun h => hz (hLzero z.1 z.2 h)))).smul hLc.continuousAt
  have hN0 (v : Fin 2 → ℝ) : N 0 v=v := by
    by_cases hv : v=0
    · simp [hv,hNzero]
    simp [N,L,div_self (norm_ne_zero_iff.mpr hv)]
  have hN1 (v : Fin 2 → ℝ) : N 1 v=P v := by
    by_cases hv : v=0
    · rw [hv,hNzero]
      funext i
      fin_cases i <;> simp [P]
    simp [N,L,hPn,div_self (norm_ne_zero_iff.mpr hv)]
  let c (z : Fin 2 → I) : Fin 2 → ℝ := fun i => (z i:ℝ)-1/2
  have hc : Continuous c := continuous_pi fun i =>
    ((continuous_subtype_val.comp (continuous_apply i)).sub continuous_const)
  have hcn (z : Fin 2 → I) : ‖c z‖ ≤ 1/2 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    change |(z i:ℝ)-1/2| ≤ 1/2
    rw [abs_le]
    constructor <;> linarith [(z i).2.1,(z i).2.2]
  have hbound (t : I) (z : Fin 2 → I) (i : Fin 2) :
      N t (c z) i+1/2 ∈ Set.Icc (0:ℝ) 1 := by
    have hi : |N t (c z) i| ≤ 1/2 :=
      (norm_le_pi_norm (N t (c z)) i).trans ((hNnorm t (c z)).le.trans (hcn z))
    rw [abs_le] at hi
    constructor <;> linarith
  let H : C(I × (Fin 2 → I),Fin 2 → I) :=
    ⟨fun p i => ⟨N p.1 (c p.2) i+1/2,hbound p.1 p.2 i⟩,by
      apply continuous_pi
      intro i
      exact (((continuous_apply i).comp (hNc.comp
        (continuous_fst.prodMk (hc.comp continuous_snd)))).add continuous_const).subtype_mk _⟩
  refine ⟨H,?_,?_,?_⟩
  · intro z
    funext i
    apply Subtype.ext
    change N 0 (c z) i+1/2=(z i:ℝ)
    rw [hN0]
    dsimp [c]
    ring
  · intro z
    funext i
    apply Subtype.ext
    change N 1 (c z) i+1/2=(![unitInterval.symm (z 1),z 0] i:ℝ)
    rw [hN1]
    fin_cases i <;> simp [P,c,unitInterval.coe_symm_eq]; ring
  · intro t z hz
    have hn : ‖c z‖=1/2 := by
      apply le_antisymm (hcn z)
      obtain ⟨i,hi⟩ := hz
      have hle := norm_le_pi_norm (c z) i
      rcases hi with hi | hi <;> norm_num [c,hi] at hle ⊢ <;> exact hle
    by_contra hh
    have hstrict : ∀ i : Fin 2, ‖N t (c z) i‖ < 1/2 := by
      intro i
      have hi₀ : H (t,z) i ≠ 0 := fun h => hh ⟨i,Or.inl h⟩
      have hi₁ : H (t,z) i ≠ 1 := fun h => hh ⟨i,Or.inr h⟩
      have hb := hbound t z i
      have h0 : N t (c z) i+1/2 ≠ 0 := fun h => hi₀ (Subtype.ext h)
      have h1 : N t (c z) i+1/2 ≠ 1 := fun h => hi₁ (Subtype.ext h)
      rw [Real.norm_eq_abs,abs_lt]
      constructor <;> grind
    have hlt : ‖N t (c z)‖ < 1/2 := (pi_norm_lt_iff (by norm_num)).mpr hstrict
    rw [hNnorm,hn] at hlt
    exact (lt_irrefl _ hlt)



open KIP126.StableHomotopy.Spectra
set_option backward.isDefEq.respectTransparency false

private noncomputable def intervalSign : ℕ → C(I,I)
  | 0 => ⟨unitInterval.symm,unitInterval.continuous_symm⟩
  | n+1 => ⟨fun t => unitInterval.symm (intervalSign n t),
      unitInterval.continuous_symm.comp (intervalSign n).continuous⟩

private theorem intervalSign_boundary (n : ℕ) (t : I) (ht : t=0 ∨ t=1) :
    intervalSign n t=0 ∨ intervalSign n t=1 := by
  induction n with
  | zero =>
    rcases ht with h | h
    · right; change unitInterval.symm t=1; rw [h]; exact unitInterval.symm_zero
    · left; change unitInterval.symm t=0; rw [h]; exact unitInterval.symm_one
  | succ n ih =>
    rcases ih with h | h
    · right; change unitInterval.symm (intervalSign n t)=1; rw [h]; exact unitInterval.symm_zero
    · left; change unitInterval.symm (intervalSign n t)=0; rw [h]; exact unitInterval.symm_one

private theorem intervalSign_flip (n : ℕ) (t : I) :
    unitInterval.symm (intervalSign (n+1) t)=intervalSign n t :=
  unitInterval.symm_symm _

private noncomputable def signedBond (X : Prespectrum.{0}) (n : ℕ) :
    (X.level n).suspension ⟶ X.level (n+1) := by
  let raw : C(X.level n × I,X.level (n+1)) :=
    (X.bond n).comp ⟨fun p => (p.1,intervalSign n p.2),
      continuous_fst.prodMk ((intervalSign n).continuous.comp continuous_snd)⟩
  have hc (p : X.level n × I) (hp : BasedSpace.SuspensionCollapsed (X.level n) p) :
      raw p=(X.level (n+1)).point := by
    rcases hp with h | h
    · change X.bond n (p.1,intervalSign n p.2)=_
      rw [h,X.bond_point]
    · rcases intervalSign_boundary n p.2 h with h | h
      · change X.bond n (p.1,intervalSign n p.2)=_; rw [h,X.bond_zero]
      · change X.bond n (p.1,intervalSign n p.2)=_; rw [h,X.bond_one]
  have hr : ∀ a b, BasedSpace.SuspensionRelation (X.level n) a b → raw a=raw b :=
    fun a b h => (hc a h.1).trans (hc b h.2).symm
  exact ⟨⟨Quot.lift raw hr,continuous_quot_lift hr raw.continuous⟩,hc _ (Or.inl rfl)⟩

private theorem signedBond_apply (X : Prespectrum.{0}) (n : ℕ) (a : X.level n) (s : I) :
    (signedBond X n).map (BasedSpace.suspensionProjection _ (a,s)) =
      X.bond n (a,intervalSign n s) := rfl

private noncomputable def cancellationLevel (X : Prespectrum.{0}) :
    ∀ n, X.desuspension.suspension.level n ⟶ X.level n
  | 0 => ⟨ContinuousMap.const _ (X.level 0).point,rfl⟩
  | n+1 => signedBond X n

private noncomputable def cancellationLeft (X : Prespectrum.{0}) (n : ℕ) :
    C(X.desuspension.suspension.level n × I,X.level (n+1)) :=
  (cancellationLevel X (n+1)).map.comp (X.desuspension.suspension.bond n)

private noncomputable def cancellationRight (X : Prespectrum.{0}) (n : ℕ) :
    C(X.desuspension.suspension.level n × I,X.level (n+1)) :=
  (X.bond n).comp ((cancellationLevel X n).map.prodMap (ContinuousMap.id I))

private theorem cancellationSquare_succ (X : Prespectrum.{0}) (n : ℕ) :
    Nonempty ((cancellationLeft X (n+1)).HomotopyRel (cancellationRight X (n+1))
      {p | BasedSpace.SuspensionCollapsed (X.desuspension.suspension.level (n+1)) p}) := by
  obtain ⟨H,hH0,hH1,hHb⟩ := cube_quarter_turn_homotopy
  let A := X.level n
  let B := X.level (n+2)
  let val (a : A) (z : Fin 2 → I) : B := X.bond (n+1) (X.bond n (a,z 0),z 1)
  have hval : Continuous (fun p : A × (Fin 2 → I) => val p.1 p.2) :=
    (X.bond (n+1)).continuous.comp
      (((X.bond n).continuous.comp
        (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))).prodMk
          ((continuous_apply 1).comp continuous_snd))
  have hvalp (z : Fin 2 → I) : val A.point z=B.point := by
    change X.bond (n+1) (X.bond n ((X.level n).point,z 0),z 1)=_
    rw [X.bond_point,X.bond_point]
  have hvalb (a : A) (z : Fin 2 → I) (hz : z ∈ Cube.boundary (Fin 2)) :
      val a z=B.point := by
    obtain ⟨i,hi⟩ := hz
    fin_cases i
    · rcases hi with h | h
      · change X.bond (n+1) (X.bond n (a,z 0),z 1)=_
        change z 0=0 at h
        rw [h,X.bond_zero,X.bond_point]
      · change X.bond (n+1) (X.bond n (a,z 0),z 1)=_
        change z 0=1 at h
        rw [h,X.bond_one,X.bond_point]
    · rcases hi with h | h
      · change z 1=0 at h
        change X.bond (n+1) (X.bond n (a,z 0),z 1)=_; rw [h,X.bond_zero]
      · change z 1=1 at h
        change X.bond (n+1) (X.bond n (a,z 0),z 1)=_; rw [h,X.bond_one]
  let raw : C((A × I) × (I × I),B) :=
    ⟨fun p => val p.1.1 (H (p.2.1,![p.2.2,intervalSign (n+1) p.1.2])),by
      refine hval.comp (f := fun p : (A × I) × (I × I) =>
        (p.1.1,H (p.2.1,![p.2.2,intervalSign (n+1) p.1.2]))) ?_
      apply Continuous.prodMk continuous_fst.fst
      apply H.continuous.comp
      apply Continuous.prodMk continuous_snd.fst
      apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_snd.snd
      · exact (intervalSign (n+1)).continuous.comp continuous_fst.snd⟩
  have hc (p : A × I) (k : I × I) (hp : BasedSpace.SuspensionCollapsed A p) :
      raw (p,k)=B.point := by
    rcases hp with h | h
    · change val p.1 (H (k.1,![k.2,intervalSign (n+1) p.2]))=B.point
      rw [h]
      exact hvalp _
    · exact hvalb _ _ (hHb _ _ ⟨1,intervalSign_boundary (n+1) p.2 h⟩)
  have hr (k : I × I) : ∀ a b, BasedSpace.SuspensionRelation A a b →
      raw (a,k)=raw (b,k) := fun a b h => (hc a k h.1).trans (hc b k h.2).symm
  let F : C(A.suspension × (I × I),B) :=
    ⟨fun p => Quot.lift (fun a => raw (a,p.2)) (hr p.2) p.1,by
      apply isQuotientMap_quot_mk.continuous_lift_prod_left
      exact raw.continuous⟩
  have hF (a : A) (s u t : I) :
      F (BasedSpace.suspensionProjection A (a,s),(u,t))=
        val a (H (u,![t,intervalSign (n+1) s])) := rfl
  have hFp (u t : I) : F (A.suspension.point,(u,t))=B.point :=
    hc (A.point,0) (u,t) (Or.inl rfl)
  refine ⟨{ toFun := fun p => F (p.2.1,(p.1,p.2.2))
            continuous_toFun := F.continuous.comp
              (continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd))
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · rintro ⟨q,t⟩
    refine Quot.inductionOn q ?_
    rintro ⟨a,s⟩
    change val a (H (0,![t,intervalSign (n+1) s])) = _
    rw [hH0]
    rfl
  · rintro ⟨q,t⟩
    refine Quot.inductionOn q ?_
    rintro ⟨a,s⟩
    change val a (H (1,![t,intervalSign (n+1) s])) = _
    rw [hH1]
    change X.bond (n+1) (X.bond n (a,unitInterval.symm (intervalSign (n+1) s)),t)=
      X.bond (n+1) (X.bond n (a,intervalSign n s),t)
    rw [intervalSign_flip]
  · intro u p hp
    have hl : cancellationLeft X (n+1) p=B.point := by
      rcases hp with h | h | h
      · change (cancellationLevel X (n+2)).map
          (X.desuspension.suspension.bond (n+1) (p.1,p.2))=B.point
        rw [h,X.desuspension.suspension.bond_point]
        exact (cancellationLevel X (n+2)).point
      · change (cancellationLevel X (n+2)).map
          (X.desuspension.suspension.bond (n+1) (p.1,p.2))=B.point
        rw [h,X.desuspension.suspension.bond_zero]
        exact (cancellationLevel X (n+2)).point
      · change (cancellationLevel X (n+2)).map
          (X.desuspension.suspension.bond (n+1) (p.1,p.2))=B.point
        rw [h,X.desuspension.suspension.bond_one]
        exact (cancellationLevel X (n+2)).point
    rw [hl]
    rcases hp with h | h
    · change F (p.1,(u,p.2))=B.point
      rw [h]
      exact hFp _ _
    · rcases p with ⟨q,t⟩
      refine Quot.inductionOn q ?_
      rintro ⟨a,s⟩
      change val a (H (u,![t,intervalSign (n+1) s]))=B.point
      exact hvalb _ _ (hHb _ _ ⟨0,h⟩)


private theorem cancellationSquare_zero (X : Prespectrum.{0}) :
    Nonempty ((cancellationLeft X 0).HomotopyRel (cancellationRight X 0)
      {p | BasedSpace.SuspensionCollapsed (X.desuspension.suspension.level 0) p}) := by
  have hL : cancellationLeft X 0=ContinuousMap.const _ (X.level 1).point := by
    apply ContinuousMap.ext
    rintro ⟨q,t⟩
    refine Quot.inductionOn q ?_
    rintro ⟨a,s⟩
    change X.bond 0 ((X.level 0).point,intervalSign 0 s)=(X.level 1).point
    exact X.bond_point _ _
  have hR : cancellationRight X 0=ContinuousMap.const _ (X.level 1).point := by
    apply ContinuousMap.ext
    rintro ⟨q,t⟩
    exact X.bond_point _ _
  rw [hL,hR]
  exact ⟨ContinuousMap.HomotopyRel.refl _ _⟩

private theorem cancellationSquare (X : Prespectrum.{0}) (n : ℕ) :
    Nonempty ((cancellationLeft X n).HomotopyRel (cancellationRight X n)
      {p | BasedSpace.SuspensionCollapsed (X.desuspension.suspension.level n) p}) := by
  cases n with
  | zero => exact cancellationSquare_zero X
  | succ n => exact cancellationSquare_succ X n

private theorem intervalSign_formula (n : ℕ) (s : I) :
    intervalSign n s=if n%2=0 then unitInterval.symm s else s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change unitInterval.symm (intervalSign n s)=_
    by_cases hn : n%2=0
    · have hn' : (n+1)%2≠0 := by omega
      rw [ih,if_pos hn,if_neg hn',unitInterval.symm_symm]
    · have hn' : (n+1)%2=0 := by omega
      rw [ih,if_neg hn,if_pos hn']

private theorem cancellationLevel_even (X : Prespectrum.{0}) (n : ℕ)
    (hn : (n+1)%2=0) (a : X.level n) (s : I) :
    (cancellationLevel X (n+1)).map (BasedSpace.suspensionProjection _ (a,s)) =
      X.bond n (a,s) := by
  change X.bond n (a,intervalSign n s)=_
  rw [intervalSign_formula,if_neg (show n%2≠0 by omega)]

private theorem cancellationHomotopyData (X : Prespectrum.{0}) :
    ∃ H : ∀ n, (cancellationLeft X n).Homotopy (cancellationRight X n),
      (∀ n u t, H n (u,((X.desuspension.suspension.level n).point,t)) =
        (X.level (n+1)).point) ∧
      (∀ n u x, H n (u,(x,0))=(X.level (n+1)).point) ∧
      (∀ n u x, H n (u,(x,1))=(X.level (n+1)).point) := by
  let H (n : ℕ) := Classical.choice (cancellationSquare X n)
  refine ⟨fun n => (H n).toHomotopy,?_,?_,?_⟩
  · intro n u t
    exact ((H n).eq_fst u (Or.inl rfl)).trans (by
      change (cancellationLevel X (n+1)).map
        (X.desuspension.suspension.bond n ((X.desuspension.suspension.level n).point,t))=_
      rw [X.desuspension.suspension.bond_point]
      exact (cancellationLevel X (n+1)).point)
  · intro n u x
    exact ((H n).eq_fst u (Or.inr (Or.inl rfl))).trans (by
      change (cancellationLevel X (n+1)).map
        (X.desuspension.suspension.bond n (x,0))=_
      rw [X.desuspension.suspension.bond_zero]
      exact (cancellationLevel X (n+1)).point)
  · intro n u x
    exact ((H n).eq_fst u (Or.inr (Or.inr rfl))).trans (by
      change (cancellationLevel X (n+1)).map
        (X.desuspension.suspension.bond n (x,1))=_
      rw [X.desuspension.suspension.bond_one]
      exact (cancellationLevel X (n+1)).point)

end KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRotation

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof
open KIP126.StableHomotopy.Spectra KIP126.StableHomotopy.Spectra.Prespectrum
open KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRotation

private theorem cancellationLevel_eq_bond_even (X : Prespectrum.{0})
    (n : ℕ) (hn : n % 2 = 0) :
    cancellationLevel X n = sourceBondAdjoint X.desuspension n := by
  apply BasedSpace.Hom.ext
  apply ContinuousMap.ext
  intro q
  cases n with
  | zero =>
    refine Quot.inductionOn q ?_
    rintro ⟨a,t⟩
    rfl
  | succ n =>
    refine Quot.inductionOn q ?_
    rintro ⟨a,t⟩
    exact cancellationLevel_even X n hn a t

private theorem source_suspension_desuspension_iso (X : Prespectrum.{0}) :
    Nonempty (sourceLocalization.obj X.desuspension.suspension ≅
      sourceLocalization.obj X) := by
  obtain ⟨H, Hpoint, Hzero, Hone⟩ := cancellationHomotopyData X
  let R := roofPrespectrum X.desuspension.suspension X (cancellationLevel X) H Hpoint Hzero Hone
  let p : R ⟶ X.desuspension.suspension :=
    roofProjection X.desuspension.suspension X (cancellationLevel X) H Hpoint Hzero Hone
  let q : R ⟶ X :=
    roofEndpoint X.desuspension.suspension X (cancellationLevel X) H Hpoint Hzero Hone
  have hp : stableEquivalences p :=
    roofProjection_stableEquivalence _ _ _ _ _ _ _
  have hq : stableEquivalences q := by
    obtain ⟨e, he⟩ := stable_cancellation_equivalence_formula
    apply roofEndpoint_stableEquivalence_of_even_formula _ _ _ _ _ _ _ (e X)
    intro d a ha
    rw [he X d a ha, cancellationLevel_eq_bond_even X a.stage ha]
  letI : IsIso (sourceLocalization.map p) := stableEquivalences.Q_inverts _ hp
  letI : IsIso (sourceLocalization.map q) := stableEquivalences.Q_inverts _ hq
  exact ⟨(asIso (sourceLocalization.map p)).symm ≪≫ asIso (sourceLocalization.map q)⟩

end KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams

namespace KIP126.AdamsSynthetic.Standard.SphereConvergence.ShiftModule
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
variable (H : Mod2EilenbergMacLane (C := C)) [(tensorLeft H.HF2).CommShift ℤ]

/-- Transport the actual action using the selected tensor-left shift comparison. -/
private noncomputable def shiftedAction {N : C} (act : H.HF2 ⊗ N ⟶ N) (d : ℤ) :
    H.HF2 ⊗ N⟦d⟧ ⟶ N⟦d⟧ :=
  ((tensorLeft H.HF2).commShiftIso d).hom.app N ≫ act⟦d⟧'

/-- The already specified unit/shift coherence preserves the actual action unit law. -/
private theorem shiftedAction_unit [(mod2UnitNatTrans H).CommShift ℤ]
    {N : C} (act : H.HF2 ⊗ N ⟶ N)
    (hact : adamsUnit H.unit N ≫ act = 𝟙 N) (d : ℤ) :
    adamsUnit H.unit (N⟦d⟧) ≫ shiftedAction H act d = 𝟙 (N⟦d⟧) := by
  rw [shiftedAction, ← Category.assoc, mod2Unit_shift,
    ← Functor.map_comp, hact]
  exact (shiftFunctor C d).map_id N


end KIP126.AdamsSynthetic.Standard.SphereConvergence.ShiftModule

end StandardSphereApplicabilitySupport

namespace KIP126.Def

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated

/-- The prespectrum suspension cancellation from §7.2, constructed
by an actual mapping-path roof. Its left leg is a levelwise based homotopy
equivalence, and the right leg is a stable equivalence by the explicit
signed-bond formulas on even representatives. All iterated instances follow
from the previously proved source desuspension functor. -/
private theorem standardSphereSourceDesuspensionCancellation :
    Nonempty
      (StableHomotopy.Spectra.sourceLocalization.obj
          StableHomotopy.Spectra.sourceHF2.spectrum.desuspension.suspension ≅
        StableHomotopy.Spectra.sourceLocalization.obj
          StableHomotopy.Spectra.sourceHF2.spectrum) := by
  exact KIP126.AdamsSynthetic.Standard.SphereConvergence.SourceCancellationRoof.source_suspension_desuspension_iso
    StableHomotopy.Spectra.sourceHF2.spectrum

/-- Recognition of all negative shifts, reduced to the actual source
cancellation above, using the same completion and SourceComparison. -/
private theorem standardSphereNegativeShiftComparison (n : ℕ) :
    Nonempty
      (standardHF2AdamsContext.sourceComparison.equivalence.functor.obj
        (StableHomotopy.Spectra.completedLocalization.obj
          ((StableHomotopy.Spectra.Prespectrum.desuspension^[n])
            StableHomotopy.Spectra.sourceHF2.spectrum)) ≅
        (CategoryTheory.shiftFunctor standardHF2AdamsContext.stableContext.Spectrum
          (-(n : ℤ))).obj standardHF2AdamsContext.stableContext.hf2.HF2) := by
  obtain ⟨e⟩ := standardSphereSourceDesuspensionCancellation
  exact ⟨KIP126.AdamsSynthetic.Standard.SphereConvergence.Local.completed_negative_shift_comparison
    standardHF2AdamsContext.sourceComparison
    (fun k => ⟨StableHomotopy.Spectra.Prespectrum.sourceCancellationIter
      StableHomotopy.Spectra.sourceHF2.spectrum e k⟩) n⟩

/-- Degreewise finiteness uses only the fixed HF₂ groups and tensor unit. -/
theorem standardSphereFiniteMod2Type : StableHomotopy.FiniteMod2Type
    standardHF2AdamsContext.stableContext.hf2
    (StableHomotopy.SphereSpectrum
      (C := standardHF2AdamsContext.stableContext.Spectrum)) :=
  StableHomotopy.finiteMod2Type_sphere _

/-- Separation of the Adams filtration on the fixed 2-completed sphere,
derived from the accepted strong-convergence background on that same tower. -/
theorem standardSphereSeparated : Classical.Adams.ClassicalSphereSeparated
    Classical.Adams.standardFoundation.hf2 := by
  have h := standardSphereApplicability
  exact (open CategoryTheory KIP126.StableHomotopy KIP126.Classical.Adams in by
    set_option backward.isDefEq.respectTransparency false in
      intro n a ha
      let V := towerAbutment (SphereSpectrum (C := standardHF2AdamsContext.stableContext.Spectrum)) n
      let S : Submodule ℤ V := Submodule.span ℤ {a}
      have hs : (ModuleCat.subobjectModule V).symm S = ⊥ := by
        apply h.strongly_convergent.separated n
        intro s
        apply (ModuleCat.subobjectModule V).symm.monotone
        apply Submodule.span_le.mpr
        intro x hx
        have hxa := Set.mem_singleton_iff.mp hx
        rw [hxa]
        change a ∈ TowerDetection.filtrationSubmodule standardFoundation.hf2.unit SphereSpectrum s n
        have hh := ha s.toNat
        simpa only [TowerDetection.filtrationSubmodule, Int.toNat_natCast] using hh
      have hz : S = ⊥ := by
        have hh := congrArg (ModuleCat.subobjectModule V) hs
        simpa using hh
      have ham : a ∈ S := Submodule.subset_span (Set.mem_singleton a)
      rw [hz] at ham
      exact (Submodule.mem_bot ℤ).mp ham)

end KIP126.Def
