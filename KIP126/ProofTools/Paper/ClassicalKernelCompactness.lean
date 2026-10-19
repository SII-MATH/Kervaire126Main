module

import KIP126.SpectralSequence.Internal.Algebra.Completion.Data
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Subobject

/-! Compactness of actual finite filtration quotients.  No convergence of an
extension spectral sequence is assumed: compatible residue classes are
constructed by the finite inverse-system theorem and lifted by the given
canonical completion cone. -/

namespace KIP126.ProofTools.Paper
open CategoryTheory CategoryTheory.Limits KIP126.Core.SpectralSequence
noncomputable section
universe v w
set_option backward.isDefEq.respectTransparency false

private theorem finite_filtration_compactness
    {ι : Type w} {A : ι → ModuleCat.{v} ℤ}
    (F : Filtration A) (i : ι) (hc : F.CompletionWitness i)
    (hf : ∀ k : ℤ, Finite (F.quotientAt k i))
    (S : ℤ → Set (A i)) (hS : Antitone S) (hne : ∀ k, (S k).Nonempty) :
    ∃ a : A i, ∀ k : ℤ, ∃ b : A i, b ∈ S k ∧
      F.quotientProjection k i a = F.quotientProjection k i b := by
  classical
  let Q : OrderDual ℤ ⥤ Type v := {
    obj := fun k => {q : F.quotientAt k i //
      ∃ a : A i, a ∈ S k ∧ F.quotientProjection k i a = q}
    map := fun {k l} f => ↾fun q => ⟨F.quotientTransition f.le i q.val, by
      obtain ⟨a, ha, hq⟩ := q.property
      refine ⟨a, hS f.le ha, ?_⟩
      rw [← hq]
      exact (ConcreteCategory.congr_hom (F.quotientProjection_transition f.le i) a).symm⟩
    map_id := by
      intro k
      ext q
      change F.quotientTransition (le_rfl : (k : ℤ) ≤ k) i q.val = q.val
      simp only [F.quotientTransition_id, ModuleCat.id_apply]
    map_comp := by
      intro k l m f g
      ext q
      exact (ConcreteCategory.congr_hom (F.quotientTransition_comp g.le f.le i) q.val).symm }
  letI : ∀ k : OrderDual ℤ, Finite (Q.obj k) := fun k => by
    haveI := hf k
    exact Subtype.finite
  letI : ∀ k : OrderDual ℤ, Nonempty (Q.obj k) := fun k => by
    obtain ⟨a, ha⟩ := hne k
    exact ⟨⟨F.quotientProjection k i a, a, ha, rfl⟩⟩
  obtain ⟨q, hq⟩ := nonempty_sections_of_finite_cofiltered_system Q
  let q' : ∀ k : OrderDual ℤ, F.quotientAt k i := fun k => (q k).val
  have hq' : q' ∈ ((F.quotientTower i) ⋙ forget (ModuleCat ℤ)).sections := by
    intro k l f
    exact congrArg Subtype.val (hq f)
  have hlim := isLimitOfPreserves (forget (ModuleCat ℤ)) hc.isLimit
  obtain ⟨a, ha, _⟩ := (Types.isLimit_iff _).mp ⟨hlim⟩ q' hq'
  refine ⟨a, fun k => ?_⟩
  obtain ⟨b, hb, hproj⟩ := (q k).property
  exact ⟨b, hb, (ha k).trans hproj.symm⟩

private theorem finite_quotientAt_of_range {ι : Type w} {A : GradedObject ι (ModuleCat.{v} ℤ)}
    (F : Filtration A) (i : ι) (s : ℤ)
    [Finite ((A i) ⧸ (F.F s i).arrow.hom.range)] : Finite (F.quotientAt s i) := by
  exact Finite.of_surjective (ModuleCat.cokernelIsoRangeQuotient
      (F.F s i).arrow).inv
    (ConcreteCategory.bijective_of_isIso _).2

private theorem finite_quotientAt_of_submodule {ι : Type w} {A : GradedObject ι (ModuleCat.{v} ℤ)}
    (F : Filtration A) (i : ι) (s : ℤ)
    [hfin : Finite ((A i) ⧸ ModuleCat.subobjectModule (A i) (F.F s i))] :
    Finite (F.quotientAt s i) := by
  have heq : ModuleCat.subobjectModule (A i) (F.F s i) =
    (F.F s i).arrow.hom.range := rfl
  rw [heq] at hfin
  exact finite_quotientAt_of_range F i s

private theorem quotientProjection_eq_iff_sub_mem {ι : Type w}
    {A : GradedObject ι (ModuleCat.{v} ℤ)} (F : Filtration A) (i : ι) (s : ℤ)
    (a b : A i) :
    F.quotientProjection s i a = F.quotientProjection s i b ↔
      a-b ∈ ModuleCat.subobjectModule (A i) (F.F s i) := by
  let e := ModuleCat.cokernelIsoRangeQuotient (F.F s i).arrow
  have heq : e.hom (F.quotientProjection s i a) = e.hom (F.quotientProjection s i b) ↔
    F.quotientProjection s i a = F.quotientProjection s i b :=
    (ConcreteCategory.bijective_of_isIso e.hom).1.eq_iff
  rw [← heq]
  have hp (c : A i) : e.hom (F.quotientProjection s i c) =
      (F.F s i).arrow.hom.range.mkQ c := by
    change (ModuleCat.cokernelIsoRangeQuotient (F.F s i).arrow).hom
      (cokernel.π (F.F s i).arrow c) = Submodule.Quotient.mk c
    exact ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply (F.F s i).arrow c
  rw [hp, hp]
  exact Submodule.Quotient.eq ((F.F s i).arrow.hom.range)

private theorem quotientTransition_surjective {ι : Type w}
    {A : GradedObject ι (ModuleCat.{v} ℤ)} (F : Filtration A) (i : ι)
    {s t : ℤ} (h : t ≤ s) : Function.Surjective (F.quotientTransition h i) := by
  intro x
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (F.quotientProjection t i)).mp
    (by change Epi (cokernel.π (F.F t i).arrow); infer_instance) x
  exact ⟨F.quotientProjection s i a,
    congrArg (fun f : A i ⟶ F.quotientAt t i => f a)
      (F.quotientProjection_transition h i)⟩

private theorem finite_quotientAt_int {ι : Type w}
    {A : GradedObject ι (ModuleCat.{v} ℤ)} (F : Filtration A) (i : ι)
    (hfin : ∀ n : ℕ, Finite (F.quotientAt n i)) (s : ℤ) :
    Finite (F.quotientAt s i) := by
  letI := hfin s.toNat
  exact Finite.of_surjective (F.quotientTransition (Int.self_le_toNat s) i)
    (quotientTransition_surjective F i _)

end
end KIP126.ProofTools.Paper
