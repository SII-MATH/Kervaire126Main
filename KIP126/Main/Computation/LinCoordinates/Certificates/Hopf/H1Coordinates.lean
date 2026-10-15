module

public import KIP126.Main.Computation.LinCoordinates.Model.E2.Proofs

public import KIP126.Main.Computation.LinCoordinates.Certificates.SquareDimension.Generators.Proofs
public import Mathlib.Algebra.Order.Monoid.Prod

@[expose] public section


/-!
# LinProgram/Certificates/Hopf/H1Coordinates

Fixed-data certificate in the original complete quotient or module; it supplies no actual-spectrum comparison.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Exact exhaustion of the degree-(1,2) component of the fixed data algebra.
No archived basis or differential table is assumed correct. -/

namespace KIP126.LinE2

open KIP126.Algebra

local instance : NeZero RawData.generatorCount := ⟨by decide⟩

/-- Only the first two generators can occur in a degree-(1,2) monomial. -/
theorem h1Degree_support (m : Generator →₀ ℕ)
    (hm : monomialDegree m = (1, 2)) :
    m.support ⊆ ({0, 1} : Finset Generator) := by
  intro i hi
  have hmi : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hle : (m i * (generatorDegree i).1, m i * (generatorDegree i).2) ≤
      monomialDegree m := by
    simpa [monomialDegree] using Finsupp.single_le_sum m
      (g := fun j a => (a * (generatorDegree j).1, a * (generatorDegree j).2))
      (by intro j a; exact ⟨Nat.zero_le _, Nat.zero_le _⟩) i
  rw [hm] at hle
  have hs : (generatorDegree i).1 ≤ 1 := by
    calc
      _ = 1 * (generatorDegree i).1 := (one_mul _).symm
      _ ≤ m i * (generatorDegree i).1 := Nat.mul_le_mul_right _ hmi
      _ ≤ 1 := hle.1
  have ht : (generatorDegree i).2 ≤ 2 := by
    calc
      _ = 1 * (generatorDegree i).2 := (one_mul _).symm
      _ ≤ m i * (generatorDegree i).2 := Nat.mul_le_mul_right _ hmi
      _ ≤ 2 := hle.2
  rw [generatorDegree_eq_row] at hs ht
  have h : ∀ j : Fin RawData.generatorCount,
      (RawData.generatorRow j.val).2.1 ≤ 1 →
      (RawData.generatorRow j.val).2.2 ≤ 2 → j.val ∈ [0, 1] := by
    decide +kernel
  simpa [Fin.ext_iff, RawData.generatorCount] using h i hs ht

/-- Degree (1,2) has exactly one possible polynomial monomial. -/
theorem monomialDegree_h1_unique (m : Generator →₀ ℕ)
    (hm : monomialDegree m = (1, 2)) :
    m = Finsupp.single (1 : Generator) 1 := by
  have hsupp := h1Degree_support m hm
  have hdegree : monomialDegree m = (m 0 + m 1, m 0 + 2 * m 1) := by
    unfold monomialDegree
    rw [m.sum_of_support_subset hsupp _ (by intros; simp)]
    simp [generatorDegree_eq_row, RawData.generatorRow, RawData.generatorChunkIndex,
      RawData.generatorChunk0, RawData.generatorCount, Nat.mul_comm]
  have hs := congrArg Prod.fst (hdegree.symm.trans hm)
  have ht := congrArg Prod.snd (hdegree.symm.trans hm)
  dsimp at hs ht
  have hvalues : m 0 = 0 ∧ m 1 = 1 := by omega
  ext i
  by_cases hi : i ∈ m.support
  · have hi' := hsupp hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
    rcases hi' with rfl | rfl <;> simp_all
  · have hz := Finsupp.notMem_support_iff.mp hi
    have hi1 : i ≠ (1 : Generator) := by
      intro he
      subst i
      omega
    simp [hz, Finsupp.single_eq_of_ne hi1]

/-- The imported quotient's degree-(1,2) component is spanned by data h₁. -/
theorem homogeneousPart_h1_eq_span : homogeneousPart 1 2 =
    Submodule.span F2 ({h1} : Set E2) := by
  unfold homogeneousPart
  apply congrArg (Submodule.span F2)
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [monomialDegree_h1_unique m hm]
    simp [← MvPolynomial.X_pow_eq_monomial, generator, h1, RawData.generatorCount]
    congr 2
  · intro hx
    have hx' : x = h1 := hx
    subst x
    refine ⟨Finsupp.single (1 : Generator) 1, ?_, ?_⟩
    · simp [monomialDegree, generatorDegree_eq_row, RawData.generatorRow,
        RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorCount]
    · simp [← MvPolynomial.X_pow_eq_monomial, generator, h1, RawData.generatorCount]
      congr 2

/-- No assumption about the CSV additive catalogue is needed for exhaustion. -/
theorem E2At_h1_eq_zero_or (x : E2At 1 2) : x = 0 ∨ x = dataH1 := by
  apply E2At_eq_zero_or_of_span dataH1 _ x
  simpa only [dataH1] using homogeneousPart_h1_eq_span

end KIP126.LinE2
