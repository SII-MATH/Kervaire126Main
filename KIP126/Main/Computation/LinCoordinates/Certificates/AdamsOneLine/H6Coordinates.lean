module

public import KIP126.Main.Computation.LinCoordinates.Model.E2.Proofs

public import KIP126.Main.Computation.LinCoordinates.Certificates.AdamsOneLine.H4Source
public import KIP126.Computation.LinCoordinates.Interpretation.Near126.Classes.Data

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-!
# LinProgram/Certificates/AdamsOneLine/H6Coordinates

Fixed-data certificate in the original complete quotient or module; it supplies no actual-spectrum comparison.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Coordinates and degree exhaustion for differential-table row 5541.
The complete fixed generator table determines the two homogeneous components;
the argument uses its checked algebraic relations and degree bounds. -/
namespace KIP126.LinE2.OneLineH6
open KIP126.Algebra

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
local instance : NeZero RawData.generatorCount := ⟨by decide⟩
attribute [local irreducible] homogeneousPart
attribute [local cbv_eval] BasisCatalogue.splitOn_pipe SquareDetection.splitOn_comma
  SquareDetection.toNat?_eq_chars

/-- The specified square in the relation quotient represents the target. -/
noncomputable def target : E2At 3 65 :=
  @mulAt 1 1 2 64 dataH0 KIP126.Computation.Near126.h5Sq

theorem target_val : target.val = generator (0 : Generator) * generator 18 ^ 2 := by
  simp only [target, mulAt, dataH0, h0, KIP126.Computation.Near126.h5Sq,
    KIP126.Computation.Near126.atom, pow_two]
  rfl

private theorem generator_bounds {s t : ℕ} (m : Generator →₀ ℕ)
    (hm : monomialDegree m = (s,t)) (i : Generator) (hi : i ∈ m.support) :
    (generatorDegree i).1 ≤ s ∧ (generatorDegree i).2 ≤ t := by
  have hmi : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hle : (m i * (generatorDegree i).1, m i * (generatorDegree i).2) ≤
      monomialDegree m := by
    simpa [monomialDegree] using Finsupp.single_le_sum m
      (g := fun j a => (a * (generatorDegree j).1, a * (generatorDegree j).2))
      (by intro j a; exact ⟨Nat.zero_le _, Nat.zero_le _⟩) i
  rw [hm] at hle
  constructor
  · calc
      _ = 1 * (generatorDegree i).1 := (one_mul _).symm
      _ ≤ m i * (generatorDegree i).1 := Nat.mul_le_mul_right _ hmi
      _ ≤ s := hle.1
  · calc
      _ = 1 * (generatorDegree i).2 := (one_mul _).symm
      _ ≤ m i * (generatorDegree i).2 := Nat.mul_le_mul_right _ hmi
      _ ≤ t := hle.2

theorem source_support (m : Generator →₀ ℕ) (hm : monomialDegree m = (1, 64)) :
    m.support ⊆ ({0, 1, 2, 3, 7, 18, 69} : Finset Generator) := by
  intro i hi
  obtain ⟨hs, ht⟩ := generator_bounds m hm i hi
  rw [generatorDegree_eq_row] at hs ht
  have h : ∀ j : Fin RawData.generatorCount,
      (RawData.generatorRow j.val).2.1 ≤ 1 →
      (RawData.generatorRow j.val).2.2 ≤ 64 → j.val ∈ [0, 1, 2, 3, 7, 18, 69] := by
    decide +kernel
  simpa [Fin.ext_iff, RawData.generatorCount] using h i hs ht

theorem source_monomial_unique (m : Generator →₀ ℕ) (hm : monomialDegree m = (1, 64)) :
    m = Finsupp.single (69 : Generator) 1 := by
  have hsupp := source_support m hm
  have hdegree : monomialDegree m = (m 0 + m 1 + m 2 + m 3 + m 7 + m 18 + m 69,
      m 0 + 2 * m 1 + 4 * m 2 + 8 * m 3 + 16 * m 7 + 32 * m 18 + 64 * m 69) := by
    unfold monomialDegree
    rw [m.sum_of_support_subset hsupp _ (by intros; simp)]
    simp [generatorDegree_eq_row, RawData.generatorRow, RawData.generatorChunkIndex,
      RawData.generatorChunk0, RawData.generatorChunk1, RawData.generatorChunk2,
      RawData.generatorCount, Nat.mul_comm, Nat.add_assoc]
  have hs := congrArg Prod.fst (hdegree.symm.trans hm)
  have ht := congrArg Prod.snd (hdegree.symm.trans hm)
  dsimp at hs ht
  have hvalues : m 0 = 0 ∧ m 1 = 0 ∧ m 2 = 0 ∧ m 3 = 0 ∧ m 7 = 0 ∧ m 18 = 0 ∧ m 69 = 1 := by omega
  rcases hvalues with ⟨h0, h1, h2, h3, h7, h18, h69⟩
  ext i
  by_cases hi : i ∈ m.support
  · have hi' := hsupp hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Finsupp.single_apply, h0, h1, h2, h3, h7, h18, h69] <;>
      norm_num [Fin.ext_iff, RawData.generatorCount]
  · have hz := Finsupp.notMem_support_iff.mp hi
    have hi69 : i ≠ (69 : Generator) := by
      intro he
      subst i
      exact Nat.one_ne_zero (h69.symm.trans hz)
    simp [hz, Finsupp.single_eq_of_ne hi69]

theorem target_support (m : Generator →₀ ℕ) (hm : monomialDegree m = (3, 65)) :
    m.support ⊆ ({0, 1, 2, 3, 4, 7, 11, 18, 38, 69} : Finset Generator) := by
  intro i hi
  obtain ⟨hs, ht⟩ := generator_bounds m hm i hi
  rw [generatorDegree_eq_row] at hs ht
  have h : ∀ j : Fin RawData.generatorCount,
      (RawData.generatorRow j.val).2.1 ≤ 3 →
      (RawData.generatorRow j.val).2.2 ≤ 65 → j.val ∈ [0, 1, 2, 3, 4, 7, 11, 18, 38, 69] := by
    decide +kernel
  simpa [Fin.ext_iff, RawData.generatorCount] using h i hs ht

theorem target_monomial_unique (m : Generator →₀ ℕ) (hm : monomialDegree m = (3, 65)) :
    m = Finsupp.single (0 : Generator) 1 + Finsupp.single (18 : Generator) 2 := by
  have hsupp := target_support m hm
  have hdegree : monomialDegree m = (m 0 + m 1 + m 2 + m 3 + 3 * m 4 + m 7 + 3 * m 11 + m 18 + 3 * m 38 + m 69,
      m 0 + 2 * m 1 + 4 * m 2 + 8 * m 3 + 11 * m 4 + 16 * m 7 + 22 * m 11 + 32 * m 18 + 44 * m 38 + 64 * m 69) := by
    unfold monomialDegree
    rw [m.sum_of_support_subset hsupp _ (by intros; simp)]
    simp [generatorDegree_eq_row, RawData.generatorRow, RawData.generatorChunkIndex,
      RawData.generatorChunk0, RawData.generatorChunk1, RawData.generatorChunk2,
      RawData.generatorCount, Nat.mul_comm, Nat.add_assoc]
  have hs := congrArg Prod.fst (hdegree.symm.trans hm)
  have ht := congrArg Prod.snd (hdegree.symm.trans hm)
  dsimp at hs ht
  have hvalues : m 0 = 1 ∧ m 1 = 0 ∧ m 2 = 0 ∧ m 3 = 0 ∧ m 4 = 0 ∧ m 7 = 0 ∧ m 11 = 0 ∧ m 18 = 2 ∧ m 38 = 0 ∧ m 69 = 0 := by omega
  rcases hvalues with ⟨h0, h1, h2, h3, h4, h7, h11, h18, h38, h69⟩
  ext i
  by_cases hi : i ∈ m.support
  · have hi' := hsupp hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Finsupp.add_apply, Finsupp.single_apply, h0, h1, h2, h3, h4, h7, h11, h18, h38, h69] <;>
      norm_num [Fin.ext_iff, RawData.generatorCount]
  · have hz := Finsupp.notMem_support_iff.mp hi
    have hi0 : i ≠ (0 : Generator) := by
      intro he
      subst i
      exact Nat.one_ne_zero (h0.symm.trans hz)
    have hi18 : i ≠ (18 : Generator) := by
      intro he
      subst i
      exact (by decide : (2 : ℕ) ≠ 0) (h18.symm.trans hz)
    simp [hz, Finsupp.single_eq_of_ne hi0, Finsupp.single_eq_of_ne hi18]

private theorem source_monomial_value :
    projection (MvPolynomial.monomial (Finsupp.single (69 : Generator) 1) (1 : F2)) =
      dataH6.val := by
  simp only [← MvPolynomial.X_pow_eq_monomial, pow_one, dataH6, generator]
  rfl

private theorem target_monomial_value :
    projection (MvPolynomial.monomial
      (Finsupp.single (0 : Generator) 1 + Finsupp.single (18 : Generator) 2) (1 : F2)) =
      target.val := by
  rw [target_val]
  have h : MvPolynomial.monomial
      (Finsupp.single (0 : Generator) 1 + Finsupp.single (18 : Generator) 2) (1 : F2) =
      MvPolynomial.X (0 : Generator) * MvPolynomial.X (18 : Generator) ^ 2 := by
    rw [MvPolynomial.X_pow_eq_monomial]
    simp [MvPolynomial.X]
  rw [h]
  simp only [map_mul, map_pow, generator]

theorem source_span : homogeneousPart 1 64 =
    Submodule.span F2 ({dataH6.val} : Set E2) := by
  unfold homogeneousPart
  apply congrArg (Submodule.span F2)
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [source_monomial_unique m hm, source_monomial_value]
    exact Set.mem_singleton _
  · intro hx
    have hx' : x = dataH6.val := hx
    subst x
    refine ⟨Finsupp.single (69 : Generator) 1, ?_, source_monomial_value.symm⟩
    simp [monomialDegree, generatorDegree_eq_row, RawData.generatorRow,
      RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorChunk2,
      RawData.generatorCount]

theorem target_span : homogeneousPart 3 65 =
    Submodule.span F2 ({target.val} : Set E2) := by
  unfold homogeneousPart
  apply congrArg (Submodule.span F2)
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [target_monomial_unique m hm, target_monomial_value]
    exact Set.mem_singleton _
  · intro hx
    have hx' : x = target.val := hx
    subst x
    refine ⟨Finsupp.single (0 : Generator) 1 + Finsupp.single (18 : Generator) 2, ?_, target_monomial_value.symm⟩
    rw [monomialDegree_add]
    simp [monomialDegree, generatorDegree_eq_row, RawData.generatorRow,
      RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorChunk2,
      RawData.generatorCount]

theorem source_eq_zero_or (x : E2At 1 64) : x = 0 ∨ x = dataH6 :=
  E2At_eq_zero_or_of_span dataH6 source_span x

theorem target_eq_zero_or (x : E2At 3 65) : x = 0 ∨ x = target :=
  E2At_eq_zero_or_of_span target target_span x

def sourceRow : BasisRow := ⟨1, 64, 0, "69,1"⟩
def targetRow : BasisRow := ⟨3, 65, 0, "0,1,18,2"⟩

theorem sourceRow_mem : sourceRow ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid "1|64|0|69,1"
  · lin_basis_line 0 "1|64|0|69,1"
  · cbv

theorem targetRow_mem : targetRow ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid "3|65|0|0,1,18,2"
  · lin_basis_line 0 "3|65|0|0,1,18,2"
  · cbv

private theorem parse_monomial (code : String) (ns : List ℕ)
    (hne : code ≠ "")
    (hp : (code.splitOn ",").map (fun n => n.toNat?.getD 0) = ns) :
    monomialOfString code = polynomialOfPowers ns := by
  simp only [monomialOfString, if_neg hne, hp]

theorem source_value : dataH6.val = basisValue sourceRow := by
  have hs : monomialOfString "69,1" = (MvPolynomial.X (69 : Generator) : Poly) := by
    rw [parse_monomial "69,1" [69,1] (by decide) (by cbv)]
    norm_num [polynomialOfPowers, RawData.generatorCount]
    rfl
  change _ = projection (monomialOfString "69,1")
  rw [hs]
  rfl

theorem target_value : target.val = basisValue targetRow := by
  have hs : monomialOfString "0,1,18,2" =
      (MvPolynomial.X (0 : Generator) * MvPolynomial.X (18 : Generator) ^ 2 : Poly) := by
    rw [parse_monomial "0,1,18,2" [0,1,18,2] (by decide) (by cbv)]
    norm_num [polynomialOfPowers, RawData.generatorCount]
    rfl
  rw [target_val]
  change _ = projection (monomialOfString "0,1,18,2")
  rw [hs]
  simp only [map_mul, map_pow, generator]

end KIP126.LinE2.OneLineH6
