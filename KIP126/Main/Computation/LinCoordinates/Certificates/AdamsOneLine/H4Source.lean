module

public import KIP126.Main.Computation.LinCoordinates.Model.E2.Proofs

public import KIP126.Main.Computation.LinCoordinates.Certificates.Hopf.H1Coordinates
public import KIP126.Main.Computation.LinCoordinates.Certificates.BasisCatalogue.Archive
public import KIP126.Main.Computation.LinCoordinates.Tactic.LinBasisLine
public import KIP126.Main.Computation.LinCoordinates.Certificates.SquareDetection.Certificate

import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-!
# LinProgram/Certificates/AdamsOneLine/H4Source

Fixed-data certificate in the original complete quotient or module; it supplies no actual-spectrum comparison.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Exact data coordinates and source exhaustion for proofs.db record 5434.
The archived rows are parsed, while homogeneity and exhaustion are proved in
 the quotientindependently of any assertion that the catalogue is a basis. -/

namespace KIP126.LinE2.OneLine

open KIP126.Algebra

local instance : NeZero RawData.generatorCount := ⟨by decide⟩

theorem h4Generator_degree : generatorDegree (7 : Generator) = (1, 16) := by
  simp [generatorDegree_eq_row, RawData.generatorRow, RawData.generatorChunkIndex,
    RawData.generatorChunk0, RawData.generatorCount]

theorem h3Generator_degree : generatorDegree (3 : Generator) = (1, 8) := by
  simp [generatorDegree_eq_row, RawData.generatorRow, RawData.generatorChunkIndex,
    RawData.generatorChunk0, RawData.generatorCount]

noncomputable def dataH4 : E2At 1 16 :=
  ⟨generator (7 : Generator), by
    simpa only [h4Generator_degree] using generator_mem (7 : Generator)⟩

private theorem h0h3Sq_monomial :
    MvPolynomial.monomial
      (Finsupp.single (0 : Generator) 1 + Finsupp.single (3 : Generator) 2) (1 : F2) =
      MvPolynomial.X (0 : Generator) * MvPolynomial.X (3 : Generator) ^ 2 := by
  rw [MvPolynomial.X_pow_eq_monomial]
  simp [MvPolynomial.X]

noncomputable def dataH0H3Sq : E2At 3 17 :=
  ⟨projection (MvPolynomial.monomial
    (Finsupp.single (0 : Generator) 1 + Finsupp.single (3 : Generator) 2) 1), by
    apply Submodule.subset_span
    refine ⟨Finsupp.single (0 : Generator) 1 + Finsupp.single (3 : Generator) 2, ?_, rfl⟩
    rw [monomialDegree_add]
    simp [monomialDegree, generatorDegree_eq_row, RawData.generatorRow,
      RawData.generatorChunkIndex, RawData.generatorChunk0, RawData.generatorCount]⟩

theorem dataH0H3Sq_val : dataH0H3Sq.val =
    generator (0 : Generator) * generator (3 : Generator) ^ 2 := by
  change projection _ = _
  rw [h0h3Sq_monomial]
  simp only [map_mul, map_pow, generator]

/-- The source degree excludes all but the first four hᵢ and h₄. -/
theorem h4Degree_support (m : Generator →₀ ℕ)
    (hm : monomialDegree m = (1, 16)) :
    m.support ⊆ ({0, 1, 2, 3, 7} : Finset Generator) := by
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
  have ht : (generatorDegree i).2 ≤ 16 := by
    calc
      _ = 1 * (generatorDegree i).2 := (one_mul _).symm
      _ ≤ m i * (generatorDegree i).2 := Nat.mul_le_mul_right _ hmi
      _ ≤ 16 := hle.2
  rw [generatorDegree_eq_row] at hs ht
  have h : ∀ j : Fin RawData.generatorCount,
      (RawData.generatorRow j.val).2.1 ≤ 1 →
      (RawData.generatorRow j.val).2.2 ≤ 16 → j.val ∈ [0, 1, 2, 3, 7] := by
    decide +kernel
  simpa [Fin.ext_iff, RawData.generatorCount] using h i hs ht

/-- There is just one polynomial monomial of source degree. -/
theorem monomialDegree_h4_unique (m : Generator →₀ ℕ)
    (hm : monomialDegree m = (1, 16)) :
    m = Finsupp.single (7 : Generator) 1 := by
  have hsupp := h4Degree_support m hm
  have hdegree : monomialDegree m =
      (m 0 + m 1 + m 2 + m 3 + m 7,
        m 0 + 2 * m 1 + 4 * m 2 + 8 * m 3 + 16 * m 7) := by
    unfold monomialDegree
    rw [m.sum_of_support_subset hsupp _ (by intros; simp)]
    simp [generatorDegree_eq_row, RawData.generatorRow, RawData.generatorChunkIndex,
      RawData.generatorChunk0, RawData.generatorCount, Nat.mul_comm, Nat.add_assoc]
  have hs := congrArg Prod.fst (hdegree.symm.trans hm)
  have ht := congrArg Prod.snd (hdegree.symm.trans hm)
  dsimp at hs ht
  have hvalues : m 0 = 0 ∧ m 1 = 0 ∧ m 2 = 0 ∧ m 3 = 0 ∧ m 7 = 1 := by omega
  ext i
  by_cases hi : i ∈ m.support
  · have hi' := hsupp hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
    rcases hi' with rfl | rfl | rfl | rfl | rfl <;> simp_all
  · have hz := Finsupp.notMem_support_iff.mp hi
    have hi7 : i ≠ (7 : Generator) := by
      intro he
      subst i
      omega
    simp [hz, Finsupp.single_eq_of_ne hi7]

theorem homogeneousPart_h4_eq_span : homogeneousPart 1 16 =
    Submodule.span F2 ({generator (7 : Generator)} : Set E2) := by
  unfold homogeneousPart
  apply congrArg (Submodule.span F2)
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [monomialDegree_h4_unique m hm]
    simp [← MvPolynomial.X_pow_eq_monomial, generator]
  · intro hx
    have hx' : x = generator (7 : Generator) := hx
    subst x
    refine ⟨Finsupp.single (7 : Generator) 1, ?_, ?_⟩
    · simp [monomialDegree, h4Generator_degree]
    · simp [← MvPolynomial.X_pow_eq_monomial, generator]

theorem E2At_h4_eq_zero_or (x : E2At 1 16) : x = 0 ∨ x = dataH4 := E2At_eq_zero_or_of_span dataH4 homogeneousPart_h4_eq_span x

def h4Row : BasisRow := ⟨1, 16, 0, "7,1"⟩
def targetRow : BasisRow := ⟨3, 17, 0, "0,1,3,2"⟩

theorem h4_value : dataH4.val = basisValue h4Row := by
  have hs : "7,1".splitOn "," = ["7", "1"] := by
    rw [SquareDetection.splitOn_comma]
    decide
  have h7 : "7".toNat? = some 7 := by
    rw [SquareDetection.toNat?_eq_chars]
    cbv
  have h1 : "1".toNat? = some 1 := by
    rw [SquareDetection.toNat?_eq_chars]
    cbv
  simp [dataH4, basisValue, h4Row, monomialOfString, hs, h7, h1,
    polynomialOfPowers, RawData.generatorCount, generator]
  congr 2

theorem target_value : dataH0H3Sq.val = basisValue targetRow := by
  rw [dataH0H3Sq_val]
  have hs : "0,1,3,2".splitOn "," = ["0", "1", "3", "2"] := by
    rw [SquareDetection.splitOn_comma]
    decide
  have h0 : "0".toNat? = some 0 := by rw [SquareDetection.toNat?_eq_chars]; cbv
  have h1 : "1".toNat? = some 1 := by rw [SquareDetection.toNat?_eq_chars]; cbv
  have h3 : "3".toNat? = some 3 := by rw [SquareDetection.toNat?_eq_chars]; cbv
  have h2 : "2".toNat? = some 2 := by rw [SquareDetection.toNat?_eq_chars]; cbv
  simp [basisValue, targetRow, monomialOfString, hs, h0, h1, h3, h2,
    polynomialOfPowers, RawData.generatorCount, generator, map_mul, map_pow]
  congr 2

attribute [local cbv_eval] BasisCatalogue.splitOn_pipe SquareDetection.toNat?_eq_chars

set_option maxRecDepth 100000 in
theorem h4Row_mem : h4Row ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid
    "1|16|0|7,1"
  · lin_basis_line 0 "1|16|0|7,1"
  · cbv

set_option maxRecDepth 100000 in
theorem targetRow_mem : targetRow ∈ basisRows := by
  apply BasisCatalogue.row_mem_of_rawLine BasisCatalogue.archivedChunks_valid
    "3|17|0|0,1,3,2"
  · lin_basis_line 0 "3|17|0|0,1,3,2"
  · cbv

end KIP126.LinE2.OneLine
