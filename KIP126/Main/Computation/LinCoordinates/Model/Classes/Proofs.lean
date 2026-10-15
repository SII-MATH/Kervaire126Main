module

public import KIP126.Main.Computation.LinCoordinates.Model.E2.Proofs

public import KIP126.Computation.LinCoordinates.Model.Classes.Data
public import Batteries.Data.String.Lemmas
public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.MvPolynomial.Basic

import all Init.Data.List.SplitOn.Basic
import all Init.Data.String.Legacy
import all Init.Data.String.Search
import all Init.Data.String.Slice

@[expose] public section

namespace KIP126.LinE2

/-- The `String.Legacy` substring splitter agrees with character splitting for a
one-character separator. This avoids reducing UTF-8 search on literals. -/
private theorem splitOnAux_char (s : String) (c : Char) (b i : String.Pos.Raw)
    (acc : List String) :
    s.splitOnAux (String.singleton c) b i 0 acc = s.splitAux (· == c) b i acc := by
  have hg : String.Pos.Raw.get (String.singleton c) 0 = c := by
    simp only [String.Pos.Raw.get, String.toList_singleton, String.Pos.Raw.utf8GetAux,
      ↓reduceIte]
  have hn : String.Pos.Raw.next (String.singleton c) 0 = ⟨c.utf8Size⟩ := by
    simp [String.Pos.Raw.next, hg, String.Pos.Raw.ext_iff]
  have he : String.Pos.Raw.atEnd (String.singleton c) ⟨c.utf8Size⟩ = true := by
    simp [String.Pos.Raw.atEnd]
  fun_induction String.splitAux s (· == c) b i acc with
  | case1 b i acc h => rw [String.splitOnAux, if_pos h]
  | case2 b i acc h _ h' i' ih =>
    have hi : String.Pos.Raw.get s i = c := by simpa using h'
    have hu : (String.Pos.Raw.next s i).unoffsetBy ⟨c.utf8Size⟩ = i := by
      simp [String.Pos.Raw.next, hi, String.Pos.Raw.unoffsetBy]
    rw [String.splitOnAux, if_neg h, hg, if_pos h', hn, if_pos he, hu]
    exact ih
  | case3 b i acc h _ h' ih =>
    have hu : i.unoffsetBy 0 = i := by cases i; simp [String.Pos.Raw.unoffsetBy]
    rw [String.splitOnAux, if_neg h, hg, if_neg h', hu]
    exact ih

private theorem splitOn_char (s : String) (c : Char) :
    s.splitOn (String.singleton c) = (s.toList.splitOn c).map String.ofList := by
  have hc : (String.singleton c == "") = false := by simp
  rw [String.splitOn, hc, if_neg Bool.false_ne_true, splitOnAux_char]
  change String.splitToList s (· == c) = _
  rw [String.splitToList_of_valid, List.splitOn_eq_splitOnP]

private theorem splitOn_comma (s : String) :
    s.splitOn "," = (s.toList.splitOn ',').map String.ofList :=
  splitOn_char s ','

private theorem splitOn_semicolon (s : String) :
    s.splitOn ";" = (s.toList.splitOn ';').map String.ofList :=
  splitOn_char s ';'

private theorem first_relation_mem (code : String)
    (h : code ∈ RawData.firstRelations) : code ∈ RawData.relations := by
  exact List.mem_append.mpr (Or.inl h)

private theorem parse_zero : "0".toNat? = some 0 := by
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
    String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList,
    String.copy_toSlice]
  decide

private theorem parse_one : "1".toNat? = some 1 := by
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
    String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList,
    String.copy_toSlice]
  decide

private theorem parse_two : "2".toNat? = some 2 := by
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
    String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList,
    String.copy_toSlice]
  decide

private theorem parse_three : "3".toNat? = some 3 := by
  simp only [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
    String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList,
    String.copy_toSlice]
  decide

private theorem quotient_neg_eq_self (x : E2) : -x = x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change -(projection p) = projection p
  rw [← map_neg]
  exact congrArg projection (CharTwo.neg_eq p)

/-- The first archived relation is the zero product `h₀h₁`. -/
theorem h0_mul_h1_eq_zero : h0 * h1 = 0 := by
  have h := csv_relation_zero "0,1,1,1"
    (first_relation_mem _ (by simp [RawData.firstRelations]))
  have hs : "0,1,1,1".splitOn ";" = ["0,1,1,1"] := by
    rw [splitOn_semicolon]
    decide
  have hc : "0,1,1,1".splitOn "," = ["0", "1", "1", "1"] := by
    rw [splitOn_comma]
    decide
  simpa [h0, h1, generator, projection, RawData.generatorCount,
    relationPolynomial, monomialOfString,
    polynomialOfPowers, hs, hc, parse_zero, parse_one, map_mul] using h

/-- The second archived relation is the zero product `h₁h₂`. -/
theorem h1_mul_h2_eq_zero : h1 * h2 = 0 := by
  have h := csv_relation_zero "1,1,2,1"
    (first_relation_mem _ (by simp [RawData.firstRelations]))
  have hs : "1,1,2,1".splitOn ";" = ["1,1,2,1"] := by
    rw [splitOn_semicolon]
    decide
  have hc : "1,1,2,1".splitOn "," = ["1", "1", "2", "1"] := by
    rw [splitOn_comma]
    decide
  simpa [h1, h2, generator, projection, RawData.generatorCount,
    relationPolynomial, monomialOfString, polynomialOfPowers,
    hs, hc, parse_one, parse_two, map_mul] using h

/-- The third archived relation identifies the two cubic monomials. -/
theorem h1_cube_eq_h0_sq_mul_h2 : h1 ^ 3 = h0 ^ 2 * h2 := by
  have h := csv_relation_zero "1,3;0,2,2,1"
    (first_relation_mem _ (by simp [RawData.firstRelations]))
  have hs : "1,3;0,2,2,1".splitOn ";" = ["1,3", "0,2,2,1"] := by
    rw [splitOn_semicolon]
    decide
  have hc1 : "1,3".splitOn "," = ["1", "3"] := by
    rw [splitOn_comma]
    decide
  have hc2 : "0,2,2,1".splitOn "," = ["0", "2", "2", "1"] := by
    rw [splitOn_comma]
    decide
  simpa [h0, h1, h2, generator, projection, RawData.generatorCount,
    relationPolynomial, monomialOfString, polynomialOfPowers,
    hs, hc1, hc2, parse_zero, parse_one, parse_two, parse_three,
    map_add, map_mul, map_pow,
    add_eq_zero_iff_eq_neg, quotient_neg_eq_self] using h

end KIP126.LinE2
