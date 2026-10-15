module

public import KIP126.Def.ComputationModel.Parsing.NaturalNumbers
public import KIP126.Computation.WellFormedness.LinCoordinates.GeneratorDegrees
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-! Total syntactic degree checking for the original polynomial parser.
A successful check implies genuine weighted homogeneity of that same polynomial.
No statement about a quotient, basis, or actual Adams comparison is used. -/
namespace KIP126.LinE2.RelationCatalogue
open KIP126.Algebra MvPolynomial SquareDetection

def powersDegree : List ℕ → ℕ × ℕ
  | [] => 0
  | i :: a :: rest =>
    if i < RawData.generatorCount then a • (RawData.generatorRow i).2 + powersDegree rest
    else 0
  | [_] => 0

theorem powers_homogeneous (xs : List ℕ) :
    IsWeightedHomogeneous generatorDegree (polynomialOfPowers xs) (powersDegree xs) := by
  induction xs using powersDegree.induct with
  | case1 => exact isWeightedHomogeneous_one _ _
  | case2 i a rest h ih =>
    simp only [polynomialOfPowers, powersDegree, dif_pos h, if_pos h]
    simpa only [generatorDegree_eq_row] using
      ((isWeightedHomogeneous_X F2 generatorDegree ⟨i, h⟩).pow a).mul ih
  | case3 i a rest h =>
    simp only [polynomialOfPowers, powersDegree, dif_neg h, if_neg h]
    exact isWeightedHomogeneous_zero _ _ _
  | case4 i => exact isWeightedHomogeneous_zero _ _ _

def monomialDegreeOfString (s : String) : ℕ × ℕ :=
  if s = "" then 0
  else powersDegree ((s.splitOn ",").map (fun n => n.toNat?.getD 0))

theorem monomial_homogeneous (s : String) :
    IsWeightedHomogeneous generatorDegree (monomialOfString s) (monomialDegreeOfString s) := by
  unfold monomialOfString monomialDegreeOfString
  split
  · exact isWeightedHomogeneous_one _ _
  · exact powers_homogeneous _

def relationDegree (s : String) : ℕ × ℕ :=
  monomialDegreeOfString ((s.splitOn ";").headD "")

def relationCheck (s : String) : Bool :=
  (s.splitOn ";").all (fun m => monomialDegreeOfString m == relationDegree s)

theorem relationCheck_sound (s : String) (h : relationCheck s = true) :
    IsWeightedHomogeneous generatorDegree (relationPolynomial s) (relationDegree s) := by
  have hm : ∀ m ∈ s.splitOn ";", monomialDegreeOfString m = relationDegree s := by
    simpa only [relationCheck, List.all_eq_true, beq_iff_eq] using h
  unfold relationPolynomial
  generalize s.splitOn ";" = ms at *
  induction ms with
  | nil => simpa using isWeightedHomogeneous_zero F2 generatorDegree (relationDegree s)
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons]
    apply IsWeightedHomogeneous.add
    · rw [← hm m (by simp)]
      exact monomial_homogeneous m
    · exact ih (fun m h => hm m (List.mem_cons_of_mem _ h))

def charsMonomialDegree (cs : List Char) : ℕ × ℕ :=
  if cs = [] then 0
  else powersDegree ((cs.splitOn ',').map (fun ns => (charsToNat? ns).getD 0))

def charsRelationCheck (cs : List Char) : Bool :=
  let ms := cs.splitOn ';'
  ms.all (fun m => charsMonomialDegree m == charsMonomialDegree (ms.headD []))

def charsChunkCheck (cs : List Char) : Bool :=
  (cs.splitOn '\n').all charsRelationCheck

def chunksCheck (ss : List String) : Bool := ss.all (fun s => charsChunkCheck s.toList)

theorem monomialDegree_eq_chars (s : String) :
    monomialDegreeOfString s = charsMonomialDegree s.toList := by
  simp only [monomialDegreeOfString, charsMonomialDegree, splitOn_comma, List.map_map,
    Function.comp_def, toNat?_eq_chars, String.toList_ofList, String.toList_eq_nil_iff]

theorem relationCheck_eq_chars (s : String) : relationCheck s = charsRelationCheck s.toList := by
  simp only [relationCheck, charsRelationCheck, relationDegree, splitOn_semicolon,
    List.all_map, Function.comp_def, monomialDegree_eq_chars, String.toList_ofList]
  cases s.toList.splitOn ';' <;> simp [List.headD, String.toList_ofList]

theorem chunkCheck_eq_chars (s : String) :
    (s.splitOn "\n").all relationCheck = charsChunkCheck s.toList := by
  simp only [charsChunkCheck, splitOn_newline, List.all_map, Function.comp_def,
    relationCheck_eq_chars, String.toList_ofList]

theorem charsChunkCheck_ofList (cs : List Char) (h : charsChunkCheck cs = true) :
    charsChunkCheck (String.ofList cs).toList = true := by rwa [String.toList_ofList]

theorem chunksCheck_nil : chunksCheck [] = true := rfl

theorem chunksCheck_cons (s : String) (ss : List String)
    (hs : charsChunkCheck s.toList = true) (hss : chunksCheck ss = true) :
    chunksCheck (s :: ss) = true := by
  simp only [chunksCheck, List.all_cons] at *
  simp only [hs, hss, Bool.and_self]

theorem chunksCheck_append (a b : List String)
    (ha : chunksCheck a = true) (hb : chunksCheck b = true) :
    chunksCheck (a ++ b) = true := by
  simp only [chunksCheck, List.all_append] at *
  simp only [ha, hb, Bool.and_self]

attribute [local cbv_eval] generatorDegree_eq_row splitOn_comma splitOn_semicolon
  splitOn_newline toNat?_eq_chars

theorem firstRelations_check : RawData.firstRelations.all relationCheck = true := by cbv

theorem allRelations_homogeneous_of_chunks
    (h : ∀ s ∈ RawData.relationChunks.toList, charsChunkCheck s.toList = true)
    (code : String) (hc : code ∈ RawData.relations) :
    ∃ d : ℕ × ℕ, IsWeightedHomogeneous generatorDegree (relationPolynomial code) d := by
  refine ⟨relationDegree code, relationCheck_sound code ?_⟩
  change code ∈ RawData.firstRelations ++
    RawData.relationChunks.toList.flatMap (fun s => s.splitOn "\n") at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact List.all_eq_true.mp firstRelations_check code hc
  · obtain ⟨s, hs, hc⟩ := List.mem_flatMap.mp hc
    exact List.all_eq_true.mp ((chunkCheck_eq_chars s).trans (h s hs)) code hc
end KIP126.LinE2.RelationCatalogue
