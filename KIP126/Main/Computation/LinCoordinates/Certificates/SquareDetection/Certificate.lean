module

public import KIP126.Main.Computation.LinCoordinates.Certificates.SquareDetection.Certificate.Data
public import KIP126.Def.ComputationModel.Certificates.SquareDetection.Parsing
public import Init.Data.String.Lemmas.Iterate
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.List.SplitOn.Basic

@[expose] public section

namespace KIP126.LinE2.SquareDetection

theorem monomialOrder_eq_chars (s : String) : monomialOrder s = charsMonomialOrder s.toList := by
  simp only [monomialOrder, charsMonomialOrder, splitOn_comma, List.map_map,
    Function.comp_def, toNat?_eq_chars, String.toList_ofList]
  simp only [String.toList_eq_nil_iff]

theorem relationCheck_eq_chars (s : String) : relationCheck s = charsRelationCheck s.toList := by
  simp only [relationCheck, charsRelationCheck, splitOn_semicolon, List.all_map,
    Function.comp_def, monomialOrder_eq_chars, String.toList_ofList]

theorem chunkCheck_eq_chars (s : String) :
    (s.splitOn "\n").all relationCheck = charsChunkCheck s.toList := by
  simp only [charsChunkCheck, splitOn_newline, List.all_map, Function.comp_def, relationCheck_eq_chars,
    String.toList_ofList]

/-- Compose character-list certificates without normalizing UTF-8 encoding.
This is the kernel-efficient form used by the certificate generator. -/
theorem charsChunkCheck_append (a b : List Char)
    (ha : charsChunkCheck a = true) (hb : charsChunkCheck b = true) :
    charsChunkCheck (a ++ '\n' :: b) = true := by
  simp only [charsChunkCheck, List.splitOn_append_cons_self, List.all_append,
    show (a.splitOn '\n').all charsRelationCheck = true from ha,
    show (b.splitOn '\n').all charsRelationCheck = true from hb, Bool.and_self]

/-- Return a list certificate to the exact string semantics. String literals
are definitionally `String.ofList`, so this avoids evaluating UTF-8 decoding. -/
theorem charsChunkCheck_ofList (cs : List Char) (h : charsChunkCheck cs = true) :
    charsChunkCheck (String.ofList cs).toList = true := by
  rwa [String.toList_ofList]

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

/-- Certificates compose at a newline. Large archived strings can therefore
be checked using small leaves without changing the archived chunk layout. -/
theorem charsChunkCheck_join (a b : String)
    (ha : charsChunkCheck a.toList = true) (hb : charsChunkCheck b.toList = true) :
    charsChunkCheck (a ++ ("\n" ++ b)).toList = true := by
  change (a.toList.splitOn '\n').all charsRelationCheck = true at ha
  change (b.toList.splitOn '\n').all charsRelationCheck = true at hb
  simp only [charsChunkCheck, String.toList_append, show "\n".toList = ['\n'] from rfl,
    List.cons_append, List.nil_append, List.splitOn_append_cons_self, List.all_append,
    ha, hb, Bool.and_self]

theorem charsChunkCheck_of_join (s a b : String) (hs : s = a ++ ("\n" ++ b))
    (ha : charsChunkCheck a.toList = true) (hb : charsChunkCheck b.toList = true) :
    charsChunkCheck s.toList = true := by
  rw [hs]
  exact charsChunkCheck_join a b ha hb

attribute [local cbv_eval] splitOn_comma splitOn_semicolon splitOn_newline toNat?_eq_chars

/-- A kernel-checked initial piece of the archived certificate. The remaining
227 chunks are not assumed to have been certified by this theorem. -/
theorem firstRelations_check : RawData.firstRelations.all relationCheck = true := by cbv

/-- Assemble certificates against the original archived strings. The only
remaining input is the finite family of chunk certificates. -/
theorem allRelationsCheck_of_chunks
    (h : ∀ s ∈ RawData.relationChunks.toList, charsChunkCheck s.toList = true) :
    allRelationsCheck = true := by
  apply List.all_eq_true.mpr
  intro code hc
  change code ∈ RawData.firstRelations ++
    RawData.relationChunks.toList.flatMap (fun s => s.splitOn "\n") at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact List.all_eq_true.mp firstRelations_check code hc
  · obtain ⟨s, hs, hc⟩ := List.mem_flatMap.mp hc
    have hcheck : (s.splitOn "\n").all relationCheck = true :=
      (chunkCheck_eq_chars s).trans (h s hs)
    exact List.all_eq_true.mp hcheck code hc

end KIP126.LinE2.SquareDetection
