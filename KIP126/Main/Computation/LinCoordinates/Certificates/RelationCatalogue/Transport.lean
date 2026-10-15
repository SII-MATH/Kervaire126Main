module

public import KIP126.Computation.WellFormedness.LinCoordinates.Certificates.RelationCatalogue.Support
import all Init.Data.List.SplitOn.Basic

@[expose] public section

/-! Concatenation lemmas for the fixed relation-degree checker.
These consequences are separate from the archive certificates needed to
construct the graded relation algebra. -/
namespace KIP126.LinE2.RelationCatalogue

theorem charsChunkCheck_append (a b : List Char)
    (ha : charsChunkCheck a = true) (hb : charsChunkCheck b = true) :
    charsChunkCheck (a ++ '\n' :: b) = true := by
  simp only [charsChunkCheck, List.splitOn_append_cons_self, List.all_append,
    show (a.splitOn '\n').all charsRelationCheck = true from ha,
    show (b.splitOn '\n').all charsRelationCheck = true from hb, Bool.and_self]

/-- Glue small string leaves without evaluating a long UTF-8 traversal. -/
theorem charsChunkCheck_joinString (a b : String)
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
  exact charsChunkCheck_joinString a b ha hb

end KIP126.LinE2.RelationCatalogue
