module

public import Batteries.Data.String.Lemmas
import all Init.Data.String.Legacy
import all Init.Data.List.SplitOn.Basic

@[expose] public section

namespace KIP126.LinE2.SquareDetection

/-- For a one-character separator the `String.Legacy` substring splitter agrees with
the character splitter. This avoids expanding its UTF-8 search during certification. -/
theorem splitOnAux_singleton (s : String) (c : Char) (b i : String.Pos.Raw)
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

/-- Kernel-proved parser replacement, valid for every string and separator
character, not merely the current archived literals. -/
theorem splitOn_singleton_eq_list (s : String) (c : Char) :
    s.splitOn (String.singleton c) = (s.toList.splitOn c).map String.ofList := by
  have hc : (String.singleton c == "") = false := by simp
  rw [String.splitOn, hc, if_neg Bool.false_ne_true, splitOnAux_singleton]
  change String.splitToList s (· == c) = _
  rw [String.splitToList_of_valid, List.splitOn_eq_splitOnP]

theorem splitOn_comma (s : String) :
    s.splitOn "," = (s.toList.splitOn ',').map String.ofList :=
  splitOn_singleton_eq_list s ','

theorem splitOn_semicolon (s : String) :
    s.splitOn ";" = (s.toList.splitOn ';').map String.ofList :=
  splitOn_singleton_eq_list s ';'

theorem splitOn_newline (s : String) :
    s.splitOn "\n" = (s.toList.splitOn '\n').map String.ofList :=
  splitOn_singleton_eq_list s '\n'

end KIP126.LinE2.SquareDetection
