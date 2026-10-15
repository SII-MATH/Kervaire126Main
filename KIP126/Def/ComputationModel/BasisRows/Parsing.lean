module

public import KIP126.Def.ComputationModel.BasisRows.Data
public import KIP126.Def.ComputationModel.Parsing.NaturalNumbers

@[expose] public section

namespace KIP126.LinE2.BasisCatalogue
open SquareDetection

def rowValid : List Char → Bool
  | cs => match cs.splitOn '|' with
    | [s,t,i,_] => (charsToNat? s).isSome && (charsToNat? t).isSome && (charsToNat? i).isSome
    | _ => false

def chunkValid (cs : List Char) : Bool := (cs.splitOn '\n').all rowValid

theorem splitOn_pipe (s : String) :
    s.splitOn "|" = (s.toList.splitOn '|').map String.ofList :=
  splitOn_singleton_eq_list s '|'

theorem decode_success (line : String) (h : rowValid line.toList = true) :
    ∃ row, decodeBasisRow line = .ok row := by
  dsimp only [rowValid] at h
  unfold decodeBasisRow
  rw [splitOn_pipe]
  generalize hp : line.toList.splitOn '|' = parts at ⊢
  rw [hp] at h
  rcases parts with _ | ⟨s, _ | ⟨t, _ | ⟨i, _ | ⟨code, _ | ⟨a, as⟩⟩⟩⟩⟩
  all_goals simp only [List.map_cons, List.map_nil] at *
  all_goals try { simp at h }
  change ((charsToNat? s).isSome && (charsToNat? t).isSome &&
    (charsToNat? i).isSome) = true at h
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨s', hs⟩, ⟨t', ht⟩⟩, ⟨i', hi⟩⟩ := h
  refine ⟨⟨s',t',i',String.ofList code⟩, ?_⟩
  simp only [toNat?_eq_chars, String.toList_ofList, hs, ht, hi]
  rfl

def chunksValid (chunks : List String) : Bool := chunks.all (fun s => chunkValid s.toList)

theorem chunkValid_append (a b : List Char)
    (ha : chunkValid a = true) (hb : chunkValid b = true) :
    chunkValid (a ++ '\n' :: b) = true := by
  simp only [chunkValid, List.splitOn_append_cons_self, List.all_append,
    show (a.splitOn '\n').all rowValid = true from ha,
    show (b.splitOn '\n').all rowValid = true from hb, Bool.and_self]

theorem chunkValid_ofList (cs : List Char) (h : chunkValid cs = true) :
    chunkValid (String.ofList cs).toList = true := by rwa [String.toList_ofList]

theorem chunksValid_nil : chunksValid [] = true := rfl

theorem chunksValid_cons (s : String) (ss : List String)
    (hs : chunkValid s.toList = true) (hss : chunksValid ss = true) :
    chunksValid (s :: ss) = true := by
  simp only [chunksValid, List.all_cons] at *
  simp only [hs, hss, Bool.and_self]

theorem chunksValid_append (a b : List String)
    (ha : chunksValid a = true) (hb : chunksValid b = true) :
    chunksValid (a ++ b) = true := by
  simp only [chunksValid, List.all_append] at *
  simp only [ha, hb, Bool.and_self]

theorem decode_list_members (lines : List String)
    (h : ∀ line ∈ lines, ∃ row, decodeBasisRow line = .ok row) :
    ∃ rows, lines.mapM decodeBasisRow = .ok rows ∧
      ∀ line ∈ lines, ∀ row, decodeBasisRow line = .ok row → row ∈ rows := by
  induction lines with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons line lines ih =>
    obtain ⟨row, hr⟩ := h line (by simp)
    obtain ⟨rows, hrs, hmem⟩ := ih (fun line hl => h line (by simp [hl]))
    refine ⟨row :: rows, by simp only [List.mapM_cons, hr, hrs]; rfl, ?_⟩
    intro line' hl row' hr'
    rcases List.mem_cons.mp hl with rfl | hl
    · have heq : row = row' := Except.ok.inj (hr.symm.trans hr')
      simp [heq]
    · exact List.mem_cons_of_mem row (hmem line' hl row' hr')


end KIP126.LinE2.BasisCatalogue
