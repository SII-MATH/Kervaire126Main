module

public import KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
import all KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
public import Batteries.Tactic.OpenPrivate

@[expose] public section

/-! Additional low-degree facts about the pinned additive-basis catalogue.
The character rows and their equality with the source chunks are shared with
`FiniteCertificates`; no second copy of the table or parser is introduced.
These certificates concern the table only. Interpreting them on the fixed
Adams page still requires the supplied computation presentation. -/
namespace KIP126.LinE2.BasisCertificates

set_option maxRecDepth 100000

open private charsDecode charsDecode_correct liftRow mapM_good splitOn_char from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private NuLow.hchunks from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows0 chunk0_string rows0_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows1 chunk1_string rows1_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows2 chunk2_string rows2_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows3 chunk3_string rows3_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows4 chunk4_string rows4_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows5 chunk5_string rows5_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows6 chunk6_string rows6_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows7 chunk7_string rows7_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows8 chunk8_string rows8_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows9 chunk9_string rows9_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows10 chunk10_string rows10_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows11 chunk11_string rows11_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows12 chunk12_string rows12_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows13 chunk13_string rows13_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows14 chunk14_string rows14_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows15 chunk15_string rows15_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows16 chunk16_string rows16_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows17 chunk17_string rows17_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows18 chunk18_string rows18_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows19 chunk19_string rows19_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows20 chunk20_string rows20_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows21 chunk21_string rows21_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows22 chunk22_string rows22_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
open private rows23 chunk23_string rows23_no_newline from KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates

private def zeroCheck (l : List Char) : Bool :=
  match charsDecode l with
  | .error _ => true
  | .ok (s, t, _, c) => !(s == 0 && t == 0) || c == []

private theorem zeroCheck_sound (s : String) (r : BasisRow)
    (hc : zeroCheck s.toList = true) (he : decodeBasisRow s = .ok r) :
    r.s = 0 → r.t = 0 → r.monomial = "" := by
  rw [charsDecode_correct] at he
  cases hd : charsDecode s.toList with
  | error e =>
    rw [hd] at he
    cases he
  | ok x =>
    simp only [hd, Except.map] at he
    cases he
    rcases x with ⟨a, b, i, c⟩
    simp only [zeroCheck, hd] at hc
    dsimp [liftRow]
    intro ha hb
    subst a
    subst b
    have hchars : c = [] := by simpa using hc
    simpa using congrArg String.ofList hchars

private theorem rows0_zero_checked : rows0.all zeroCheck = true := by
  decide +kernel

private theorem chunk0_zero_checked :
    ((RawData.basisChunks[0]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk0_string, String.toList_ofList,
    List.splitOn_intercalate _ rows0_no_newline (by decide +kernel)]
  exact rows0_zero_checked

private theorem rows1_zero_checked : rows1.all zeroCheck = true := by
  decide +kernel

private theorem chunk1_zero_checked :
    ((RawData.basisChunks[1]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk1_string, String.toList_ofList,
    List.splitOn_intercalate _ rows1_no_newline (by decide +kernel)]
  exact rows1_zero_checked

private theorem rows2_zero_checked : rows2.all zeroCheck = true := by
  decide +kernel

private theorem chunk2_zero_checked :
    ((RawData.basisChunks[2]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk2_string, String.toList_ofList,
    List.splitOn_intercalate _ rows2_no_newline (by decide +kernel)]
  exact rows2_zero_checked

private theorem rows3_zero_checked : rows3.all zeroCheck = true := by
  decide +kernel

private theorem chunk3_zero_checked :
    ((RawData.basisChunks[3]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk3_string, String.toList_ofList,
    List.splitOn_intercalate _ rows3_no_newline (by decide +kernel)]
  exact rows3_zero_checked

private theorem rows4_zero_checked : rows4.all zeroCheck = true := by
  decide +kernel

private theorem chunk4_zero_checked :
    ((RawData.basisChunks[4]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk4_string, String.toList_ofList,
    List.splitOn_intercalate _ rows4_no_newline (by decide +kernel)]
  exact rows4_zero_checked

private theorem rows5_zero_checked : rows5.all zeroCheck = true := by
  decide +kernel

private theorem chunk5_zero_checked :
    ((RawData.basisChunks[5]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk5_string, String.toList_ofList,
    List.splitOn_intercalate _ rows5_no_newline (by decide +kernel)]
  exact rows5_zero_checked

private theorem rows6_zero_checked : rows6.all zeroCheck = true := by
  decide +kernel

private theorem chunk6_zero_checked :
    ((RawData.basisChunks[6]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk6_string, String.toList_ofList,
    List.splitOn_intercalate _ rows6_no_newline (by decide +kernel)]
  exact rows6_zero_checked

private theorem rows7_zero_checked : rows7.all zeroCheck = true := by
  decide +kernel

private theorem chunk7_zero_checked :
    ((RawData.basisChunks[7]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk7_string, String.toList_ofList,
    List.splitOn_intercalate _ rows7_no_newline (by decide +kernel)]
  exact rows7_zero_checked

private theorem rows8_zero_checked : rows8.all zeroCheck = true := by
  decide +kernel

private theorem chunk8_zero_checked :
    ((RawData.basisChunks[8]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk8_string, String.toList_ofList,
    List.splitOn_intercalate _ rows8_no_newline (by decide +kernel)]
  exact rows8_zero_checked

private theorem rows9_zero_checked : rows9.all zeroCheck = true := by
  decide +kernel

private theorem chunk9_zero_checked :
    ((RawData.basisChunks[9]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk9_string, String.toList_ofList,
    List.splitOn_intercalate _ rows9_no_newline (by decide +kernel)]
  exact rows9_zero_checked

private theorem rows10_zero_checked : rows10.all zeroCheck = true := by
  decide +kernel

private theorem chunk10_zero_checked :
    ((RawData.basisChunks[10]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk10_string, String.toList_ofList,
    List.splitOn_intercalate _ rows10_no_newline (by decide +kernel)]
  exact rows10_zero_checked

private theorem rows11_zero_checked : rows11.all zeroCheck = true := by
  decide +kernel

private theorem chunk11_zero_checked :
    ((RawData.basisChunks[11]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk11_string, String.toList_ofList,
    List.splitOn_intercalate _ rows11_no_newline (by decide +kernel)]
  exact rows11_zero_checked

private theorem rows12_zero_checked : rows12.all zeroCheck = true := by
  decide +kernel

private theorem chunk12_zero_checked :
    ((RawData.basisChunks[12]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk12_string, String.toList_ofList,
    List.splitOn_intercalate _ rows12_no_newline (by decide +kernel)]
  exact rows12_zero_checked

private theorem rows13_zero_checked : rows13.all zeroCheck = true := by
  decide +kernel

private theorem chunk13_zero_checked :
    ((RawData.basisChunks[13]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk13_string, String.toList_ofList,
    List.splitOn_intercalate _ rows13_no_newline (by decide +kernel)]
  exact rows13_zero_checked

private theorem rows14_zero_checked : rows14.all zeroCheck = true := by
  decide +kernel

private theorem chunk14_zero_checked :
    ((RawData.basisChunks[14]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk14_string, String.toList_ofList,
    List.splitOn_intercalate _ rows14_no_newline (by decide +kernel)]
  exact rows14_zero_checked

private theorem rows15_zero_checked : rows15.all zeroCheck = true := by
  decide +kernel

private theorem chunk15_zero_checked :
    ((RawData.basisChunks[15]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk15_string, String.toList_ofList,
    List.splitOn_intercalate _ rows15_no_newline (by decide +kernel)]
  exact rows15_zero_checked

private theorem rows16_zero_checked : rows16.all zeroCheck = true := by
  decide +kernel

private theorem chunk16_zero_checked :
    ((RawData.basisChunks[16]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk16_string, String.toList_ofList,
    List.splitOn_intercalate _ rows16_no_newline (by decide +kernel)]
  exact rows16_zero_checked

private theorem rows17_zero_checked : rows17.all zeroCheck = true := by
  decide +kernel

private theorem chunk17_zero_checked :
    ((RawData.basisChunks[17]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk17_string, String.toList_ofList,
    List.splitOn_intercalate _ rows17_no_newline (by decide +kernel)]
  exact rows17_zero_checked

private theorem rows18_zero_checked : rows18.all zeroCheck = true := by
  decide +kernel

private theorem chunk18_zero_checked :
    ((RawData.basisChunks[18]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk18_string, String.toList_ofList,
    List.splitOn_intercalate _ rows18_no_newline (by decide +kernel)]
  exact rows18_zero_checked

private theorem rows19_zero_checked : rows19.all zeroCheck = true := by
  decide +kernel

private theorem chunk19_zero_checked :
    ((RawData.basisChunks[19]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk19_string, String.toList_ofList,
    List.splitOn_intercalate _ rows19_no_newline (by decide +kernel)]
  exact rows19_zero_checked

private theorem rows20_zero_checked : rows20.all zeroCheck = true := by
  decide +kernel

private theorem chunk20_zero_checked :
    ((RawData.basisChunks[20]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk20_string, String.toList_ofList,
    List.splitOn_intercalate _ rows20_no_newline (by decide +kernel)]
  exact rows20_zero_checked

private theorem rows21_zero_checked : rows21.all zeroCheck = true := by
  decide +kernel

private theorem chunk21_zero_checked :
    ((RawData.basisChunks[21]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk21_string, String.toList_ofList,
    List.splitOn_intercalate _ rows21_no_newline (by decide +kernel)]
  exact rows21_zero_checked

private theorem rows22_zero_checked : rows22.all zeroCheck = true := by
  decide +kernel

private theorem chunk22_zero_checked :
    ((RawData.basisChunks[22]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk22_string, String.toList_ofList,
    List.splitOn_intercalate _ rows22_no_newline (by decide +kernel)]
  exact rows22_zero_checked

private theorem rows23_zero_checked : rows23.all zeroCheck = true := by
  decide +kernel

private theorem chunk23_zero_checked :
    ((RawData.basisChunks[23]!).toList.splitOn '\n').all zeroCheck = true := by
  rw [chunk23_string, String.toList_ofList,
    List.splitOn_intercalate _ rows23_no_newline (by decide +kernel)]
  exact rows23_zero_checked

/-- Every recorded basis row in bidegree `(0,0)` is the unit monomial. -/
theorem zero_unique : ∀ r ∈ basisRows, r.s = 0 → r.t = 0 → r.monomial = "" := by
  have hc : ∀ chunk ∈ RawData.basisChunks.toList,
      (chunk.toList.splitOn '\n').all zeroCheck = true := by
    intro chunk hchunk
    rw [NuLow.hchunks] at hchunk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hchunk
    rcases hchunk with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23
    · subst chunk; exact chunk0_zero_checked
    · subst chunk; exact chunk1_zero_checked
    · subst chunk; exact chunk2_zero_checked
    · subst chunk; exact chunk3_zero_checked
    · subst chunk; exact chunk4_zero_checked
    · subst chunk; exact chunk5_zero_checked
    · subst chunk; exact chunk6_zero_checked
    · subst chunk; exact chunk7_zero_checked
    · subst chunk; exact chunk8_zero_checked
    · subst chunk; exact chunk9_zero_checked
    · subst chunk; exact chunk10_zero_checked
    · subst chunk; exact chunk11_zero_checked
    · subst chunk; exact chunk12_zero_checked
    · subst chunk; exact chunk13_zero_checked
    · subst chunk; exact chunk14_zero_checked
    · subst chunk; exact chunk15_zero_checked
    · subst chunk; exact chunk16_zero_checked
    · subst chunk; exact chunk17_zero_checked
    · subst chunk; exact chunk18_zero_checked
    · subst chunk; exact chunk19_zero_checked
    · subst chunk; exact chunk20_zero_checked
    · subst chunk; exact chunk21_zero_checked
    · subst chunk; exact chunk22_zero_checked
    · subst chunk; exact chunk23_zero_checked
  unfold basisRows
  cases he : parseBasisRows with
  | error e =>
    change ∀ r ∈ ([] : List BasisRow), r.s = 0 → r.t = 0 → r.monomial = ""
    simp
  | ok rs =>
    simp only [Except.toOption, Option.getD]
    apply mapM_good (RowGood := fun r => r.s = 0 → r.t = 0 → r.monomial = "") _ ?_ rs he
    intro s hs r hr
    rcases List.mem_flatMap.mp hs with ⟨chunk, hchunk, hs⟩
    rw [show "\n" = String.singleton '\n' from rfl, splitOn_char] at hs
    rcases List.mem_map.mp hs with ⟨cs, hcs, rfl⟩
    apply zeroCheck_sound _ _ ?_ hr
    simpa only [String.toList_ofList] using (List.all_eq_true.mp (hc chunk hchunk) cs hcs)

end KIP126.LinE2.BasisCertificates
