module

public import KIP126.Main.Computation.LinCoordinates.Model.E2.Proofs

public import KIP126.Main.Computation.LinCoordinates.Model.RelationCertificates
public import Batteries.Tactic.OpenPrivate

import all KIP126.Main.Computation.LinCoordinates.Model.RelationCertificates
import all Init.Data.String.Legacy
import all Init.Data.String.Search
import all Init.Data.String.Slice

@[expose] public section

/-! Pinned relation-table certificates used in the theta--B Massey calculation.
The shared character transcription is checked against the original artifact;
these equations concern its presented algebra, with no Adams-page claim. -/
namespace KIP126.LinE2.RelationCertificates
open private splitOn_char thetaRelationChunkChars thetaRelationChunk_eq_chars
  from KIP126.Main.Computation.LinCoordinates.Model.RelationCertificates
set_option maxRecDepth 100000

private theorem theta_relation_member_85 : "18,1,85,1" ∈ RawData.relations := by
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨RawData.relationChunks[2], Array.getElem_mem_toList (by decide), ?_⟩
  rw [thetaRelationChunk_eq_chars, show "\n" = String.singleton '\n' from rfl,
    splitOn_char, String.toList_ofList]
  apply List.mem_map.mpr
  exact ⟨"18,1,85,1".toList, by decide +kernel, by simp⟩

theorem theta_massey_h5_mul_85_zero : generator ⟨18,by decide⟩ * generator ⟨85,by decide⟩ = 0 := by
  have hr := csv_relation_zero "18,1,85,1" theta_relation_member_85
  have hs : "18,1,85,1".splitOn ";"=["18,1,85,1"] := by
    simp +decide [String.splitOn,String.splitOnAux]
  have hp0 : "18,1,85,1" ≠ "" := by decide
  have hp : (("18,1,85,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [18,1,85,1] := by
    have hs : "18,1,85,1".splitOn "," = ["18","1","85","1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    rw [hs]
    simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
      String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
  norm_num [relationPolynomial,hs,monomialOfString,hp,hp0,polynomialOfPowers,
    RawData.generatorCount,generator,map_add,map_mul,map_pow,mul_assoc] at hr
  exact hr

private theorem theta_relation_member_84 : "18,1,84,1" ∈ RawData.relations := by
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨RawData.relationChunks[2], Array.getElem_mem_toList (by decide), ?_⟩
  rw [thetaRelationChunk_eq_chars, show "\n" = String.singleton '\n' from rfl,
    splitOn_char, String.toList_ofList]
  apply List.mem_map.mpr
  exact ⟨"18,1,84,1".toList, by decide +kernel, by simp⟩

theorem theta_massey_h5_mul_84_zero : generator ⟨18,by decide⟩ * generator ⟨84,by decide⟩ = 0 := by
  have hr := csv_relation_zero "18,1,84,1" theta_relation_member_84
  have hs : "18,1,84,1".splitOn ";"=["18,1,84,1"] := by
    simp +decide [String.splitOn,String.splitOnAux]
  have hp0 : "18,1,84,1" ≠ "" := by decide
  have hp : (("18,1,84,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [18,1,84,1] := by
    have hs : "18,1,84,1".splitOn "," = ["18","1","84","1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    rw [hs]
    simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
      String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
  norm_num [relationPolynomial,hs,monomialOfString,hp,hp0,polynomialOfPowers,
    RawData.generatorCount,generator,map_add,map_mul,map_pow,mul_assoc] at hr
  exact hr

private theorem theta_relation_member_69 : "18,1,69,1" ∈ RawData.relations := by
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨RawData.relationChunks[2], Array.getElem_mem_toList (by decide), ?_⟩
  rw [thetaRelationChunk_eq_chars, show "\n" = String.singleton '\n' from rfl,
    splitOn_char, String.toList_ofList]
  apply List.mem_map.mpr
  exact ⟨"18,1,69,1".toList, by decide +kernel, by simp⟩

theorem theta_massey_h5_mul_69_zero : generator ⟨18,by decide⟩ * generator ⟨69,by decide⟩ = 0 := by
  have hr := csv_relation_zero "18,1,69,1" theta_relation_member_69
  have hs : "18,1,69,1".splitOn ";"=["18,1,69,1"] := by
    simp +decide [String.splitOn,String.splitOnAux]
  have hp0 : "18,1,69,1" ≠ "" := by decide
  have hp : (("18,1,69,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [18,1,69,1] := by
    have hs : "18,1,69,1".splitOn "," = ["18","1","69","1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    rw [hs]
    simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
      String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
  norm_num [relationPolynomial,hs,monomialOfString,hp,hp0,polynomialOfPowers,
    RawData.generatorCount,generator,map_add,map_mul,map_pow,mul_assoc] at hr
  exact hr

end KIP126.LinE2.RelationCertificates
