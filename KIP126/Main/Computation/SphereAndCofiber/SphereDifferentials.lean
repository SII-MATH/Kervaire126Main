module

public import KIP126.Main.Computation.LinCoordinates.Model.E2.Proofs

public import KIP126.Main.Computation.SphereAndCofiber.Bounds
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Legacy

/-! Private named sphere differentials and product obstructions. -/

@[expose] public section

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory.Limits KIP126.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
open KIP126.SpectralSequence.FinitePageCalculus
open KIP126.LinE2.RelationCertificates
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.LinE2 KIP126.Computation.Near126
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

variable {D : AdamsComparison H M Syn} {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}

section SphereFactsProof
open CategoryTheory.Limits KIP126.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

private theorem sphere_named_differentials_hD3sq_h324 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (13,137) (16,139) (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by
    exact List.mem_of_getElem? (i := 324) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (13,137) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD3sq_h366 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 14, 138, [1], 16, 139, [1, 2], "S0_AdamsE2_ss", 3072⟩ (by
    exact List.mem_of_getElem? (i := 366) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD3sq_h367 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 14, 138, [0, 1], 16, 139, [2], "S0_AdamsE2_ss", 3073⟩ (by
    exact List.mem_of_getElem? (i := 367) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD3sq_h654 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (15,138) (18,140) (I.interpretation.basis .sphere 15 138 2) (I.interpretation.basis .sphere 18 140 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 15, 138, [2], 18, 140, [2], "proofs.db/log", 462481⟩ (by
    exact List.mem_of_getElem? (i := 654) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (15,138) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 138 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_d2_16
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : (sequence D .sphere).d 2 (16,139)=0  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e16_139,he16_139⟩ := I.basis ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_139
  change ∀i : Fin 3, e16_139.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 139 i.val at he16_139
  have h324 : HasDifferential E 3 (13,137) (16,139) (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := sphere_named_differentials_hD3sq_h324 I
  have h366 : HasDifferential E 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2) := sphere_named_differentials_hD3sq_h366 I
  have h367 : HasDifferential E 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 2) := sphere_named_differentials_hD3sq_h367 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _

  obtain ⟨_,_,y0,_,hy0,_⟩ := h324
  have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2;omega)
    (by decide : (2:ℤ)<3) (hrep2 _) ⟨y0,hy0⟩
  have d12 : E.d 2 (16,139) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2)=0 := by
    have hd := h366.eq_on_page_two.2
    change E.d 2 (14,138) _ = _ at hd
    rw [←hd]
    exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
  have d2 : E.d 2 (16,139) (I.interpretation.basis .sphere 16 139 2)=0 := by
    have hd := h367.eq_on_page_two.2
    change E.d 2 (14,138) _ = _ at hd
    rw [←hd]
    exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
  have d1 : E.d 2 (16,139) (I.interpretation.basis .sphere 16 139 1)=0 := by
    simpa only [map_add,d2,add_zero] using d12
  ext a
  change E.d 2 (16,139) a=0
  obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e16_139
    (fun i => e16_139.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
  rw [hc,map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  fin_cases i <;> simp only [apply_ite,map_zero,he16_139,d0,d1,d2,ite_self]


private theorem sphere_named_differentials_hD3sq (I : AdamsComputationTheorems D L G) : Derived.Differential I.interpretation 3 (mulAt h0Sq (atom .x_123_13_2))
    (mulAt h0Sq (atom .x_122_16)) := by
  classical
  let E := sequence D .sphere
  have stem122_d3_target_nonzero :
    HasNonzeroDifferential E 3 (15,138) (18,140)
      (I.interpretation.basis .sphere 15 138 2) (I.interpretation.basis .sphere 18 140 2) := by
    let E := sequence D .sphere
    obtain ⟨e16_139,he16_139⟩ := I.basis ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
      exact List.mem_of_getElem? (i := 230) (by rfl))
    change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_139
    change ∀i : Fin 3, e16_139.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 139 i.val at he16_139
    obtain ⟨e18_140,he18_140⟩ := I.basis ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
      exact List.mem_of_getElem? (i := 244) (by rfl))
    change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
    change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 18 140 i.val at he18_140
    have h324 : HasDifferential E 3 (13,137) (16,139) (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := sphere_named_differentials_hD3sq_h324 I
    have h366 : HasDifferential E 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2) := sphere_named_differentials_hD3sq_h366 I
    have h367 : HasDifferential E 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 2) := sphere_named_differentials_hD3sq_h367 I
    have h654 : HasDifferential E 3 (15,138) (18,140) (I.interpretation.basis .sphere 15 138 2) (I.interpretation.basis .sphere 18 140 2) := sphere_named_differentials_hD3sq_h654 I
    have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
      exact represents_two_self _
    have d2_16 : E.d 2 (16,139)=0 :=
      sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_d2_16 I
    obtain ⟨hdeg,xr,yr,hxr,hyr,hd⟩ := h654
    refine ⟨hdeg,xr,yr,hxr,hyr,hd,?_⟩
    have bne : I.interpretation.basis .sphere 18 140 2 ≠ 0 := by
      rw [show I.interpretation.basis .sphere 18 140 2=e18_140.symm (Finsupp.single 2 1) from (he18_140 2).symm]
      intro h
      have hh := congrArg e18_140 h
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 2) hh
      norm_num at hh'
    exact represents_next_nonzero_of_incoming_zero_at
      (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)≤2)
      (by exact d2_16) hyr (hrep2 _) bne
  have label15_138_2 : I.interpretation.sphere 15 138 (mulAt h0Sq (atom .x_123_13_2)) = I.interpretation.basis .sphere 15 138 2 := by
    have hc := I.monomials ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
      exact List.mem_of_getElem? (i := 222) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (2 : Fin 3)
    have heq : (mulAt h0Sq (atom .x_123_13_2))=z := by
      apply Subtype.ext
      rw [hz]
      change (generator ⟨0,by decide⟩ * generator ⟨0,by decide⟩) * generator ⟨418,by decide⟩ = projection (monomialOfString "0,2,418,1")
      have hs : "0,2,418,1" ≠ "" := by decide
      have hp : (("0,2,418,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0,2,418,1] := by
        have split : "0,2,418,1".splitOn "," = ["0", "2", "418", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
    rw [heq]
    exact he
  have label18_140_2 : I.interpretation.sphere 18 140 (mulAt h0Sq (atom .x_122_16)) = I.interpretation.basis .sphere 18 140 2 := by
    have hc := I.monomials ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
      exact List.mem_of_getElem? (i := 244) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (2 : Fin 3)
    have heq : (mulAt h0Sq (atom .x_122_16))=z := by
      apply Subtype.ext
      rw [hz]
      change (generator ⟨0,by decide⟩ * generator ⟨0,by decide⟩) * generator ⟨437,by decide⟩ = projection (monomialOfString "0,2,437,1")
      have hs : "0,2,437,1" ≠ "" := by decide
      have hp : (("0,2,437,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0,2,437,1] := by
        have split : "0,2,437,1".splitOn "," = ["0", "2", "437", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
    rw [heq]
    exact he
  change HasNonzeroDifferential E 3 (15,138) (18,140)
    (I.interpretation.sphere 15 138 (mulAt h0Sq (atom .x_123_13_2)))
    (I.interpretation.sphere 18 140 (mulAt h0Sq (atom .x_122_16)))
  rw [label15_138_2,label18_140_2]
  exact stem122_d3_target_nonzero

private theorem sphere_named_differentials_hD3x1264_h153 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (3,130) (5,131) (I.interpretation.basis .sphere 3 130 1) (I.interpretation.basis .sphere 5 131 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 3, 130, [1], 5, 131, [0], "S0_AdamsE2_ss", 2439⟩ (by
    exact List.mem_of_getElem? (i := 153) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (3,130) (5,131) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 3 130 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 5 131 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD3x1264_h655 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (4,130) (7,132) (I.interpretation.basis .sphere 4 130 0) (I.interpretation.basis .sphere 7 132 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 4, 130, [0], 7, 132, [0], "proofs.db/log", 929469⟩ (by
    exact List.mem_of_getElem? (i := 655) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (4,130) (7,132) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 132 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD3x1264_label4_130_0 (I : AdamsComputationTheorems D L G) : I.interpretation.sphere 4 130 (atom .x_126_4) = I.interpretation.basis .sphere 4 130 0  := by
  have hc := I.monomials ⟨.sphere, 4, 130, ["341,1", "0,2,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 119) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (0 : Fin 2)
  have heq : (atom .x_126_4)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨341,by decide⟩ = projection (monomialOfString "341,1")
    have hs : "341,1" ≠ "" := by decide
    have hp : (("341,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [341,1] := by
      have split : "341,1".splitOn "," = ["341", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem sphere_named_differentials_hD3x1264_label7_132_0 (I : AdamsComputationTheorems D L G) : I.interpretation.sphere 7 132 (mulAt h0Sq (atom .x_125_5)) = I.interpretation.basis .sphere 7 132 0  := by
  have hc := I.monomials ⟨.sphere, 7, 132, ["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (0 : Fin 1)
  have heq : (mulAt h0Sq (atom .x_125_5))=z := by
    apply Subtype.ext
    rw [hz]
    change (generator ⟨0,by decide⟩ * generator ⟨0,by decide⟩) * generator ⟨340,by decide⟩ = projection (monomialOfString "0,2,340,1")
    have hs : "0,2,340,1" ≠ "" := by decide
    have hp : (("0,2,340,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0,2,340,1] := by
      have split : "0,2,340,1".splitOn "," = ["0", "2", "340", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem sphere_named_differentials_hD3x1264 (I : AdamsComputationTheorems D L G) : Derived.Differential I.interpretation 3 (atom .x_126_4) (mulAt h0Sq (atom .x_125_5)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e5_131,he5_131⟩ := I.basis ⟨.sphere, 5, 131, ["0,3,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 127) (by rfl))
  change E.Page 2 (5,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e5_131
  change ∀i : Fin 1, e5_131.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 5 131 i.val at he5_131
  obtain ⟨e7_132,he7_132⟩ := I.basis ⟨.sphere, 7, 132, ["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (i := 149) (by rfl))
  change E.Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e7_132
  change ∀i : Fin 1, e7_132.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 132 i.val at he7_132
  have h153 : HasDifferential E 2 (3,130) (5,131) (I.interpretation.basis .sphere 3 130 1) (I.interpretation.basis .sphere 5 131 0) := sphere_named_differentials_hD3x1264_h153 I
  have h655 : HasDifferential E 3 (4,130) (7,132) (I.interpretation.basis .sphere 4 130 0) (I.interpretation.basis .sphere 7 132 0) := sphere_named_differentials_hD3x1264_h655 I
  have label4_130_0 : I.interpretation.sphere 4 130 (atom .x_126_4) = I.interpretation.basis .sphere 4 130 0  := sphere_named_differentials_hD3x1264_label4_130_0 I
  have label7_132_0 : I.interpretation.sphere 7 132 (mulAt h0Sq (atom .x_125_5)) = I.interpretation.basis .sphere 7 132 0  := sphere_named_differentials_hD3x1264_label7_132_0 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    as_aux_lemma =>
      exact represents_two_self _
  have d2_5 : E.d 2 (5,131)=0 := by
    obtain ⟨y,hy,hd⟩ := differential_target_cycle h153
    have d0 : E.d 2 (5,131) (I.interpretation.basis .sphere 5 131 0)=0 := by
      exact (congrArg (fun z => E.d 2 (5,131) z) hy.eq_on_page_two).trans hd
    apply d_zero_of_complete_representatives (by decide : (2:ℤ)≤2) e5_131
    intro i
    fin_cases i
    refine ⟨I.interpretation.basis .sphere 5 131 0,?_,d0⟩
    rw [he5_131]
    exact represents_two_self _
  change HasNonzeroDifferential E 3 (4,130) (7,132)
    (I.interpretation.sphere 4 130 (atom .x_126_4))
    (I.interpretation.sphere 7 132 (mulAt h0Sq (atom .x_125_5)))
  rw [label4_130_0,label7_132_0]
  obtain ⟨hdeg,xr,yr,hxr,hyr,hd⟩ := h655
  refine ⟨hdeg,xr,yr,hxr,hyr,hd,?_⟩
  have bne : I.interpretation.basis .sphere 7 132 0≠0 := by
    rw [show I.interpretation.basis .sphere 7 132 0 = e7_132.symm (Finsupp.single 0 1) from (he7_132 0).symm]
    exact basis_vector_ne_zero e7_132 0
  exact represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)≤2)
    d2_5 hyr (hrep2 _) bne

private theorem sphere_named_differentials_hD7source_h324 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (13,137) (16,139) (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by
    exact List.mem_of_getElem? (i := 324) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (13,137) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h366 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 14, 138, [1], 16, 139, [1, 2], "S0_AdamsE2_ss", 3072⟩ (by
    exact List.mem_of_getElem? (i := 366) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h367 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 14, 138, [0, 1], 16, 139, [2], "S0_AdamsE2_ss", 3073⟩ (by
    exact List.mem_of_getElem? (i := 367) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h654 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (15,138) (18,140) (I.interpretation.basis .sphere 15 138 2) (I.interpretation.basis .sphere 18 140 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 15, 138, [2], 18, 140, [2], "proofs.db/log", 462481⟩ (by
    exact List.mem_of_getElem? (i := 654) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (15,138) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 138 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h656 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 7 (11,134) (18,140) (I.interpretation.basis .sphere 11 134 0 + I.interpretation.basis .sphere 11 134 1 + I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 18 140 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 7, 11, 134, [0, 1, 3], 18, 140, [1], "proofs.db/log", 2671068⟩ (by
    exact List.mem_of_getElem? (i := 656) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 7 (11,134) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 134 [0, 1, 3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h250 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 5 (10,134) (15,138) (I.interpretation.basis .sphere 10 134 3) (I.interpretation.basis .sphere 15 138 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 5, 10, 134, [3], 15, 138, [1], "S0_AdamsE2_ss", 2694⟩ (by
    exact List.mem_of_getElem? (i := 250) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (10,134) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h277 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (11,135) (15,138) (I.interpretation.basis .sphere 11 135 1 + I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 15 138 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 4, 11, 135, [1, 2], 15, 138, [0], "S0_AdamsE2_ss", 2781⟩ (by
    exact List.mem_of_getElem? (i := 277) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (11,135) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h339 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (14,137) (17,139) (I.interpretation.basis .sphere 14 137 1) (I.interpretation.basis .sphere 17 139 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 14, 137, [1], 17, 139, [1], "S0_AdamsE2_ss", 2912⟩ (by
    exact List.mem_of_getElem? (i := 339) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (14,137) (17,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h340 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (14,137) (17,139) (I.interpretation.basis .sphere 14 137 0) (I.interpretation.basis .sphere 17 139 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 14, 137, [0], 17, 139, [0], "S0_AdamsE2_ss", 2913⟩ (by
    exact List.mem_of_getElem? (i := 340) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (14,137) (17,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h304 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (12,136) (14,137) (I.interpretation.basis .sphere 12 136 2) (I.interpretation.basis .sphere 14 137 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 12, 136, [2], 14, 137, [2], "S0_AdamsE2_ss", 2849⟩ (by
    exact List.mem_of_getElem? (i := 304) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,136) (14,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 136 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 137 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h319 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (13,136) (16,138) (I.interpretation.basis .sphere 13 136 1) (I.interpretation.basis .sphere 16 138 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 13, 136, [1], 16, 138, [1], "S0_AdamsE2_ss", 2843⟩ (by
    exact List.mem_of_getElem? (i := 319) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (13,136) (16,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 136 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 138 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h320 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (13,136) (16,138) (I.interpretation.basis .sphere 13 136 0) (I.interpretation.basis .sphere 16 138 0 + I.interpretation.basis .sphere 16 138 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 13, 136, [0], 16, 138, [0, 2], "S0_AdamsE2_ss", 2844⟩ (by
    exact List.mem_of_getElem? (i := 320) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (13,136) (16,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 138 [0, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h278 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (11,135) (13,136) (I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 13 136 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 11, 135, [2], 13, 136, [2], "S0_AdamsE2_ss", 2782⟩ (by
    exact List.mem_of_getElem? (i := 278) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,135) (13,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 136 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h297 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,133) (12,135) (I.interpretation.basis .sphere 9 133 1 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 9, 133, [1, 2], 12, 135, [0], "S0_AdamsE2_ss", 2775⟩ (by
    exact List.mem_of_getElem? (i := 297) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,133) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h298 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,133) (12,135) (I.interpretation.basis .sphere 9 133 0 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 1 + I.interpretation.basis .sphere 12 135 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 9, 133, [0, 2], 12, 135, [1, 2], "S0_AdamsE2_ss", 2776⟩ (by
    exact List.mem_of_getElem? (i := 298) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,133) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [0, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_h299 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 5 (7,131) (12,135) (I.interpretation.basis .sphere 7 131 1) (I.interpretation.basis .sphere 12 135 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 5, 7, 131, [1], 12, 135, [2], "S0_AdamsE2_ss", 2777⟩ (by
    exact List.mem_of_getElem? (i := 299) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (7,131) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_source12
    (I : AdamsComputationTheorems D L G) : Subsingleton ((sequence D .sphere).Page 6 (12,135))  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e12_135,he12_135⟩ := I.basis ⟨.sphere, 12, 135, ["408,1", "0,1,386,1", "0,2,69,1,80,1"]⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  change E.Page 2 (12,135) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e12_135
  change ∀i : Fin 3, e12_135.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 135 i.val at he12_135
  have h297 : HasDifferential E 3 (9,133) (12,135) (I.interpretation.basis .sphere 9 133 1 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 0) := sphere_named_differentials_hD7source_h297 I
  have h298 : HasDifferential E 3 (9,133) (12,135) (I.interpretation.basis .sphere 9 133 0 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 1 + I.interpretation.basis .sphere 12 135 2) := sphere_named_differentials_hD7source_h298 I
  have h299 : HasDifferential E 5 (7,131) (12,135) (I.interpretation.basis .sphere 7 131 1) (I.interpretation.basis .sphere 12 135 2) := sphere_named_differentials_hD7source_h299 I
  have hsub {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)

  have z0 := differential_target_later_zero (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<6) h297
  have z12 := differential_target_later_zero (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<6) h298
  have z2 := differential_target_later_zero (by change (2:ℤ)≤5;omega) (by decide : (5:ℤ)<6) h299
  have z1 : RepresentsOnPage E 6 (12,135) (I.interpretation.basis .sphere 12 135 1) 0 := by
    simpa only [add_sub_cancel_right,sub_self] using hsub z12 z2
  have hv (i : Fin 3) : RepresentsOnPage E 6 (12,135) (e12_135.symm (Finsupp.single i 1)) 0 := by
    fin_cases i
    · simpa only [he12_135] using z0
    · simpa only [he12_135] using z1
    · simpa only [he12_135] using z2
  have all (a : E.Page 6 (12,135)) : a=0 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤6) e12_135 (fun _ => 0) hv a
    simpa only [ite_self,Finset.sum_const_zero] using hc
  exact ⟨fun x y => (all x).trans (all y).symm⟩

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_source13
    (I : AdamsComputationTheorems D L G) : Subsingleton ((sequence D .sphere).Page 4 (13,136))  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e14_137,he14_137⟩ := I.basis ⟨.sphere, 14, 137, ["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 215) (by rfl))
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_137
  change ∀i : Fin 3, e14_137.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 137 i.val at he14_137
  obtain ⟨e13_136,he13_136⟩ := I.basis ⟨.sphere, 13, 136, ["418,1", "417,1", "0,2,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 207) (by rfl))
  change E.Page 2 (13,136) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e13_136
  change ∀i : Fin 3, e13_136.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 136 i.val at he13_136
  obtain ⟨e16_138,he16_138⟩ := I.basis ⟨.sphere, 16, 138, ["437,1", "23,1,189,1", "0,1,424,1"]⟩ (by
    exact List.mem_of_getElem? (i := 229) (by rfl))
  change E.Page 2 (16,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_138
  change ∀i : Fin 3, e16_138.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 138 i.val at he16_138
  have h339 : HasDifferential E 3 (14,137) (17,139) (I.interpretation.basis .sphere 14 137 1) (I.interpretation.basis .sphere 17 139 1) := sphere_named_differentials_hD7source_h339 I
  have h340 : HasDifferential E 3 (14,137) (17,139) (I.interpretation.basis .sphere 14 137 0) (I.interpretation.basis .sphere 17 139 0) := sphere_named_differentials_hD7source_h340 I
  have h304 : HasDifferential E 2 (12,136) (14,137) (I.interpretation.basis .sphere 12 136 2) (I.interpretation.basis .sphere 14 137 2) := sphere_named_differentials_hD7source_h304 I
  have h319 : HasDifferential E 3 (13,136) (16,138) (I.interpretation.basis .sphere 13 136 1) (I.interpretation.basis .sphere 16 138 1) := sphere_named_differentials_hD7source_h319 I
  have h320 : HasDifferential E 3 (13,136) (16,138) (I.interpretation.basis .sphere 13 136 0) (I.interpretation.basis .sphere 16 138 0 + I.interpretation.basis .sphere 16 138 2) := sphere_named_differentials_hD7source_h320 I
  have h278 : HasDifferential E 2 (11,135) (13,136) (I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 13 136 2) := sphere_named_differentials_hD7source_h278 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
  have e2_map_zero {p : ℤ × ℤ} {N : ℕ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin N →₀ F2))
      (h : ∀ i, E.d 2 p (e.symm (Finsupp.single i 1))=0) : E.d 2 p=0 := by
    ext a
    change E.d 2 p a=0
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e
      (fun i => e.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
    rw [hc,map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [apply_ite,map_zero,h,ite_self]
  have d2_14 : E.d 2 (14,137)=0 := by
    obtain ⟨_,b0,_,hb0,_,_⟩ := h340
    obtain ⟨_,b1,_,hb1,_,_⟩ := h339
    apply e2_map_zero e14_137
    intro i
    fin_cases i
    · rw [he14_137]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨b0,hb0⟩
    · rw [he14_137]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨b1,hb1⟩
    · rw [he14_137]
      have hd := h304.eq_on_page_two.2
      change E.d 2 (12,136) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (12,136)) _

  apply fourth_zero_of_three_basis (by change (2:ℤ)≤2; omega) e13_136 (I.interpretation.basis .sphere 16 138 0+I.interpretation.basis .sphere 16 138 2)
    (I.interpretation.basis .sphere 16 138 1)
  · rw [he13_136]
    exact h320
  · rw [he13_136]
    exact h319
  · rw [he13_136]
    exact differential_target_later_zero (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) h278
  · exact d2_14
  all_goals intro hz; have hh := congrArg e16_138 hz
  all_goals simp only [map_add,show I.interpretation.basis .sphere 16 138 0=e16_138.symm (Finsupp.single 0 1) from (he16_138 0).symm,
    show I.interpretation.basis .sphere 16 138 1=e16_138.symm (Finsupp.single 1 1) from (he16_138 1).symm,
    show I.interpretation.basis .sphere 16 138 2=e16_138.symm (Finsupp.single 2 1) from (he16_138 2).symm,
    LinearEquiv.apply_symm_apply,map_zero] at hh
  · have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 0) hh
    norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
  · have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
    norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
  · have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 0) hh
    norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_source14
    (I : AdamsComputationTheorems D L G) : Subsingleton ((sequence D .sphere).Page 4 (14,137))  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e15_138,he15_138⟩ := I.basis ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e15_138
  change ∀i : Fin 3, e15_138.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 15 138 i.val at he15_138
  obtain ⟨e14_137,he14_137⟩ := I.basis ⟨.sphere, 14, 137, ["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 215) (by rfl))
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_137
  change ∀i : Fin 3, e14_137.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 137 i.val at he14_137
  obtain ⟨e17_139,he17_139⟩ := I.basis ⟨.sphere, 17, 139, ["13,3,76,1", "0,1,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 237) (by rfl))
  change E.Page 2 (17,139) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e17_139
  change ∀i : Fin 2, e17_139.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 17 139 i.val at he17_139
  have h654 : HasDifferential E 3 (15,138) (18,140) (I.interpretation.basis .sphere 15 138 2) (I.interpretation.basis .sphere 18 140 2) := sphere_named_differentials_hD7source_h654 I
  have h250 : HasDifferential E 5 (10,134) (15,138) (I.interpretation.basis .sphere 10 134 3) (I.interpretation.basis .sphere 15 138 1) := sphere_named_differentials_hD7source_h250 I
  have h277 : HasDifferential E 4 (11,135) (15,138) (I.interpretation.basis .sphere 11 135 1 + I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 15 138 0) := sphere_named_differentials_hD7source_h277 I
  have h339 : HasDifferential E 3 (14,137) (17,139) (I.interpretation.basis .sphere 14 137 1) (I.interpretation.basis .sphere 17 139 1) := sphere_named_differentials_hD7source_h339 I
  have h340 : HasDifferential E 3 (14,137) (17,139) (I.interpretation.basis .sphere 14 137 0) (I.interpretation.basis .sphere 17 139 0) := sphere_named_differentials_hD7source_h340 I
  have h304 : HasDifferential E 2 (12,136) (14,137) (I.interpretation.basis .sphere 12 136 2) (I.interpretation.basis .sphere 14 137 2) := sphere_named_differentials_hD7source_h304 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
  have e2_map_zero {p : ℤ × ℤ} {N : ℕ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin N →₀ F2))
      (h : ∀ i, E.d 2 p (e.symm (Finsupp.single i 1))=0) : E.d 2 p=0 := by
    ext a
    change E.d 2 p a=0
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e
      (fun i => e.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
    rw [hc,map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [apply_ite,map_zero,h,ite_self]
  have d2_15 : E.d 2 (15,138)=0 := by
    obtain ⟨_,_,b0,_,hb0,_⟩ := h277
    obtain ⟨_,_,b1,_,hb1,_⟩ := h250
    obtain ⟨_,b2,_,hb2,_,_⟩ := h654
    apply e2_map_zero e15_138
    intro i
    fin_cases i
    · rw [he15_138]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨b0,hb0⟩
    · rw [he15_138]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<5) (hrep2 _) ⟨b1,hb1⟩
    · rw [he15_138]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨b2,hb2⟩

  apply fourth_zero_of_three_basis (by change (2:ℤ)≤2; omega) e14_137 (I.interpretation.basis .sphere 17 139 0) (I.interpretation.basis .sphere 17 139 1)
  · rw [he14_137]
    exact h340
  · rw [he14_137]
    exact h339
  · rw [he14_137]
    exact differential_target_later_zero (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) h304
  · exact d2_15
  all_goals intro hz; have hh := congrArg e17_139 hz
  all_goals simp only [map_add,show I.interpretation.basis .sphere 17 139 0=e17_139.symm (Finsupp.single 0 1) from (he17_139 0).symm,
    show I.interpretation.basis .sphere 17 139 1=e17_139.symm (Finsupp.single 1 1) from (he17_139 1).symm,
    LinearEquiv.apply_symm_apply,map_zero] at hh
  · have hh' := congrArg (fun f : Fin 2 →₀ F2 => f 0) hh
    norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
  · have hh' := congrArg (fun f : Fin 2 →₀ F2 => f 1) hh
    norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
  · have hh' := congrArg (fun f : Fin 2 →₀ F2 => f 0) hh
    norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'


private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_bne
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : I.interpretation.basis .sphere 18 140 1 ≠ 0  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e18_140,he18_140⟩ := I.basis ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
  change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 18 140 i.val at he18_140

  rw [show I.interpretation.basis .sphere 18 140 1=e18_140.symm (Finsupp.single 1 1) from (he18_140 1).symm]
  intro h
  have hh := congrArg e18_140 h
  simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
  have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
  norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_bdne
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) : I.interpretation.basis .sphere 18 140 1-I.interpretation.basis .sphere 18 140 2 ≠ 0  := by
  classical
  let E := sequence D .sphere
  obtain ⟨e18_140,he18_140⟩ := I.basis ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
  change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 18 140 i.val at he18_140

  intro h
  have hh := congrArg e18_140 h
  simp only [map_sub,
    show I.interpretation.basis .sphere 18 140 1=e18_140.symm (Finsupp.single 1 1) from (he18_140 1).symm,
    show I.interpretation.basis .sphere 18 140 2=e18_140.symm (Finsupp.single 2 1) from (he18_140 2).symm,
    LinearEquiv.apply_symm_apply,map_zero] at hh
  have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
  norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_third_image (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
    ∃ b : (sequence D .sphere).Page 3 (18,140),
    RepresentsOnPage (sequence D .sphere) 3 (18,140)
      (I.interpretation.basis .sphere 18 140 2) b ∧
    (∀ v : (sequence D .sphere).Page 3 (15,138),
      (sequence D .sphere).d 3 (15,138) v=0 ∨ (sequence D .sphere).d 3 (15,138) v=b) := by

  classical

  let E := sequence D .sphere
  obtain ⟨e15_138,he15_138⟩ := I.basis ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e15_138
  change ∀i : Fin 3, e15_138.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 15 138 i.val at he15_138
  have h654 : HasDifferential E 3 (15,138) (18,140) (I.interpretation.basis .sphere 15 138 2) (I.interpretation.basis .sphere 18 140 2) := sphere_named_differentials_hD7source_h654 I
  have h250 : HasDifferential E 5 (10,134) (15,138) (I.interpretation.basis .sphere 10 134 3) (I.interpretation.basis .sphere 15 138 1) := sphere_named_differentials_hD7source_h250 I
  have h277 : HasDifferential E 4 (11,135) (15,138) (I.interpretation.basis .sphere 11 135 1 + I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 15 138 0) := sphere_named_differentials_hD7source_h277 I
  obtain ⟨_,s0,t0,hs0,ht0,_⟩ := h277
  obtain ⟨_,s1,t1,hs1,ht1,_⟩ := h250
  obtain ⟨_,a2,b2,ha2,hb2,hd2⟩ := h654
  change E.d 3 (15,138) a2=b2 at hd2
  obtain ⟨a0,ha0⟩ := represents_before (E := E) (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ht0
  obtain ⟨a1,ha1⟩ := represents_before (E := E) (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) ht1
  have d0 : E.d 3 (15,138) a0=0 := represents_d_zero_of_later (by change (2:ℤ)≤3;omega)
    (by decide : (3:ℤ)<4) ha0 ⟨t0,ht0⟩
  have d1 : E.d 3 (15,138) a1=0 := represents_d_zero_of_later (by change (2:ℤ)≤3;omega)
    (by decide : (3:ℤ)<5) ha1 ⟨t1,ht1⟩
  have image3 (v : E.Page 3 (15,138)) : E.d 3 (15,138) v=0 ∨ E.d 3 (15,138) v=b2 := by
    let vv : Fin 3 → E.Page 3 (15,138) := ![a0,a1,a2]
    have hv (i : Fin 3) : RepresentsOnPage E 3 (15,138) (e15_138.symm (Finsupp.single i 1)) (vv i) := by
      fin_cases i
      · change RepresentsOnPage E 3 (15,138) _ a0
        rw [he15_138]
        exact ha0
      · change RepresentsOnPage E 3 (15,138) _ a1
        rw [he15_138]
        exact ha1
      · change RepresentsOnPage E 3 (15,138) _ a2
        rw [he15_138]
        exact ha2
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e15_138 vv hv v
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hc
    change v=(if c 0=0 then 0 else a0)+((if c 1=0 then 0 else a1)+(if c 2=0 then 0 else a2)) at hc
    rw [hc]
    simp only [map_add,apply_ite,map_zero,d0,d1,hd2,ite_self,zero_add]
    by_cases hc2 : c 2=0
    · exact Or.inl (by simp only [hc2,ite_true])
    · exact Or.inr (by simp only [hc2,ite_false])
  exact ⟨b2,hb2,image3⟩

private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero (I : AdamsComputationTheorems D L G)
    {y4 : (sequence D .sphere).Page 4 (18,140)}
    (hy4 : RepresentsOnPage (sequence D .sphere) 4 (18,140)
      (I.interpretation.basis .sphere 18 140 1) y4) : y4 ≠ 0 := by
  classical
  let E := sequence D .sphere
  have d2_16 : E.d 2 (16,139)=0 := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_d2_16 I
  obtain ⟨b2,hb2,image3⟩ := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_third_image I
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hy4
  have bne : I.interpretation.basis .sphere 18 140 1 ≠ 0  := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_bne I
  have bdne : I.interpretation.basis .sphere 18 140 1-I.interpretation.basis .sphere 18 140 2 ≠ 0  := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero_bdne I
  have y3ne : y3≠0 := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 2) (p := (18,140)) (by change (2:ℤ)≤2;omega)
    (by decide) d2_16 hy3 (represents_two_self _) bne
  have y3diff : y3-b2≠0 := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 2) (p := (18,140)) (by change (2:ℤ)≤2;omega)
    (by decide) d2_16 (represents_sub_tail hy3 hb2) (represents_two_self _) bdne

  apply represents_next_nonzero_of_incoming_two_cases_at
    (r := 3) (p := (18,140)) (q := (15,138)) (by rfl)
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) hy4 hy3 ?_ y3ne y3diff
  intro v
  change E.d 3 (15,138) v=0 ∨ E.d 3 (15,138) v=b2
  exact image3 v


private theorem sphere_named_differentials_hD7source_stem122_d7_target_nonzero (I : AdamsComputationTheorems D L G) :
  HasNonzeroDifferential (sequence D .sphere) 7 (11,134) (18,140)
    (I.interpretation.basis .sphere 11 134 0 + I.interpretation.basis .sphere 11 134 1 + I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 18 140 1)  := by
  let E := sequence D .sphere
  have h656 : HasDifferential E 7 (11,134) (18,140) (I.interpretation.basis .sphere 11 134 0 + I.interpretation.basis .sphere 11 134 1 + I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 18 140 1) := sphere_named_differentials_hD7source_h656 I
  have source14 : Subsingleton (E.Page 4 (14,137))  := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_source14 I
  have source13 : Subsingleton (E.Page 4 (13,136))  := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_source13 I
  have source12 : Subsingleton (E.Page 6 (12,135))  := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_source12 I
  obtain ⟨hdeg,x7,y7,hx7,hy7,hd7⟩ := h656
  obtain ⟨y4,hy4⟩ := represents_before (E := E) (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤7) hy7
  have y4ne : y4≠0 := sphere_named_differentials_hD7source_stem122_d7_target_nonzero_target_page_four_nonzero I hy4
  have incoming4 : E.d 4 (14,137)=0 := by
    ext v
    change E.d 4 (14,137) v=0
    rw [source14.elim v 0,map_zero]
  have incoming5 : E.d 5 (13,136)=0 := by
    have hz := adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 5 13 136
      (by decide) (by decide) source13
    ext v
    change E.d 5 (13,136) v=0
    rw [hz.elim v 0,map_zero]
  have incoming6 : E.d 6 (12,135)=0 := by
    ext v
    change E.d 6 (12,135) v=0
    rw [source12.elim v 0,map_zero]
  obtain ⟨y5,hy5⟩ := represents_before (E := E) (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤7) hy7
  obtain ⟨y6,hy6⟩ := represents_before (E := E) (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤7) hy7
  have y5ne := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 4) (p := (18,140)) (by change (2:ℤ)≤4;omega) (by decide) incoming4 hy5 hy4 y4ne
  have y6ne := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 5) (p := (18,140)) (by change (2:ℤ)≤5;omega) (by decide) incoming5 hy6 hy5 y5ne
  have y7ne := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 6) (p := (18,140)) (by change (2:ℤ)≤6;omega) (by decide) incoming6 hy7 hy6 y6ne
  exact ⟨hdeg,x7,y7,hx7,hy7,hd7,y7ne⟩


private theorem sphere_named_differentials_hD7source_label11_134_0 (I : AdamsComputationTheorems D L G) : I.interpretation.sphere 11 134 (atom .x_123_11_2) = I.interpretation.basis .sphere 11 134 0  := by
  have hc := I.monomials ⟨.sphere, 11, 134, ["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (0 : Fin 5)
  have heq : (atom .x_123_11_2)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨387,by decide⟩ = projection (monomialOfString "387,1")
    have hs : "387,1" ≠ "" := by decide
    have hp : (("387,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [387,1] := by
      have split : "387,1".splitOn "," = ["387", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two,mul_assoc]
  rw [heq]
  exact he


private theorem sphere_named_differentials_hD7source_label11_134_1 (I : AdamsComputationTheorems D L G) : I.interpretation.sphere 11 134 (atom .x_123_11) = I.interpretation.basis .sphere 11 134 1  := by
  have hc := I.monomials ⟨.sphere, 11, 134, ["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (1 : Fin 5)
  have heq : (atom .x_123_11)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨386,by decide⟩ = projection (monomialOfString "386,1")
    have hs : "386,1" ≠ "" := by decide
    have hp : (("386,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [386,1] := by
      have split : "386,1".splitOn "," = ["386", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two,mul_assoc]
  rw [heq]
  exact he


private theorem sphere_named_differentials_hD7source_label11_134_3 (I : AdamsComputationTheorems D L G) : I.interpretation.sphere 11 134 (mulAt (mulAt dataH0 dataH6) (atom .b4)) = I.interpretation.basis .sphere 11 134 3  := by
  have hc := I.monomials ⟨.sphere, 11, 134, ["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (3 : Fin 5)
  have heq : (mulAt (mulAt dataH0 dataH6) (atom .b4))=z := by
    apply Subtype.ext
    rw [hz]
    change (generator ⟨0,by decide⟩ * generator ⟨69,by decide⟩) * generator ⟨80,by decide⟩ = projection (monomialOfString "0,1,69,1,80,1")
    have hs : "0,1,69,1,80,1" ≠ "" := by decide
    have hp : (("0,1,69,1,80,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0,1,69,1,80,1] := by
      have split : "0,1,69,1,80,1".splitOn "," = ["0", "1", "69", "1", "80", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two,mul_assoc]
  rw [heq]
  exact he


private theorem sphere_named_differentials_hD7source_label18_140_1 (I : AdamsComputationTheorems D L G) : I.interpretation.sphere 18 140 (mulAt dataH1 (atom .x_121_17)) = I.interpretation.basis .sphere 18 140 1  := by
  have hc := I.monomials ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (1 : Fin 3)
  have heq : (mulAt dataH1 (atom .x_121_17))=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨1,by decide⟩ * generator ⟨436,by decide⟩ = projection (monomialOfString "1,1,436,1")
    have hs : "1,1,436,1" ≠ "" := by decide
    have hp : (("1,1,436,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1,1,436,1] := by
      have split : "1,1,436,1".splitOn "," = ["1", "1", "436", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two,mul_assoc]
  rw [heq]
  exact he


private theorem sphere_named_differentials_hD7source (I : AdamsComputationTheorems D L G) : Derived.Differential I.interpretation 7 d7Source (mulAt dataH1 (atom .x_121_17)) := by
  classical
  have stem122_d7_target_nonzero :
    HasNonzeroDifferential (sequence D .sphere) 7 (11,134) (18,140)
      (I.interpretation.basis .sphere 11 134 0 + I.interpretation.basis .sphere 11 134 1 + I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 18 140 1)  := sphere_named_differentials_hD7source_stem122_d7_target_nonzero I
  have label11_134_0 : I.interpretation.sphere 11 134 (atom .x_123_11_2) = I.interpretation.basis .sphere 11 134 0  := sphere_named_differentials_hD7source_label11_134_0 I
  have label11_134_1 : I.interpretation.sphere 11 134 (atom .x_123_11) = I.interpretation.basis .sphere 11 134 1  := sphere_named_differentials_hD7source_label11_134_1 I
  have label11_134_3 : I.interpretation.sphere 11 134 (mulAt (mulAt dataH0 dataH6) (atom .b4)) = I.interpretation.basis .sphere 11 134 3  := sphere_named_differentials_hD7source_label11_134_3 I
  have label18_140_1 : I.interpretation.sphere 18 140 (mulAt dataH1 (atom .x_121_17)) = I.interpretation.basis .sphere 18 140 1  := sphere_named_differentials_hD7source_label18_140_1 I
  change HasNonzeroDifferential (sequence D .sphere) 7 (11,134) (18,140)
    (I.interpretation.sphere 11 134 d7Source)
    (I.interpretation.sphere 18 140 (mulAt dataH1 (atom .x_121_17)))
  simp only [d7Source,map_add,label11_134_0,label11_134_1,label11_134_3,label18_140_1]
  exact stem122_d7_target_nonzero

private theorem sphere_named_differentials (I : AdamsComputationTheorems D L G) :
    (Derived.Differential I.interpretation 3 (mulAt h0Sq (atom .x_123_13_2))
      (mulAt h0Sq (atom .x_122_16))) ∧
    (Derived.Differential I.interpretation 3 (atom .x_126_4) (mulAt h0Sq (atom .x_125_5))) ∧
    (Derived.Differential I.interpretation 7 d7Source (mulAt dataH1 (atom .x_121_17))) := by
  classical
  exact ⟨(sphere_named_differentials_hD3sq I), (sphere_named_differentials_hD3x1264 I), (sphere_named_differentials_hD7source I)⟩

private theorem pq_p_label (I : AdamsComputationTheorems D L G)
    (hc0 : "2,1,79,1;0,1,89,1" ∈ RawData.relations) :
    I.interpretation.sphere 12 137 (mulAt P (atom .h2))=I.interpretation.basis .sphere 12 137 2 := by
  classical
  have hc := I.monomials (⟨.sphere,12,137,["426,1","425,1","0,1,69,1,89,1","0,3,391,1","0,4,375,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 201) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (2:Fin 5)
  have hm0 : "0,1,69,1,89,1"≠"" := by decide
  have hm : (("0,1,69,1,89,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 1, 69, 1, 89, 1] := by
    have hs : "0,1,69,1,89,1".splitOn ","=["0", "1", "69", "1", "89", "1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    rw [hs]
    simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
      String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
  have hm : projection (monomialOfString "0,1,69,1,89,1")=generator ⟨0,by decide⟩*(generator ⟨69,by decide⟩*generator ⟨89,by decide⟩) := by
    norm_num [monomialOfString,hm,hm0,polynomialOfPowers,RawData.generatorCount,map_mul,map_pow,generator]
  have hv : mulAt P (atom .h2)=z := by
    apply Subtype.ext
    rw [hz]
    change (generator ⟨69,by decide⟩*generator ⟨79,by decide⟩)*generator ⟨2,by decide⟩=projection (monomialOfString "0,1,69,1,89,1")
    rw [hm]
    calc
      _ = generator ⟨69,by decide⟩*(generator ⟨2,by decide⟩*generator ⟨79,by decide⟩) := by ac_rfl
      _ = generator ⟨69,by decide⟩*(generator ⟨0,by decide⟩*generator ⟨89,by decide⟩) := by rw [pq_relation0 hc0]
      _ = _ := by ac_rfl
  rw [hv]
  exact he

private theorem pq_q_label (I : AdamsComputationTheorems D L G)
    (hc1 : "2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1" ∈ RawData.relations)
    (hc2 : "0,1,426,1;0,4,391,1" ∈ RawData.relations)
    (hc3 : "0,2,69,1,89,1;0,5,375,1" ∈ RawData.relations) :
    I.interpretation.sphere 13 138 (mulAt Q (atom .h2))=
      I.interpretation.basis .sphere 13 138 3+I.interpretation.basis .sphere 13 138 4 := by
  classical
  have hc := I.monomials (⟨.sphere,13,138,["24,1,190,1","3,1,335,1","0,1,425,1","0,4,391,1","0,5,375,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 209) (by rfl)) rfl
  obtain ⟨z3,hz3,he3⟩ := hc (3:Fin 5)
  obtain ⟨z4,hz4,he4⟩ := hc (4:Fin 5)
  have hp30 : "0,4,391,1"≠"" := by decide
  have hp3 : (("0,4,391,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 4, 391, 1] := by
    have hs : "0,4,391,1".splitOn ","=["0", "4", "391", "1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    rw [hs]
    simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
      String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
  have hp40 : "0,5,375,1"≠"" := by decide
  have hp4 : (("0,5,375,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 5, 375, 1] := by
    have hs : "0,5,375,1".splitOn ","=["0", "5", "375", "1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    rw [hs]
    simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
      String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
  have hm3 : projection (monomialOfString "0,4,391,1")=generator ⟨0,by decide⟩^4*generator ⟨391,by decide⟩ := by
    norm_num [monomialOfString,hp3,hp30,polynomialOfPowers,RawData.generatorCount,map_mul,map_pow,generator]
  have hm4 : projection (monomialOfString "0,5,375,1")=generator ⟨0,by decide⟩^5*generator ⟨375,by decide⟩ := by
    norm_num [monomialOfString,hp4,hp40,polynomialOfPowers,RawData.generatorCount,map_mul,map_pow,generator]
  have hv : mulAt Q (atom .h2)=z3+z4 := by
    apply Subtype.ext
    change (generator ⟨18,by decide⟩*generator ⟨188,by decide⟩)*generator ⟨2,by decide⟩=z3.val+z4.val
    rw [hz3,hz4]
    change _=projection (monomialOfString "0,4,391,1")+projection (monomialOfString "0,5,375,1")
    rw [hm3,hm4]
    calc
      _ = generator ⟨2,by decide⟩*(generator ⟨18,by decide⟩*generator ⟨188,by decide⟩) := by ac_rfl
      _ = _ := (pq_relation1 hc1).trans (congrArg₂ (·+·) (pq_relation2 hc2) (pq_relation3 hc3))
  rw [hv,map_add,he3,he4]
  rfl

private theorem pq_p_boundary_h260 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,136) (12,137)
    ((I.interpretation.basis .sphere 10 136 0)) ((I.interpretation.basis .sphere 12 137 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,136,[0],12,137,[2],"S0_AdamsE2_ss",2859⟩ (by
    exact List.mem_of_getElem? (i := 260) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,136) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem pq_p_boundary (I : AdamsComputationTheorems D L G)
    (hc0 : "2,1,79,1;0,1,89,1" ∈ RawData.relations) :
    IsBoundaryBy (sequence D .sphere) 2 (12,137)
      (I.interpretation.sphere 12 137 (mulAt P (atom .h2))) := by
  classical
  let E := sequence D .sphere
  have h260 : HasDifferential E 2 (10,136) (12,137)
      ((I.interpretation.basis .sphere 10 136 0)) ((I.interpretation.basis .sphere 12 137 2)) := pq_p_boundary_h260 I
  rw [pq_p_label I hc0]
  exact pq_rep3zero_boundary (differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h260)

private theorem pq_q_boundary_h288 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    ((I.interpretation.basis .sphere 11 137 0)) ((I.interpretation.basis .sphere 13 138 3)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,137,[0],13,138,[3],"S0_AdamsE2_ss",2927⟩ (by
    exact List.mem_of_getElem? (i := 288) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,137) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem pq_q_boundary_h289 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    ((I.interpretation.basis .sphere 11 137 3)) ((I.interpretation.basis .sphere 13 138 4)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,137,[3],13,138,[4],"S0_AdamsE2_ss",2928⟩ (by
    exact List.mem_of_getElem? (i := 289) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,137) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem pq_q_boundary (I : AdamsComputationTheorems D L G)
    (hc1 : "2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1" ∈ RawData.relations)
    (hc2 : "0,1,426,1;0,4,391,1" ∈ RawData.relations)
    (hc3 : "0,2,69,1,89,1;0,5,375,1" ∈ RawData.relations) :
    IsBoundaryBy (sequence D .sphere) 2 (13,138)
      (I.interpretation.sphere 13 138 (mulAt Q (atom .h2))) := by
  classical
  let E := sequence D .sphere
  have h288 : HasDifferential E 2 (11,137) (13,138)
      ((I.interpretation.basis .sphere 11 137 0)) ((I.interpretation.basis .sphere 13 138 3)) := pq_q_boundary_h288 I
  have h289 : HasDifferential E 2 (11,137) (13,138)
      ((I.interpretation.basis .sphere 11 137 3)) ((I.interpretation.basis .sphere 13 138 4)) := pq_q_boundary_h289 I
  rw [pq_q_label I hc1 hc2 hc3]
  apply pq_rep3zero_boundary
  simpa only [add_zero] using middle_add
    (differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h288)
    (differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h289)

private theorem sphere_product_obstructions_h180 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (7,70) (9,71)
    (I.interpretation.basis .sphere 7 70 2) (I.interpretation.basis .sphere 9 71 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,7,70,[2],9,71,[0],"S0_AdamsE2_ss",513⟩ (by
    exact List.mem_of_getElem? (i := 180) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (7,70) (9,71) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 70 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 71 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_product_obstructions_hD2H0six
    (I : AdamsComputationTheorems D L G) : Derived.Differential I.interpretation 2 (mulAt h0Six dataH6) (mulAt dataH0 B)  := by
  classical

  have hmem := relation_member5
  let E := sequence D .sphere
  have hs : I.interpretation.sphere 7 70 (mulAt h0Six dataH6) = I.interpretation.basis .sphere 7 70 2 := by
    have hc := I.monomials (⟨.sphere,7,70,["85,1", "84,1", "0,6,69,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 143) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (2:Fin 3)
    have heq : (mulAt h0Six dataH6)=z := by
      apply Subtype.ext
      rw [hz]
      change ((generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*(generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*(generator ⟨0,by decide⟩*generator ⟨0,by decide⟩))*generator ⟨69,by decide⟩ = projection (monomialOfString "0,6,69,1")
      have hp : (("0,6,69,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 6, 69, 1] := by
        have split : "0,6,69,1".splitOn "," = ["0", "6", "69", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "0,6,69,1"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have ht0 : I.interpretation.sphere 9 71 (mulAt (mulAt h0Six dataH0) h5Sq) = I.interpretation.basis .sphere 9 71 0 := by
    have hc := I.monomials (⟨.sphere,9,71,["0,7,18,2"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 167) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
    have heq : (mulAt (mulAt h0Six dataH0) h5Sq)=z := by
      apply Subtype.ext
      rw [hz]
      change (((generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*(generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*(generator ⟨0,by decide⟩*generator ⟨0,by decide⟩))*generator ⟨0,by decide⟩)*(generator ⟨18,by decide⟩*generator ⟨18,by decide⟩) = projection (monomialOfString "0,7,18,2")
      have hp : (("0,7,18,2".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 7, 18, 2] := by
        have split : "0,7,18,2".splitOn "," = ["0", "7", "18", "2"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "0,7,18,2"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have hrel : mulAt dataH0 B = mulAt (mulAt h0Six dataH0) h5Sq := by
    apply Subtype.ext
    have hz := csv_relation_zero "0,1,82,1;0,7,18,2" hmem
    have hsplit : "0,1,82,1;0,7,18,2".splitOn ";" = ["0,1,82,1","0,7,18,2"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hp0 : (("0,1,82,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 1, 82, 1] := by
      have split : "0,1,82,1".splitOn "," = ["0", "1", "82", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hp1 : (("0,7,18,2".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 7, 18, 2] := by
      have split : "0,7,18,2".splitOn "," = ["0", "7", "18", "2"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hneg (x : KIP126.LinE2.E2) : -x = x := by
      obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
      change -(projection p)=projection p
      rw [←map_neg]
      exact congrArg projection (CharTwo.neg_eq p)
    norm_num [relationPolynomial,hsplit,monomialOfString,hp0,hp1,polynomialOfPowers,
      RawData.generatorCount,generator,map_mul,map_add,pow_succ,mul_assoc] at hz
    have heq := (eq_neg_of_add_eq_zero_left hz).trans (hneg _)
    simpa [mulAt,dataH0,B,atom,h0Six,h0Sq,h5Sq,generator,h0,RawData.generatorCount,
      pow_succ,mul_assoc,map_mul] using heq
  have ht : I.interpretation.sphere 9 71 (mulAt dataH0 B) = I.interpretation.basis .sphere 9 71 0 := by
    rw [hrel]
    exact ht0
  have h180 : HasDifferential E 2 (7,70) (9,71)
      (I.interpretation.basis .sphere 7 70 2) (I.interpretation.basis .sphere 9 71 0) := sphere_product_obstructions_h180 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,71,["0,7,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 167) (by rfl))
  change E.Page 2 (9,71) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 9 71 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 9 71 0 := he 0
  change HasNonzeroDifferential E 2 (7,70) (9,71) _ _
  rw [hs,ht]
  obtain ⟨hd,x,y,hx,hy,hxy⟩ := h180
  refine ⟨hd,x,y,hx,hy,hxy,?_⟩
  rw [←hy.eq_on_page_two,←he0]
  intro h
  have hh := congrArg (fun x => e x 0) h
  simp at hh

private theorem sphere_product_obstructions_hH5B
    (I : AdamsComputationTheorems D L G) : I.interpretation.sphere 10 134 (mulAt h5Sq B)=0  := by
  classical

  have hmem := relation_member4
  have hcode : "18,1,82,1" ∈ RawData.relations := hmem
  have hz := csv_relation_zero _ hcode
  have hs : "18,1,82,1".splitOn ";" = ["18,1,82,1"] := by
    simp +decide [String.splitOn,String.splitOnAux]
  have hc : (("18,1,82,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [18,1,82,1] := by
    have hsplit : "18,1,82,1".splitOn "," = ["18","1","82","1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    rw [hsplit]
    simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
      String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
  have hmul : generator ⟨18,by decide⟩ * generator ⟨82,by decide⟩ = 0 := by
    simpa [relationPolynomial,hs,monomialOfString,hc,polynomialOfPowers,
      RawData.generatorCount,generator,map_mul] using hz
  have h : mulAt h5Sq B = 0 := by
    apply Subtype.ext
    change (generator ⟨18,by decide⟩ * generator ⟨18,by decide⟩) * generator ⟨82,by decide⟩ = 0
    rw [mul_assoc,hmul,mul_zero]
  rw [h,map_zero]

private theorem sphere_product_obstructions_hH1Correction
    (I : AdamsComputationTheorems D L G) : I.interpretation.sphere 14 139 (mulAt dataH1 correction)=0  := by
  classical

  have hm0 := relation_member6
  have hm1 := relation_member7
  have hm2 := relation_member8
  have hm3 := relation_member9
  have hm4 := relation_member1
  have hm5 := relation_member2
  have hm6 := relation_member3
  have pq_neg_eq_self (x : KIP126.LinE2.E2) : -x=x := by
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
    change -(projection p)=projection p
    rw [←map_neg]
    exact congrArg projection (CharTwo.neg_eq p)
  have pq_relation1 (hc : "2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1" ∈ RawData.relations) :
      generator ⟨2,by decide⟩*(generator ⟨18,by decide⟩*generator ⟨188,by decide⟩) = generator ⟨0,by decide⟩*generator ⟨426,by decide⟩+generator ⟨0,by decide⟩^2*(generator ⟨69,by decide⟩*generator ⟨89,by decide⟩) := by
    have hz := csv_relation_zero "2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1" hc
    have hs : "2,1,18,1,188,1;0,1,426,1;0,2,69,1,89,1".splitOn ";"=["2,1,18,1,188,1", "0,1,426,1", "0,2,69,1,89,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hp00 : "2,1,18,1,188,1"≠"" := by decide
    have hp0 : (("2,1,18,1,188,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[2, 1, 18, 1, 188, 1] := by
      have hs : "2,1,18,1,188,1".splitOn ","=["2", "1", "18", "1", "188", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hp10 : "0,1,426,1"≠"" := by decide
    have hp1 : (("0,1,426,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 1, 426, 1] := by
      have hs : "0,1,426,1".splitOn ","=["0", "1", "426", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hp20 : "0,2,69,1,89,1"≠"" := by decide
    have hp2 : (("0,2,69,1,89,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 2, 69, 1, 89, 1] := by
      have hs : "0,2,69,1,89,1".splitOn ","=["0", "2", "69", "1", "89", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hp00,hp1,hp10,hp2,hp20,polynomialOfPowers,RawData.generatorCount,
      map_add,map_mul,map_pow,generator] at hz
    exact (eq_neg_of_add_eq_zero_left hz).trans (pq_neg_eq_self _)
  have pq_relation2 (hc : "0,1,426,1;0,4,391,1" ∈ RawData.relations) :
      generator ⟨0,by decide⟩*generator ⟨426,by decide⟩=generator ⟨0,by decide⟩^4*generator ⟨391,by decide⟩ := by
    have hz := csv_relation_zero "0,1,426,1;0,4,391,1" hc
    have hs : "0,1,426,1;0,4,391,1".splitOn ";"=["0,1,426,1", "0,4,391,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hp00 : "0,1,426,1"≠"" := by decide
    have hp0 : (("0,1,426,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 1, 426, 1] := by
      have hs : "0,1,426,1".splitOn ","=["0", "1", "426", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hp10 : "0,4,391,1"≠"" := by decide
    have hp1 : (("0,4,391,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 4, 391, 1] := by
      have hs : "0,4,391,1".splitOn ","=["0", "4", "391", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hp00,hp1,hp10,polynomialOfPowers,RawData.generatorCount,
      map_add,map_mul,map_pow,generator] at hz
    exact (eq_neg_of_add_eq_zero_left hz).trans (pq_neg_eq_self _)
  have pq_relation3 (hc : "0,2,69,1,89,1;0,5,375,1" ∈ RawData.relations) :
      generator ⟨0,by decide⟩^2*(generator ⟨69,by decide⟩*generator ⟨89,by decide⟩)=generator ⟨0,by decide⟩^5*generator ⟨375,by decide⟩ := by
    have hz := csv_relation_zero "0,2,69,1,89,1;0,5,375,1" hc
    have hs : "0,2,69,1,89,1;0,5,375,1".splitOn ";"=["0,2,69,1,89,1", "0,5,375,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hp00 : "0,2,69,1,89,1"≠"" := by decide
    have hp0 : (("0,2,69,1,89,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 2, 69, 1, 89, 1] := by
      have hs : "0,2,69,1,89,1".splitOn ","=["0", "2", "69", "1", "89", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hp10 : "0,5,375,1"≠"" := by decide
    have hp1 : (("0,5,375,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 5, 375, 1] := by
      have hs : "0,5,375,1".splitOn ","=["0", "5", "375", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hp00,hp1,hp10,polynomialOfPowers,RawData.generatorCount,
      map_add,map_mul,map_pow,generator] at hz
    exact (eq_neg_of_add_eq_zero_left hz).trans (pq_neg_eq_self _)
  have corr_relation0 (hc : "2,1,239,1;1,1,251,1" ∈ RawData.relations) :
      (generator ⟨2,by decide⟩ * generator ⟨239,by decide⟩) = (generator ⟨1,by decide⟩ * generator ⟨251,by decide⟩) := by
    have hz := csv_relation_zero "2,1,239,1;1,1,251,1" hc
    have hs : "2,1,239,1;1,1,251,1".splitOn ";"=["2,1,239,1", "1,1,251,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hne0 : "2,1,239,1" ≠ "" := by decide
    have hp0 : (("2,1,239,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[2, 1, 239, 1] := by
      have split : "2,1,239,1".splitOn ","=["2", "1", "239", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hne1 : "1,1,251,1" ≠ "" := by decide
    have hp1 : (("1,1,251,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[1, 1, 251, 1] := by
      have split : "1,1,251,1".splitOn ","=["1", "1", "251", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hne0,hp1,hne1,polynomialOfPowers,RawData.generatorCount,map_add,map_mul,map_pow,generator] at hz
    simpa [mul_assoc,generator,RawData.generatorCount] using (eq_neg_of_add_eq_zero_left hz).trans (pq_neg_eq_self _)
  have corr_relation1 (hc : "9,1,239,1;0,1,18,1,188,1" ∈ RawData.relations) :
      (generator ⟨9,by decide⟩ * generator ⟨239,by decide⟩) = (generator ⟨0,by decide⟩ * generator ⟨18,by decide⟩ * generator ⟨188,by decide⟩) := by
    have hz := csv_relation_zero "9,1,239,1;0,1,18,1,188,1" hc
    have hs : "9,1,239,1;0,1,18,1,188,1".splitOn ";"=["9,1,239,1", "0,1,18,1,188,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hne0 : "9,1,239,1" ≠ "" := by decide
    have hp0 : (("9,1,239,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[9, 1, 239, 1] := by
      have split : "9,1,239,1".splitOn ","=["9", "1", "239", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    have hne1 : "0,1,18,1,188,1" ≠ "" := by decide
    have hp1 : (("0,1,18,1,188,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 1, 18, 1, 188, 1] := by
      have split : "0,1,18,1,188,1".splitOn ","=["0", "1", "18", "1", "188", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hne0,hp1,hne1,polynomialOfPowers,RawData.generatorCount,map_add,map_mul,map_pow,generator] at hz
    simpa [mul_assoc,generator,RawData.generatorCount] using (eq_neg_of_add_eq_zero_left hz).trans (pq_neg_eq_self _)
  have corr_relation2 (hc : "0,5,391,1" ∈ RawData.relations) :
      (generator ⟨0,by decide⟩^5 * generator ⟨391,by decide⟩) = 0 := by
    have hz := csv_relation_zero "0,5,391,1" hc
    have hs : "0,5,391,1".splitOn ";"=["0,5,391,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hne0 : "0,5,391,1" ≠ "" := by decide
    have hp0 : (("0,5,391,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 5, 391, 1] := by
      have split : "0,5,391,1".splitOn ","=["0", "5", "391", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hne0,polynomialOfPowers,RawData.generatorCount,map_add,map_mul,map_pow,generator] at hz
    simpa [mul_assoc,generator,RawData.generatorCount] using hz
  have corr_relation3 (hc : "0,6,375,1" ∈ RawData.relations) :
      (generator ⟨0,by decide⟩^6 * generator ⟨375,by decide⟩) = 0 := by
    have hz := csv_relation_zero "0,6,375,1" hc
    have hs : "0,6,375,1".splitOn ";"=["0,6,375,1"] := by
      simp +decide [String.splitOn,String.splitOnAux]
    have hne0 : "0,6,375,1" ≠ "" := by decide
    have hp0 : (("0,6,375,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0, 6, 375, 1] := by
      have split : "0,6,375,1".splitOn ","=["0", "6", "375", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [relationPolynomial,hs,monomialOfString,hp0,hne0,polynomialOfPowers,RawData.generatorCount,map_add,map_mul,map_pow,generator] at hz
    simpa [mul_assoc,generator,RawData.generatorCount] using hz
  have h : mulAt dataH1 correction=0 := by
    apply Subtype.ext
    let g (i : Fin RawData.generatorCount) := generator i
    change g ⟨1,by decide⟩ * (g ⟨9,by decide⟩ * g ⟨251,by decide⟩)=0
    have h0 := corr_relation0 hm0
    have h1 := corr_relation1 hm1
    have h2 := corr_relation2 hm2
    have h3 := corr_relation3 hm3
    have h4 := pq_relation1 hm4
    have h5 := pq_relation2 hm5
    have h6 := pq_relation3 hm6
    change g ⟨2,by decide⟩*g ⟨239,by decide⟩=g ⟨1,by decide⟩*g ⟨251,by decide⟩ at h0
    change g ⟨9,by decide⟩*g ⟨239,by decide⟩=g ⟨0,by decide⟩*g ⟨18,by decide⟩*g ⟨188,by decide⟩ at h1
    change g ⟨0,by decide⟩^5*g ⟨391,by decide⟩=0 at h2
    change g ⟨0,by decide⟩^6*g ⟨375,by decide⟩=0 at h3
    change g ⟨2,by decide⟩*(g ⟨18,by decide⟩*g ⟨188,by decide⟩)=g ⟨0,by decide⟩*g ⟨426,by decide⟩+g ⟨0,by decide⟩^2*(g ⟨69,by decide⟩*g ⟨89,by decide⟩) at h4
    change g ⟨0,by decide⟩*g ⟨426,by decide⟩=g ⟨0,by decide⟩^4*g ⟨391,by decide⟩ at h5
    change g ⟨0,by decide⟩^2*(g ⟨69,by decide⟩*g ⟨89,by decide⟩)=g ⟨0,by decide⟩^5*g ⟨375,by decide⟩ at h6
    calc
      _ = g ⟨9,by decide⟩*(g ⟨1,by decide⟩*g ⟨251,by decide⟩) := by ac_rfl
      _ = g ⟨9,by decide⟩*(g ⟨2,by decide⟩*g ⟨239,by decide⟩) := by rw [←h0]
      _ = g ⟨2,by decide⟩*(g ⟨9,by decide⟩*g ⟨239,by decide⟩) := by ac_rfl
      _ = g ⟨2,by decide⟩*(g ⟨0,by decide⟩*g ⟨18,by decide⟩*g ⟨188,by decide⟩) := by rw [h1]
      _ = g ⟨0,by decide⟩*(g ⟨2,by decide⟩*(g ⟨18,by decide⟩*g ⟨188,by decide⟩)) := by ac_rfl
      _ = g ⟨0,by decide⟩*(g ⟨0,by decide⟩*g ⟨426,by decide⟩+g ⟨0,by decide⟩^2*(g ⟨69,by decide⟩*g ⟨89,by decide⟩)) := by rw [h4]
      _ = g ⟨0,by decide⟩*(g ⟨0,by decide⟩^4*g ⟨391,by decide⟩+g ⟨0,by decide⟩^5*g ⟨375,by decide⟩) := by rw [h5,h6]
      _ = g ⟨0,by decide⟩^5*g ⟨391,by decide⟩+g ⟨0,by decide⟩^6*g ⟨375,by decide⟩ := by ring
      _ = 0 := by rw [h2,h3,add_zero]
  rw [h,map_zero]

private def h0_product_map : E2 H SphereSpectrum 13 138 →ₗ[ℤ] E2 H SphereSpectrum 14 139 where
  toFun := Sphere.Internal.product H M (s := 1) (t := 1) (s' := 13) (t' := 138)
    (Sphere.Internal.hi H M 0)
  map_add' := Sphere.Internal.product_add_right H M (s := 1) (t := 1) (s' := 13) (t' := 138) (Sphere.Internal.hi H M 0)
  map_smul' := by
    intro n a
    have hs := int_smul_eq_zsmul (ModuleCat.isModule (E2 H SphereSpectrum 13 138)) n a
    have ht := int_smul_eq_zsmul (ModuleCat.isModule (E2 H SphereSpectrum 14 139)) n
      (Sphere.Internal.product H M (s := 1) (t := 1) (s' := 13) (t' := 138) (Sphere.Internal.hi H M 0) a)
    exact (congrArg (Sphere.Internal.product H M (s := 1) (t := 1) (s' := 13) (t' := 138)
      (Sphere.Internal.hi H M 0)) hs).trans
        ((Sphere.Internal.product_zsmul_right H M (s := 1) (t := 1) (s' := 13) (t' := 138)
          (Sphere.Internal.hi H M 0) a n).trans ht.symm)


private theorem h0_product_map_apply (a : E2 H SphereSpectrum 13 138) :
    h0_product_map (H := H) (M := M) a = Sphere.Internal.product H M
      (s := 1) (t := 1) (s' := 13) (t' := 138) (Sphere.Internal.hi H M 0) a := rfl


attribute [local irreducible] h0_product_map

private theorem sphere_product_obstructions_hTnotH0
    (I : AdamsComputationTheorems D L G) : ¬ ∃ a : E2 H SphereSpectrum 13 138,
      Sphere.Internal.product H M (s := 1) (t := 1) (s' := 13) (t' := 138)
        (Sphere.Internal.hi H M 0) a = I.interpretation.sphere 14 139 T  := by
  classical

  have hc0 := relation_member10
  have hc1 := relation_member11
  have hc2 := relation_member8
  have hc3 := relation_member9
  classical
  let E := sequence D .sphere
  have rel0 : (generator ⟨0,by decide⟩)*(generator ⟨24,by decide⟩)=0 := h0_obstruction_rel0
  have rel1 : (generator ⟨0,by decide⟩)*(generator ⟨3,by decide⟩)*(generator ⟨335,by decide⟩)=(generator ⟨0,by decide⟩^2)*(generator ⟨425,by decide⟩) := h0_obstruction_rel1
  have rel2 : (generator ⟨0,by decide⟩^5)*(generator ⟨391,by decide⟩)=0 := h0_obstruction_rel2
  have rel3 : (generator ⟨0,by decide⟩^6)*(generator ⟨375,by decide⟩)=0 := h0_obstruction_rel3
  obtain ⟨e13_138,he13_138⟩ := I.basis ⟨.sphere, 13, 138, ["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 209) (by rfl))
  change E2 H SphereSpectrum 13 138 ≃ₗ[ℤ] (Fin 5 →₀ F2) at e13_138
  change ∀i : Fin 5, e13_138.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 138 i.val at he13_138
  obtain ⟨e14_139,he14_139⟩ := I.basis ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (i := 217) (by rfl))
  change E2 H SphereSpectrum 14 139 ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_139
  change ∀i : Fin 3, e14_139.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 139 i.val at he14_139
  have hcsv := I.monomials ⟨.sphere, 13, 138, ["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 209) (by rfl)) rfl
  choose z hz he using hcsv
  change Fin 5 → E2At 13 138 at z
  change ∀ i : Fin 5, I.interpretation.sphere 13 138 (z i) = I.interpretation.basis .sphere 13 138 i.val at he
  have mon0 : projection (monomialOfString "24,1,190,1") = (generator ⟨24,by decide⟩)*(generator ⟨190,by decide⟩) := h0_obstruction_mon0
  have zv0 : (z (0 : Fin 5)).val = (generator ⟨24,by decide⟩)*(generator ⟨190,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon0
  have mon1 : projection (monomialOfString "3,1,335,1") = (generator ⟨3,by decide⟩)*(generator ⟨335,by decide⟩) := h0_obstruction_mon1
  have zv1 : (z (1 : Fin 5)).val = (generator ⟨3,by decide⟩)*(generator ⟨335,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon1
  have mon2 : projection (monomialOfString "0,1,425,1") = (generator ⟨0,by decide⟩)*(generator ⟨425,by decide⟩) := h0_obstruction_mon2
  have zv2 : (z (2 : Fin 5)).val = (generator ⟨0,by decide⟩)*(generator ⟨425,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon2
  have mon3 : projection (monomialOfString "0,4,391,1") = (generator ⟨0,by decide⟩^4)*(generator ⟨391,by decide⟩) := h0_obstruction_mon3
  have zv3 : (z (3 : Fin 5)).val = (generator ⟨0,by decide⟩^4)*(generator ⟨391,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon3
  have mon4 : projection (monomialOfString "0,5,375,1") = (generator ⟨0,by decide⟩^5)*(generator ⟨375,by decide⟩) := h0_obstruction_mon4
  have zv4 : (z (4 : Fin 5)).val = (generator ⟨0,by decide⟩^5)*(generator ⟨375,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon4
  have monT : projection (monomialOfString "1,1,7,1,275,1") = (generator ⟨1,by decide⟩)*(generator ⟨7,by decide⟩)*(generator ⟨275,by decide⟩) := h0_obstruction_monT
  have targetCSV := I.monomials ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (i := 217) (by rfl)) rfl
  have labelT : I.interpretation.sphere 14 139 T = I.interpretation.basis .sphere 14 139 1 := by
    as_aux_lemma =>
      obtain ⟨y,hy,heq⟩ := targetCSV (1 : Fin 3)
      have hyT : T=y := by
        as_aux_lemma =>
          apply Subtype.ext
          rw [hy]
          change generator ⟨1,by decide⟩*(generator ⟨7,by decide⟩*generator ⟨275,by decide⟩)=projection (monomialOfString "1,1,7,1,275,1")
          rw [monT]
          exact (mul_assoc _ _ _).symm
      rw [hyT]
      exact heq
  let f := h0_product_map (H := H) (M := M)
  have hf (a : E2 H SphereSpectrum 13 138) : f a = Sphere.Internal.product H M
      (s := 1) (t := 1) (s' := 13) (t' := 138) (Sphere.Internal.hi H M 0) a := h0_product_map_apply a
  have hprod (i : Fin 5) : f (I.interpretation.basis .sphere 13 138 i.val) =
      I.interpretation.sphere 14 139 (mulAt (dataH0) (z i)) := by
    as_aux_lemma =>
      rw [←he i,hf,←I.distinguishedClasses.h0]
      exact (I.products ⟨1,1,13,138⟩ (by simp [Raw.products]) (dataH0) (z i)).symm
  obtain ⟨y2,hy2,hey2⟩ := targetCSV (2 : Fin 3)
  have monTarget2 : projection (monomialOfString "0,2,425,1") = (generator ⟨0,by decide⟩^2)*(generator ⟨425,by decide⟩) := h0_obstruction_monTarget2
  have mul0 : mulAt dataH0 (z (0 : Fin 5))=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨0,by decide⟩*(z (0 : Fin 5)).val=0
      rw [zv0,←mul_assoc,rel0,zero_mul]
  have mul1 : mulAt dataH0 (z (1 : Fin 5))=y2 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨0,by decide⟩*(z (1 : Fin 5)).val=y2.val
      rw [zv1,hy2]
      change _=projection (monomialOfString "0,2,425,1")
      rw [monTarget2]
      simpa only [mul_assoc] using rel1
  have mul2 : mulAt dataH0 (z (2 : Fin 5))=y2 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨0,by decide⟩*(z (2 : Fin 5)).val=y2.val
      rw [zv2,hy2]
      change _=projection (monomialOfString "0,2,425,1")
      rw [monTarget2]
      ring
  have mul3 : mulAt dataH0 (z (3 : Fin 5))=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨0,by decide⟩*(z (3 : Fin 5)).val=0
      rw [zv3]
      calc
        _=generator ⟨0,by decide⟩^5*generator ⟨391,by decide⟩ := by ring
        _=0 := rel2
  have mul4 : mulAt dataH0 (z (4 : Fin 5))=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨0,by decide⟩*(z (4 : Fin 5)).val=0
      rw [zv4]
      calc
        _=generator ⟨0,by decide⟩^6*generator ⟨375,by decide⟩ := by ring
        _=0 := rel3
  have target2coord : (e14_139 (I.interpretation.basis .sphere 14 139 2)) 1=0 := by
    as_aux_lemma =>
      rw [show I.interpretation.basis .sphere 14 139 2=e14_139.symm (Finsupp.single 2 1) from (he14_139 2).symm,
        LinearEquiv.apply_symm_apply]
      simp
  have basisCoord (i : Fin 5) : (e14_139 (f (e13_138.symm (Finsupp.single i 1)))) 1=0 := by
    as_aux_lemma =>
      rw [he13_138,hprod]
      fin_cases i
      · change (e14_139 (I.interpretation.sphere 14 139 (mulAt dataH0 (z (0 : Fin 5))))) 1=0
        rw [mul0]
        rw [map_zero,map_zero]
        rfl
      · change (e14_139 (I.interpretation.sphere 14 139 (mulAt dataH0 (z (1 : Fin 5))))) 1=0
        rw [mul1]
        rw [hey2]
        exact target2coord
      · change (e14_139 (I.interpretation.sphere 14 139 (mulAt dataH0 (z (2 : Fin 5))))) 1=0
        rw [mul2]
        rw [hey2]
        exact target2coord
      · change (e14_139 (I.interpretation.sphere 14 139 (mulAt dataH0 (z (3 : Fin 5))))) 1=0
        rw [mul3]
        rw [map_zero,map_zero]
        rfl
      · change (e14_139 (I.interpretation.sphere 14 139 (mulAt dataH0 (z (4 : Fin 5))))) 1=0
        rw [mul4]
        rw [map_zero,map_zero]
        rfl
  have allCoord (a : E2 H SphereSpectrum 13 138) : (e14_139 (f a)) 1=0 := by
    as_aux_lemma =>
      rw [finite_basis_expansion e13_138 a,map_sum,map_sum,Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hc : (e13_138 a) i=0
      · simp only [hc,ite_true,map_zero,Finsupp.zero_apply]
      · simpa only [hc,ite_false] using basisCoord i
  rintro ⟨a,ha⟩
  have hz := allCoord a
  rw [hf,ha,labelT] at hz
  rw [show I.interpretation.basis .sphere 14 139 1=e14_139.symm (Finsupp.single 1 1) from (he14_139 1).symm,
    LinearEquiv.apply_symm_apply,Finsupp.single_eq_same] at hz
  exact one_ne_zero hz

private def h2_product_map : E2 H SphereSpectrum 13 135 →ₗ[ℤ] E2 H SphereSpectrum 14 139 where
  toFun := Sphere.Internal.product H M (s := 1) (t := 4) (s' := 13) (t' := 135)
    (Sphere.Internal.hi H M 2)
  map_add' := Sphere.Internal.product_add_right H M (s := 1) (t := 4) (s' := 13) (t' := 135) (Sphere.Internal.hi H M 2)
  map_smul' := by
    intro n a
    have hs := int_smul_eq_zsmul (ModuleCat.isModule (E2 H SphereSpectrum 13 135)) n a
    have ht := int_smul_eq_zsmul (ModuleCat.isModule (E2 H SphereSpectrum 14 139)) n
      (Sphere.Internal.product H M (s := 1) (t := 4) (s' := 13) (t' := 135) (Sphere.Internal.hi H M 2) a)
    exact (congrArg (Sphere.Internal.product H M (s := 1) (t := 4) (s' := 13) (t' := 135)
      (Sphere.Internal.hi H M 2)) hs).trans
        ((Sphere.Internal.product_zsmul_right H M (s := 1) (t := 4) (s' := 13) (t' := 135)
          (Sphere.Internal.hi H M 2) a n).trans ht.symm)


private theorem h2_product_map_apply (a : E2 H SphereSpectrum 13 135) :
    h2_product_map (H := H) (M := M) a = Sphere.Internal.product H M
      (s := 1) (t := 4) (s' := 13) (t' := 135) (Sphere.Internal.hi H M 2) a := rfl


attribute [local irreducible] h2_product_map

private theorem sphere_product_obstructions_hTnotH2
    (I : AdamsComputationTheorems D L G) : ¬ ∃ a : E2 H SphereSpectrum 13 135,
      Sphere.Internal.product H M (s := 1) (t := 4) (s' := 13) (t' := 135)
        (Sphere.Internal.hi H M 2) a = I.interpretation.sphere 14 139 T  := by
  classical

  have hc0 := relation_member12
  have hc1 := relation_member0
  have hc2 := relation_member13
  classical
  let E := sequence D .sphere
  have rel0 : (generator ⟨2,by decide⟩)*(generator ⟨407,by decide⟩)=0 := h2_obstruction_rel0
  have rel1 : (generator ⟨2,by decide⟩)*(generator ⟨79,by decide⟩)=(generator ⟨0,by decide⟩)*(generator ⟨89,by decide⟩) := h2_obstruction_rel1
  have rel2 : (generator ⟨0,by decide⟩^3)*(generator ⟨89,by decide⟩)=0 := h2_obstruction_rel2
  obtain ⟨e13_135,he13_135⟩ := I.basis ⟨.sphere, 13, 135, ["407,1", "1,2,351,1", "0,2,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 206) (by rfl))
  change E2 H SphereSpectrum 13 135 ≃ₗ[ℤ] (Fin 3 →₀ F2) at e13_135
  change ∀i : Fin 3, e13_135.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 135 i.val at he13_135
  obtain ⟨e14_139,he14_139⟩ := I.basis ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (i := 217) (by rfl))
  change E2 H SphereSpectrum 14 139 ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_139
  change ∀i : Fin 3, e14_139.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 139 i.val at he14_139
  have hcsv := I.monomials ⟨.sphere, 13, 135, ["407,1", "1,2,351,1", "0,2,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 206) (by rfl)) rfl
  choose z hz he using hcsv
  change Fin 3 → E2At 13 135 at z
  change ∀ i : Fin 3, I.interpretation.sphere 13 135 (z i) = I.interpretation.basis .sphere 13 135 i.val at he
  have mon0 : projection (monomialOfString "407,1") = (generator ⟨407,by decide⟩) := h2_obstruction_mon0
  have zv0 : (z (0 : Fin 3)).val = (generator ⟨407,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon0
  have mon1 : projection (monomialOfString "1,2,351,1") = (generator ⟨1,by decide⟩^2)*(generator ⟨351,by decide⟩) := h2_obstruction_mon1
  have zv1 : (z (1 : Fin 3)).val = (generator ⟨1,by decide⟩^2)*(generator ⟨351,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon1
  have mon2 : projection (monomialOfString "0,2,69,1,79,1") = (generator ⟨0,by decide⟩^2)*(generator ⟨69,by decide⟩)*(generator ⟨79,by decide⟩) := h2_obstruction_mon2
  have zv2 : (z (2 : Fin 3)).val = (generator ⟨0,by decide⟩^2)*(generator ⟨69,by decide⟩)*(generator ⟨79,by decide⟩) := by
    as_aux_lemma =>
      rw [hz]
      exact mon2
  have monT : projection (monomialOfString "1,1,7,1,275,1") = (generator ⟨1,by decide⟩)*(generator ⟨7,by decide⟩)*(generator ⟨275,by decide⟩) := h2_obstruction_monT
  have targetCSV := I.monomials ⟨.sphere, 14, 139, ["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (i := 217) (by rfl)) rfl
  have labelT : I.interpretation.sphere 14 139 T = I.interpretation.basis .sphere 14 139 1 := by
    as_aux_lemma =>
      obtain ⟨y,hy,heq⟩ := targetCSV (1 : Fin 3)
      have hyT : T=y := by
        as_aux_lemma =>
          apply Subtype.ext
          rw [hy]
          change generator ⟨1,by decide⟩*(generator ⟨7,by decide⟩*generator ⟨275,by decide⟩)=projection (monomialOfString "1,1,7,1,275,1")
          rw [monT]
          exact (mul_assoc _ _ _).symm
      rw [hyT]
      exact heq
  let f := h2_product_map (H := H) (M := M)
  have hf (a : E2 H SphereSpectrum 13 135) : f a = Sphere.Internal.product H M
      (s := 1) (t := 4) (s' := 13) (t' := 135) (Sphere.Internal.hi H M 2) a := h2_product_map_apply a
  have hprod (i : Fin 3) : f (I.interpretation.basis .sphere 13 135 i.val) =
      I.interpretation.sphere 14 139 (mulAt (atom .h2) (z i)) := by
    as_aux_lemma =>
      rw [←he i,hf,←I.distinguishedClasses.h2]
      exact (I.products ⟨1,4,13,135⟩ (by simp [Raw.products]) (atom .h2) (z i)).symm
  have mul0 : mulAt (atom .h2) (z (0 : Fin 3))=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨2,by decide⟩*(z (0 : Fin 3)).val=0
      rw [zv0]
      exact rel0
  have mul1 : mulAt (atom .h2) (z (1 : Fin 3))=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨2,by decide⟩*(z (1 : Fin 3)).val=0
      rw [zv1]
      have h12 : generator ⟨1,by decide⟩*generator ⟨2,by decide⟩=0 := h1_mul_h2_eq_zero
      calc
        _=(generator ⟨1,by decide⟩*generator ⟨2,by decide⟩)*
          (generator ⟨1,by decide⟩*generator ⟨351,by decide⟩) := by ring
        _=0 := by rw [h12,zero_mul]
  have mul2 : mulAt (atom .h2) (z (2 : Fin 3))=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change generator ⟨2,by decide⟩*(z (2 : Fin 3)).val=0
      rw [zv2]
      calc
        _=generator ⟨0,by decide⟩^2*generator ⟨69,by decide⟩*
          (generator ⟨2,by decide⟩*generator ⟨79,by decide⟩) := by ring
        _=generator ⟨0,by decide⟩^2*generator ⟨69,by decide⟩*
          (generator ⟨0,by decide⟩*generator ⟨89,by decide⟩) := by rw [rel1]
        _=generator ⟨69,by decide⟩*(generator ⟨0,by decide⟩^3*generator ⟨89,by decide⟩) := by ring
        _=0 := by rw [rel2,mul_zero]
  have basisCoord (i : Fin 3) : (e14_139 (f (e13_135.symm (Finsupp.single i 1)))) 1=0 := by
    as_aux_lemma =>
      rw [he13_135,hprod]
      fin_cases i
      · change (e14_139 (I.interpretation.sphere 14 139 (mulAt (atom .h2) (z (0 : Fin 3))))) 1=0
        rw [mul0,map_zero,map_zero]
        rfl
      · change (e14_139 (I.interpretation.sphere 14 139 (mulAt (atom .h2) (z (1 : Fin 3))))) 1=0
        rw [mul1,map_zero,map_zero]
        rfl
      · change (e14_139 (I.interpretation.sphere 14 139 (mulAt (atom .h2) (z (2 : Fin 3))))) 1=0
        rw [mul2,map_zero,map_zero]
        rfl
  have allCoord (a : E2 H SphereSpectrum 13 135) : (e14_139 (f a)) 1=0 := by
    as_aux_lemma =>
      rw [finite_basis_expansion e13_135 a,map_sum,map_sum,Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hc : (e13_135 a) i=0
      · simp only [hc,ite_true,map_zero,Finsupp.zero_apply]
      · simpa only [hc,ite_false] using basisCoord i
  rintro ⟨a,ha⟩
  have hz := allCoord a
  rw [hf,ha,labelT] at hz
  rw [show I.interpretation.basis .sphere 14 139 1=e14_139.symm (Finsupp.single 1 1) from (he14_139 1).symm,
    LinearEquiv.apply_symm_apply,Finsupp.single_eq_same] at hz
  exact one_ne_zero hz

private theorem sphere_product_obstructions (I : AdamsComputationTheorems D L G) :
    (Derived.Differential I.interpretation 2 (mulAt h0Six dataH6) (mulAt dataH0 B)) ∧
    (I.interpretation.sphere 10 134 (mulAt h5Sq B)=0) ∧
    (I.interpretation.sphere 14 139 (mulAt dataH1 correction)=0) ∧
    (IsBoundaryBy (sequence D .sphere) 2 (12,137)
      (I.interpretation.sphere 12 137 (mulAt P (atom .h2)))) ∧
    (IsBoundaryBy (sequence D .sphere) 2 (13,138)
      (I.interpretation.sphere 13 138 (mulAt Q (atom .h2)))) ∧
    (¬ ∃ a : E2 H SphereSpectrum 13 138,
      Sphere.Internal.product H M (s := 1) (t := 1) (s' := 13) (t' := 138)
        (Sphere.Internal.hi H M 0) a = I.interpretation.sphere 14 139 T) ∧
    (¬ ∃ a : E2 H SphereSpectrum 13 135,
      Sphere.Internal.product H M (s := 1) (t := 4) (s' := 13) (t' := 135)
        (Sphere.Internal.hi H M 2) a = I.interpretation.sphere 14 139 T) := by
  classical
  have hD2H0six : Derived.Differential I.interpretation 2 (mulAt h0Six dataH6) (mulAt dataH0 B)  := sphere_product_obstructions_hD2H0six I
  have hH5B : I.interpretation.sphere 10 134 (mulAt h5Sq B)=0  := sphere_product_obstructions_hH5B I
  have hH1Correction : I.interpretation.sphere 14 139 (mulAt dataH1 correction)=0  := sphere_product_obstructions_hH1Correction I
  have p_h2_boundary : IsBoundaryBy (sequence D .sphere) 2 (12,137)
      (I.interpretation.sphere 12 137 (mulAt P (atom .h2))) :=
    pq_p_boundary I relation_member0
  have q_h2_boundary : IsBoundaryBy (sequence D .sphere) 2 (13,138)
      (I.interpretation.sphere 13 138 (mulAt Q (atom .h2))) :=
    pq_q_boundary I relation_member1 relation_member2 relation_member3
  have hTnotH0 : ¬ ∃ a : E2 H SphereSpectrum 13 138,
      Sphere.Internal.product H M (s := 1) (t := 1) (s' := 13) (t' := 138)
        (Sphere.Internal.hi H M 0) a = I.interpretation.sphere 14 139 T  := sphere_product_obstructions_hTnotH0 I
  have hTnotH2 : ¬ ∃ a : E2 H SphereSpectrum 13 135,
      Sphere.Internal.product H M (s := 1) (t := 4) (s' := 13) (t' := 135)
        (Sphere.Internal.hi H M 2) a = I.interpretation.sphere 14 139 T  := sphere_product_obstructions_hTnotH2 I
  exact ⟨hD2H0six, hH5B, hH1Correction, p_h2_boundary, q_h2_boundary, hTnotH0, hTnotH2⟩


end SphereFactsProof

end
end KIP126.Computation.SphereAndCofiber
end
