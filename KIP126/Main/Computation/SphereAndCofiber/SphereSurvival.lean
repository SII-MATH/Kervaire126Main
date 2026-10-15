module

public import KIP126.Main.Computation.SphereAndCofiber.Bounds
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Legacy

/-! Private sphere survival and low-page vanishing calculations. -/

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

private theorem vx_empty_page (I : AdamsComputationTheorems D L G) (s t : ℕ)
    (h : (⟨.sphere,s,t,[]⟩ : Raw.Degree) ∈ Raw.degrees) (r : ℤ) (hr : 2≤r) :
    Subsingleton ((sequence D .sphere).Page r (s,t)) := by
  classical
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,s,t,[]⟩ h
  change (sequence D .sphere).Page 2 (s,t) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  have hzero : Subsingleton ((sequence D .sphere).Page 2 (s,t)) := e.injective.subsingleton
  exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r s t
    (by decide) hr hzero


private theorem v_incoming2_zero_h163 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (5,130) (7,131)
    ((I.interpretation.basis .sphere 5 130 0)) ((I.interpretation.basis .sphere 7 131 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,5,130,[0],7,131,[2],"S0_AdamsE2_ss",2435⟩ (by
    exact List.mem_of_getElem? (i := 163) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (5,130) (7,131) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 131 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem v_incoming2_zero_h182 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 5 (7,131) (12,135)
    ((I.interpretation.basis .sphere 7 131 1)) ((I.interpretation.basis .sphere 12 135 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,5,7,131,[1],12,135,[2],"S0_AdamsE2_ss",2490⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (7,131) (12,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem v_incoming2_zero_h183 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (7,131) (10,133)
    ((I.interpretation.basis .sphere 7 131 0)) ((I.interpretation.basis .sphere 10 133 0) + (I.interpretation.basis .sphere 10 133 1)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,7,131,[0],10,133,[0, 1],"S0_AdamsE2_ss",2491⟩ (by
    exact List.mem_of_getElem? (i := 183) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (7,131) (10,133) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0, 1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem v_incoming2_zero (I : AdamsComputationTheorems D L G) :
    (sequence D .sphere).d 2 (7,131)=0 := by
  classical
  let E := sequence D .sphere
  have h163 : HasDifferential E 2 (5,130) (7,131)
      ((I.interpretation.basis .sphere 5 130 0)) ((I.interpretation.basis .sphere 7 131 2)) := v_incoming2_zero_h163 I
  have h182 : HasDifferential E 5 (7,131) (12,135)
      ((I.interpretation.basis .sphere 7 131 1)) ((I.interpretation.basis .sphere 12 135 2)) := v_incoming2_zero_h182 I
  have h183 : HasDifferential E 3 (7,131) (10,133)
      ((I.interpretation.basis .sphere 7 131 0)) ((I.interpretation.basis .sphere 10 133 0) + (I.interpretation.basis .sphere 10 133 1)) := v_incoming2_zero_h183 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,7,131,["353,1", "69,1,75,1", "0,1,339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 148) (by rfl))
  change E.Page 2 (7,131) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 131 i.val at he
  have d0 : E.d 2 (7,131) (I.interpretation.basis .sphere 7 131 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h183
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d1 : E.d 2 (7,131) (I.interpretation.basis .sphere 7 131 1) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h182
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d2 : E.d 2 (7,131) (I.interpretation.basis .sphere 7 131 2)=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(5,130)) ⟨_,h163.eq_on_page_two.2⟩
  have hall (a : Fin 3 →₀ F2) : E.d 2 (7,131) (e.symm a)=0 := by
    induction a using Finsupp.induction with
    | zero => simp
    | @single_add i c a hi hc ih =>
      rw [map_add,map_add,ih,add_zero]
      fin_cases c
      · simp
      · change E.d 2 (7,131) (e.symm (Finsupp.single i 1))=0
        rw [he i]
        fin_cases i
        · exact d0
        · exact d1
        · exact d2
  ext x
  change E.d 2 (7,131) x=0
  simpa only [LinearEquiv.symm_apply_apply] using hall (e x)


private theorem v_incoming3_zero_h170 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 5 (6,130) (11,134)
    ((I.interpretation.basis .sphere 6 130 0)) ((I.interpretation.basis .sphere 11 134 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,5,6,130,[0],11,134,[2],"S0_AdamsE2_ss",2434⟩ (by
    exact List.mem_of_getElem? (i := 170) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (6,130) (11,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 134 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem v_incoming3_zero (I : AdamsComputationTheorems D L G) :
    (sequence D .sphere).d 3 (6,130)=0 := by
  classical
  let E := sequence D .sphere
  have h170 : HasDifferential E 5 (6,130) (11,134)
      ((I.interpretation.basis .sphere 6 130 0)) ((I.interpretation.basis .sphere 11 134 2)) := v_incoming3_zero_h170 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,6,130,["339,1"]⟩ (by
    exact List.mem_of_getElem? (i := 136) (by rfl))
  change E.Page 2 (6,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 6 130 i.val at he
  obtain ⟨_,aLate,_,haLate,_,_⟩ := h170
  obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) haLate
  have da : E.d 3 (6,130) a=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) ha ⟨aLate,haLate⟩
  ext z
  change E.d 3 (6,130) z=0
  let vv : Fin 1 → E.Page 3 (6,130) := fun _ => a
  have hv (i : Fin 1) : RepresentsOnPage E 3 (6,130) (e.symm (Finsupp.single i 1)) (vv i) := by
    rw [he i]
    fin_cases i
    exact ha
  obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e vv hv z
  simp only [Fin.sum_univ_succ] at hc
  change z=(if c 0=0 then 0 else a)+0 at hc
  rw [hc]
  by_cases h0 : c 0=0
  all_goals simp only [h0,ite_true,ite_false,map_zero,da,add_zero]


private theorem v_incoming_zero (I : AdamsComputationTheorems D L G) (r : ℤ) (hr : 2≤r) :
    (sequence D .sphere).d r ((9,132)-(sequence D .sphere).diffDeg r)=0 := by
  classical
  let E := sequence D .sphere
  by_cases hlate : 9<r
  · haveI : Subsingleton (E.Page r (9-r,132-(r-1))) :=
      adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r (9-r) (132-(r-1)) (by omega)
    change E.d r (9-r,132-(r-1))=0
    ext z
    rw [Subsingleton.elim z 0,map_zero]
    rfl
  · have hrhi : r≤9 := by omega
    interval_cases r
    · exact v_incoming2_zero I
    · exact v_incoming3_zero I
    · haveI : Subsingleton (E.Page 4 (5,129)) := vx_empty_page I 5 129 (by
        exact List.mem_of_getElem? (i := 125) (by rfl)) 4 (by decide)
      change E.d 4 (5,129)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 5 (4,128)) := vx_empty_page I 4 128 (by
        exact List.mem_of_getElem? (i := 117) (by rfl)) 5 (by decide)
      change E.d 5 (4,128)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 6 (3,127)) := vx_empty_page I 3 127 (by
        exact List.mem_of_getElem? (i := 106) (by rfl)) 6 (by decide)
      change E.d 6 (3,127)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 7 (2,126)) := vx_empty_page I 2 126 (by
        exact List.mem_of_getElem? (i := 98) (by rfl)) 7 (by decide)
      change E.d 7 (2,126)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 8 (1,125)) := vx_empty_page I 1 125 (by
        exact List.mem_of_getElem? (i := 88) (by rfl)) 8 (by decide)
      change E.d 8 (1,125)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 9 (0,124)) := vx_empty_page I 0 124 (by
        exact List.mem_of_getElem? (i := 75) (by rfl)) 9 (by decide)
      change E.d 9 (0,124)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl


private theorem v_never_hit (I : AdamsComputationTheorems D L G) :
    NeverHit (sequence D .sphere) (9,132) (I.interpretation.sphere 9 132 KIP126.Computation.Near126.V) := by
  classical
  let E := sequence D .sphere
  intro r hr q h y hy hyn z hd
  have hq : q=(9,132)-E.diffDeg r := eq_sub_iff_add_eq.mpr h
  subst q
  have heq : (E.d r ((9,132)-E.diffDeg r) ≫ eqToHom (congrArg (E.Page r) h)) z=0 := by
    rw [v_incoming_zero I r hr]
    simp only [zero_comp]
    rfl
  exact hyn (hd.symm.trans heq)


private theorem x_incoming_zero (I : AdamsComputationTheorems D L G) (r : ℤ) (hr : 2≤r) :
    (sequence D .sphere).d r ((8,130)-(sequence D .sphere).diffDeg r)=0 := by
  classical
  let E := sequence D .sphere
  by_cases hlate : 8<r
  · haveI : Subsingleton (E.Page r (8-r,130-(r-1))) :=
      adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r (8-r) (130-(r-1)) (by omega)
    change E.d r (8-r,130-(r-1))=0
    ext z
    rw [Subsingleton.elim z 0,map_zero]
    rfl
  · have hrhi : r≤8 := by omega
    interval_cases r
    · haveI : Subsingleton (E.Page 2 (6,129)) := vx_empty_page I 6 129 (by
        exact List.mem_of_getElem? (i := 135) (by rfl)) 2 (by decide)
      change E.d 2 (6,129)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 3 (5,128)) := vx_empty_page I 5 128 (by
        exact List.mem_of_getElem? (i := 124) (by rfl)) 3 (by decide)
      change E.d 3 (5,128)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 4 (4,127)) := vx_empty_page I 4 127 (by
        exact List.mem_of_getElem? (i := 116) (by rfl)) 4 (by decide)
      change E.d 4 (4,127)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 5 (3,126)) := vx_empty_page I 3 126 (by
        exact List.mem_of_getElem? (i := 105) (by rfl)) 5 (by decide)
      change E.d 5 (3,126)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 6 (2,125)) := vx_empty_page I 2 125 (by
        exact List.mem_of_getElem? (i := 97) (by rfl)) 6 (by decide)
      change E.d 6 (2,125)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 7 (1,124)) := vx_empty_page I 1 124 (by
        exact List.mem_of_getElem? (i := 87) (by rfl)) 7 (by decide)
      change E.d 7 (1,124)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl
    · haveI : Subsingleton (E.Page 8 (0,123)) := vx_empty_page I 0 123 (by
        exact List.mem_of_getElem? (i := 74) (by rfl)) 8 (by decide)
      change E.d 8 (0,123)=0
      ext z
      rw [Subsingleton.elim z 0,map_zero]
      rfl


private theorem x_never_hit (I : AdamsComputationTheorems D L G) :
    NeverHit (sequence D .sphere) (8,130) (I.interpretation.sphere 8 130 X) := by
  classical
  let E := sequence D .sphere
  intro r hr q h y hy hyn z hd
  have hq : q=(8,130)-E.diffDeg r := eq_sub_iff_add_eq.mpr h
  subst q
  have heq : (E.d r ((8,130)-E.diffDeg r) ≫ eqToHom (congrArg (E.Page r) h)) z=0 := by
    rw [x_incoming_zero I r hr]
    simp only [zero_comp]
    rfl
  exact hyn (hd.symm.trans heq)


private theorem vx_v_first (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 9 132 (atom .x_123_9) = I.interpretation.basis .sphere 9 132 0 := by
  classical
  have hc := I.monomials (⟨.sphere,9,132,["366,1", "0,1,352,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 171) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (0:Fin 2)
  have heq : (atom .x_123_9)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨366,by decide⟩ = projection (monomialOfString "366,1")
    have hs : "366,1" ≠ "" := by decide
    have hp : (("366,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [366, 1] := by
      have split : "366,1".splitOn "," = ["366", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem vx_v_second (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 9 132 (mulAt dataH0 (atom .x_123_8)) = I.interpretation.basis .sphere 9 132 1 := by
  classical
  have hc := I.monomials (⟨.sphere,9,132,["366,1", "0,1,352,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 171) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (1:Fin 2)
  have heq : (mulAt dataH0 (atom .x_123_8))=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨0,by decide⟩ * generator ⟨352,by decide⟩ = projection (monomialOfString "0,1,352,1")
    have hs : "0,1,352,1" ≠ "" := by decide
    have hp : (("0,1,352,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 1, 352, 1] := by
      have split : "0,1,352,1".splitOn "," = ["0", "1", "352", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem vx_x_label (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 8 130 (X) = I.interpretation.basis .sphere 8 130 0 := by
  classical
  have hc := I.monomials (⟨.sphere,8,130,["1,1,323,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 158) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
  have heq : (X)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨1,by decide⟩ * generator ⟨323,by decide⟩ = projection (monomialOfString "1,1,323,1")
    have hs : "1,1,323,1" ≠ "" := by decide
    have hp : (("1,1,323,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1, 1, 323, 1] := by
      have split : "1,1,323,1".splitOn "," = ["1", "1", "323", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem v_survives (I : AdamsComputationTheorems D L G) :
    SurvivesTo (sequence D .sphere) 12 (9,132) (I.interpretation.sphere 9 132 KIP126.Computation.Near126.V) := by
  classical
  let E := sequence D .sphere
  have hreach : ReachesPage E 12 (9,132) (I.interpretation.basis .sphere 9 132 0 + I.interpretation.basis .sphere 9 132 1) := by
    have hh := I.adamsStatements ⟨.sphere,.reaches,12,9,132,[0, 1],9,132,[],"S0_AdamsE2_ss",2569⟩ (by
      exact List.mem_of_getElem? (i := 219) (by rfl))
    dsimp only [AdamsStatement] at hh
    obtain ⟨x,hx,hh⟩ := hh
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0, 1]=true := rfl
    simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hh
    exact hh
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,132,["366,1", "0,1,352,1"]⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  change E.Page 2 (9,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 9 132 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1)=I.interpretation.basis .sphere 9 132 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1)=I.interpretation.basis .sphere 9 132 1 := he 1
  have hn : (I.interpretation.basis .sphere 9 132 0 + I.interpretation.basis .sphere 9 132 1)≠0 := by
    intro hh
    have hc := congrArg (fun y => e y 0) hh
    simp only [map_add,map_zero,←he0,←he1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hc
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hc
  have hlabel : I.interpretation.sphere 9 132 KIP126.Computation.Near126.V=I.interpretation.basis .sphere 9 132 0+I.interpretation.basis .sphere 9 132 1 := by
    change I.interpretation.sphere 9 132 (atom .x_123_9+mulAt dataH0 (atom .x_123_8))=_
    rw [map_add,vx_v_first I,vx_v_second I]
  rw [hlabel]
  obtain ⟨y,hy⟩ := hreach
  exact ⟨y,hy,vx_nonzero_no_incoming (by change (2:ℤ)≤2; omega) (v_incoming_zero I) hy hn⟩


private theorem x_survives (I : AdamsComputationTheorems D L G) :
    SurvivesTo (sequence D .sphere) 6 (8,130) (I.interpretation.sphere 8 130 X) := by
  classical
  let E := sequence D .sphere
  have hreach : ReachesPage E 6 (8,130) (I.interpretation.basis .sphere 8 130 0) := by
    have hh := I.adamsStatements ⟨.sphere,.reaches,6,8,130,[0],8,130,[],"S0_AdamsE2_ss",2433⟩ (by
      exact List.mem_of_getElem? (i := 197) (by rfl))
    dsimp only [AdamsStatement] at hh
    obtain ⟨x,hx,hh⟩ := hh
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 130 [0]=true := rfl
    simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hh
    exact hh
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,8,130,["1,1,323,1"]⟩ (by
    exact List.mem_of_getElem? (i := 158) (by rfl))
  change E.Page 2 (8,130) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 8 130 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1)=I.interpretation.basis .sphere 8 130 0 := he 0
  have hn : (I.interpretation.basis .sphere 8 130 0)≠0 := by
    intro hh
    have hc := congrArg (fun y => e y 0) hh
    simp only [map_zero,←he0,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hc
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hc
  rw [vx_x_label I]
  obtain ⟨y,hy⟩ := hreach
  exact ⟨y,hy,vx_nonzero_no_incoming (by change (2:ℤ)≤2; omega) (x_incoming_zero I) hy hn⟩


private theorem y_incoming2_zero_h190 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (7,134) (9,135)
    ((I.interpretation.basis .sphere 7 134 1)) ((I.interpretation.basis .sphere 9 135 4)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,7,134,[1],9,135,[4],"S0_AdamsE2_ss",2709⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (7,134) (9,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming2_zero_h191 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (7,134) (9,135)
    ((I.interpretation.basis .sphere 7 134 4)) ((I.interpretation.basis .sphere 9 135 5)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,7,134,[4],9,135,[5],"S0_AdamsE2_ss",2710⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (7,134) (9,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [5] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming2_zero_h231 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    ((I.interpretation.basis .sphere 9 135 2)) ((I.interpretation.basis .sphere 13 138 0)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,9,135,[2],13,138,[0],"S0_AdamsE2_ss",2790⟩ (by
    exact List.mem_of_getElem? (i := 231) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (9,135) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming2_zero_h232 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    ((I.interpretation.basis .sphere 9 135 1)) ((I.interpretation.basis .sphere 13 138 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,9,135,[1],13,138,[2],"S0_AdamsE2_ss",2791⟩ (by
    exact List.mem_of_getElem? (i := 232) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (9,135) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming2_zero_h233 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    ((I.interpretation.basis .sphere 9 135 0)) ((I.interpretation.basis .sphere 12 137 3) + (I.interpretation.basis .sphere 12 137 4)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,135,[0],12,137,[3, 4],"S0_AdamsE2_ss",2792⟩ (by
    exact List.mem_of_getElem? (i := 233) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,135) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming2_zero_h234 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    ((I.interpretation.basis .sphere 9 135 3)) ((I.interpretation.basis .sphere 12 137 3)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,135,[3],12,137,[3],"S0_AdamsE2_ss",2793⟩ (by
    exact List.mem_of_getElem? (i := 234) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,135) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming2_zero (I : AdamsComputationTheorems D L G) : (sequence D .sphere).d 2 (9,135)=0 := by
  classical
  let E := sequence D .sphere
  have h190 : HasDifferential E 2 (7,134) (9,135)
      ((I.interpretation.basis .sphere 7 134 1)) ((I.interpretation.basis .sphere 9 135 4)) := y_incoming2_zero_h190 I
  have h191 : HasDifferential E 2 (7,134) (9,135)
      ((I.interpretation.basis .sphere 7 134 4)) ((I.interpretation.basis .sphere 9 135 5)) := y_incoming2_zero_h191 I
  have h231 : HasDifferential E 4 (9,135) (13,138)
      ((I.interpretation.basis .sphere 9 135 2)) ((I.interpretation.basis .sphere 13 138 0)) := y_incoming2_zero_h231 I
  have h232 : HasDifferential E 4 (9,135) (13,138)
      ((I.interpretation.basis .sphere 9 135 1)) ((I.interpretation.basis .sphere 13 138 2)) := y_incoming2_zero_h232 I
  have h233 : HasDifferential E 3 (9,135) (12,137)
      ((I.interpretation.basis .sphere 9 135 0)) ((I.interpretation.basis .sphere 12 137 3) + (I.interpretation.basis .sphere 12 137 4)) := y_incoming2_zero_h233 I
  have h234 : HasDifferential E 3 (9,135) (12,137)
      ((I.interpretation.basis .sphere 9 135 3)) ((I.interpretation.basis .sphere 12 137 3)) := y_incoming2_zero_h234 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,135,["414,1", "1,1,376,1", "1,1,375,1", "0,1,394,1", "0,1,392,1", "0,7,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 174) (by rfl))
  change E.Page 2 (9,135) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 9 135 i.val at he
  have d0 : E.d 2 (9,135) (I.interpretation.basis .sphere 9 135 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h233
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d1 : E.d 2 (9,135) (I.interpretation.basis .sphere 9 135 1) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h232
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d2 : E.d 2 (9,135) (I.interpretation.basis .sphere 9 135 2) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h231
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d3 : E.d 2 (9,135) (I.interpretation.basis .sphere 9 135 3) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h234
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d4 : E.d 2 (9,135) (I.interpretation.basis .sphere 9 135 4)=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(7,134)) ⟨_,h190.eq_on_page_two.2⟩
  have d5 : E.d 2 (9,135) (I.interpretation.basis .sphere 9 135 5)=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(7,134)) ⟨_,h191.eq_on_page_two.2⟩
  have hall (a : Fin 6 →₀ F2) : E.d 2 (9,135) (e.symm a)=0 := by
    induction a using Finsupp.induction with
    | zero => simp
    | @single_add i c a hi hc ih =>
      rw [map_add,map_add,ih,add_zero]
      fin_cases c
      · simp
      · change E.d 2 (9,135) (e.symm (Finsupp.single i 1))=0
        rw [he i]
        fin_cases i
        · exact d0
        · exact d1
        · exact d2
        · exact d3
        · exact d4
        · exact d5
  ext x
  change E.d 2 (9,135) x=0
  simpa only [LinearEquiv.symm_apply_apply] using hall (e x)


private theorem y_incoming4_zero_h185 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (5,132) (7,133)
    ((I.interpretation.basis .sphere 5 132 0)) ((I.interpretation.basis .sphere 7 133 1)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,5,132,[0],7,133,[1],"S0_AdamsE2_ss",2631⟩ (by
    exact List.mem_of_getElem? (i := 185) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (5,132) (7,133) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 133 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming4_zero_h186 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 18 (7,133) (I.interpretation.basis .sphere 7 133 0) := by
  classical
  have hh := I.adamsStatements ⟨.sphere,.reaches,18,7,133,[0],7,133,[],"S0_AdamsE2_ss",2632⟩ (by
    exact List.mem_of_getElem? (i := 186) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 133 [0]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem y_incoming4_zero (I : AdamsComputationTheorems D L G) : (sequence D .sphere).d 4 (7,133)=0 := by
  classical
  let E := sequence D .sphere
  have h185 : HasDifferential E 2 (5,132) (7,133)
      ((I.interpretation.basis .sphere 5 132 0)) ((I.interpretation.basis .sphere 7 133 1)) := y_incoming4_zero_h185 I
  have h186 : ReachesPage E 18 (7,133) (I.interpretation.basis .sphere 7 133 0) := y_incoming4_zero_h186 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,7,133,["1,1,69,1,76,1", "0,5,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 150) (by rfl))
  change E.Page 2 (7,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 133 i.val at he
  obtain ⟨aLate,haLate⟩ := h186
  obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤18) haLate
  have da : E.d 4 (7,133) a=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<18) ha ⟨aLate,haLate⟩
  have hb : RepresentsOnPage E 4 (7,133) (I.interpretation.basis .sphere 7 133 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h185
  ext z
  change E.d 4 (7,133) z=0
  let vv : Fin 2 → E.Page 4 (7,133) := ![a,0]
  have hv (i : Fin 2) : RepresentsOnPage E 4 (7,133) (e.symm (Finsupp.single i 1)) (vv i) := by
    rw [he i]
    fin_cases i
    · exact ha
    · exact hb
  obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤4) e vv hv z
  simp only [Fin.sum_univ_succ] at hc
  change z=(if c 0=0 then 0 else a)+((if c 1=0 then 0 else 0)+0) at hc
  simp only [ite_self,add_zero] at hc
  rw [hc]
  by_cases h0 : c 0=0
  all_goals simp only [h0,ite_true,ite_false,map_zero,da]


private theorem y_incoming3_represented_h279 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (8,134) (11,136)
    ((I.interpretation.basis .sphere 8 134 3)) ((I.interpretation.basis .sphere 11 136 1)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,8,134,[3],11,136,[1],"S0_AdamsE2_ss",2850⟩ (by
    exact List.mem_of_getElem? (i := 279) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,134) (11,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming3_represented_h280 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (8,134) (11,136)
    ((I.interpretation.basis .sphere 8 134 2)) ((I.interpretation.basis .sphere 11 136 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,8,134,[2],11,136,[2],"S0_AdamsE2_ss",2851⟩ (by
    exact List.mem_of_getElem? (i := 280) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,134) (11,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming3_represented_h207 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,134) (10,135)
    ((I.interpretation.basis .sphere 8 134 1)) ((I.interpretation.basis .sphere 10 135 3)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2705⟩ (by
    exact List.mem_of_getElem? (i := 207) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,134) (10,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming3_represented_h202 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (6,133) (8,134)
    ((I.interpretation.basis .sphere 6 133 1)) ((I.interpretation.basis .sphere 8 134 5)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,6,133,[1],8,134,[5],"S0_AdamsE2_ss",2700⟩ (by
    exact List.mem_of_getElem? (i := 202) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (6,133) (8,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 8 134 [5] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem y_incoming3_represented_h203 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 17 (8,134) (I.interpretation.basis .sphere 8 134 4) := by
  classical
  have hh := I.adamsStatements ⟨.sphere,.reaches,17,8,134,[4],8,134,[],"S0_AdamsE2_ss",2701⟩ (by
    exact List.mem_of_getElem? (i := 203) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [4]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem y_incoming3_represented_h204 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 6 (8,134) (I.interpretation.basis .sphere 8 134 0 + I.interpretation.basis .sphere 8 134 3) := by
  classical
  have hh := I.adamsStatements ⟨.sphere,.reaches,6,8,134,[0, 3],8,134,[],"S0_AdamsE2_ss",2702⟩ (by
    exact List.mem_of_getElem? (i := 204) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [0, 3]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem y_incoming3_represented (I : AdamsComputationTheorems D L G) :
    ∀ z : (sequence D .sphere).Page 3 (8,134),
    ∃ x : (sequence D .sphere).Page 2 (11,136),
      RepresentsOnPage (sequence D .sphere) 3 (11,136) x ((sequence D .sphere).d 3 (8,134) z) ∧
      ∀ (e : (sequence D .sphere).Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2)),
      (∀ i : Fin 5, e.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 11 136 i.val) → e x 3=0 := by
  classical
  let E := sequence D .sphere
  have h279 : HasDifferential E 3 (8,134) (11,136)
      ((I.interpretation.basis .sphere 8 134 3)) ((I.interpretation.basis .sphere 11 136 1)) := y_incoming3_represented_h279 I
  have h280 : HasDifferential E 3 (8,134) (11,136)
      ((I.interpretation.basis .sphere 8 134 2)) ((I.interpretation.basis .sphere 11 136 2)) := y_incoming3_represented_h280 I
  have h207 : HasDifferential E 2 (8,134) (10,135)
      ((I.interpretation.basis .sphere 8 134 1)) ((I.interpretation.basis .sphere 10 135 3)) := y_incoming3_represented_h207 I
  have h202 : HasDifferential E 2 (6,133) (8,134)
      ((I.interpretation.basis .sphere 6 133 1)) ((I.interpretation.basis .sphere 8 134 5)) := y_incoming3_represented_h202 I
  have h203 : ReachesPage E 17 (8,134) (I.interpretation.basis .sphere 8 134 4) := y_incoming3_represented_h203 I
  have h204 : ReachesPage E 6 (8,134) (I.interpretation.basis .sphere 8 134 0 + I.interpretation.basis .sphere 8 134 3) := y_incoming3_represented_h204 I
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,8,134,["395,1", "394,1", "393,1", "392,1", "69,1,85,1", "0,6,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 162) (by rfl))
  change E.Page 2 (8,134) ≃ₗ[ℤ] (Fin 6 →₀ F2) at f
  change ∀ i : Fin 6, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 8 134 i.val at hf
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
  change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 135 i.val at hk
  have hf0 : f.symm (Finsupp.single (0:Fin 6) 1)=I.interpretation.basis .sphere 8 134 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 6) 1)=I.interpretation.basis .sphere 8 134 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 6) 1)=I.interpretation.basis .sphere 8 134 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 6) 1)=I.interpretation.basis .sphere 8 134 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 6) 1)=I.interpretation.basis .sphere 8 134 4 := hf 4
  have hf5 : f.symm (Finsupp.single (5:Fin 6) 1)=I.interpretation.basis .sphere 8 134 5 := hf 5
  have hk0 : k.symm (Finsupp.single (0:Fin 5) 1)=I.interpretation.basis .sphere 10 135 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 5) 1)=I.interpretation.basis .sphere 10 135 1 := hk 1
  have hk2 : k.symm (Finsupp.single (2:Fin 5) 1)=I.interpretation.basis .sphere 10 135 2 := hk 2
  have hk3 : k.symm (Finsupp.single (3:Fin 5) 1)=I.interpretation.basis .sphere 10 135 3 := hk 3
  have hk4 : k.symm (Finsupp.single (4:Fin 5) 1)=I.interpretation.basis .sphere 10 135 4 := hk 4
  have hsub {r : ℤ} {p : ℤ×ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  obtain ⟨_,a3,t1,ha3,ht1,da3⟩ := h279
  obtain ⟨_,a2,t2,ha2,ht2,da2⟩ := h280
  have da3' : E.d 3 (8,134) a3=t1 := da3
  have da2' : E.d 3 (8,134) a2=t2 := da2
  obtain ⟨aSumLate,hSumLate⟩ := h204
  obtain ⟨aSum,hSum⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤6) hSumLate
  have dSum : E.d 3 (8,134) aSum=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hSum ⟨aSumLate,hSumLate⟩
  let a0 := aSum-a3
  have ha0 : RepresentsOnPage E 3 (8,134) (I.interpretation.basis .sphere 8 134 0) a0 := by
    simpa only [add_sub_cancel_right] using hsub hSum ha3
  have da0 : E.d 3 (8,134) a0= -t1 := by
    change E.d 3 (8,134) (aSum-a3)= -t1
    rw [map_sub,dSum,da3',zero_sub]
  obtain ⟨a4Late,ha4Late⟩ := h203
  obtain ⟨a4,ha4⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤17) ha4Late
  have da4 : E.d 3 (8,134) a4=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<17) ha4 ⟨a4Late,ha4Late⟩
  have ha5 : RepresentsOnPage E 3 (8,134) (I.interpretation.basis .sphere 8 134 5) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h202
  have d1 : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 1)=I.interpretation.basis .sphere 10 135 3 := h207.eq_on_page_two.2
  have d0 : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 0)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      (middle_rep2 (by decide) ha0) ⟨_,ha0⟩
  have d2 : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      (middle_rep2 (by decide) ha2) ⟨_,ha2⟩
  have d3 : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 3)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      (middle_rep2 (by decide) ha3) ⟨_,ha3⟩
  have d4 : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 4)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      (middle_rep2 (by decide) ha4) ⟨_,ha4⟩
  have d5 : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 5)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      (middle_rep2 (by decide) ha5) ⟨_,ha5⟩
  intro z
  let A := E.ssData (8,134)
  haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨w,hw⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance z
  let x : E.Page 2 (8,134) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) w
  have hx : RepresentsOnPage E 3 (8,134) x z := ⟨by decide,w,rfl,hw⟩
  have dx : E.d 2 (8,134) x=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (middle_rep2 (by decide) hx) ⟨z,hx⟩
  let c : Fin 6 → F2 := f x
  have hcoef := congrArg f.symm (FinitePageCalculus.f2_expand (f x))
  simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
  change x=(if c 0=0 then 0 else f.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else f.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else f.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else f.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else f.symm (Finsupp.single 4 1)) + ((if c 5=0 then 0 else f.symm (Finsupp.single 5 1)) + 0))))) at hcoef
  simp only [hf0,hf1,hf2,hf3,hf4,hf5,add_zero] at hcoef
  have difif2 (c : F2) (a : E.Page 2 (8,134)) :
      E.d 2 (8,134) (if c=0 then 0 else a)=if c=0 then 0 else E.d 2 (8,134) a := by
    split_ifs <;> simp only [map_zero]
  have hd := congrArg (E.d 2 (8,134)) hcoef
  rw [dx] at hd
  simp only [map_add,difif2,d0,d1,d2,d3,d4,d5,ite_self,zero_add,add_zero] at hd
  have c1 : c 1=0 := by
    by_contra hc1
    simp only [hc1,ite_false] at hd
    have hh := congrArg (fun y=>k y 3) hd
    rw [←hk3,LinearEquiv.apply_symm_apply,map_zero] at hh
    norm_num [Finsupp.single_apply] at hh
  have hform : z=(if c 0=0 then 0 else a0)+((if c 2=0 then 0 else a2)+((if c 3=0 then 0 else a3)+(if c 4=0 then 0 else a4))) := by
    apply represents_unique hx
    rw [hcoef]
    simp only [c1,ite_true,zero_add]
    have hh := middle_add (middle_if (c 0) ha0) (middle_add (middle_if (c 2) ha2)
      (middle_add (middle_if (c 3) ha3) (middle_add (middle_if (c 4) ha4) (middle_if (c 5) ha5))))
    simpa only [ite_self,add_zero] using hh
  have difif3 (c : F2) (a : E.Page 3 (8,134)) :
      E.d 3 (8,134) (if c=0 then 0 else a)=if c=0 then 0 else E.d 3 (8,134) a := by
    split_ifs <;> simp only [map_zero]
  have hdform := congrArg (E.d 3 (8,134)) hform
  simp only [map_add,difif3,da0,da2',da3',da4,ite_self,add_zero] at hdform
  let out : E.Page 2 (11,136) := (if c 0=0 then 0 else -I.interpretation.basis .sphere 11 136 1)+
    ((if c 2=0 then 0 else I.interpretation.basis .sphere 11 136 2)+(if c 3=0 then 0 else I.interpretation.basis .sphere 11 136 1))
  have hn1 : RepresentsOnPage E 3 (11,136) (-I.interpretation.basis .sphere 11 136 1) (-t1) := by
    simpa only [zero_sub] using hsub (RepresentsOnPage.zero (by decide)) ht1
  refine ⟨out,?_,?_⟩
  · rw [hdform]
    exact middle_add (middle_if (c 0) hn1) (middle_add (middle_if (c 2) ht2) (middle_if (c 3) ht1))
  · intro e he
    have he1 : e.symm (Finsupp.single (1:Fin 5) 1)=I.interpretation.basis .sphere 11 136 1 := he 1
    have he2 : e.symm (Finsupp.single (2:Fin 5) 1)=I.interpretation.basis .sphere 11 136 2 := he 2
    by_cases h0 : c 0=0 <;> by_cases h2 : c 2=0 <;> by_cases h3 : c 3=0
    all_goals simp only [out,h0,h2,h3,ite_true,ite_false,map_add,map_neg,map_zero,←he1,←he2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.neg_apply,Finsupp.zero_apply]
    all_goals norm_num [Finsupp.single_apply,Fin.ext_iff]


private theorem y_raw_survives_five_h281 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 5 (11,136) (I.interpretation.basis .sphere 11 136 3) := by
  classical
  have hh := I.adamsStatements ⟨.sphere,.reaches,5,11,136,[3],11,136,[],"S0_AdamsE2_ss",2852⟩ (by
    exact List.mem_of_getElem? (i := 281) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [3]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem y_raw_survives_five (I : AdamsComputationTheorems D L G) :
    SurvivesTo (sequence D .sphere) 5 (11,136) (I.interpretation.basis .sphere 11 136 3) := by
  classical
  let E := sequence D .sphere
  have h281 : ReachesPage E 5 (11,136) (I.interpretation.basis .sphere 11 136 3) := y_raw_survives_five_h281 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,11,136,["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 192) (by rfl))
  change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 136 i.val at he
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1)=I.interpretation.basis .sphere 11 136 3 := he 3
  have hsub {r : ℤ} {p : ℤ×ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  have nonzero3 {x : E.Page 2 (11,136)} {a : E.Page 3 (11,136)}
      (hx : e x 3=1) (ha : RepresentsOnPage E 3 (11,136) x a) : a≠0 := by
    have hn : x≠0 := by
      intro hh
      rw [hh,map_zero,Finsupp.zero_apply] at hx
      exact zero_ne_one hx
    exact represents_next_nonzero_of_incoming_zero_at (E:=E) (r:=2) (p:=(11,136))
      (by change (2:ℤ)≤2; omega) (by decide) (y_incoming2_zero I) ha (middle_rep2 (by decide) ha) hn
  obtain ⟨y5,hy5⟩ := h281
  obtain ⟨y4,hy4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hy5
  have hn4 : y4≠0 := by
    intro hy40
    obtain ⟨_,z,hz2,hz4⟩ := hy4
    let A := E.ssData (11,136)
    let i := Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide : (1:WithTop ℕ)≤2))
    let y3 := A.pageπ 1 (i z)
    have hy3 : RepresentsOnPage E 3 (11,136) (I.interpretation.basis .sphere 11 136 3) y3 := by
      refine ⟨by decide,i z,?_,rfl⟩
      change (i ≫ Subobject.ofLE _ _ _ ≫ A.pageπ 0) z=_
      dsimp only [i]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
      exact hz2
    obtain ⟨u,hu⟩ := (next_projection_zero_iff_incoming E 3 (by change (2:ℤ)≤3; omega) (8,134) z).mp (hz4.trans hy40)
    change E.d 3 (8,134) u=y3 at hu
    obtain ⟨out,hout,hell⟩ := y_incoming3_represented I u
    have hcoord : e out 3=0 := hell e he
    rw [hu] at hout
    have hdiff : RepresentsOnPage E 3 (11,136) (I.interpretation.basis .sphere 11 136 3-out) 0 := by
      simpa only [sub_self] using hsub hy3 hout
    have hx : e (I.interpretation.basis .sphere 11 136 3-out) 3=1 := by
      rw [map_sub,Finsupp.sub_apply,←he3,LinearEquiv.apply_symm_apply,hcoord]
      norm_num [Finsupp.single_apply]
    exact nonzero3 hx hdiff rfl
  exact ⟨y5,hy5,represents_next_nonzero_of_incoming_zero_at (E:=E) (r:=4) (p:=(11,136))
    (by change (2:ℤ)≤4; omega) (by decide) (y_incoming4_zero I) hy5 hy4 hn4⟩


private theorem y_basis_label (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y=I.interpretation.basis .sphere 11 136 3 := by
  classical
  have hc := I.monomials (⟨.sphere,11,136,["69,1,89,1","1,1,389,1","1,1,388,1","0,2,391,1","0,3,375,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 192) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (3:Fin 5)
  have heq : KIP126.Computation.Near126.Y=z := by
    apply Subtype.ext
    rw [hz]
    change (generator ⟨0,by decide⟩ * generator ⟨0,by decide⟩) * generator ⟨391,by decide⟩ = projection (monomialOfString "0,2,391,1")
    have hs : "0,2,391,1" ≠ "" := by decide
    have hp : (("0,2,391,1".splitOn ",").map (fun n => n.toNat?.getD 0))=[0,2,391,1] := by
      have split : "0,2,391,1".splitOn ","=["0","2","391","1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he


private theorem y_survives_five (I : AdamsComputationTheorems D L G) :
    Derived.Survival I.interpretation 5 KIP126.Computation.Near126.Y := by
  classical
  unfold Derived.Survival
  rw [y_basis_label I]
  exact y_raw_survives_five I


private theorem y_not_multiple (I : AdamsComputationTheorems D L G) : ¬ ∃ a : E2 H SphereSpectrum 10 132,
    Sphere.Internal.product H M (s := 1) (t := 4) (s' := 10) (t' := 132)
      (Sphere.Internal.hi H M 2) a = I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y := by
  classical
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,132,[]⟩ (by
    exact List.mem_of_getElem? (i := 179) (by rfl))
  change (sequence D .sphere).Page 2 (10,132) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  haveI : Subsingleton (E2 H SphereSpectrum 10 132) := e.injective.subsingleton
  intro ⟨a,ha⟩
  have ha0 : a=0 := Subsingleton.elim _ _
  have hY : I.interpretation.sphere 11 136 KIP126.Computation.Near126.Y=0 := by
    rw [ha0] at ha
    simpa only [Sphere.Internal.product,map_zero] using ha.symm
  obtain ⟨y,hy,hyn⟩ := y_survives_five I
  rw [hY] at hy
  exact hyn (represents_unique hy (RepresentsOnPage.zero (by decide)))


private theorem sphere_basic_survival_hd2h6_h142 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (1,64) (3,65)
    (I.interpretation.basis .sphere 1 64 0) (I.interpretation.basis .sphere 3 65 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,1,64,[0],3,65,[0],"S0_AdamsE2_ss",401⟩ (by
    exact List.mem_of_getElem? (i := 142) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (1,64) (3,65) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 1 64 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 3 65 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_basic_survival_hd2h6 (I : AdamsComputationTheorems D L G) : Derived.Differential I.interpretation 2 dataH6 (mulAt dataH0 h5Sq) := by
  classical
  let E := sequence D .sphere
  have hs : I.interpretation.sphere 1 64 (dataH6) = I.interpretation.basis .sphere 1 64 0 := by
    have hc := I.monomials (⟨.sphere,1,64,["69,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 85) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
    have heq : (dataH6)=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨69,by decide⟩ = projection (monomialOfString "69,1")
      have hp : (("69,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [69, 1] := by
        have split : "69,1".splitOn "," = ["69", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "69,1"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have ht : I.interpretation.sphere 3 65 (mulAt dataH0 h5Sq) = I.interpretation.basis .sphere 3 65 0 := by
    have hc := I.monomials (⟨.sphere,3,65,["0,1,18,2"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 102) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
    have heq : (mulAt dataH0 h5Sq)=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨0,by decide⟩ * (generator ⟨18,by decide⟩*generator ⟨18,by decide⟩) = projection (monomialOfString "0,1,18,2")
      have hp : (("0,1,18,2".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 1, 18, 2] := by
        have split : "0,1,18,2".splitOn "," = ["0", "1", "18", "2"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "0,1,18,2"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have h142 : HasDifferential E 2 (1,64) (3,65)
      (I.interpretation.basis .sphere 1 64 0) (I.interpretation.basis .sphere 3 65 0) := sphere_basic_survival_hd2h6_h142 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,3,65,["0,1,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 102) (by rfl))
  change E.Page 2 (3,65) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 3 65 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 3 65 0 := he 0
  change HasNonzeroDifferential E 2 (1,64) (3,65) _ _
  rw [hs,ht]
  obtain ⟨hd,x,y,hx,hy,hxy⟩ := h142
  refine ⟨hd,x,y,hx,hy,hxy,?_⟩
  rw [←hy.eq_on_page_two,←he0]
  intro h
  have hh := congrArg (fun x => e x 0) h
  simp at hh

private theorem sphere_basic_survival_hd2x_h201 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,133) (10,134)
    (I.interpretation.basis .sphere 8 133 1) (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,133,[1],10,134,[2, 4],"S0_AdamsE2_ss",2630⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,133) (10,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_basic_survival_hd2x (I : AdamsComputationTheorems D L G) : Derived.Differential I.interpretation 2 (atom .x_125_8) (mulAt dataH1 KIP126.Computation.Near126.V + U) := by
  classical
  let E := sequence D .sphere
  have hs : I.interpretation.sphere 8 133 (atom .x_125_8) = I.interpretation.basis .sphere 8 133 1 := by
    have hc := I.monomials (⟨.sphere,8,133,["376,1", "375,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 161) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (1:Fin 2)
    have heq : (atom .x_125_8)=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨375,by decide⟩ = projection (monomialOfString "375,1")
      have hp : (("375,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [375, 1] := by
        have split : "375,1".splitOn "," = ["375", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "375,1"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have ht : I.interpretation.sphere 10 134 (mulAt dataH1 (atom .x_123_9)) = I.interpretation.basis .sphere 10 134 2 := by
    have hc := I.monomials (⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 181) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (2:Fin 5)
    have heq : (mulAt dataH1 (atom .x_123_9))=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨1,by decide⟩*generator ⟨366,by decide⟩ = projection (monomialOfString "1,1,366,1")
      have hp : (("1,1,366,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1, 1, 366, 1] := by
        have split : "1,1,366,1".splitOn "," = ["1", "1", "366", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "1,1,366,1"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have hu : I.interpretation.sphere 10 134 (U) = I.interpretation.basis .sphere 10 134 4 := by
    have hc := I.monomials (⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 181) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (4:Fin 5)
    have heq : (U)=z := by
      apply Subtype.ext
      rw [hz]
      change (generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*generator ⟨367,by decide⟩ = projection (monomialOfString "0,2,367,1")
      have hp : (("0,2,367,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 2, 367, 1] := by
        have split : "0,2,367,1".splitOn "," = ["0", "2", "367", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,show "0,2,367,1"≠"" by decide,if_false,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have hV : mulAt dataH1 KIP126.Computation.Near126.V = mulAt dataH1 (atom .x_123_9) := by
    apply Subtype.ext
    change h1*((atom .x_123_9).val+h0*(atom .x_123_8).val)=h1*(atom .x_123_9).val
    rw [mul_add,←mul_assoc,mul_comm h1 h0,h0_mul_h1_eq_zero,zero_mul,add_zero]
  have h201 : HasDifferential E 2 (8,133) (10,134)
      (I.interpretation.basis .sphere 8 133 1) (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) := sphere_basic_survival_hd2x_h201 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 134 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 10 134 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 10 134 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 10 134 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 10 134 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 10 134 4 := he 4
  change HasNonzeroDifferential E 2 (8,133) (10,134) _ _
  rw [hs,hV,map_add,ht,hu]
  obtain ⟨hd,x,y,hx,hy,hxy⟩ := h201
  refine ⟨hd,x,y,hx,hy,hxy,?_⟩
  rw [←hy.eq_on_page_two,←he2,←he4]
  intro h
  have hh := congrArg (fun x => e x 2) h
  simp at hh

private theorem sphere_basic_survival_hVX (I : AdamsComputationTheorems D L G) : Derived.Survival I.interpretation 12 KIP126.Computation.Near126.V ∧ Derived.NotHit I.interpretation KIP126.Computation.Near126.V ∧
  Derived.Survival I.interpretation 6 X ∧ Derived.NotHit I.interpretation X := by
  classical

  exact ⟨v_survives I,v_never_hit I,x_survives I,x_never_hit I⟩

private theorem sphere_basic_survival_hY (I : AdamsComputationTheorems D L G) : Derived.Survival I.interpretation 5 Y ∧
  (¬ ∃ a : E2 H SphereSpectrum 10 132,
    Sphere.Internal.product H M (s := 1) (t := 4) (s' := 10) (t' := 132)
      (Sphere.Internal.hi H M 2) a = I.interpretation.sphere 11 136 Y) := by
  classical

  exact ⟨y_survives_five I,y_not_multiple I⟩

private theorem sphere_basic_survival (I : AdamsComputationTheorems D L G) :
    (Derived.Differential I.interpretation 2 dataH6 (mulAt dataH0 h5Sq)) ∧
    (Derived.Differential I.interpretation 2 (atom .x_125_8) (mulAt dataH1 KIP126.Computation.Near126.V + U)) ∧
    (Derived.Survival I.interpretation 12 KIP126.Computation.Near126.V ∧ Derived.NotHit I.interpretation KIP126.Computation.Near126.V ∧
    Derived.Survival I.interpretation 6 X ∧ Derived.NotHit I.interpretation X) ∧
    (Derived.Survival I.interpretation 5 Y ∧
    (¬ ∃ a : E2 H SphereSpectrum 10 132,
      Sphere.Internal.product H M (s := 1) (t := 4) (s' := 10) (t' := 132)
        (Sphere.Internal.hi H M 2) a = I.interpretation.sphere 11 136 Y)) := by
  classical
  exact ⟨(sphere_basic_survival_hd2h6 I), (sphere_basic_survival_hd2x I), (sphere_basic_survival_hVX I), (sphere_basic_survival_hY I)⟩

private theorem stem125_af12_four_h260 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,136) (12,137)
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

private theorem stem125_af12_four_h234 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    ((I.interpretation.basis .sphere 9 135 3)) ((I.interpretation.basis .sphere 12 137 3)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,135,[3],12,137,[3],"S0_AdamsE2_ss",2793⟩ (by
    exact List.mem_of_getElem? (i := 234) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,135) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af12_four_h307 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    ((I.interpretation.basis .sphere 9 135 0) + (I.interpretation.basis .sphere 9 135 3)) ((I.interpretation.basis .sphere 12 137 4)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,135,[0, 3],12,137,[4],"S0_AdamsE2_ss",2920⟩ (by
    exact List.mem_of_getElem? (i := 307) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,135) (12,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [0, 3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 137 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af12_four_h308 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (12,137) (14,138)
    ((I.interpretation.basis .sphere 12 137 1)) ((I.interpretation.basis .sphere 14 138 4)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,137,[1],14,138,[4],"S0_AdamsE2_ss",2921⟩ (by
    exact List.mem_of_getElem? (i := 308) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,137) (14,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af12_four_h309 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (12,137) (14,138)
    ((I.interpretation.basis .sphere 12 137 0)) ((I.interpretation.basis .sphere 14 138 3)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,137,[0],14,138,[3],"S0_AdamsE2_ss",2922⟩ (by
    exact List.mem_of_getElem? (i := 309) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,137) (14,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 138 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af12_four (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (12,137)) := by
  classical
  let E := sequence D .sphere
  have h260 : HasDifferential E 2 (10,136) (12,137)
      ((I.interpretation.basis .sphere 10 136 0)) ((I.interpretation.basis .sphere 12 137 2)) := stem125_af12_four_h260 I
  have h234 : HasDifferential E 3 (9,135) (12,137)
      ((I.interpretation.basis .sphere 9 135 3)) ((I.interpretation.basis .sphere 12 137 3)) := stem125_af12_four_h234 I
  have h307 : HasDifferential E 3 (9,135) (12,137)
      ((I.interpretation.basis .sphere 9 135 0) + (I.interpretation.basis .sphere 9 135 3)) ((I.interpretation.basis .sphere 12 137 4)) := stem125_af12_four_h307 I
  have h308 : HasDifferential E 2 (12,137) (14,138)
      ((I.interpretation.basis .sphere 12 137 1)) ((I.interpretation.basis .sphere 14 138 4)) := stem125_af12_four_h308 I
  have h309 : HasDifferential E 2 (12,137) (14,138)
      ((I.interpretation.basis .sphere 12 137 0)) ((I.interpretation.basis .sphere 14 138 3)) := stem125_af12_four_h309 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,12,137,["426,1", "425,1", "0,1,69,1,89,1", "0,3,391,1", "0,4,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  change E.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 137 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,14,138,["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩ (by
    exact List.mem_of_getElem? (i := 216) (by rfl))
  change E.Page 2 (14,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 138 i.val at hf
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 12 137 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 12 137 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 12 137 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 12 137 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 12 137 4 := he 4
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 14 138 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 14 138 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 14 138 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 14 138 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 14 138 4 := hf 4
  have hz2 : RepresentsOnPage E 4 (12,137) (I.interpretation.basis .sphere 12 137 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h260
  have d2 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (middle_rep2 (by decide) hz2) ⟨0,hz2⟩
  have hz3 : RepresentsOnPage E 4 (12,137) (I.interpretation.basis .sphere 12 137 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h234
  have d3 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 3)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (middle_rep2 (by decide) hz3) ⟨0,hz3⟩
  have hz4 : RepresentsOnPage E 4 (12,137) (I.interpretation.basis .sphere 12 137 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h307
  have d4 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 4)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (middle_rep2 (by decide) hz4) ⟨0,hz4⟩
  have d0 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 0)=I.interpretation.basis .sphere 14 138 3 := h309.eq_on_page_two.2
  have d1 : E.d 2 (12,137) (I.interpretation.basis .sphere 12 137 1)=I.interpretation.basis .sphere 14 138 4 := h308.eq_on_page_two.2
  suffices hall : ∀ y : E.Page 4 (12,137), y=0 by
    exact ⟨fun x y => (hall x).trans (hall y).symm⟩
  intro y
  let A := E.ssData (12,137)
  haveI : Epi (A.pageπ 2) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 2)).mp inferInstance y
  let x : E.Page 2 (12,137) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
  have hx : RepresentsOnPage E 4 (12,137) x y := ⟨by decide,z,rfl,hz⟩
  have dx : E.d 2 (12,137) x=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (middle_rep2 (by decide) hx) ⟨y,hx⟩
  let c : Fin 5 → F2 := e x
  have hcoef := congrArg e.symm (FinitePageCalculus.f2_expand (e x))
  simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
  change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
  simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
  have hd := congrArg (E.d 2 (12,137)) hcoef
  rw [dx] at hd
  simp only [map_add,apply_ite,map_zero] at hd
  simp only [d0,d1,d2,d3,d4,ite_self,add_zero] at hd
  have c0 : c 0=0 := by
    by_contra h0
    simp only [h0,ite_false] at hd
    by_cases h1 : c 1=0
    all_goals simp only [h1,ite_true,ite_false] at hd
    all_goals have hh := congrArg (fun z => f z 3) hd
    all_goals simp only [map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,←hf3,←hf4,LinearEquiv.apply_symm_apply] at hh
    all_goals norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have c1 : c 1=0 := by
    by_contra h1
    simp only [c0,h1,ite_true,ite_false,zero_add] at hd
    have hh := congrArg (fun z => f z 4) hd
    simp only [map_zero,Finsupp.zero_apply,←hf4,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  apply represents_unique hx
  rw [hcoef]
  simp only [c0,c1,ite_true,zero_add]
  have hh := middle_add (middle_if (c 2) hz2) (middle_add (middle_if (c 3) hz3) (middle_if (c 4) hz4))
  simpa only [ite_self,zero_add] using hh


private theorem stem125_af13_five_h231 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    ((I.interpretation.basis .sphere 9 135 2)) ((I.interpretation.basis .sphere 13 138 0)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,9,135,[2],13,138,[0],"S0_AdamsE2_ss",2790⟩ (by
    exact List.mem_of_getElem? (i := 231) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (9,135) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af13_five_h232 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    ((I.interpretation.basis .sphere 9 135 1)) ((I.interpretation.basis .sphere 13 138 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,9,135,[1],13,138,[2],"S0_AdamsE2_ss",2791⟩ (by
    exact List.mem_of_getElem? (i := 232) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (9,135) (13,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 138 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af13_five_h288 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
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

private theorem stem125_af13_five_h289 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
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

private theorem stem125_af13_five_h329 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (13,138) (16,140)
    ((I.interpretation.basis .sphere 13 138 1)) ((I.interpretation.basis .sphere 16 140 1)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,13,138,[1],16,140,[1],"S0_AdamsE2_ss",3012⟩ (by
    exact List.mem_of_getElem? (i := 329) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (13,138) (16,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 140 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af13_five_h314 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (12,138) (14,139)
    ((I.interpretation.basis .sphere 12 138 1)) ((I.interpretation.basis .sphere 14 139 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,138,[1],14,139,[2],"S0_AdamsE2_ss",3017⟩ (by
    exact List.mem_of_getElem? (i := 314) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,138) (14,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 139 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af13_five_h343 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (14,139) (16,140)
    ((I.interpretation.basis .sphere 14 139 0)) ((I.interpretation.basis .sphere 16 140 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,14,139,[0],16,140,[2],"S0_AdamsE2_ss",3081⟩ (by
    exact List.mem_of_getElem? (i := 343) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,139) (16,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 140 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af13_five_h342 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (14,139) (I.interpretation.basis .sphere 14 139 1) := by
  classical
  have hh := I.adamsStatements ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
    exact List.mem_of_getElem? (i := 342) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem stem125_af13_five (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (13,138)) := by
  classical
  let E := sequence D .sphere
  have h231 : HasDifferential E 4 (9,135) (13,138)
      ((I.interpretation.basis .sphere 9 135 2)) ((I.interpretation.basis .sphere 13 138 0)) := stem125_af13_five_h231 I
  have h232 : HasDifferential E 4 (9,135) (13,138)
      ((I.interpretation.basis .sphere 9 135 1)) ((I.interpretation.basis .sphere 13 138 2)) := stem125_af13_five_h232 I
  have h288 : HasDifferential E 2 (11,137) (13,138)
      ((I.interpretation.basis .sphere 11 137 0)) ((I.interpretation.basis .sphere 13 138 3)) := stem125_af13_five_h288 I
  have h289 : HasDifferential E 2 (11,137) (13,138)
      ((I.interpretation.basis .sphere 11 137 3)) ((I.interpretation.basis .sphere 13 138 4)) := stem125_af13_five_h289 I
  have h329 : HasDifferential E 3 (13,138) (16,140)
      ((I.interpretation.basis .sphere 13 138 1)) ((I.interpretation.basis .sphere 16 140 1)) := stem125_af13_five_h329 I
  have h314 : HasDifferential E 2 (12,138) (14,139)
      ((I.interpretation.basis .sphere 12 138 1)) ((I.interpretation.basis .sphere 14 139 2)) := stem125_af13_five_h314 I
  have h343 : HasDifferential E 2 (14,139) (16,140)
      ((I.interpretation.basis .sphere 14 139 0)) ((I.interpretation.basis .sphere 16 140 2)) := stem125_af13_five_h343 I
  have h342 : ReachesPage E 1000 (14,139) (I.interpretation.basis .sphere 14 139 1) := stem125_af13_five_h342 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 209) (by rfl))
  change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 138 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,14,139,["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (i := 217) (by rfl))
  change E.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 139 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,16,140,["9,1,261,1", "1,1,438,1", "0,1,448,1", "0,2,440,1", "0,2,439,1"]⟩ (by
    exact List.mem_of_getElem? (i := 231) (by rfl))
  change E.Page 2 (16,140) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 140 i.val at hg
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 13 138 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 13 138 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 13 138 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 13 138 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 13 138 4 := he 4
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 14 139 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 14 139 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 14 139 2 := hf 2
  have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 16 140 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 16 140 1 := hg 1
  have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 16 140 2 := hg 2
  have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 16 140 3 := hg 3
  have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 16 140 4 := hg 4
  have df0 : E.d 2 (14,139) (I.interpretation.basis .sphere 14 139 0)=I.interpretation.basis .sphere 16 140 2 := h343.eq_on_page_two.2
  have df1 : E.d 2 (14,139) (I.interpretation.basis .sphere 14 139 1)=0 := by
    obtain ⟨x,hx⟩ := h342
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<1000)
      (middle_rep2 (by decide) hx) ⟨x,hx⟩
  have df2 : E.d 2 (14,139) (I.interpretation.basis .sphere 14 139 2)=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(12,138)) ⟨_,h314.eq_on_page_two.2⟩
  have incoming (x : E.Page 2 (14,139)) : g (E.d 2 (14,139) x) 1=0 := by
    have all (a : Fin 3 →₀ F2) : g (E.d 2 (14,139) (f.symm a)) 1=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hc ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (14,139) (f.symm (Finsupp.single i 1))) 1=0
          rw [hf]
          fin_cases i
          all_goals dsimp only
          all_goals simp only [df0,df1,df2,map_zero,Finsupp.zero_apply,←hg2,LinearEquiv.apply_symm_apply]
          all_goals norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using all (f x)
  obtain ⟨_,b1,t,hb1,ht,db1⟩ := h329
  have db1' : E.d 3 (13,138) b1=t := db1
  have tn : t≠0 := by
    intro ht0
    obtain ⟨_,z,hz,hzt⟩ := ht
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (14,139) z).mp (hzt.trans ht0)
    change (Subobject.ofLE _ _ ((E.ssData (16,140)).Z_anti bot_le) ≫ (E.ssData (16,140)).pageπ 0) z ∈ LinearMap.range (E.d 2 (14,139)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (16,140)).Z_anti bot_le) ≫ (E.ssData (16,140)).pageπ 0) z = I.interpretation.basis .sphere 16 140 1 at hz
    rw [hz] at hh
    obtain ⟨u,hu⟩ := hh
    have hh := incoming u
    rw [hu,←hg1,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  have hz0 : RepresentsOnPage E 5 (13,138) (I.interpretation.basis .sphere 13 138 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h231
  have hz2 : RepresentsOnPage E 5 (13,138) (I.interpretation.basis .sphere 13 138 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h232
  have hz3 : RepresentsOnPage E 5 (13,138) (I.interpretation.basis .sphere 13 138 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) h288
  have hz4 : RepresentsOnPage E 5 (13,138) (I.interpretation.basis .sphere 13 138 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) h289
  obtain ⟨_,_,b0late,_,hb0late,_⟩ := h231
  obtain ⟨b0,hb0⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hb0late
  have db0 : E.d 3 (13,138) b0=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) hb0 ⟨b0late,hb0late⟩
  obtain ⟨_,_,b2late,_,hb2late,_⟩ := h232
  obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hb2late
  have db2 : E.d 3 (13,138) b2=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) hb2 ⟨b2late,hb2late⟩
  have hb3 : RepresentsOnPage E 3 (13,138) (I.interpretation.basis .sphere 13 138 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h288
  have hb4 : RepresentsOnPage E 3 (13,138) (I.interpretation.basis .sphere 13 138 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h289
  suffices hall : ∀ y : E.Page 5 (13,138), y=0 by
    exact ⟨fun x y => (hall x).trans (hall y).symm⟩
  intro y
  let A := E.ssData (13,138)
  haveI : Epi (A.pageπ 3) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 3)).mp inferInstance y
  let x : E.Page 2 (13,138) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
  have hx : RepresentsOnPage E 5 (13,138) x y := ⟨by decide,z,rfl,hz⟩
  let c : Fin 5 → F2 := e x
  have hcoef := congrArg e.symm (FinitePageCalculus.f2_expand (e x))
  simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
  change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
  simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
  have hrep3 : RepresentsOnPage E 3 (13,138) x
      ((if c 0=0 then 0 else b0)+((if c 1=0 then 0 else b1)+(if c 2=0 then 0 else b2))) := by
    rw [hcoef]
    have hh := middle_add (middle_if (c 0) hb0) (middle_add (middle_if (c 1) hb1)
      (middle_add (middle_if (c 2) hb2) (middle_add (middle_if (c 3) hb3) (middle_if (c 4) hb4))))
    simpa only [ite_self,add_zero] using hh
  have dx3 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) hrep3 ⟨y,hx⟩
  have c1 : c 1=0 := by
    by_contra hc1
    apply tn
    simpa only [map_add,apply_ite,map_zero,db0,db1',db2,hc1,ite_false,ite_self,zero_add,add_zero] using dx3
  apply represents_unique hx
  rw [hcoef]
  simp only [c1,ite_true,zero_add]
  have hh := middle_add (middle_if (c 0) hz0) (middle_add (middle_if (c 2) hz2)
    (middle_add (middle_if (c 3) hz3) (middle_if (c 4) hz4)))
  simpa only [ite_self,zero_add] using hh


private theorem stem125_e2_low (I : AdamsComputationTheorems D L G) (s : ℕ) (hs : s≤4) :
    Subsingleton ((sequence D .sphere).Page 2 (s,(s:ℤ)+125)) := by
  classical
  let E := sequence D .sphere
  interval_cases s
  · change Subsingleton (E.Page 2 (0,125))
    obtain ⟨e,he⟩ := I.basis ⟨.sphere,0,125,[]⟩ (by
      exact List.mem_of_getElem? (i := 76) (by rfl))
    change E.Page 2 (0,125) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 0 125 i.val at he
    exact e.injective.subsingleton
  · change Subsingleton (E.Page 2 (1,126))
    obtain ⟨e,he⟩ := I.basis ⟨.sphere,1,126,[]⟩ (by
      exact List.mem_of_getElem? (i := 89) (by rfl))
    change E.Page 2 (1,126) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 1 126 i.val at he
    exact e.injective.subsingleton
  · change Subsingleton (E.Page 2 (2,127))
    obtain ⟨e,he⟩ := I.basis ⟨.sphere,2,127,[]⟩ (by
      exact List.mem_of_getElem? (i := 99) (by rfl))
    change E.Page 2 (2,127) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 2 127 i.val at he
    exact e.injective.subsingleton
  · change Subsingleton (E.Page 2 (3,128))
    obtain ⟨e,he⟩ := I.basis ⟨.sphere,3,128,[]⟩ (by
      exact List.mem_of_getElem? (i := 107) (by rfl))
    change E.Page 2 (3,128) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 3 128 i.val at he
    exact e.injective.subsingleton
  · change Subsingleton (E.Page 2 (4,129))
    obtain ⟨e,he⟩ := I.basis ⟨.sphere,4,129,[]⟩ (by
      exact List.mem_of_getElem? (i := 118) (by rfl))
    change E.Page 2 (4,129) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
    change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 4 129 i.val at he
    exact e.injective.subsingleton

private theorem sphere_low_page_vanishing_hMiddle125 (I : AdamsComputationTheorems D L G) : Subsingleton ((sequence D .sphere).Page 4 (12,137)) ∧
  Subsingleton ((sequence D .sphere).Page 5 (13,138)) := by
  classical

  exact ⟨stem125_af12_four I,stem125_af13_five I⟩

private theorem sphere_low_page_vanishing_hAF11_h171 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 0) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 4, 6, 131, [0], 10, 134, [0, 3], "S0_AdamsE2_ss", 2492⟩ (by
    exact List.mem_of_getElem? (i := 171) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h172 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 1) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 1 + I.interpretation.basis .sphere 10 134 3 + I.interpretation.basis .sphere 10 134 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 4, 6, 131, [1], 10, 134, [0, 1, 3, 4], "S0_AdamsE2_ss", 2493⟩ (by
    exact List.mem_of_getElem? (i := 172) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (6,131) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [0, 1, 3, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h201 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,133) (10,134) (I.interpretation.basis .sphere 8 133 1) (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 8, 133, [1], 10, 134, [2, 4], "S0_AdamsE2_ss", 2630⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,133) (10,134) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 134 [2, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h250 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 5 (10,134) (15,138) (I.interpretation.basis .sphere 10 134 3) (I.interpretation.basis .sphere 15 138 1) := by
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

private theorem sphere_low_page_vanishing_hAF11_h200 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (8,133) (11,135) (I.interpretation.basis .sphere 8 133 0) (I.interpretation.basis .sphere 11 135 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 8, 133, [0], 11, 135, [0], "S0_AdamsE2_ss", 2629⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,133) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 133 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h226 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,134) (12,136) (I.interpretation.basis .sphere 9 134 1) (I.interpretation.basis .sphere 12 136 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 9, 134, [1], 12, 136, [0], "S0_AdamsE2_ss", 2697⟩ (by
    exact List.mem_of_getElem? (i := 226) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,134) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h227 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135) (I.interpretation.basis .sphere 9 134 0) (I.interpretation.basis .sphere 11 135 3 + I.interpretation.basis .sphere 11 135 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 9, 134, [0], 11, 135, [3, 4], "S0_AdamsE2_ss", 2698⟩ (by
    exact List.mem_of_getElem? (i := 227) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h228 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135) (I.interpretation.basis .sphere 9 134 4) (I.interpretation.basis .sphere 11 135 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 9, 134, [4], 11, 135, [4], "S0_AdamsE2_ss", 2699⟩ (by
    exact List.mem_of_getElem? (i := 228) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h253 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136) (I.interpretation.basis .sphere 10 135 1) (I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 10, 135, [1], 12, 136, [1, 2], "S0_AdamsE2_ss", 2785⟩ (by
    exact List.mem_of_getElem? (i := 253) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h254 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136) (I.interpretation.basis .sphere 10 135 2) (I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 10, 135, [2], 12, 136, [3, 4], "S0_AdamsE2_ss", 2786⟩ (by
    exact List.mem_of_getElem? (i := 254) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h255 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136) (I.interpretation.basis .sphere 10 135 4) (I.interpretation.basis .sphere 12 136 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 10, 135, [4], 12, 136, [4], "S0_AdamsE2_ss", 2787⟩ (by
    exact List.mem_of_getElem? (i := 255) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h277 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (11,135) (15,138) (I.interpretation.basis .sphere 11 135 1 + I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 15 138 0) := by
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

private theorem sphere_low_page_vanishing_hAF11_h278 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (11,135) (13,136) (I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 13 136 2) := by
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

private theorem sphere_low_page_vanishing_hAF11_h304 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (12,136) (14,137) (I.interpretation.basis .sphere 12 136 2) (I.interpretation.basis .sphere 14 137 2) := by
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

private theorem sphere_low_page_vanishing_hAF11_h321 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (11,136) (13,137) (I.interpretation.basis .sphere 11 136 4) (I.interpretation.basis .sphere 13 137 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 11, 136, [4], 13, 137, [3], "S0_AdamsE2_ss", 2914⟩ (by
    exact List.mem_of_getElem? (i := 321) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (11,136) (13,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h322 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (10,135) (13,137) (I.interpretation.basis .sphere 10 135 0) (I.interpretation.basis .sphere 13 137 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 10, 135, [0], 13, 137, [0], "S0_AdamsE2_ss", 2915⟩ (by
    exact List.mem_of_getElem? (i := 322) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (10,135) (13,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem sphere_low_page_vanishing_hAF11_h323 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (13,137) (I.interpretation.basis .sphere 13 137 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .reaches, 1000, 13, 137, [1], 13, 137, [], "S0_AdamsE2_ss", 2916⟩ (by
    exact List.mem_of_getElem? (i := 323) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,h⟩ := hrow
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha
  rw [←ha] at h
  exact h

private theorem sphere_low_page_vanishing_hAF11_h324 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (13,137) (16,139) (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := by
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

private theorem sphere_low_page_vanishing_hAF11 (I : AdamsComputationTheorems D L G) : Subsingleton ((sequence D .sphere).Page 5 (11,135)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e10_134,he10_134⟩ := I.basis ⟨.sphere, 10, 134, ["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 181) (by rfl))
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e10_134
  change ∀i : Fin 5, e10_134.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 134 i.val at he10_134
  have he10_134_0 : e10_134.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 10 134 0 := he10_134 0
  have he10_134_1 : e10_134.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 10 134 1 := he10_134 1
  have he10_134_2 : e10_134.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 10 134 2 := he10_134 2
  have he10_134_3 : e10_134.symm (Finsupp.single 3 1) = I.interpretation.basis .sphere 10 134 3 := he10_134 3
  have he10_134_4 : e10_134.symm (Finsupp.single 4 1) = I.interpretation.basis .sphere 10 134 4 := he10_134 4
  obtain ⟨e11_135,he11_135⟩ := I.basis ⟨.sphere, 11, 135, ["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e11_135
  change ∀i : Fin 5, e11_135.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 135 i.val at he11_135
  have he11_135_0 : e11_135.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 11 135 0 := he11_135 0
  have he11_135_1 : e11_135.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 11 135 1 := he11_135 1
  have he11_135_2 : e11_135.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 11 135 2 := he11_135 2
  have he11_135_3 : e11_135.symm (Finsupp.single 3 1) = I.interpretation.basis .sphere 11 135 3 := he11_135 3
  have he11_135_4 : e11_135.symm (Finsupp.single 4 1) = I.interpretation.basis .sphere 11 135 4 := he11_135 4
  obtain ⟨e12_136,he12_136⟩ := I.basis ⟨.sphere, 12, 136, ["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e12_136
  change ∀i : Fin 5, e12_136.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 136 i.val at he12_136
  have he12_136_0 : e12_136.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 12 136 0 := he12_136 0
  have he12_136_1 : e12_136.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 12 136 1 := he12_136 1
  have he12_136_2 : e12_136.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 12 136 2 := he12_136 2
  have he12_136_3 : e12_136.symm (Finsupp.single 3 1) = I.interpretation.basis .sphere 12 136 3 := he12_136 3
  have he12_136_4 : e12_136.symm (Finsupp.single 4 1) = I.interpretation.basis .sphere 12 136 4 := he12_136 4
  obtain ⟨e13_137,he13_137⟩ := I.basis ⟨.sphere, 13, 137, ["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 208) (by rfl))
  change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e13_137
  change ∀i : Fin 4, e13_137.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 137 i.val at he13_137
  have he13_137_0 : e13_137.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 13 137 0 := he13_137 0
  have he13_137_1 : e13_137.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 13 137 1 := he13_137 1
  have he13_137_2 : e13_137.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 13 137 2 := he13_137 2
  have he13_137_3 : e13_137.symm (Finsupp.single 3 1) = I.interpretation.basis .sphere 13 137 3 := he13_137 3
  obtain ⟨e15_138,he15_138⟩ := I.basis ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e15_138
  change ∀i : Fin 3, e15_138.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 15 138 i.val at he15_138
  have he15_138_0 : e15_138.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 15 138 0 := he15_138 0
  have he15_138_1 : e15_138.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 15 138 1 := he15_138 1
  have he15_138_2 : e15_138.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 15 138 2 := he15_138 2
  obtain ⟨e13_136,he13_136⟩ := I.basis ⟨.sphere, 13, 136, ["418,1", "417,1", "0,2,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 207) (by rfl))
  change E.Page 2 (13,136) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e13_136
  change ∀i : Fin 3, e13_136.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 136 i.val at he13_136
  have he13_136_0 : e13_136.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 13 136 0 := he13_136 0
  have he13_136_1 : e13_136.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 13 136 1 := he13_136 1
  have he13_136_2 : e13_136.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 13 136 2 := he13_136 2
  obtain ⟨e14_137,he14_137⟩ := I.basis ⟨.sphere, 14, 137, ["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 215) (by rfl))
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_137
  change ∀i : Fin 3, e14_137.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 137 i.val at he14_137
  have he14_137_0 : e14_137.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 14 137 0 := he14_137 0
  have he14_137_1 : e14_137.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 14 137 1 := he14_137 1
  have he14_137_2 : e14_137.symm (Finsupp.single 2 1) = I.interpretation.basis .sphere 14 137 2 := he14_137 2
  have h171 : HasDifferential E 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 0) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 3) := sphere_low_page_vanishing_hAF11_h171 I
  have h172 : HasDifferential E 4 (6,131) (10,134) (I.interpretation.basis .sphere 6 131 1) (I.interpretation.basis .sphere 10 134 0 + I.interpretation.basis .sphere 10 134 1 + I.interpretation.basis .sphere 10 134 3 + I.interpretation.basis .sphere 10 134 4) := sphere_low_page_vanishing_hAF11_h172 I
  have h201 : HasDifferential E 2 (8,133) (10,134) (I.interpretation.basis .sphere 8 133 1) (I.interpretation.basis .sphere 10 134 2 + I.interpretation.basis .sphere 10 134 4) := sphere_low_page_vanishing_hAF11_h201 I
  have h250 : HasDifferential E 5 (10,134) (15,138) (I.interpretation.basis .sphere 10 134 3) (I.interpretation.basis .sphere 15 138 1) := sphere_low_page_vanishing_hAF11_h250 I
  have h200 : HasDifferential E 3 (8,133) (11,135) (I.interpretation.basis .sphere 8 133 0) (I.interpretation.basis .sphere 11 135 0) := sphere_low_page_vanishing_hAF11_h200 I
  have h226 : HasDifferential E 3 (9,134) (12,136) (I.interpretation.basis .sphere 9 134 1) (I.interpretation.basis .sphere 12 136 0) := sphere_low_page_vanishing_hAF11_h226 I
  have h227 : HasDifferential E 2 (9,134) (11,135) (I.interpretation.basis .sphere 9 134 0) (I.interpretation.basis .sphere 11 135 3 + I.interpretation.basis .sphere 11 135 4) := sphere_low_page_vanishing_hAF11_h227 I
  have h228 : HasDifferential E 2 (9,134) (11,135) (I.interpretation.basis .sphere 9 134 4) (I.interpretation.basis .sphere 11 135 4) := sphere_low_page_vanishing_hAF11_h228 I
  have h253 : HasDifferential E 2 (10,135) (12,136) (I.interpretation.basis .sphere 10 135 1) (I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) := sphere_low_page_vanishing_hAF11_h253 I
  have h254 : HasDifferential E 2 (10,135) (12,136) (I.interpretation.basis .sphere 10 135 2) (I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4) := sphere_low_page_vanishing_hAF11_h254 I
  have h255 : HasDifferential E 2 (10,135) (12,136) (I.interpretation.basis .sphere 10 135 4) (I.interpretation.basis .sphere 12 136 4) := sphere_low_page_vanishing_hAF11_h255 I
  have h277 : HasDifferential E 4 (11,135) (15,138) (I.interpretation.basis .sphere 11 135 1 + I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 15 138 0) := sphere_low_page_vanishing_hAF11_h277 I
  have h278 : HasDifferential E 2 (11,135) (13,136) (I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 13 136 2) := sphere_low_page_vanishing_hAF11_h278 I
  have h304 : HasDifferential E 2 (12,136) (14,137) (I.interpretation.basis .sphere 12 136 2) (I.interpretation.basis .sphere 14 137 2) := sphere_low_page_vanishing_hAF11_h304 I
  have h321 : HasDifferential E 2 (11,136) (13,137) (I.interpretation.basis .sphere 11 136 4) (I.interpretation.basis .sphere 13 137 3) := sphere_low_page_vanishing_hAF11_h321 I
  have h322 : HasDifferential E 3 (10,135) (13,137) (I.interpretation.basis .sphere 10 135 0) (I.interpretation.basis .sphere 13 137 0) := sphere_low_page_vanishing_hAF11_h322 I
  have h323 : ReachesPage E 1000 (13,137) (I.interpretation.basis .sphere 13 137 1) := sphere_low_page_vanishing_hAF11_h323 I
  have h324 : HasDifferential E 3 (13,137) (16,139) (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := sphere_low_page_vanishing_hAF11_h324 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
  have hsub {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  have lift_e2 {r : ℤ} (hr : 2 ≤ r) {p : ℤ × ℤ} (x : E.Page r p) :
      ∃ a : E.Page 2 p, RepresentsOnPage E r p a x := by
    exact page_has_representative hr x
  have f2_expand {N : ℕ} (f : Fin N →₀ F2) :
      f = ∑ i : Fin N, if f i=0 then 0 else Finsupp.single i 1 := by
    exact FinitePageCalculus.f2_expand f
  have rep_zero {r : ℤ} {p : ℤ × ℤ} {x : E.Page r p}
      (h : RepresentsOnPage E r p 0 x) : x=0 :=
    represents_unique h (RepresentsOnPage.zero h.1)
  have rep_double {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (hx : x+x=0) (ha : RepresentsOnPage E r p x a) : a+a=0 := by
    exact rep_zero (by simpa only [hx] using hadd ha ha)
  -- All four possible incoming d2 directions reach E3.
  have d2_13 : E.d 2 (13,137)=0 := by
    obtain ⟨_,x0,y0,hx0,hy0,_⟩ := h322
    obtain ⟨_,x2,y2,hx2,hy2,_⟩ := h324
    have h0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨y0,hy0⟩
    have h1 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<1000) (hrep2 _) h323
    have h2 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨x2,hx2⟩
    have h3 : E.d 2 (13,137) (I.interpretation.basis .sphere 13 137 3)=0 := by
      have hd := h321.eq_on_page_two.2
      change E.d 2 (11,136) _ = _ at hd
      rw [←hd]
      exact congrArg (fun f => f (I.interpretation.basis .sphere 11 136 4)) (E.d_comp_d 2 (11,136))
    have one (i : Fin 4) : E.d 2 (13,137) (e13_137.symm (Finsupp.single i 1))=0 := by
      rw [he13_137]
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    have all (f : Fin 4 →₀ F2) : E.d 2 (13,137) (e13_137.symm f)=0 := by
      induction f using Finsupp.induction with
      | zero => simp
      | @single_add i a f hi ha ih =>
        rw [map_add,map_add,ih,add_zero]
        fin_cases a
        · simp
        · exact one i
    ext x
    simpa only [LinearEquiv.symm_apply_apply,ModuleCat.hom_zero,LinearMap.zero_apply] using all (e13_137 x)
  have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (c : F2) (h : RepresentsOnPage E r p x a) :
      RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
    split
    · exact RepresentsOnPage.zero h.1
    · exact h
  -- The complete d2 kernel in degree (12,136) consists of the d3 target
  -- basis0 and three d2 boundaries; consequently its entire d3 map is zero.
  have d3_12 : E.d 3 (12,136)=0 := by
    obtain ⟨_,in0,a0,hin0,ha0,hda0⟩ := h226
    have hd0 : E.d 3 (12,136) a0=0 :=
      IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(9,134)) ⟨in0,hda0⟩
    have rz12 : RepresentsOnPage E 3 (12,136)
        (I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h253
    have rz34 : RepresentsOnPage E 3 (12,136)
        (I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h254
    have rz4 : RepresentsOnPage E 3 (12,136) (I.interpretation.basis .sphere 12 136 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h255
    have rz3 : RepresentsOnPage E 3 (12,136) (I.interpretation.basis .sphere 12 136 3) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using hsub rz34 rz4
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a0,ha0⟩
    have d12 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨0,rz12⟩
    have d3 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨0,rz3⟩
    have d4 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨0,rz4⟩
    have d2 := h304.eq_on_page_two.2
    change E.d 2 (12,136) (I.interpretation.basis .sphere 12 136 2) = I.interpretation.basis .sphere 14 137 2 at d2
    have tn : I.interpretation.basis .sphere 14 137 2 ≠ 0 := by
      rw [←he14_137_2]
      intro h
      have hh := congrArg e14_137 h
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 2) hh
      norm_num at hh'
    have d1 : E.d 2 (12,136) (I.interpretation.basis .sphere 12 136 1) = -I.interpretation.basis .sphere 14 137 2 := by
      simpa only [map_add,d2,eq_neg_iff_add_eq_zero] using d12
    ext x
    obtain ⟨a,ha⟩ := lift_e2 (by decide : (2:ℤ)≤3) x
    have da := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 a) ⟨x,ha⟩
    let c : Fin 5 → F2 := e12_136 a
    have hcoef := congrArg e12_136.symm (f2_expand (e12_136 a))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change a = (if c 0=0 then 0 else e12_136.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e12_136.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e12_136.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e12_136.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e12_136.symm (Finsupp.single 4 1)) + 0)))) at hcoef
    simp only [he12_136_0,he12_136_1,he12_136_2,he12_136_3,he12_136_4,add_zero] at hcoef
    have hc : (c 1=0) ↔ (c 2=0) := by
      have hd := congrArg (E.d 2 (12,136)) hcoef
      simp only [map_add,apply_ite,map_zero] at hd
      rw [da,d0,d1,d2,d3,d4] at hd
      simp only [ite_self,zero_add,add_zero] at hd
      constructor
      · intro h1
        by_contra h2
        simp only [h1,h2,ite_true,ite_false,zero_add] at hd
        exact tn hd.symm
      · intro h2
        by_contra h1
        simp only [h1,h2,ite_true,ite_false,add_zero] at hd
        exact tn (neg_eq_zero.mp hd.symm)
    have hacomb : a = (if c 0=0 then 0 else I.interpretation.basis .sphere 12 136 0) +
        (if c 1=0 then 0 else I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) +
        (if c 3=0 then 0 else I.interpretation.basis .sphere 12 136 3) +
        (if c 4=0 then 0 else I.interpretation.basis .sphere 12 136 4) := by
      rw [hcoef]
      by_cases h1 : c 1=0
      · have h2 := hc.mp h1
        simp only [h1,h2,ite_true,zero_add,add_zero]
        abel
      · have h2 := mt hc.mpr h1
        simp only [h1,h2,ite_false]
        abel
    have hx : x=(if c 0=0 then 0 else a0) := by
      apply represents_unique ha
      rw [hacomb]
      simpa only [ite_self,add_zero] using hadd (hadd (hadd (hif (c 0) ha0) (hif (c 1) rz12)) (hif (c 3) rz3)) (hif (c 4) rz4)
    rw [hx]
    simp only [apply_ite,map_zero,hd0,ite_self,ModuleCat.hom_zero,LinearMap.zero_apply]
  obtain ⟨_,a4,t0,ha4,ht0,hda4⟩ := h277
  have hd4 : E.d 4 (11,135) a4=t0 := hda4
  -- Incoming d2 and d3 kill every E4 direction except basis1+basis2.
  have kernel_11 (x : E.Page 4 (11,135)) : x=0 ∨ x=a4 := by
    have rz0 : RepresentsOnPage E 4 (11,135) (I.interpretation.basis .sphere 11 135 0) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h200
    have rz34 : RepresentsOnPage E 4 (11,135)
        (I.interpretation.basis .sphere 11 135 3 + I.interpretation.basis .sphere 11 135 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h227
    have rz4 : RepresentsOnPage E 4 (11,135) (I.interpretation.basis .sphere 11 135 4) 0 :=
      differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h228
    have rz3 : RepresentsOnPage E 4 (11,135) (I.interpretation.basis .sphere 11 135 3) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using hsub rz34 rz4
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz0⟩
    have d12 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨a4,ha4⟩
    have d3 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz3⟩
    have d4 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz4⟩
    have d2 := h278.eq_on_page_two.2
    change E.d 2 (11,135) (I.interpretation.basis .sphere 11 135 2) = I.interpretation.basis .sphere 13 136 2 at d2
    have tn : I.interpretation.basis .sphere 13 136 2 ≠ 0 := by
      rw [←he13_136_2]
      intro h
      have hh := congrArg e13_136 h
      simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
      have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 2) hh
      norm_num at hh'
    have d1 : E.d 2 (11,135) (I.interpretation.basis .sphere 11 135 1) = -I.interpretation.basis .sphere 13 136 2 := by
      simpa only [map_add,d2,eq_neg_iff_add_eq_zero] using d12
    obtain ⟨a,ha⟩ := lift_e2 (by decide : (2:ℤ)≤4) x
    have da := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 a) ⟨x,ha⟩
    let c : Fin 5 → F2 := e11_135 a
    have hcoef := congrArg e11_135.symm (f2_expand (e11_135 a))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change a = (if c 0=0 then 0 else e11_135.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e11_135.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e11_135.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e11_135.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e11_135.symm (Finsupp.single 4 1)) + 0)))) at hcoef
    simp only [he11_135_0,he11_135_1,he11_135_2,he11_135_3,he11_135_4,add_zero] at hcoef
    have hc : (c 1=0) ↔ (c 2=0) := by
      have hd := congrArg (E.d 2 (11,135)) hcoef
      simp only [map_add,apply_ite,map_zero] at hd
      rw [da,d0,d1,d2,d3,d4] at hd
      simp only [ite_self,zero_add,add_zero] at hd
      constructor
      · intro h1
        by_contra h2
        simp only [h1,h2,ite_true,ite_false,zero_add] at hd
        exact tn hd.symm
      · intro h2
        by_contra h1
        simp only [h1,h2,ite_true,ite_false,add_zero] at hd
        exact tn (neg_eq_zero.mp hd.symm)
    have hacomb : a = (if c 0=0 then 0 else I.interpretation.basis .sphere 11 135 0) +
        (if c 1=0 then 0 else I.interpretation.basis .sphere 11 135 1 + I.interpretation.basis .sphere 11 135 2) +
        (if c 3=0 then 0 else I.interpretation.basis .sphere 11 135 3) +
        (if c 4=0 then 0 else I.interpretation.basis .sphere 11 135 4) := by
      rw [hcoef]
      by_cases h1 : c 1=0
      · have h2 := hc.mp h1
        simp only [h1,h2,ite_true,zero_add,add_zero]
        abel
      · have h2 := mt hc.mpr h1
        simp only [h1,h2,ite_false]
        abel
    have hx : x=(if c 1=0 then 0 else a4) := by
      apply represents_unique ha
      rw [hacomb]
      simpa only [ite_self,add_zero,zero_add] using hadd (hadd (hadd (hif (c 0) rz0) (hif (c 1) ha4)) (hif (c 3) rz3)) (hif (c 4) rz4)
    by_cases h : c 1=0
    · exact Or.inl (by simpa only [h,ite_true] using hx)
    · exact Or.inr (by simpa only [h,ite_false] using hx)
  -- No d2 or d3 enters the d5 target degree, so distinct E2 labels
  -- that reach E4 remain distinct there.
  have nonzero4 {x : E.Page 2 (15,138)} (hx : x ≠ 0) {a : E.Page 4 (15,138)}
      (ha : RepresentsOnPage E 4 (15,138) x a) : a ≠ 0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
    have hn3 : b ≠ 0 := represents_next_nonzero_of_incoming_zero_at
      (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)≤2) (by exact d2_13) hb (hrep2 x) hx
    exact represents_next_nonzero_of_incoming_zero_at
      (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) (by exact d3_12) ha hb hn3

  have ht0n : t0≠0 := nonzero4 (by
    rw [←he15_138_0]
    intro h
    have hh := congrArg (fun z => e15_138 z 0) h
    simp at hh) ht0
  have hnext := next_page_two_of_kernel E 4 (by change (2:ℤ)≤4;omega) (11,135) 0 (by
    intro a ha
    rcases kernel_11 a with h|h
    · exact Or.inl h
    · rw [h,hd4] at ha
      exact (ht0n ha).elim)
  have hall (a : E.Page 5 (11,135)) : a=0 := by
    rcases hnext a with h|h
    · exact h
    · simpa only [map_zero] using h
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem sphere_low_page_vanishing_hAF12_h226 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,134) (12,136)
    (I.interpretation.basis .sphere 9 134 1) (I.interpretation.basis .sphere 12 136 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
    exact List.mem_of_getElem? (i := 226) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (9,134) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_low_page_vanishing_hAF12_h253 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.interpretation.basis .sphere 10 135 1) (I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2785⟩ (by
    exact List.mem_of_getElem? (i := 253) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_low_page_vanishing_hAF12_h254 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.interpretation.basis .sphere 10 135 2) (I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2786⟩ (by
    exact List.mem_of_getElem? (i := 254) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [3, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_low_page_vanishing_hAF12_h255 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    (I.interpretation.basis .sphere 10 135 4) (I.interpretation.basis .sphere 12 136 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2787⟩ (by
    exact List.mem_of_getElem? (i := 255) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,135) (12,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 136 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_low_page_vanishing_hAF12_h304 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (12,136) (14,137)
    (I.interpretation.basis .sphere 12 136 2) (I.interpretation.basis .sphere 14 137 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,136,[2],14,137,[2],"S0_AdamsE2_ss",2849⟩ (by
    exact List.mem_of_getElem? (i := 304) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,136) (14,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 136 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 137 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem sphere_low_page_vanishing_hAF12 (I : AdamsComputationTheorems D L G) : Subsingleton ((sequence D .sphere).Page 4 (12,136)) := by
  classical
  let E := sequence D .sphere
  have h226 : HasDifferential E 3 (9,134) (12,136)
      (I.interpretation.basis .sphere 9 134 1) (I.interpretation.basis .sphere 12 136 0) := sphere_low_page_vanishing_hAF12_h226 I
  have h253 : HasDifferential E 2 (10,135) (12,136)
      (I.interpretation.basis .sphere 10 135 1) (I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) := sphere_low_page_vanishing_hAF12_h253 I
  have h254 : HasDifferential E 2 (10,135) (12,136)
      (I.interpretation.basis .sphere 10 135 2) (I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4) := sphere_low_page_vanishing_hAF12_h254 I
  have h255 : HasDifferential E 2 (10,135) (12,136)
      (I.interpretation.basis .sphere 10 135 4) (I.interpretation.basis .sphere 12 136 4) := sphere_low_page_vanishing_hAF12_h255 I
  have h304 : HasDifferential E 2 (12,136) (14,137)
      (I.interpretation.basis .sphere 12 136 2) (I.interpretation.basis .sphere 14 137 2) := sphere_low_page_vanishing_hAF12_h304 I
  obtain ⟨e12_136,he12_136⟩ := I.basis ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e12_136
  change ∀ i : Fin 5, e12_136.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 136 i.val at he12_136
  have he12_136_0 : e12_136.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 12 136 0 := he12_136 0
  have he12_136_1 : e12_136.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 12 136 1 := he12_136 1
  have he12_136_2 : e12_136.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 12 136 2 := he12_136 2
  have he12_136_3 : e12_136.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 12 136 3 := he12_136 3
  have he12_136_4 : e12_136.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 12 136 4 := he12_136 4
  obtain ⟨e14_137,he14_137⟩ := I.basis ⟨.sphere,14,137,["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 215) (by rfl))
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_137
  change ∀ i : Fin 3, e14_137.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 137 i.val at he14_137
  have he14_137_0 : e14_137.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 14 137 0 := he14_137 0
  have he14_137_1 : e14_137.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 14 137 1 := he14_137 1
  have he14_137_2 : e14_137.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 14 137 2 := he14_137 2
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
  have hsub {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  have lift_e2 {r : ℤ} (hr : 2 ≤ r) {p : ℤ × ℤ} (x : E.Page r p) :
      ∃ a : E.Page 2 p, RepresentsOnPage E r p a x := by
    exact page_has_representative hr x
  have f2_expand {N : ℕ} (f : Fin N →₀ F2) :
      f = ∑ i : Fin N, if f i=0 then 0 else Finsupp.single i 1 := by
    exact FinitePageCalculus.f2_expand f
  have rep_zero {r : ℤ} {p : ℤ × ℤ} {x : E.Page r p}
      (h : RepresentsOnPage E r p 0 x) : x=0 :=
    represents_unique h (RepresentsOnPage.zero h.1)
  have rep_double {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (hx : x+x=0) (ha : RepresentsOnPage E r p x a) : a+a=0 := by
    exact rep_zero (by simpa only [hx] using hadd ha ha)
  -- All four possible incoming d2 directions reach E3.
  have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (c : F2) (h : RepresentsOnPage E r p x a) :
      RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
    split
    · exact RepresentsOnPage.zero h.1
    · exact h
  have h226copy := h226
  obtain ⟨_,in0,a0,hin0,ha0,hda0⟩ := h226
  have ha00 : RepresentsOnPage E 4 (12,136) (I.interpretation.basis .sphere 12 136 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<4) h226copy
  have rz12 : RepresentsOnPage E 4 (12,136)
      (I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h253
  have rz34 : RepresentsOnPage E 4 (12,136)
      (I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h254
  have rz4 : RepresentsOnPage E 4 (12,136) (I.interpretation.basis .sphere 12 136 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h255
  have rz3 : RepresentsOnPage E 4 (12,136) (I.interpretation.basis .sphere 12 136 3) 0 := by
    simpa only [add_sub_cancel_right,sub_self] using hsub rz34 rz4
  have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨a0,ha0⟩
  have d12 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz12⟩
  have d3 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz3⟩
  have d4 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨0,rz4⟩
  have d2 := h304.eq_on_page_two.2
  change E.d 2 (12,136) (I.interpretation.basis .sphere 12 136 2) = I.interpretation.basis .sphere 14 137 2 at d2
  have tn : I.interpretation.basis .sphere 14 137 2 ≠ 0 := by
    rw [←he14_137_2]
    intro h
    have hh := congrArg e14_137 h
    simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
    have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 2) hh
    norm_num at hh'
  have d1 : E.d 2 (12,136) (I.interpretation.basis .sphere 12 136 1) = -I.interpretation.basis .sphere 14 137 2 := by
    simpa only [map_add,d2,eq_neg_iff_add_eq_zero] using d12
  have hall (x : E.Page 4 (12,136)) : x=0 := by
    obtain ⟨a,ha⟩ := lift_e2 (by decide : (2:ℤ)≤4) x
    have da := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 a) ⟨x,ha⟩
    let c : Fin 5 → F2 := e12_136 a
    have hcoef := congrArg e12_136.symm (f2_expand (e12_136 a))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change a = (if c 0=0 then 0 else e12_136.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e12_136.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e12_136.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e12_136.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e12_136.symm (Finsupp.single 4 1)) + 0)))) at hcoef
    simp only [he12_136_0,he12_136_1,he12_136_2,he12_136_3,he12_136_4,add_zero] at hcoef
    have hc : (c 1=0) ↔ (c 2=0) := by
      have hd := congrArg (E.d 2 (12,136)) hcoef
      simp only [map_add,apply_ite,map_zero] at hd
      rw [da,d0,d1,d2,d3,d4] at hd
      simp only [ite_self,zero_add,add_zero] at hd
      constructor
      · intro h1
        by_contra h2
        simp only [h1,h2,ite_true,ite_false,zero_add] at hd
        exact tn hd.symm
      · intro h2
        by_contra h1
        simp only [h1,h2,ite_true,ite_false,add_zero] at hd
        exact tn (neg_eq_zero.mp hd.symm)
    have hacomb : a = (if c 0=0 then 0 else I.interpretation.basis .sphere 12 136 0) +
        (if c 1=0 then 0 else I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2) +
        (if c 3=0 then 0 else I.interpretation.basis .sphere 12 136 3) +
        (if c 4=0 then 0 else I.interpretation.basis .sphere 12 136 4) := by
      rw [hcoef]
      by_cases h1 : c 1=0
      · have h2 := hc.mp h1
        simp only [h1,h2,ite_true,zero_add,add_zero]
        abel
      · have h2 := mt hc.mpr h1
        simp only [h1,h2,ite_false]
        abel
    have hx : x=0 := by
      apply represents_unique ha
      rw [hacomb]
      simpa only [ite_self,add_zero] using hadd (hadd (hadd (hif (c 0) ha00) (hif (c 1) rz12)) (hif (c 3) rz3)) (hif (c 4) rz4)
    exact hx
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem sphere_low_page_vanishing_hxH2 (I : AdamsComputationTheorems D L G) : I.interpretation.sphere 9 134 (mulAt X (atom .h2)) = 0 := by
  classical
  have h : mulAt X (atom .h2) = 0 := by
    apply Subtype.ext
    change (h1 * (atom .x_121_7).val) * h2 = 0
    calc
      _ = (h1*h2) * (atom .x_121_7).val := by ac_rfl
      _ = 0 := by rw [h1_mul_h2_eq_zero,zero_mul]
  rw [h,map_zero]

private theorem sphere_low_page_vanishing (I : AdamsComputationTheorems D L G) :
    (Subsingleton ((sequence D .sphere).Page 4 (12,137)) ∧
    Subsingleton ((sequence D .sphere).Page 5 (13,138))) ∧
    (Subsingleton ((sequence D .sphere).Page 5 (11,135))) ∧
    (Subsingleton ((sequence D .sphere).Page 4 (12,136))) ∧
    (I.interpretation.sphere 9 134 (mulAt X (atom .h2)) = 0) ∧
    (∀ (s : ℕ) (_hs : s≤4),
      Subsingleton ((sequence D .sphere).Page 2 (s,(s:ℤ)+125))) := by
  classical
  exact ⟨(sphere_low_page_vanishing_hMiddle125 I), (sphere_low_page_vanishing_hAF11 I), (sphere_low_page_vanishing_hAF12 I), (sphere_low_page_vanishing_hxH2 I), stem125_e2_low I⟩


end SphereFactsProof

end
end KIP126.Computation.SphereAndCofiber
end
