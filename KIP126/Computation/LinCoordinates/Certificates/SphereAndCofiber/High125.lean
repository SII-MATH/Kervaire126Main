module

public import KIP126.Computation.LinCoordinates.Certificates.SphereAndCofiber.Bounds
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Legacy

/-! The unique nonzero high125 component on the fifth page. -/

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
section
open CategoryTheory.Limits KIP126.Algebra KIP126.Computation.Near126 in
/-- The six d4 root refutations, d4([1])=[3], and the reconstructed E4
source/target groups yield precisely this E5 component.  Nonzero is on E5. -/
private theorem high_incoming2_zero_h415 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (19,146) (23,149)
    ((I.interpretation.basis .sphere 19 146 0)) ((I.interpretation.basis .sphere 23 149 0)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,19,146,[0],23,149,[0],"S0_AdamsE2_ss",3636⟩ (by
    exact List.mem_of_getElem? (i := 415) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (19,146) (23,149) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 19 146 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 23 149 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_incoming2_zero_h425 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (20,147) (23,149)
    ((I.interpretation.basis .sphere 20 147 2)) ((I.interpretation.basis .sphere 23 149 1)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,20,147,[2],23,149,[1],"S0_AdamsE2_ss",3753⟩ (by
    exact List.mem_of_getElem? (i := 425) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (20,147) (23,149) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 20 147 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 23 149 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_incoming2_zero (I : AdamsComputationTheorems D L G) :
    (sequence D .sphere).d 2 (23,149) = 0 := by
  classical
  let E := sequence D .sphere
  have h415 : HasDifferential E 4 (19,146) (23,149)
      ((I.interpretation.basis .sphere 19 146 0)) ((I.interpretation.basis .sphere 23 149 0)) := high_incoming2_zero_h415 I
  have h425 : HasDifferential E 3 (20,147) (23,149)
      ((I.interpretation.basis .sphere 20 147 2)) ((I.interpretation.basis .sphere 23 149 1)) := high_incoming2_zero_h425 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,23,149,["549,1", "0,5,500,1"]⟩ (by
    exact List.mem_of_getElem? (i := 272) (by rfl))
  change E.Page 2 (23,149) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 23 149 i.val at he
  have d0 : E.d 2 (23,149) (I.interpretation.basis .sphere 23 149 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h415
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hy
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hy⟩
  have d1 : E.d 2 (23,149) (I.interpretation.basis .sphere 23 149 1) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h425
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hy
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hy⟩
  have hall (a : Fin 2 →₀ F2) : E.d 2 (23,149) (e.symm a)=0 := by
    induction a using Finsupp.induction with
    | zero => simp
    | @single_add i c a hi hc ih =>
      rw [map_add,map_add,ih,add_zero]
      fin_cases c
      · simp
      · change E.d 2 (23,149) (e.symm (Finsupp.single i 1))=0
        rw [he i]
        fin_cases i
        · exact d0
        · exact d1
  ext x
  change E.d 2 (23,149) x=0
  simpa only [LinearEquiv.symm_apply_apply] using hall (e x)

private theorem high_incoming3_zero_h440 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (19,146) (22,148)
    ((I.interpretation.basis .sphere 19 146 4)) ((I.interpretation.basis .sphere 22 148 1)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,19,146,[4],22,148,[1],"S0_AdamsE2_ss",3814⟩ (by
    exact List.mem_of_getElem? (i := 440) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (19,146) (22,148) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 19 146 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 22 148 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_incoming3_zero_h441 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (19,146) (22,148)
    ((I.interpretation.basis .sphere 19 146 1) + (I.interpretation.basis .sphere 19 146 4)) ((I.interpretation.basis .sphere 22 148 0)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,19,146,[1, 4],22,148,[0],"S0_AdamsE2_ss",3815⟩ (by
    exact List.mem_of_getElem? (i := 441) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (19,146) (22,148) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 19 146 [1, 4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 22 148 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_incoming3_zero (I : AdamsComputationTheorems D L G) :
    (sequence D .sphere).d 3 (22,148) = 0 := by
  classical
  let E := sequence D .sphere
  have h440 : HasDifferential E 3 (19,146) (22,148)
      ((I.interpretation.basis .sphere 19 146 4)) ((I.interpretation.basis .sphere 22 148 1)) := high_incoming3_zero_h440 I
  have h441 : HasDifferential E 3 (19,146) (22,148)
      ((I.interpretation.basis .sphere 19 146 1) + (I.interpretation.basis .sphere 19 146 4)) ((I.interpretation.basis .sphere 22 148 0)) := high_incoming3_zero_h441 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,22,148,["0,1,530,1", "0,4,500,1"]⟩ (by
    exact List.mem_of_getElem? (i := 267) (by rfl))
  change E.Page 2 (22,148) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 22 148 i.val at he
  obtain ⟨_,x0,y0,hx0,hy0,hd0⟩ := h441
  obtain ⟨_,x1,y1,hx1,hy1,hd1⟩ := h440
  have dy0 : E.d 3 (22,148) y0=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(19,146)) ⟨x0,hd0⟩
  have dy1 : E.d 3 (22,148) y1=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(19,146)) ⟨x1,hd1⟩
  ext z
  change E.d 3 (22,148) z=0
  let vv : Fin 2 → E.Page 3 (22,148) := ![y0,y1]
  have hv (i : Fin 2) : RepresentsOnPage E 3 (22,148) (e.symm (Finsupp.single i 1)) (vv i) := by
    rw [he i]
    fin_cases i
    · exact hy0
    · exact hy1
  obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e vv hv z
  simp only [Fin.sum_univ_succ] at hc
  change z=(if c 0=0 then 0 else y0)+((if c 1=0 then 0 else y1)+0) at hc
  rw [hc]
  by_cases h0 : c 0=0 <;> by_cases h1 : c 1=0
  all_goals simp only [h0,h1,ite_true,ite_false,map_zero,map_add,dy0,dy1,add_zero]

private theorem high_component_raw_h407 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (18,145) (21,147)
    ((I.interpretation.basis .sphere 18 145 4)) ((I.interpretation.basis .sphere 21 147 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,18,145,[4],21,147,[2],"S0_AdamsE2_ss",3565⟩ (by
    exact List.mem_of_getElem? (i := 407) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (18,145) (21,147) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 18 145 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 21 147 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_component_raw_h430 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (21,147) (25,150)
    ((I.interpretation.basis .sphere 21 147 1)) ((I.interpretation.basis .sphere 25 150 3)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,21,147,[1],25,150,[3],"S0_AdamsE2_ss",3749⟩ (by
    exact List.mem_of_getElem? (i := 430) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (21,147) (25,150) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_component_raw_h464 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (25,150) (27,151)
    ((I.interpretation.basis .sphere 25 150 1)) ((I.interpretation.basis .sphere 27 151 0)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,25,150,[1],27,151,[0],"S0_AdamsE2_ss",3995⟩ (by
    exact List.mem_of_getElem? (i := 464) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (25,150) (27,151) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 25 150 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 27 151 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem high_component_raw_h431 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 4 (21,147) (I.interpretation.basis .sphere 21 147 0) := by
  classical
  have hh := I.adamsStatements ⟨.sphere,.reaches,4,21,147,[0],21,147,[],"S0_AdamsE2_ss",3750⟩ (by
    exact List.mem_of_getElem? (i := 431) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem high_component_raw_h462 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (25,150) (I.interpretation.basis .sphere 25 150 2) := by
  classical
  have hh := I.adamsStatements ⟨.sphere,.reaches,1000,25,150,[2],25,150,[],"S0_AdamsE2_ss",3993⟩ (by
    exact List.mem_of_getElem? (i := 462) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 25 150 [2]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem high_component_raw_h463 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (25,150) (I.interpretation.basis .sphere 25 150 0 + I.interpretation.basis .sphere 25 150 1) := by
  classical
  have hh := I.adamsStatements ⟨.sphere,.reaches,1000,25,150,[0, 1],25,150,[],"S0_AdamsE2_ss",3994⟩ (by
    exact List.mem_of_getElem? (i := 463) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 25 150 [0, 1]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem high_component_raw_zero4
    (I : AdamsComputationTheorems D L G) {x : (sequence D .sphere).Page 2 (25,150)} (hx : RepresentsOnPage (sequence D .sphere) 4 (25,150) x 0) : x=0  := by
  classical
  let E := sequence D .sphere
  have hrep2 {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (hr : 2≤r) (ha : RepresentsOnPage E r p x a) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _

  by_contra hn
  obtain ⟨x3,h3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hx
  have n3 : x3≠0 := represents_next_nonzero_of_incoming_zero_at (E:=E) (r:=2) (p:=(25,150))
    (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)≤2) (high_incoming2_zero I)
    h3 (hrep2 (by decide) hx) hn
  have n4 : (0 : E.Page 4 (25,150))≠0 := represents_next_nonzero_of_incoming_zero_at (E:=E) (r:=3) (p:=(25,150))
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) (high_incoming3_zero I) hx h3 n3
  exact n4 rfl

private theorem high_component_raw_n661
    (I : AdamsComputationTheorems D L G) : ¬ HasDifferential (sequence D .sphere) 4 (21,147) (25,150) (I.interpretation.basis .sphere 21 147 0) (0)  := by
  classical
  let E := sequence D .sphere

  have hh := I.adamsStatements ⟨.sphere,.refutation,4,21,147,[0],25,150,[],"proofs.db/log",154532⟩ (by
    exact List.mem_of_getElem? (i := 661) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,y,hy,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 []=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hh
  simpa only [E,Nat.cast_ofNat,add_assoc] using hh

private theorem high_component_raw_n662
    (I : AdamsComputationTheorems D L G) : ¬ HasDifferential (sequence D .sphere) 4 (21,147) (25,150) (I.interpretation.basis .sphere 21 147 0) (I.interpretation.basis .sphere 25 150 3)  := by
  classical
  let E := sequence D .sphere

  have hh := I.adamsStatements ⟨.sphere,.refutation,4,21,147,[0],25,150,[3],"proofs.db/log",154533⟩ (by
    exact List.mem_of_getElem? (i := 662) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,y,hy,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [3]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hh
  simpa only [E,Nat.cast_ofNat,add_assoc] using hh

private theorem high_component_raw_n663
    (I : AdamsComputationTheorems D L G) : ¬ HasDifferential (sequence D .sphere) 4 (21,147) (25,150) (I.interpretation.basis .sphere 21 147 0) (I.interpretation.basis .sphere 25 150 2)  := by
  classical
  let E := sequence D .sphere

  have hh := I.adamsStatements ⟨.sphere,.refutation,4,21,147,[0],25,150,[2],"proofs.db/log",154534⟩ (by
    exact List.mem_of_getElem? (i := 663) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,y,hy,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [2]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hh
  simpa only [E,Nat.cast_ofNat,add_assoc] using hh

private theorem high_component_raw_n664
    (I : AdamsComputationTheorems D L G) : ¬ HasDifferential (sequence D .sphere) 4 (21,147) (25,150) (I.interpretation.basis .sphere 21 147 0) (I.interpretation.basis .sphere 25 150 2 + I.interpretation.basis .sphere 25 150 3)  := by
  classical
  let E := sequence D .sphere

  have hh := I.adamsStatements ⟨.sphere,.refutation,4,21,147,[0],25,150,[2, 3],"proofs.db/log",154535⟩ (by
    exact List.mem_of_getElem? (i := 664) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,y,hy,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [2, 3]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hh
  simpa only [E,Nat.cast_ofNat,add_assoc] using hh

private theorem high_component_raw_n665
    (I : AdamsComputationTheorems D L G) : ¬ HasDifferential (sequence D .sphere) 4 (21,147) (25,150) (I.interpretation.basis .sphere 21 147 0) (I.interpretation.basis .sphere 25 150 0 + I.interpretation.basis .sphere 25 150 1)  := by
  classical
  let E := sequence D .sphere

  have hh := I.adamsStatements ⟨.sphere,.refutation,4,21,147,[0],25,150,[0, 1],"proofs.db/log",154536⟩ (by
    exact List.mem_of_getElem? (i := 665) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,y,hy,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [0, 1]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hh
  simpa only [E,Nat.cast_ofNat,add_assoc] using hh

private theorem high_component_raw_n666
    (I : AdamsComputationTheorems D L G) : ¬ HasDifferential (sequence D .sphere) 4 (21,147) (25,150) (I.interpretation.basis .sphere 21 147 0) (I.interpretation.basis .sphere 25 150 0 + I.interpretation.basis .sphere 25 150 1 + I.interpretation.basis .sphere 25 150 3)  := by
  classical
  let E := sequence D .sphere

  have hh := I.adamsStatements ⟨.sphere,.refutation,4,21,147,[0],25,150,[0, 1, 3],"proofs.db/log",154537⟩ (by
    exact List.mem_of_getElem? (i := 666) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,y,hy,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 21 147 [0]=true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 25 150 [0, 1, 3]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hh
  simpa only [E,Nat.cast_ofNat,add_assoc] using hh

private theorem high_component_page_four (I : AdamsComputationTheorems D L G) :
    ∃ e : (sequence D .sphere).Page 2 (25,150) ≃ₗ[ℤ] (Fin 4 →₀ F2),
    ∃ a b c : (sequence D .sphere).Page 4 (25,150),
    ∃ u v : (sequence D .sphere).Page 4 (21,147),
    (∀ i : Fin 4, e.symm (Finsupp.single i 1)=I.interpretation.basis .sphere 25 150 i.val) ∧
    RepresentsOnPage (sequence D .sphere) 4 (25,150)
      (I.interpretation.basis .sphere 25 150 0+I.interpretation.basis .sphere 25 150 1) a ∧
    RepresentsOnPage (sequence D .sphere) 4 (25,150) (I.interpretation.basis .sphere 25 150 2) b ∧
    RepresentsOnPage (sequence D .sphere) 4 (25,150) (I.interpretation.basis .sphere 25 150 3) c ∧
    RepresentsOnPage (sequence D .sphere) 4 (21,147) (I.interpretation.basis .sphere 21 147 0) u ∧
    (∀ z : (sequence D .sphere).Page 4 (25,150),
      z=0 ∨ z=c ∨ z=b ∨ z=b+c ∨ z=a ∨ z=a+c ∨ z=a+b ∨ z=a+b+c) ∧
    (sequence D .sphere).d 4 (21,147) v=c ∧
    (∀ z : (sequence D .sphere).Page 4 (21,147), z=0 ∨ z=u ∨ z=v ∨ z=u+v) ∧
    ((sequence D .sphere).d 4 (21,147) u=a+b ∨
      (sequence D .sphere).d 4 (21,147) u=a+b+c) := by
  classical
  let E := sequence D .sphere
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    as_aux_lemma =>
      exact represents_add_tail (by assumption) (by assumption)
  have hrep2 {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (hr : 2≤r) (ha : RepresentsOnPage E r p x a) : RepresentsOnPage E 2 p x x := by
    as_aux_lemma =>
      exact represents_two_self _
  have h407 : HasDifferential E 3 (18,145) (21,147)
      ((I.interpretation.basis .sphere 18 145 4)) ((I.interpretation.basis .sphere 21 147 2)) := high_component_raw_h407 I
  have h430 : HasDifferential E 4 (21,147) (25,150)
      ((I.interpretation.basis .sphere 21 147 1)) ((I.interpretation.basis .sphere 25 150 3)) := high_component_raw_h430 I
  have h464 : HasDifferential E 2 (25,150) (27,151)
      ((I.interpretation.basis .sphere 25 150 1)) ((I.interpretation.basis .sphere 27 151 0)) := high_component_raw_h464 I
  have h431 : ReachesPage E 4 (21,147) (I.interpretation.basis .sphere 21 147 0) := high_component_raw_h431 I
  have h462 : ReachesPage E 1000 (25,150) (I.interpretation.basis .sphere 25 150 2) := high_component_raw_h462 I
  have h463 : ReachesPage E 1000 (25,150) (I.interpretation.basis .sphere 25 150 0 + I.interpretation.basis .sphere 25 150 1) := high_component_raw_h463 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,25,150,["559,1", "558,1", "13,4,51,1", "8,2,9,1,13,1,80,1"]⟩ (by
    exact List.mem_of_getElem? (i := 281) (by rfl))
  change E.Page 2 (25,150) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 25 150 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,27,151,["0,1,557,1", "0,2,17,1,260,1"]⟩ (by
    exact List.mem_of_getElem? (i := 289) (by rfl))
  change E.Page 2 (27,151) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 27 151 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,21,147,["530,1", "1,1,510,1", "0,3,500,1"]⟩ (by
    exact List.mem_of_getElem? (i := 262) (by rfl))
  change E.Page 2 (21,147) ≃ₗ[ℤ] (Fin 3 →₀ F2) at g
  change ∀ i : Fin 3, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 21 147 i.val at hg
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 25 150 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 25 150 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 25 150 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 25 150 3 := he 3
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 27 151 0 := hf 0
  obtain ⟨aLate,haLate⟩ := h463
  obtain ⟨bLate,hbLate⟩ := h462
  obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) haLate
  obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) hbLate
  obtain ⟨_,v,c,hv,hc,dvc⟩ := h430
  have dvc' : E.d 4 (21,147) v=c := dvc
  obtain ⟨u,hu⟩ := h431
  have hg2zero : RepresentsOnPage E 4 (21,147) (I.interpretation.basis .sphere 21 147 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h407
  have sourceFrame (z : E.Page 4 (21,147)) : z=0 ∨ z=u ∨ z=v ∨ z=u+v := by
    as_aux_lemma =>
      let vv : Fin 3 → E.Page 4 (21,147) := ![u,v,0]
      have hh (i : Fin 3) : RepresentsOnPage E 4 (21,147) (g.symm (Finsupp.single i 1)) (vv i) := by
        as_aux_lemma =>
          rw [hg i]
          fin_cases i
          · exact hu
          · exact hv
          · exact hg2zero
      obtain ⟨cs,hcs⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤4) g vv hh z
      simp only [Fin.sum_univ_succ] at hcs
      change z=(if cs 0=0 then 0 else u)+((if cs 1=0 then 0 else v)+((if cs 2=0 then 0 else 0)+0)) at hcs
      simp only [ite_self,add_zero] at hcs
      by_cases h0 : cs 0=0 <;> by_cases h1 : cs 1=0
      · exact Or.inl (by simpa only [h0,h1,ite_true,zero_add] using hcs)
      · exact Or.inr (Or.inr (Or.inl (by simpa only [h0,h1,ite_true,ite_false,zero_add] using hcs)))
      · exact Or.inr (Or.inl (by simpa only [h0,h1,ite_true,ite_false,add_zero] using hcs))
      · exact Or.inr (Or.inr (Or.inr (by simpa only [h0,h1,ite_false] using hcs)))
  have d1 : E.d 2 (25,150) (I.interpretation.basis .sphere 25 150 1)=I.interpretation.basis .sphere 27 151 0 := h464.eq_on_page_two.2
  have da : E.d 2 (25,150) (I.interpretation.basis .sphere 25 150 0+I.interpretation.basis .sphere 25 150 1)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 (by decide) ha) ⟨a,ha⟩
  have d0 : E.d 2 (25,150) (I.interpretation.basis .sphere 25 150 0)=I.interpretation.basis .sphere 27 151 0 := by
    as_aux_lemma =>
      have hh := da
      rw [map_add,d1] at hh
      have ff : I.interpretation.basis .sphere 27 151 0+I.interpretation.basis .sphere 27 151 0=0 := by
        as_aux_lemma =>
          rw [←hf0,←map_add f.symm]
          have zz : Finsupp.single (0:Fin 2) (1:F2)+Finsupp.single 0 1=0 := by
            as_aux_lemma =>
              ext i
              simp only [Finsupp.add_apply,Finsupp.zero_apply]
              exact CharTwo.add_self_eq_zero _
          rw [zz,map_zero]
      exact add_right_cancel (hh.trans ff.symm)
  have d2 : E.d 2 (25,150) (I.interpretation.basis .sphere 25 150 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 (by decide) hb) ⟨b,hb⟩
  have d3 : E.d 2 (25,150) (I.interpretation.basis .sphere 25 150 3)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) (hrep2 (by decide) hc) ⟨c,hc⟩
  have targetFrame (z : E.Page 4 (25,150)) :
      z=0 ∨ z=c ∨ z=b ∨ z=b+c ∨ z=a ∨ z=a+c ∨ z=a+b ∨ z=a+b+c := by
    as_aux_lemma =>
      apply fourth_frame_of_four_basis_at (E := E) (p := (25,150)) (q := (27,151)) (by rfl) (by change (2:ℤ)≤2; omega) e f a b c
      · simpa only [he0,he1] using ha
      · simpa only [he2] using hb
      · simpa only [he3] using hc
      · change E.d 2 (25,150) (e.symm (Finsupp.single 0 1))=f.symm (Finsupp.single 0 1)
        rw [he0]
        exact d0.trans hf0.symm
      · change E.d 2 (25,150) (e.symm (Finsupp.single 1 1))=f.symm (Finsupp.single 0 1)
        rw [he1]
        exact d1.trans hf0.symm
      · simpa only [he2] using d2
      · simpa only [he3] using d3
  have n661 : ¬ HasDifferential E 4 (21,147) (25,150) (I.interpretation.basis .sphere 21 147 0) (0)  := high_component_raw_n661 I
  have n662 : ¬ HasDifferential E 4 (21,147) (25,150) (I.interpretation.basis .sphere 21 147 0) (I.interpretation.basis .sphere 25 150 3)  := high_component_raw_n662 I
  have n663 : ¬ HasDifferential E 4 (21,147) (25,150) (I.interpretation.basis .sphere 21 147 0) (I.interpretation.basis .sphere 25 150 2)  := high_component_raw_n663 I
  have n664 : ¬ HasDifferential E 4 (21,147) (25,150) (I.interpretation.basis .sphere 21 147 0) (I.interpretation.basis .sphere 25 150 2 + I.interpretation.basis .sphere 25 150 3)  := high_component_raw_n664 I
  have n665 : ¬ HasDifferential E 4 (21,147) (25,150) (I.interpretation.basis .sphere 21 147 0) (I.interpretation.basis .sphere 25 150 0 + I.interpretation.basis .sphere 25 150 1)  := high_component_raw_n665 I
  have n666 : ¬ HasDifferential E 4 (21,147) (25,150) (I.interpretation.basis .sphere 21 147 0) (I.interpretation.basis .sphere 25 150 0 + I.interpretation.basis .sphere 25 150 1 + I.interpretation.basis .sphere 25 150 3)  := high_component_raw_n666 I
  have hdu : E.d 4 (21,147) u=a+b ∨ E.d 4 (21,147) u=a+b+c := by
    as_aux_lemma =>
      rcases targetFrame (E.d 4 (21,147) u) with hh|hh|hh|hh|hh|hh|hh|hh
      · apply (n661 ?_).elim
        exact ⟨rfl,u,_,hu,(RepresentsOnPage.zero (by decide)),hh⟩
      · apply (n662 ?_).elim
        exact ⟨rfl,u,_,hu,(hc),hh⟩
      · apply (n663 ?_).elim
        exact ⟨rfl,u,_,hu,(hb),hh⟩
      · apply (n664 ?_).elim
        exact ⟨rfl,u,_,hu,(hadd hb hc),hh⟩
      · apply (n665 ?_).elim
        exact ⟨rfl,u,_,hu,(ha),hh⟩
      · apply (n666 ?_).elim
        exact ⟨rfl,u,_,hu,(hadd ha hc),hh⟩
      · exact Or.inl hh
      · exact Or.inr hh
  exact ⟨e,a,b,c,u,v,he,ha,hb,hc,hu,targetFrame,dvc',sourceFrame,hdu⟩

private theorem high_component_raw (I : AdamsComputationTheorems D L G) :
  ∃ y : (sequence D .sphere).Page 5 (25,150),
    RepresentsOnPage (sequence D .sphere) 5 (25,150)
      (I.interpretation.basis .sphere 25 150 2) y ∧ y≠0 ∧
    ∀ z : (sequence D .sphere).Page 5 (25,150), z=0 ∨ z=y := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,a,b,c,u,v,he,ha,hb,hc,hu,targetFrame,dvc',sourceFrame,hdu⟩ := high_component_page_four I
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1)=I.interpretation.basis .sphere 25 150 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1)=I.interpretation.basis .sphere 25 150 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1)=I.interpretation.basis .sphere 25 150 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1)=I.interpretation.basis .sphere 25 150 3 := he 3
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := represents_add_tail hx hy
  have zero4 {x : E.Page 2 (25,150)} (hx : RepresentsOnPage E 4 (25,150) x 0) : x=0 :=
    high_component_raw_zero4 I hx
  have inj4 {x y : E.Page 2 (25,150)} {a b : E.Page 4 (25,150)}
      (hx : RepresentsOnPage E 4 (25,150) x a) (hy : RepresentsOnPage E 4 (25,150) y b)
      (hab : a=b) : x=y := by
    as_aux_lemma =>
      apply sub_eq_zero.mp
      apply zero4
      simpa only [hab,sub_self] using represents_sub_tail hx hy
  obtain ⟨aLate,haLate⟩ := high_component_raw_h463 I
  obtain ⟨bLate,hbLate⟩ := high_component_raw_h462 I
  have hc0 : RepresentsOnPage E 5 (25,150) (I.interpretation.basis .sphere 25 150 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4;omega)
      (by decide : (4:ℤ)<5) (high_component_raw_h430 I)
  obtain ⟨a5,ha5⟩ := represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤1000) haLate
  obtain ⟨b5,hb5⟩ := represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤1000) hbLate
  have bb2 : I.interpretation.basis .sphere 25 150 2+I.interpretation.basis .sphere 25 150 2=0 := by
    as_aux_lemma =>
      rw [←he2,←map_add e.symm]
      have zz : Finsupp.single (2:Fin 4) (1:F2)+Finsupp.single 2 1=0 := by
        as_aux_lemma =>
          ext i
          simp only [Finsupp.add_apply,Finsupp.zero_apply]
          exact CharTwo.add_self_eq_zero _
      rw [zz,map_zero]
  have bb5 : b5+b5=0 := by
    as_aux_lemma =>
      apply represents_unique (hadd hb5 hb5)
      rw [bb2]
      exact RepresentsOnPage.zero (by decide)
  have eqab : a5=b5 := by
    as_aux_lemma =>
      have hh : a5+b5=0 := by
        as_aux_lemma =>
          rcases hdu with hh|hh
          · have hd : HasDifferential E 4 (21,147) (25,150)
                (I.interpretation.basis .sphere 21 147 0)
                (I.interpretation.basis .sphere 25 150 0+I.interpretation.basis .sphere 25 150 1+I.interpretation.basis .sphere 25 150 2) :=
              ⟨rfl,u,a+b,hu,hadd ha hb,hh⟩
            exact represents_unique (hadd ha5 hb5)
              (differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) hd)
          · have hd : HasDifferential E 4 (21,147) (25,150)
                (I.interpretation.basis .sphere 21 147 0)
                (I.interpretation.basis .sphere 25 150 0+I.interpretation.basis .sphere 25 150 1+I.interpretation.basis .sphere 25 150 2+I.interpretation.basis .sphere 25 150 3) :=
              ⟨rfl,u,a+b+c,hu,hadd (hadd ha hb) hc,hh⟩
            have heq := represents_unique (hadd (hadd ha5 hb5) hc0)
              (differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) hd)
            simpa only [add_zero] using heq
      exact add_right_cancel (hh.trans bb5.symm)
  have bn5 : b5≠0 := by
    as_aux_lemma =>
      apply represents_next_nonzero_of_not_incoming_at
        (r := 4) (p := (25,150)) (q := (21,147)) (by rfl)
        (by change (2:ℤ)≤4; omega) (by decide : (2:ℤ)≤4) hb5 hb
      intro q hq
      change E.d 4 (21,147) q=b at hq
      rcases sourceFrame q with hqf|hqf|hqf|hqf
      · rw [hqf,map_zero] at hq
        have heq := inj4 hb (RepresentsOnPage.zero (by decide)) hq.symm
        have hco := congrArg (fun z => e z 2) heq
        rw [←he2,LinearEquiv.apply_symm_apply,map_zero] at hco
        norm_num [Finsupp.single_apply] at hco
      · rw [hqf] at hq
        rcases hdu with hdu|hdu
        · have heq := inj4 (hadd ha hb) hb (hdu.symm.trans hq)
          have hco := congrArg (fun z => e z 0) heq
          simp only [map_add,←he0,←he1,←he2,LinearEquiv.apply_symm_apply,Finsupp.add_apply] at hco
          norm_num [Finsupp.single_apply,Fin.ext_iff] at hco
        · have heq := inj4 (hadd (hadd ha hb) hc) hb (hdu.symm.trans hq)
          have hco := congrArg (fun z => e z 0) heq
          simp only [map_add,←he0,←he1,←he2,←he3,LinearEquiv.apply_symm_apply,Finsupp.add_apply] at hco
          norm_num [Finsupp.single_apply,Fin.ext_iff] at hco
      · rw [hqf,dvc'] at hq
        have heq := inj4 hc hb hq
        have hco := congrArg (fun z => e z 2) heq
        simp only [←he2,←he3,LinearEquiv.apply_symm_apply] at hco
        norm_num [Finsupp.single_apply,Fin.ext_iff] at hco
      · rw [hqf,map_add,dvc'] at hq
        rcases hdu with hdu|hdu
        · rw [hdu] at hq
          have heq := inj4 (hadd (hadd ha hb) hc) hb hq
          have hco := congrArg (fun z => e z 0) heq
          simp only [map_add,←he0,←he1,←he2,←he3,LinearEquiv.apply_symm_apply,Finsupp.add_apply] at hco
          norm_num [Finsupp.single_apply,Fin.ext_iff] at hco
        · rw [hdu] at hq
          have heq := inj4 (hadd (hadd (hadd ha hb) hc) hc) hb hq
          have hco := congrArg (fun z => e z 0) heq
          simp only [map_add,←he0,←he1,←he2,←he3,LinearEquiv.apply_symm_apply,Finsupp.add_apply] at hco
          norm_num [Finsupp.single_apply,Fin.ext_iff] at hco
  refine ⟨b5,hb5,bn5,?_⟩
  intro z
  let A := E.ssData (25,150)
  haveI : Epi (A.pageπ 3) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨q,hq⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 3)).mp inferInstance z
  let x : E.Page 2 (25,150) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) q
  have hx : RepresentsOnPage E 5 (25,150) x z := ⟨by decide,q,rfl,hq⟩
  obtain ⟨z4,hz4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hx
  rcases targetFrame z4 with hh|hh|hh|hh|hh|hh|hh|hh
  · have hx2 := inj4 hz4 (RepresentsOnPage.zero (by decide)) hh
    rw [hx2] at hx
    have hz := represents_unique hx (RepresentsOnPage.zero (by decide))
    left
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (hc) hh
    rw [hx2] at hx
    have hz := represents_unique hx (hc0)
    left
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (hb) hh
    rw [hx2] at hx
    have hz := represents_unique hx (hb5)
    right
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (hadd hb hc) hh
    rw [hx2] at hx
    have hz := represents_unique hx (hadd hb5 hc0)
    right
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (ha) hh
    rw [hx2] at hx
    have hz := represents_unique hx (ha5)
    right
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (hadd ha hc) hh
    rw [hx2] at hx
    have hz := represents_unique hx (hadd ha5 hc0)
    right
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (hadd ha hb) hh
    rw [hx2] at hx
    have hz := represents_unique hx (hadd ha5 hb5)
    left
    simpa only [eqab,bb5,add_zero] using hz
  · have hx2 := inj4 hz4 (hadd (hadd ha hb) hc) hh
    rw [hx2] at hx
    have hz := represents_unique hx (hadd (hadd ha5 hb5) hc0)
    left
    simpa only [eqab,bb5,add_zero] using hz

private theorem high_basis_label (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 25 150 highClass = I.interpretation.basis .sphere 25 150 2 := by
  classical
  have hc := I.monomials (⟨.sphere,25,150,["559,1","558,1","13,4,51,1","8,2,9,1,13,1,80,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 281) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (2:Fin 4)
  have heq : highClass=z := by
    apply Subtype.ext
    rw [hz]
    change ((generator ⟨13,by decide⟩ * generator ⟨13,by decide⟩) *
      (generator ⟨13,by decide⟩ * generator ⟨13,by decide⟩)) * generator ⟨51,by decide⟩ =
        projection (monomialOfString "13,4,51,1")
    have hs : "13,4,51,1" ≠ "" := by decide
    have hp : (("13,4,51,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [13,4,51,1] := by
      have split : "13,4,51,1".splitOn "," = ["13","4","51","1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
  rw [heq]
  exact he

theorem high125_component (I : AdamsComputationTheorems D L G) :
    Derived.High125Component I.interpretation := by
  classical

  unfold Derived.High125Component
  rw [high_basis_label I]
  exact high_component_raw I
end

end
end KIP126.Computation.SphereAndCofiber
end
