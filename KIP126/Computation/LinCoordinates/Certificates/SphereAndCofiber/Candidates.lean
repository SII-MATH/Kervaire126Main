module

public import KIP126.Computation.LinCoordinates.Certificates.SphereAndCofiber.Bounds
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Legacy

/-! The two nonzero candidates for the differential on x_126_6. -/

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
/-- The two depth-1 T rows refute zero and one excluded E3 target.
The conclusion requires reconstruction of the whole actual E3 target group
from the basis and d2 rows, not a claim that retained trials were exhaustive. -/
private theorem candidates_raw_h226 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,134) (12,136)
    ((I.interpretation.basis .sphere 9 134 1)) ((I.interpretation.basis .sphere 12 136 0)) := by
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
  exact hd

private theorem candidates_raw_h227 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135)
    ((I.interpretation.basis .sphere 9 134 0)) ((I.interpretation.basis .sphere 11 135 3) + (I.interpretation.basis .sphere 11 135 4)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,9,134,[0],11,135,[3, 4],"S0_AdamsE2_ss",2698⟩ (by
    exact List.mem_of_getElem? (i := 227) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [3, 4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem candidates_raw_h228 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (9,134) (11,135)
    ((I.interpretation.basis .sphere 9 134 4)) ((I.interpretation.basis .sphere 11 135 4)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,9,134,[4],11,135,[4],"S0_AdamsE2_ss",2699⟩ (by
    exact List.mem_of_getElem? (i := 228) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,134) (11,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 135 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem candidates_raw_h251 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,134) (10,135)
    ((I.interpretation.basis .sphere 8 134 1)) ((I.interpretation.basis .sphere 10 135 3)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
    exact List.mem_of_getElem? (i := 251) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,134) (10,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 135 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem candidates_raw_h252 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (10,135) (13,137)
    ((I.interpretation.basis .sphere 10 135 0)) ((I.interpretation.basis .sphere 13 137 0)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2784⟩ (by
    exact List.mem_of_getElem? (i := 252) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (10,135) (13,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem candidates_raw_h253 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    ((I.interpretation.basis .sphere 10 135 1)) ((I.interpretation.basis .sphere 12 136 1) + (I.interpretation.basis .sphere 12 136 2)) := by
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
  exact hd

private theorem candidates_raw_h254 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    ((I.interpretation.basis .sphere 10 135 2)) ((I.interpretation.basis .sphere 12 136 3) + (I.interpretation.basis .sphere 12 136 4)) := by
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
  exact hd

private theorem candidates_raw_h255 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,135) (12,136)
    ((I.interpretation.basis .sphere 10 135 4)) ((I.interpretation.basis .sphere 12 136 4)) := by
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
  exact hd

private theorem candidates_raw_h174 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 3 (6,132) (I.interpretation.basis .sphere 6 132 0) := by
  classical
  have hh := I.adamsStatements ⟨.sphere,.reaches,3,6,132,[0],6,132,[],"S0_AdamsE2_ss",2574⟩ (by
    exact List.mem_of_getElem? (i := 174) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem candidates_raw_h224 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (9,134) (I.interpretation.basis .sphere 9 134 2) := by
  classical
  have hh := I.adamsStatements ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩ (by
    exact List.mem_of_getElem? (i := 224) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem candidates_raw_h225 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 7 (9,134) (I.interpretation.basis .sphere 9 134 3) := by
  classical
  have hh := I.adamsStatements ⟨.sphere,.reaches,7,9,134,[3],9,134,[],"S0_AdamsE2_ss",2696⟩ (by
    exact List.mem_of_getElem? (i := 225) (by rfl))
  dsimp only [AdamsStatement] at hh
  obtain ⟨x,hx,hh⟩ := hh
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [3]=true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hh
  exact hh

private theorem candidates_raw (I : AdamsComputationTheorems D L G) :
    HasNonzeroDifferential (sequence D .sphere) 3 (6,132) (9,134)
      (I.interpretation.basis .sphere 6 132 0) (I.interpretation.basis .sphere 9 134 3) ∨
    HasNonzeroDifferential (sequence D .sphere) 3 (6,132) (9,134)
      (I.interpretation.basis .sphere 6 132 0) (I.interpretation.basis .sphere 9 134 3 + I.interpretation.basis .sphere 9 134 2) := by
  classical
  let E := sequence D .sphere
  have h226 : HasDifferential E 3 (9,134) (12,136)
      ((I.interpretation.basis .sphere 9 134 1)) ((I.interpretation.basis .sphere 12 136 0)) := candidates_raw_h226 I
  have h227 : HasDifferential E 2 (9,134) (11,135)
      ((I.interpretation.basis .sphere 9 134 0)) ((I.interpretation.basis .sphere 11 135 3) + (I.interpretation.basis .sphere 11 135 4)) := candidates_raw_h227 I
  have h228 : HasDifferential E 2 (9,134) (11,135)
      ((I.interpretation.basis .sphere 9 134 4)) ((I.interpretation.basis .sphere 11 135 4)) := candidates_raw_h228 I
  have h251 : HasDifferential E 2 (8,134) (10,135)
      ((I.interpretation.basis .sphere 8 134 1)) ((I.interpretation.basis .sphere 10 135 3)) := candidates_raw_h251 I
  have h252 : HasDifferential E 3 (10,135) (13,137)
      ((I.interpretation.basis .sphere 10 135 0)) ((I.interpretation.basis .sphere 13 137 0)) := candidates_raw_h252 I
  have h253 : HasDifferential E 2 (10,135) (12,136)
      ((I.interpretation.basis .sphere 10 135 1)) ((I.interpretation.basis .sphere 12 136 1) + (I.interpretation.basis .sphere 12 136 2)) := candidates_raw_h253 I
  have h254 : HasDifferential E 2 (10,135) (12,136)
      ((I.interpretation.basis .sphere 10 135 2)) ((I.interpretation.basis .sphere 12 136 3) + (I.interpretation.basis .sphere 12 136 4)) := candidates_raw_h254 I
  have h255 : HasDifferential E 2 (10,135) (12,136)
      ((I.interpretation.basis .sphere 10 135 4)) ((I.interpretation.basis .sphere 12 136 4)) := candidates_raw_h255 I
  have h174 : ReachesPage E 3 (6,132) (I.interpretation.basis .sphere 6 132 0) := candidates_raw_h174 I
  have h224 : ReachesPage E 1000 (9,134) (I.interpretation.basis .sphere 9 134 2) := candidates_raw_h224 I
  have h225 : ReachesPage E 7 (9,134) (I.interpretation.basis .sphere 9 134 3) := candidates_raw_h225 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 173) (by rfl))
  change E.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 9 134 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 191) (by rfl))
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 135 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 135 i.val at hg
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
  change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 136 i.val at hk
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 9 134 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 9 134 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 9 134 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 9 134 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 9 134 4 := he 4
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 11 135 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 11 135 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 11 135 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 11 135 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 11 135 4 := hf 4
  have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 10 135 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 10 135 1 := hg 1
  have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 10 135 2 := hg 2
  have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 10 135 3 := hg 3
  have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 10 135 4 := hg 4
  have hk0 : k.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 12 136 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 12 136 1 := hk 1
  have hk2 : k.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 12 136 2 := hk 2
  have hk3 : k.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 12 136 3 := hk 3
  have hk4 : k.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 12 136 4 := hk 4
  have dg0 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h252
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have dg3 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 3)=0 := by
    have hd : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 1)=I.interpretation.basis .sphere 10 135 3 := h251.eq_on_page_two.2
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(8,134)) ⟨_,hd⟩
  have dg1 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 1)=I.interpretation.basis .sphere 12 136 1 + I.interpretation.basis .sphere 12 136 2 := h253.eq_on_page_two.2
  have dg2 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 2)=I.interpretation.basis .sphere 12 136 3 + I.interpretation.basis .sphere 12 136 4 := h254.eq_on_page_two.2
  have dg4 : E.d 2 (10,135) (I.interpretation.basis .sphere 10 135 4)=I.interpretation.basis .sphere 12 136 4 := h255.eq_on_page_two.2
  have incoming (x : E.Page 2 (10,135)) : k (E.d 2 (10,135) x) 0=0 := by
    have all (a : Fin 5 →₀ F2) : k (E.d 2 (10,135) (g.symm a)) 0=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hc ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change k (E.d 2 (10,135) (g.symm (Finsupp.single i 1))) 0=0
          rw [hg]
          fin_cases i
          all_goals dsimp only
          all_goals simp only [dg0,dg1,dg2,dg3,dg4,map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,←hk1,←hk2,←hk3,←hk4,LinearEquiv.apply_symm_apply]
          all_goals norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using all (g x)
  obtain ⟨_,b1,t,hb1,ht,hd1⟩ := h226
  have db1 : E.d 3 (9,134) b1=t := hd1
  have tn : t≠0 := by
    intro ht0
    obtain ⟨_,z,hz,hzt⟩ := ht
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (10,135) z).mp (hzt.trans ht0)
    change (Subobject.ofLE _ _ ((E.ssData (12,136)).Z_anti bot_le) ≫ (E.ssData (12,136)).pageπ 0) z ∈ LinearMap.range (E.d 2 (10,135)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (12,136)).Z_anti bot_le) ≫ (E.ssData (12,136)).pageπ 0) z = I.interpretation.basis .sphere 12 136 0 at hz
    rw [hz] at hh
    obtain ⟨u,hu⟩ := hh
    have hh := incoming u
    rw [hu,←hk0,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  obtain ⟨b2late,hb2late⟩ := h224
  obtain ⟨b3late,hb3late⟩ := h225
  obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤1000) hb2late
  obtain ⟨b3,hb3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤7) hb3late
  have db2 : E.d 3 (9,134) b2=0 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) hb2 ⟨b2late,hb2late⟩
  have db3 : E.d 3 (9,134) b3=0 := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) hb3 ⟨b3late,hb3late⟩
  have hrep2 {p : ℤ × ℤ} {r : ℤ} {x : E.Page 2 p} {a : E.Page r p} (hr : 2≤r) (ha : RepresentsOnPage E r p x a) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have d1 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 1)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb1) ⟨b1,hb1⟩
  have d2 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb2) ⟨b2,hb2⟩
  have d3 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 3)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb3) ⟨b3,hb3⟩
  have d0 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 0)=I.interpretation.basis .sphere 11 135 3+I.interpretation.basis .sphere 11 135 4 := h227.eq_on_page_two.2
  have d4 : E.d 2 (9,134) (I.interpretation.basis .sphere 9 134 4)=I.interpretation.basis .sphere 11 135 4 := h228.eq_on_page_two.2
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
  have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (c : F2) (h : RepresentsOnPage E r p x a) :
      RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
    split
    · exact RepresentsOnPage.zero h.1
    · exact h
  have f2_expand {N : ℕ} (f : Fin N →₀ F2) :
      f = ∑ i : Fin N, if f i=0 then 0 else Finsupp.single i 1 := by
    exact FinitePageCalculus.f2_expand f
  have frame (y : E.Page 3 (9,134)) (hy : E.d 3 (9,134) y=0) : y=0 ∨ y=b2 ∨ y=b3 ∨ y=b3+b2 := by
    let A := E.ssData (9,134)
    haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance y
    let x : E.Page 2 (9,134) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
    have hx : RepresentsOnPage E 3 (9,134) x y := ⟨by decide,z,rfl,hz⟩
    have dx : E.d 2 (9,134) x=0 := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hx) ⟨y,hx⟩
    let c : Fin 5 → F2 := e x
    have hcoef := congrArg e.symm (f2_expand (e x))
    simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
    change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
    simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
    have hd := congrArg (E.d 2 (9,134)) hcoef
    rw [dx] at hd
    simp only [map_add,apply_ite,map_zero] at hd
    simp only [d0,d1,d2,d3,d4,ite_self,zero_add,add_zero] at hd
    have c0 : c 0=0 := by
      by_contra h0
      simp only [h0,ite_false] at hd
      by_cases h4 : c 4=0
      all_goals simp only [h4,ite_true,ite_false] at hd
      all_goals have hh := congrArg (fun z => f z 3) hd
      all_goals simp only [map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply,←hf3,←hf4,LinearEquiv.apply_symm_apply] at hh
      all_goals norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    have c4 : c 4=0 := by
      by_contra h4
      simp only [c0,h4,ite_true,ite_false,zero_add] at hd
      have hh := congrArg (fun z => f z 4) hd
      simp only [map_zero,Finsupp.zero_apply,←hf4,LinearEquiv.apply_symm_apply] at hh
      norm_num [Finsupp.single_apply] at hh
    have hform : y=(if c 1=0 then 0 else b1)+((if c 2=0 then 0 else b2)+(if c 3=0 then 0 else b3)) := by
      apply represents_unique hx
      rw [hcoef]
      simp only [c0,c4,ite_true,zero_add,add_zero]
      exact hadd (hif (c 1) hb1) (hadd (hif (c 2) hb2) (hif (c 3) hb3))
    have c1 : c 1=0 := by
      by_contra h1
      have hh := congrArg (E.d 3 (9,134)) hform
      simp only [hy,map_add,apply_ite,map_zero,db1,db2,db3,h1,ite_false,ite_self,add_zero] at hh
      exact tn hh.symm
    simp only [c1,ite_true,zero_add] at hform
    by_cases h2 : c 2=0 <;> by_cases h3 : c 3=0
    · exact Or.inl (by simpa only [h2,h3,ite_true,zero_add] using hform)
    · exact Or.inr (Or.inr (Or.inl (by simpa only [h2,h3,ite_true,ite_false,zero_add] using hform)))
    · exact Or.inr (Or.inl (by simpa only [h2,h3,ite_true,ite_false,add_zero] using hform))
    · exact Or.inr (Or.inr (Or.inr (by simpa only [h2,h3,ite_false,add_comm] using hform)))
  have n659 : ¬ HasDifferential E 3 (6,132) (9,134) (I.interpretation.basis .sphere 6 132 0) (0) := by
    have hh := I.adamsStatements ⟨.sphere,.refutation,3,6,132,[0],9,134,[],"proofs.db/log",2047477⟩ (by
      exact List.mem_of_getElem? (i := 659) (by rfl))
    dsimp only [AdamsStatement] at hh
    obtain ⟨x,hx,y,hy,hh⟩ := hh
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 9 134 []=true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hh
    exact hh
  have n660 : ¬ HasDifferential E 3 (6,132) (9,134) (I.interpretation.basis .sphere 6 132 0) (I.interpretation.basis .sphere 9 134 2) := by
    have hh := I.adamsStatements ⟨.sphere,.refutation,3,6,132,[0],9,134,[2],"proofs.db/log",2047478⟩ (by
      exact List.mem_of_getElem? (i := 660) (by rfl))
    dsimp only [AdamsStatement] at hh
    obtain ⟨x,hx,y,hy,hh⟩ := hh
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 132 [0]=true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2]=true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hh
    exact hh
  obtain ⟨xr,hxr⟩ := h174
  let yr : E.Page 3 (9,134) := E.d 3 (6,132) xr
  have hd : E.d 3 (6,132) xr=yr := rfl
  have hyn : yr≠0 := by
    intro hz
    apply n659
    refine ⟨rfl,xr,0,hxr,RepresentsOnPage.zero (by decide),?_⟩
    change E.d 3 (6,132) xr=0
    exact hd.trans hz
  have hdy : E.d 3 (9,134) yr=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(6,132)) ⟨xr,hd⟩
  rcases frame yr hdy with h|h|h|h
  · exact (hyn h).elim
  · apply (n660 ?_).elim
    refine ⟨rfl,xr,yr,hxr,?_,?_⟩
    · rw [h]; exact hb2
    · exact hd
  · left
    refine ⟨rfl,xr,yr,hxr,?_,hd,hyn⟩
    rw [h]; exact hb3
  · right
    refine ⟨rfl,xr,yr,hxr,?_,hd,hyn⟩
    rw [h]; exact hadd hb3 hb2

private theorem source_label (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 6 132 (atom .x_126_6) = I.interpretation.basis .sphere 6 132 0 := by
  classical
  have hc := I.monomials (⟨.sphere,6,132,["368,1", "0,4,69,2"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 138) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (0:Fin 2)
  have heq : (atom .x_126_6)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨368,by decide⟩ = projection (monomialOfString "368,1")
    have hs : "368,1" ≠ "" := by decide
    have hp : (("368,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [368, 1] := by
      have split : "368,1".splitOn "," = ["368", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he

private theorem candidate_label (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 9 134 (d3Candidate) = I.interpretation.basis .sphere 9 134 3 := by
  classical
  have hc := I.monomials (⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 173) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (3:Fin 5)
  have heq : (d3Candidate)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨18,by decide⟩ * generator ⟨190,by decide⟩ = projection (monomialOfString "18,1,190,1")
    have hs : "18,1,190,1" ≠ "" := by decide
    have hp : (("18,1,190,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [18, 1, 190, 1] := by
      have split : "18,1,190,1".splitOn "," = ["18", "1", "190", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he

private theorem h6b_label (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 9 134 (mulAt dataH6 B) = I.interpretation.basis .sphere 9 134 2 := by
  classical
  have hc := I.monomials (⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ : Raw.Degree) (by
    exact List.mem_of_getElem? (i := 173) (by rfl)) rfl
  obtain ⟨z,hz,he⟩ := hc (2:Fin 5)
  have heq : (mulAt dataH6 B)=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨69,by decide⟩ * generator ⟨82,by decide⟩ = projection (monomialOfString "69,1,82,1")
    have hs : "69,1,82,1" ≠ "" := by decide
    have hp : (("69,1,82,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [69, 1, 82, 1] := by
      have split : "69,1,82,1".splitOn "," = ["69", "1", "82", "1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_two]
  rw [heq]
  exact he

theorem d3_x_126_6_candidates (I : AdamsComputationTheorems D L G) :
    Derived.Differential I.interpretation 3 (atom .x_126_6) d3Candidate ∨
      Derived.Differential I.interpretation 3 (atom .x_126_6) d3OtherCandidate := by
  classical

  have other : I.interpretation.sphere 9 134 d3OtherCandidate =
      I.interpretation.basis .sphere 9 134 3 + I.interpretation.basis .sphere 9 134 2 := by
    change I.interpretation.sphere 9 134 (d3Candidate + mulAt dataH6 B) = _
    rw [map_add,candidate_label I,h6b_label I]
  unfold Derived.Differential
  rw [source_label I,candidate_label I,other]
  exact candidates_raw I
end

end
end KIP126.Computation.SphereAndCofiber
end
