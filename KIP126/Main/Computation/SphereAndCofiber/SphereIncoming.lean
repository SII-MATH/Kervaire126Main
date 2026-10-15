module

public import KIP126.Main.Computation.SphereAndCofiber.Bounds
import all KIP126.Main.Computation.SphereAndCofiber.SphereDifferentials
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Legacy

/-! Private incoming-differential exhaustion for the target T. -/

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

open private sphere_named_differentials_hD3x1264_h153
  sphere_named_differentials_hD3x1264_h655
  from KIP126.Main.Computation.SphereAndCofiber.SphereDifferentials

private theorem t_label (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 14 139 T = I.interpretation.basis .sphere 14 139 1 := by
  classical
  have hmem : (⟨.sphere,14,139,["449,1","1,1,7,1,275,1","0,2,425,1"]⟩ : Raw.Degree) ∈ Raw.degrees := by
    exact List.mem_of_getElem? (i := 217) (by rfl)
  have hc := I.monomials _ hmem rfl
  obtain ⟨z,hz,he⟩ := hc (1 : Fin 3)
  have heq : T=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨1,by decide⟩ * (generator ⟨7,by decide⟩ * generator ⟨275,by decide⟩) = projection (monomialOfString "1,1,7,1,275,1")
    have hs : "1,1,7,1,275,1" ≠ "" := by decide
    have hp : (("1,1,7,1,275,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1,1,7,1,275,1] := by
      have split : "1,1,7,1,275,1".splitOn "," = ["1","1","7","1","275","1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,mul_assoc]
  rw [heq]
  exact he


private theorem t_permanent_cycle_h342 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (14,139) (I.interpretation.basis .sphere 14 139 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
    exact List.mem_of_getElem? (i := 342) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (14,139) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_permanent_cycle (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H) :
    IsPermanentCycle (sequence D .sphere) (14,139) (I.interpretation.sphere 14 139 T) := by
  classical
  let E := sequence D .sphere
  have h342 : ReachesPage E 1000 (14,139) (I.interpretation.basis .sphere 14 139 1) := t_permanent_cycle_h342 I
  rw [t_label I]
  apply isPermanentCycle_of_reachesPage E 1000 (by change (2:ℤ)≤1000; omega) (14,139) _ h342
  intro r hr
  haveI : Subsingleton (E.Page r ((14,139)+E.diffDeg r)) := by
    change Subsingleton (E.Page r ((14:ℤ)+r,(139:ℤ)+(r-1)))
    exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r (14+r) (139+(r-1))
      (by decide) (by omega) (V _ _ (by omega) (by omega))
  ext x
  exact Subsingleton.elim _ _


private theorem w_to_e6_h152 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 14 (3,130) (I.interpretation.basis .sphere 3 130 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,14,3,130,[0],3,130,[],"S0_AdamsE2_ss",2438⟩ (by
    exact List.mem_of_getElem? (i := 152) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 14 (3,130) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 3 130 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_h175 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 4 (6,133) (I.interpretation.basis .sphere 6 133 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,4,6,133,[0],6,133,[],"S0_AdamsE2_ss",2633⟩ (by
    exact List.mem_of_getElem? (i := 175) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 4 (6,133) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 133 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_h204 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 6 (8,134) (I.interpretation.basis .sphere 8 134 0 + I.interpretation.basis .sphere 8 134 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,6,8,134,[0, 3],8,134,[],"S0_AdamsE2_ss",2702⟩ (by
    exact List.mem_of_getElem? (i := 204) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 6 (8,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [0, 3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_h153 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (3,130) (5,131)
    (I.interpretation.basis .sphere 3 130 1) (I.interpretation.basis .sphere 5 131 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,3,130,[1],5,131,[0],"S0_AdamsE2_ss",2439⟩ (by
    exact List.mem_of_getElem? (i := 153) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (3,130) (5,131) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 3 130 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 5 131 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_h158 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (4,131) (6,132)
    (I.interpretation.basis .sphere 4 131 0) (I.interpretation.basis .sphere 6 132 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,4,131,[0],6,132,[1],"S0_AdamsE2_ss",2495⟩ (by
    exact List.mem_of_getElem? (i := 158) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (4,131) (6,132) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 6 132 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_h165 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (5,132) (7,133)
    (I.interpretation.basis .sphere 5 132 0) (I.interpretation.basis .sphere 7 133 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,5,132,[0],7,133,[1],"S0_AdamsE2_ss",2575⟩ (by
    exact List.mem_of_getElem? (i := 165) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (5,132) (7,133) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 7 133 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_h176 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (6,133) (8,134)
    (I.interpretation.basis .sphere 6 133 1) (I.interpretation.basis .sphere 8 134 5) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,6,133,[1],8,134,[5],"S0_AdamsE2_ss",2634⟩ (by
    exact List.mem_of_getElem? (i := 176) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (6,133) (8,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 8 134 [5] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem w_to_e6_w_survives6_coordinate (I : AdamsComputationTheorems D L G) :
      SurvivesTo (sequence D .sphere) 6 (8,134)
        (I.interpretation.basis .sphere 8 134 0 + I.interpretation.basis .sphere 8 134 3) := by
  classical
  let E := sequence D .sphere
  have h152 : ReachesPage E 14 (3,130) (I.interpretation.basis .sphere 3 130 0) := w_to_e6_h152 I
  have h175 : ReachesPage E 4 (6,133) (I.interpretation.basis .sphere 6 133 0) := w_to_e6_h175 I
  have h204 : ReachesPage E 6 (8,134) (I.interpretation.basis .sphere 8 134 0 + I.interpretation.basis .sphere 8 134 3) := w_to_e6_h204 I
  have h153 : HasDifferential E 2 (3,130) (5,131)
      (I.interpretation.basis .sphere 3 130 1) (I.interpretation.basis .sphere 5 131 0) := w_to_e6_h153 I
  have h158 : HasDifferential E 2 (4,131) (6,132)
      (I.interpretation.basis .sphere 4 131 0) (I.interpretation.basis .sphere 6 132 1) := w_to_e6_h158 I
  have h165 : HasDifferential E 2 (5,132) (7,133)
      (I.interpretation.basis .sphere 5 132 0) (I.interpretation.basis .sphere 7 133 1) := w_to_e6_h165 I
  have h176 : HasDifferential E 2 (6,133) (8,134)
      (I.interpretation.basis .sphere 6 133 1) (I.interpretation.basis .sphere 8 134 5) := w_to_e6_h176 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,8,134,["395,1", "394,1", "393,1", "392,1", "69,1,85,1", "0,6,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 162) (by rfl))
  change E.Page 2 (8,134) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 8 134 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 6) 1) = I.interpretation.basis .sphere 8 134 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 6) 1) = I.interpretation.basis .sphere 8 134 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 6) 1) = I.interpretation.basis .sphere 8 134 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 6) 1) = I.interpretation.basis .sphere 8 134 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 6) 1) = I.interpretation.basis .sphere 8 134 4 := he 4
  have he5 : e.symm (Finsupp.single (5:Fin 6) 1) = I.interpretation.basis .sphere 8 134 5 := he 5
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,6,133,["377,1", "0,5,324,1"]⟩ (by
    exact List.mem_of_getElem? (i := 139) (by rfl))
  change E.Page 2 (6,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 6 133 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 6 133 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 6 133 1 := hf 1
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,5,132,["0,4,324,1"]⟩ (by
    exact List.mem_of_getElem? (i := 128) (by rfl))
  change E.Page 2 (5,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at g
  change ∀ i : Fin 1, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 5 132 i.val at hg
  have hg0 : g.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 5 132 0 := hg 0
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,4,131,["0,3,324,1"]⟩ (by
    exact List.mem_of_getElem? (i := 120) (by rfl))
  change E.Page 2 (4,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at k
  change ∀ i : Fin 1, k.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 4 131 i.val at hk
  have hk0 : k.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 4 131 0 := hk 0
  obtain ⟨m,hm⟩ := I.basis ⟨.sphere,3,130,["1,1,69,2", "0,2,324,1"]⟩ (by
    exact List.mem_of_getElem? (i := 109) (by rfl))
  change E.Page 2 (3,130) ≃ₗ[ℤ] (Fin 2 →₀ F2) at m
  change ∀ i : Fin 2, m.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 3 130 i.val at hm
  have hm0 : m.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 3 130 0 := hm 0
  have hm1 : m.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 3 130 1 := hm 1
  obtain ⟨t5,ht5⟩ := I.basis ⟨.sphere,7,133,["1,1,69,1,76,1", "0,5,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 150) (by rfl))
  change E.Page 2 (7,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at t5
  change ∀ i : Fin 2, t5.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 133 i.val at ht5
  have ht50 : t5.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 7 133 0 := ht5 0
  have ht51 : t5.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 7 133 1 := ht5 1
  obtain ⟨t4,ht4⟩ := I.basis ⟨.sphere,6,132,["368,1", "0,4,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 138) (by rfl))
  change E.Page 2 (6,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at t4
  change ∀ i : Fin 2, t4.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 6 132 i.val at ht4
  have ht40 : t4.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 6 132 0 := ht4 0
  have ht41 : t4.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 6 132 1 := ht4 1
  obtain ⟨t3,ht3⟩ := I.basis ⟨.sphere,5,131,["0,3,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 127) (by rfl))
  change E.Page 2 (5,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at t3
  change ∀ i : Fin 1, t3.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 5 131 i.val at ht3
  have ht30 : t3.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 5 131 0 := ht3 0
  have one_cases {p : ℤ×ℤ} (j : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ F2)) (x : E.Page 2 p) :
      x=0 ∨ x=j.symm (Finsupp.single 0 1) := by
    as_aux_lemma =>
      have h : j x 0=0 ∨ j x 0=1 := by generalize j x 0=c; fin_cases c <;> simp
      rcases h with h|h
      · left
        apply j.injective
        apply Finsupp.ext
        intro i
        fin_cases i
        simpa using h
      · right
        apply j.injective
        apply Finsupp.ext
        intro i
        fin_cases i
        simpa using h
  have rank_one_zero {p : ℤ×ℤ} (j : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ F2))
      (hn : E.d 2 p (j.symm (Finsupp.single 0 1))≠0) : Subsingleton (E.Page 3 p) := by
    as_aux_lemma =>
      apply third_zero_of_second_kernel (by change (2:ℤ)≤2; omega) p
      intro x hx
      rcases one_cases j x with rfl|rfl
      · exact RepresentsOnPage.zero (by decide)
      · exact False.elim (hn hx)
  have h53 : Subsingleton (E.Page 3 (5,132)) := by
    as_aux_lemma =>
      apply rank_one_zero g
      have hd : E.d 2 (5,132) (I.interpretation.basis .sphere 5 132 0)=I.interpretation.basis .sphere 7 133 1 := h165.eq_on_page_two.2
      rw [hg0,hd]
      intro hz
      have hh := congrArg (fun x=>t5 x 1) hz
      rw [←ht51,LinearEquiv.apply_symm_apply,map_zero] at hh
      norm_num [Finsupp.single_apply] at hh
  have h43 : Subsingleton (E.Page 3 (4,131)) := by
    as_aux_lemma =>
      apply rank_one_zero k
      have hd : E.d 2 (4,131) (I.interpretation.basis .sphere 4 131 0)=I.interpretation.basis .sphere 6 132 1 := h158.eq_on_page_two.2
      rw [hk0,hd]
      intro hz
      have hh := congrArg (fun x=>t4 x 1) hz
      rw [←ht41,LinearEquiv.apply_symm_apply,map_zero] at hh
      norm_num [Finsupp.single_apply] at hh
  have hin3 : E.d 3 (5,132)=0 := by
    as_aux_lemma =>
      ext x
      change E.d 3 (5,132) x=0
      rw [h53.elim x 0,map_zero]
  have hin4 : E.d 4 (4,131)=0 := by
    as_aux_lemma =>
      have h44 : Subsingleton (E.Page 4 (4,131)) :=
        adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 3 4 4 131 (by decide) (by decide) h43
      ext x
      change E.d 4 (4,131) x=0
      rw [h44.elim x 0,map_zero]
  have hin5 : E.d 5 (3,130)=0 := by
    as_aux_lemma =>
      obtain ⟨a14,ha14⟩ := h152
      obtain ⟨a5,ha5⟩ := represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤14) ha14
      have hn : E.d 2 (3,130) (m.symm (Finsupp.single 1 1))≠0 := by
        as_aux_lemma =>
          have hd : E.d 2 (3,130) (I.interpretation.basis .sphere 3 130 1)=I.interpretation.basis .sphere 5 131 0 := h153.eq_on_page_two.2
          rw [hm1,hd]
          intro hz
          have hh := congrArg (fun x=>t3 x 0) hz
          rw [←ht30,LinearEquiv.apply_symm_apply,t3.map_zero] at hh
          norm_num [Finsupp.single_apply] at hh
      have hd0 : E.d 5 (3,130) a5=0 :=
        represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<14) ha5 ⟨a14,ha14⟩
      ext x
      change E.d 5 (3,130) x=0
      rcases frame_after_second (by change (2:ℤ)≤2; omega) (by decide : (3:ℤ)≤5) m (by rw [hm0]; exact ha5) hn x with rfl|rfl
      · exact map_zero _
      · exact hd0
  have hd0 : E.d 2 (6,133) (I.interpretation.basis .sphere 6 133 0)=0 := by
    as_aux_lemma =>
      obtain ⟨a4,ha4⟩ := h175
      obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) ha4
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) ha2 ⟨a4,ha4⟩
      simpa only [ha2.eq_on_page_two] using hh
  have hd1 : E.d 2 (6,133) (I.interpretation.basis .sphere 6 133 1)=I.interpretation.basis .sphere 8 134 5 := h176.eq_on_page_two.2
  have incoming2 (x : E.Page 2 (6,133)) : e (E.d 2 (6,133) x) 0=0 := by
    as_aux_lemma =>
      have hall (a : Fin 2 →₀ F2) : e (E.d 2 (6,133) (f.symm a)) 0=0 := by
        as_aux_lemma =>
          induction a using Finsupp.induction with
          | zero => simp
          | @single_add i c a hi hci ih =>
            rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
            fin_cases c
            · simp
            · change e (E.d 2 (6,133) (f.symm (Finsupp.single i 1))) 0=0
              fin_cases i
              · change e (E.d 2 (6,133) (f.symm (Finsupp.single 0 1))) 0=0
                simp only [hf0,hd0,map_zero,Finsupp.zero_apply]
              · change e (E.d 2 (6,133) (f.symm (Finsupp.single 1 1))) 0=0
                simp only [hf1,hd1,←he5,LinearEquiv.apply_symm_apply]
                norm_num [Finsupp.single_apply,Fin.ext_iff]
      simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨a6,ha6⟩ := h204
  obtain ⟨a5,ha5⟩ := represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤6) ha6
  obtain ⟨a4,ha4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) ha5
  obtain ⟨a3,ha3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha4
  have hn3 : a3≠0 := by
    apply represents_next_nonzero_of_not_incoming_at
      (r := 2) (p := (8,134)) (q := (6,133)) (by rfl)
      (by change (2:ℤ)≤2; omega) (by decide) ha3
      (represents_two_self _)
    intro x hx
    change E.d 2 (6,133) x =
      I.interpretation.basis .sphere 8 134 0 + I.interpretation.basis .sphere 8 134 3 at hx
    have hzero := incoming2 x
    rw [hx,map_add,←he0,←he3,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.add_apply,Finsupp.single_apply,Fin.ext_iff] at hzero
  have hn4 : a4≠0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) (by exact hin3) ha4 ha3 hn3
  have hn5 : a5≠0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤4; omega) (by decide : (2:ℤ)≤4) (by exact hin4) ha5 ha4 hn4
  refine ⟨a6,ha6,?_⟩
  exact represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤5; omega) (by decide : (2:ℤ)≤5) (by exact hin5) ha6 ha5 hn5



private theorem w_to_e6_w_label (I : AdamsComputationTheorems D L G) :
      I.interpretation.sphere 8 134 W = I.interpretation.basis .sphere 8 134 0 + I.interpretation.basis .sphere 8 134 3 := by
  classical
  let E := sequence D .sphere
  have hmem : (⟨.sphere,8,134,["395,1","394,1","393,1","392,1","69,1,85,1","0,6,69,2"]⟩ : Raw.Degree) ∈ Raw.degrees := by
    exact List.mem_of_getElem? (i := 162) (by rfl)
  have hc := I.monomials _ hmem rfl
  have a : I.interpretation.sphere 8 134 (atom .x_126_8_4) = I.interpretation.basis .sphere 8 134 0 := by
    obtain ⟨z,hz,he⟩ := hc (0 : Fin 6)
    have heq : atom .x_126_8_4=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨395,by decide⟩ = projection (monomialOfString "395,1")
      have hs : "395,1" ≠ "" := by decide
      have hp : (("395,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [395,1] := by
        have split : "395,1".splitOn "," = ["395","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul]
    rw [heq]
    exact he
  have b : I.interpretation.sphere 8 134 (atom .x_126_8) = I.interpretation.basis .sphere 8 134 3 := by
    obtain ⟨z,hz,he⟩ := hc (3 : Fin 6)
    have heq : atom .x_126_8=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨392,by decide⟩ = projection (monomialOfString "392,1")
      have hs : "392,1" ≠ "" := by decide
      have hp : (("392,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [392,1] := by
        have split : "392,1".splitOn "," = ["392","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul]
    rw [heq]
    exact he
  change I.interpretation.sphere 8 134 ((atom .x_126_8_4)+(atom .x_126_8))=_
  rw [map_add,a,b]


private theorem w_to_e6 (I : AdamsComputationTheorems D L G) : Derived.Survival I.interpretation 6 W := by
  let E := sequence D .sphere
  classical

  change SurvivesTo E 6 (8,134) _
  rw [w_to_e6_w_label I]
  exact w_to_e6_w_survives6_coordinate I

private theorem w_d6_targets_h342 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (14,139) (I.interpretation.basis .sphere 14 139 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
    exact List.mem_of_getElem? (i := 342) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (14,139) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem w_d6_targets_h341 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (12,138) (14,139)
    (I.interpretation.basis .sphere 12 138 1) (I.interpretation.basis .sphere 14 139 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,138,[1],14,139,[2],"S0_AdamsE2_ss",3079⟩ (by
    exact List.mem_of_getElem? (i := 341) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,138) (14,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 139 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem w_d6_targets_h343 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (14,139) (16,140)
    (I.interpretation.basis .sphere 14 139 0) (I.interpretation.basis .sphere 16 140 2) := by
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
  simpa only [add_assoc] using hd

private theorem w_d6_targets_t_label (I : AdamsComputationTheorems D L G) :
      I.interpretation.sphere 14 139 T = I.interpretation.basis .sphere 14 139 1 := by
  classical
  let E := sequence D .sphere
  have hmem : (⟨.sphere,14,139,["449,1","1,1,7,1,275,1","0,2,425,1"]⟩ : Raw.Degree) ∈ Raw.degrees := by
    exact List.mem_of_getElem? (i := 217) (by rfl)
  have hc := I.monomials _ hmem rfl
  obtain ⟨z,hz,he⟩ := hc (1 : Fin 3)
  have heq : T=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨1,by decide⟩ * (generator ⟨7,by decide⟩ * generator ⟨275,by decide⟩) = projection (monomialOfString "1,1,7,1,275,1")
    have hs : "1,1,7,1,275,1" ≠ "" := by decide
    have hp : (("1,1,7,1,275,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1,1,7,1,275,1] := by
      have split : "1,1,7,1,275,1".splitOn "," = ["1","1","7","1","275","1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,mul_assoc]
  rw [heq]
  exact he



private theorem w_d6_targets_t_page6_frame (I : AdamsComputationTheorems D L G) :
      ∃ a : (sequence D .sphere).Page 6 (14,139),
        RepresentsOnPage (sequence D .sphere) 6 (14,139) (I.interpretation.basis .sphere 14 139 1) a ∧
        ∀ y : (sequence D .sphere).Page 6 (14,139), y=0 ∨ y=a := by
  classical
  let E := sequence D .sphere
  have h342 : ReachesPage E 1000 (14,139) (I.interpretation.basis .sphere 14 139 1) := w_d6_targets_h342 I
  have h341 : HasDifferential E 2 (12,138) (14,139)
      (I.interpretation.basis .sphere 12 138 1) (I.interpretation.basis .sphere 14 139 2) := w_d6_targets_h341 I
  have h343 : HasDifferential E 2 (14,139) (16,140)
      (I.interpretation.basis .sphere 14 139 0) (I.interpretation.basis .sphere 16 140 2) := w_d6_targets_h343 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,14,139,["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (i := 217) (by rfl))
  change E.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 139 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 14 139 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 14 139 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 14 139 2 := he 2
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,16,140,["9,1,261,1", "1,1,438,1", "0,1,448,1", "0,2,440,1", "0,2,439,1"]⟩ (by
    exact List.mem_of_getElem? (i := 231) (by rfl))
  change E.Page 2 (16,140) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 140 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 16 140 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 16 140 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 16 140 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 16 140 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 16 140 4 := hf 4
  obtain ⟨a1000,ha1000⟩ := h342
  obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤1000) ha1000
  have hz2 : RepresentsOnPage E 6 (14,139) (I.interpretation.basis .sphere 14 139 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h341
  have hd0 : E.d 2 (14,139) (I.interpretation.basis .sphere 14 139 0)≠0 := by
    have hn : I.interpretation.basis .sphere 16 140 2≠0 := by
      rw [←hf2]
      exact basis_vector_ne_zero f 2
    exact fun h => hn (h343.eq_on_page_two.2.symm.trans h)
  refine ⟨a,ha,?_⟩
  exact choice_frame_of_three_basis (by decide) (by change (2:ℤ)≤2; omega)
    e _ _ _ he0 he1 he2 a ha hz2 hd0


private theorem w_d6_targets (I : AdamsComputationTheorems D L G) :
    DifferentialTargets (sequence D .sphere) 6 (8,134)
      (I.interpretation.sphere 8 134 W) (I.interpretation.sphere 14 139 T) := by
  let E := sequence D .sphere
  classical

  obtain ⟨a,ha,hall⟩ := w_d6_targets_t_page6_frame I
  intro x hx
  rcases hall (E.d 6 (8,134) x) with hz|hz
  · exact Or.inl hz
  · exact Or.inr ⟨a,by rw [w_d6_targets_t_label I]; exact ha,hz⟩

private theorem t_incoming_y_incoming2_zero_h190 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (7,134) (9,135)
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

private theorem t_incoming_y_incoming2_zero_h191 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (7,134) (9,135)
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

private theorem t_incoming_y_incoming2_zero_h231 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
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

private theorem t_incoming_y_incoming2_zero_h232 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
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

private theorem t_incoming_y_incoming2_zero_h233 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
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

private theorem t_incoming_y_incoming2_zero_h234 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
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

private theorem t_incoming_y_incoming2_zero (I : AdamsComputationTheorems D L G) : (sequence D .sphere).d 2 (9,135)=0 := by
  classical
  let E := sequence D .sphere
  have h190 : HasDifferential E 2 (7,134) (9,135)
      ((I.interpretation.basis .sphere 7 134 1)) ((I.interpretation.basis .sphere 9 135 4)) := t_incoming_y_incoming2_zero_h190 I
  have h191 : HasDifferential E 2 (7,134) (9,135)
      ((I.interpretation.basis .sphere 7 134 4)) ((I.interpretation.basis .sphere 9 135 5)) := t_incoming_y_incoming2_zero_h191 I
  have h231 : HasDifferential E 4 (9,135) (13,138)
      ((I.interpretation.basis .sphere 9 135 2)) ((I.interpretation.basis .sphere 13 138 0)) := t_incoming_y_incoming2_zero_h231 I
  have h232 : HasDifferential E 4 (9,135) (13,138)
      ((I.interpretation.basis .sphere 9 135 1)) ((I.interpretation.basis .sphere 13 138 2)) := t_incoming_y_incoming2_zero_h232 I
  have h233 : HasDifferential E 3 (9,135) (12,137)
      ((I.interpretation.basis .sphere 9 135 0)) ((I.interpretation.basis .sphere 12 137 3) + (I.interpretation.basis .sphere 12 137 4)) := t_incoming_y_incoming2_zero_h233 I
  have h234 : HasDifferential E 3 (9,135) (12,137)
      ((I.interpretation.basis .sphere 9 135 3)) ((I.interpretation.basis .sphere 12 137 3)) := t_incoming_y_incoming2_zero_h234 I
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


private theorem t_incoming_t_label (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 14 139 T = I.interpretation.basis .sphere 14 139 1 := by
  classical
  have hmem : (⟨.sphere,14,139,["449,1","1,1,7,1,275,1","0,2,425,1"]⟩ : Raw.Degree) ∈ Raw.degrees := by
    exact List.mem_of_getElem? (i := 217) (by rfl)
  have hc := I.monomials _ hmem rfl
  obtain ⟨z,hz,he⟩ := hc (1 : Fin 3)
  have heq : T=z := by
    apply Subtype.ext
    rw [hz]
    change generator ⟨1,by decide⟩ * (generator ⟨7,by decide⟩ * generator ⟨275,by decide⟩) = projection (monomialOfString "1,1,7,1,275,1")
    have hs : "1,1,7,1,275,1" ≠ "" := by decide
    have hp : (("1,1,7,1,275,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [1,1,7,1,275,1] := by
      have split : "1,1,7,1,275,1".splitOn "," = ["1","1","7","1","275","1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [split]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    simp only [monomialOfString,if_neg hs,hp]
    norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,mul_assoc]
  rw [heq]
  exact he


private theorem t_incoming_w_label (I : AdamsComputationTheorems D L G) :
    I.interpretation.sphere 8 134 W = I.interpretation.basis .sphere 8 134 0 + I.interpretation.basis .sphere 8 134 3 := by
  classical
  have hmem : (⟨.sphere,8,134,["395,1","394,1","393,1","392,1","69,1,85,1","0,6,69,2"]⟩ : Raw.Degree) ∈ Raw.degrees := by
    exact List.mem_of_getElem? (i := 162) (by rfl)
  have hc := I.monomials _ hmem rfl
  have a : I.interpretation.sphere 8 134 (atom .x_126_8_4) = I.interpretation.basis .sphere 8 134 0 := by
    obtain ⟨z,hz,he⟩ := hc (0 : Fin 6)
    have heq : atom .x_126_8_4=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨395,by decide⟩ = projection (monomialOfString "395,1")
      have hs : "395,1" ≠ "" := by decide
      have hp : (("395,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [395,1] := by
        have split : "395,1".splitOn "," = ["395","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul]
    rw [heq]
    exact he
  have b : I.interpretation.sphere 8 134 (atom .x_126_8) = I.interpretation.basis .sphere 8 134 3 := by
    obtain ⟨z,hz,he⟩ := hc (3 : Fin 6)
    have heq : atom .x_126_8=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨392,by decide⟩ = projection (monomialOfString "392,1")
      have hs : "392,1" ≠ "" := by decide
      have hp : (("392,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [392,1] := by
        have split : "392,1".splitOn "," = ["392","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul]
    rw [heq]
    exact he
  change I.interpretation.sphere 8 134 ((atom .x_126_8_4)+(atom .x_126_8))=_
  rw [map_add,a,b]


private theorem t_incoming_t_incoming2_not_hit_h264 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,137) (12,138)
    (I.interpretation.basis .sphere 10 137 0) (I.interpretation.basis .sphere 12 138 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,137,[0],12,138,[0],"S0_AdamsE2_ss",2932⟩ (by
    exact List.mem_of_getElem? (i := 264) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,137) (12,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 138 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming2_not_hit_h265 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,137) (12,138)
    (I.interpretation.basis .sphere 10 137 1) (I.interpretation.basis .sphere 12 138 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,137,[1],12,138,[2],"S0_AdamsE2_ss",2933⟩ (by
    exact List.mem_of_getElem? (i := 265) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,137) (12,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 137 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 138 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming2_not_hit_h266 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,137) (12,138)
    (I.interpretation.basis .sphere 10 137 5) (I.interpretation.basis .sphere 12 138 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,137,[5],12,138,[4],"S0_AdamsE2_ss",2934⟩ (by
    exact List.mem_of_getElem? (i := 266) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (10,137) (12,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 137 [5] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 138 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming2_not_hit_h313 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (12,138) (16,141)
    (I.interpretation.basis .sphere 12 138 3) (I.interpretation.basis .sphere 16 141 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,12,138,[3],16,141,[1],"S0_AdamsE2_ss",3016⟩ (by
    exact List.mem_of_getElem? (i := 313) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (12,138) (16,141) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming2_not_hit_h314 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (12,138) (14,139)
    (I.interpretation.basis .sphere 12 138 1) (I.interpretation.basis .sphere 14 139 2) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming2_not_hit (I : AdamsComputationTheorems D L G) :
    ¬ HitOnPage (sequence D .sphere) 2 (14,139) (I.interpretation.basis .sphere 14 139 1) := by
  classical
  let E := sequence D .sphere
  have h264 : HasDifferential E 2 (10,137) (12,138)
      (I.interpretation.basis .sphere 10 137 0) (I.interpretation.basis .sphere 12 138 0) := t_incoming_t_incoming2_not_hit_h264 I
  have h265 : HasDifferential E 2 (10,137) (12,138)
      (I.interpretation.basis .sphere 10 137 1) (I.interpretation.basis .sphere 12 138 2) := t_incoming_t_incoming2_not_hit_h265 I
  have h266 : HasDifferential E 2 (10,137) (12,138)
      (I.interpretation.basis .sphere 10 137 5) (I.interpretation.basis .sphere 12 138 4) := t_incoming_t_incoming2_not_hit_h266 I
  have h313 : HasDifferential E 4 (12,138) (16,141)
      (I.interpretation.basis .sphere 12 138 3) (I.interpretation.basis .sphere 16 141 1) := t_incoming_t_incoming2_not_hit_h313 I
  have h314 : HasDifferential E 2 (12,138) (14,139)
      (I.interpretation.basis .sphere 12 138 1) (I.interpretation.basis .sphere 14 139 2) := t_incoming_t_incoming2_not_hit_h314 I
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,12,138,["25,1,190,1", "3,1,336,1", "0,1,427,1", "0,2,419,1", "0,10,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 202) (by rfl))
  change E.Page 2 (12,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 138 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 12 138 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 12 138 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 12 138 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 12 138 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 12 138 4 := hf 4
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,14,139,["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (i := 217) (by rfl))
  change E.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 139 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 14 139 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 14 139 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 14 139 2 := he 2
  have hd0 : E.d 2 (12,138) (I.interpretation.basis .sphere 12 138 0)=0 := by
    have he : E.d 2 (10,137) (I.interpretation.basis .sphere 10 137 0)=I.interpretation.basis .sphere 12 138 0 := h264.eq_on_page_two.2
    rw [←he]
    exact ConcreteCategory.congr_hom (E.d_comp_d 2 (10,137)) _
  have hd2 : E.d 2 (12,138) (I.interpretation.basis .sphere 12 138 2)=0 := by
    have he : E.d 2 (10,137) (I.interpretation.basis .sphere 10 137 1)=I.interpretation.basis .sphere 12 138 2 := h265.eq_on_page_two.2
    rw [←he]
    exact ConcreteCategory.congr_hom (E.d_comp_d 2 (10,137)) _
  have hd4 : E.d 2 (12,138) (I.interpretation.basis .sphere 12 138 4)=0 := by
    have he : E.d 2 (10,137) (I.interpretation.basis .sphere 10 137 5)=I.interpretation.basis .sphere 12 138 4 := h266.eq_on_page_two.2
    rw [←he]
    exact ConcreteCategory.congr_hom (E.d_comp_d 2 (10,137)) _
  have hd3 : E.d 2 (12,138) (I.interpretation.basis .sphere 12 138 3)=0 := by
    obtain ⟨_,a4,b4,ha4,_,_⟩ := h313
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) ha4
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) ha2 ⟨a4,ha4⟩
    simpa only [ha2.eq_on_page_two] using hh
  have hd1 : E.d 2 (12,138) (I.interpretation.basis .sphere 12 138 1)=I.interpretation.basis .sphere 14 139 2 := h314.eq_on_page_two.2
  have hin (x : E.Page 2 (12,138)) : e (E.d 2 (12,138) x) 1=0 := by
    have hall (a : Fin 5 →₀ F2) : e (E.d 2 (12,138) (f.symm a)) 1=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change e (E.d 2 (12,138) (f.symm (Finsupp.single i 1))) 1=0
          rw [hf i]
          fin_cases i
          · change e (E.d 2 (12,138) (I.interpretation.basis .sphere 12 138 0)) 1=0
            rw [hd0,e.map_zero]
            rfl
          · change e (E.d 2 (12,138) (I.interpretation.basis .sphere 12 138 1)) 1=0
            rw [hd1,←he2,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
          · change e (E.d 2 (12,138) (I.interpretation.basis .sphere 12 138 2)) 1=0
            rw [hd2,e.map_zero]
            rfl
          · change e (E.d 2 (12,138) (I.interpretation.basis .sphere 12 138 3)) 1=0
            rw [hd3,e.map_zero]
            rfl
          · change e (E.d 2 (12,138) (I.interpretation.basis .sphere 12 138 4)) 1=0
            rw [hd4,e.map_zero]
            rfl
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  rintro ⟨p,hp,x,y,hy,hyn,hd⟩
  have hq : p=(12,138) := add_right_cancel (hp.trans (show (14,139)=(12,138)+E.diffDeg 2 from rfl))
  subst p
  change E.d 2 (12,138) x=y at hd
  have hh := hin x
  rw [hd,←hy.eq_on_page_two,←he1,LinearEquiv.apply_symm_apply] at hh
  norm_num [Finsupp.single_apply] at hh


private theorem t_incoming_t_incoming3_zero_h284 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (9,136) (11,137)
    (I.interpretation.basis .sphere 9 136 2) (I.interpretation.basis .sphere 11 137 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,9,136,[2],11,137,[4],"S0_AdamsE2_ss",2923⟩ (by
    exact List.mem_of_getElem? (i := 284) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,136) (11,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 136 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 137 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming3_zero_h285 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (9,136) (11,137)
    (I.interpretation.basis .sphere 9 136 4) (I.interpretation.basis .sphere 11 137 5) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,9,136,[4],11,137,[5],"S0_AdamsE2_ss",2924⟩ (by
    exact List.mem_of_getElem? (i := 285) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,136) (11,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 136 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 137 [5] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming3_zero_h287 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (11,137) (15,140)
    (I.interpretation.basis .sphere 11 137 2) (I.interpretation.basis .sphere 15 140 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,11,137,[2],15,140,[1],"S0_AdamsE2_ss",2926⟩ (by
    exact List.mem_of_getElem? (i := 287) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (11,137) (15,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 140 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming3_zero_h288 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    (I.interpretation.basis .sphere 11 137 0) (I.interpretation.basis .sphere 13 138 3) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming3_zero_h289 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    (I.interpretation.basis .sphere 11 137 3) (I.interpretation.basis .sphere 13 138 4) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming3_zero_h286 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (11,137) (I.interpretation.basis .sphere 11 137 1 + I.interpretation.basis .sphere 11 137 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,1000,11,137,[1, 2],11,137,[],"S0_AdamsE2_ss",2925⟩ (by
    exact List.mem_of_getElem? (i := 286) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (11,137) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming3_zero (I : AdamsComputationTheorems D L G) : (sequence D .sphere).d 3 (11,137)=0 := by
  classical
  let E := sequence D .sphere
  have h284 : HasDifferential E 2 (9,136) (11,137)
      (I.interpretation.basis .sphere 9 136 2) (I.interpretation.basis .sphere 11 137 4) := t_incoming_t_incoming3_zero_h284 I
  have h285 : HasDifferential E 2 (9,136) (11,137)
      (I.interpretation.basis .sphere 9 136 4) (I.interpretation.basis .sphere 11 137 5) := t_incoming_t_incoming3_zero_h285 I
  have h287 : HasDifferential E 4 (11,137) (15,140)
      (I.interpretation.basis .sphere 11 137 2) (I.interpretation.basis .sphere 15 140 1) := t_incoming_t_incoming3_zero_h287 I
  have h288 : HasDifferential E 2 (11,137) (13,138)
      (I.interpretation.basis .sphere 11 137 0) (I.interpretation.basis .sphere 13 138 3) := t_incoming_t_incoming3_zero_h288 I
  have h289 : HasDifferential E 2 (11,137) (13,138)
      (I.interpretation.basis .sphere 11 137 3) (I.interpretation.basis .sphere 13 138 4) := t_incoming_t_incoming3_zero_h289 I
  have h286 : ReachesPage E 1000 (11,137) (I.interpretation.basis .sphere 11 137 1 + I.interpretation.basis .sphere 11 137 2) := t_incoming_t_incoming3_zero_h286 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,11,137,["427,1", "1,1,413,1", "1,1,412,1", "0,1,419,1", "0,2,414,1", "0,9,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 193) (by rfl))
  change E.Page 2 (11,137) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 137 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 6) 1) = I.interpretation.basis .sphere 11 137 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 6) 1) = I.interpretation.basis .sphere 11 137 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 6) 1) = I.interpretation.basis .sphere 11 137 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 6) 1) = I.interpretation.basis .sphere 11 137 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 6) 1) = I.interpretation.basis .sphere 11 137 4 := he 4
  have he5 : e.symm (Finsupp.single (5:Fin 6) 1) = I.interpretation.basis .sphere 11 137 5 := he 5
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 209) (by rfl))
  change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 138 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 13 138 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 13 138 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 13 138 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 13 138 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 13 138 4 := hf 4
  have hr2 : ReachesPage E 4 (11,137) (I.interpretation.basis .sphere 11 137 2) := by
    obtain ⟨_,a,b,ha,_,_⟩ := h287
    exact ⟨a,ha⟩
  have hr1 : ReachesPage E 4 (11,137) (I.interpretation.basis .sphere 11 137 1) := by
    obtain ⟨a1000,ha1000⟩ := h286
    obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) ha1000
    obtain ⟨b,hb⟩ := hr2
    have hab := represents_add_tail ha hb
    have heq : (I.interpretation.basis .sphere 11 137 1+I.interpretation.basis .sphere 11 137 2)+I.interpretation.basis .sphere 11 137 2=I.interpretation.basis .sphere 11 137 1 := by
      apply e.injective
      simp only [map_add,←he1,←he2,LinearEquiv.apply_symm_apply]
      apply Finsupp.ext
      intro i
      fin_cases i <;> norm_num [Finsupp.add_apply,Finsupp.single_apply,Fin.ext_iff]; decide
    exact ⟨a+b,by simpa only [heq] using hab⟩
  have hr4 : ReachesPage E 4 (11,137) (I.interpretation.basis .sphere 11 137 4) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h284⟩
  have hr5 : ReachesPage E 4 (11,137) (I.interpretation.basis .sphere 11 137 5) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h285⟩
  have dz {x : E.Page 2 (11,137)} (hx : ReachesPage E 4 (11,137) x) : E.d 2 (11,137) x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) ha
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) ha2 ⟨a,ha⟩
    simpa only [ha2.eq_on_page_two] using h
  have hd0 : E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 0)=I.interpretation.basis .sphere 13 138 3 := h288.eq_on_page_two.2
  have hd3 : E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 3)=I.interpretation.basis .sphere 13 138 4 := h289.eq_on_page_two.2
  have hd1 : E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 1)=0 := dz hr1
  have hd2 : E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 2)=0 := dz hr2
  have hd4 : E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 4)=0 := dz hr4
  have hd5 : E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 5)=0 := dz hr5
  have coord0 (x : E.Page 2 (11,137)) : f (E.d 2 (11,137) x) 3=e x 0 := by
    have hall (c : Fin 6 →₀ F2) : f (E.d 2 (11,137) (e.symm c)) 3=c 0 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,Finsupp.add_apply,ih]
        congr 1
        fin_cases c
        · simp
        · change f (E.d 2 (11,137) (e.symm (Finsupp.single i 1))) 3=(Finsupp.single i (1:F2)) 0
          rw [he i]
          fin_cases i
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 0)) 3=(Finsupp.single (0:Fin 6) (1:F2)) 0
            rw [hd0,←hf3,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 1)) 3=(Finsupp.single (1:Fin 6) (1:F2)) 0
            rw [hd1,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 2)) 3=(Finsupp.single (2:Fin 6) (1:F2)) 0
            rw [hd2,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 3)) 3=(Finsupp.single (3:Fin 6) (1:F2)) 0
            rw [hd3,←hf4,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 4)) 3=(Finsupp.single (4:Fin 6) (1:F2)) 0
            rw [hd4,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 5)) 3=(Finsupp.single (5:Fin 6) (1:F2)) 0
            rw [hd5,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)
  have coord3 (x : E.Page 2 (11,137)) : f (E.d 2 (11,137) x) 4=e x 3 := by
    have hall (c : Fin 6 →₀ F2) : f (E.d 2 (11,137) (e.symm c)) 4=c 3 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,Finsupp.add_apply,ih]
        congr 1
        fin_cases c
        · simp
        · change f (E.d 2 (11,137) (e.symm (Finsupp.single i 1))) 4=(Finsupp.single i (1:F2)) 3
          rw [he i]
          fin_cases i
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 0)) 4=(Finsupp.single (0:Fin 6) (1:F2)) 3
            rw [hd0,←hf3,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 1)) 4=(Finsupp.single (1:Fin 6) (1:F2)) 3
            rw [hd1,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 2)) 4=(Finsupp.single (2:Fin 6) (1:F2)) 3
            rw [hd2,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 3)) 4=(Finsupp.single (3:Fin 6) (1:F2)) 3
            rw [hd3,←hf4,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 4)) 4=(Finsupp.single (4:Fin 6) (1:F2)) 3
            rw [hd4,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 5)) 4=(Finsupp.single (5:Fin 6) (1:F2)) 3
            rw [hd5,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)
  apply d_zero_of_second_kernel_extends (by change (2:ℤ)≤2; omega) (by decide : (3:ℤ)≤3)
  intro x hx
  have hc0 : e x 0=0 := by
    have h := coord0 x
    rw [hx,f.map_zero,Finsupp.zero_apply] at h
    exact h.symm
  have hc3 : e x 3=0 := by
    have h := coord3 x
    rw [hx,f.map_zero,Finsupp.zero_apply] at h
    exact h.symm
  apply reaches_from_support (by decide : (2:ℤ)≤4) e x
  intro i hi
  rw [he i]
  fin_cases i
  · change e x 0≠0 at hi
    exact False.elim (hi hc0)
  · exact hr1
  · exact hr2
  · change e x 3≠0 at hi
    exact False.elim (hi hc3)
  · exact hr4
  · exact hr5


private theorem t_incoming_t_incoming4_zero_h256 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.interpretation.basis .sphere 8 135 0) (I.interpretation.basis .sphere 10 136 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,135,[0],10,136,[1],"S0_AdamsE2_ss",2855⟩ (by
    exact List.mem_of_getElem? (i := 256) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming4_zero_h257 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.interpretation.basis .sphere 8 135 4) (I.interpretation.basis .sphere 10 136 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,135,[4],10,136,[3],"S0_AdamsE2_ss",2856⟩ (by
    exact List.mem_of_getElem? (i := 257) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming4_zero_h258 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.interpretation.basis .sphere 8 135 6) (I.interpretation.basis .sphere 10 136 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,135,[6],10,136,[4],"S0_AdamsE2_ss",2857⟩ (by
    exact List.mem_of_getElem? (i := 258) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [6] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming4_zero_h260 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,136) (12,137)
    (I.interpretation.basis .sphere 10 136 0) (I.interpretation.basis .sphere 12 137 2) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming4_zero_h259 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (10,136) (I.interpretation.basis .sphere 10 136 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,1000,10,136,[2],10,136,[],"S0_AdamsE2_ss",2858⟩ (by
    exact List.mem_of_getElem? (i := 259) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (10,136) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming4_zero (I : AdamsComputationTheorems D L G) : (sequence D .sphere).d 4 (10,136)=0 := by
  classical
  let E := sequence D .sphere
  have h256 : HasDifferential E 2 (8,135) (10,136)
      (I.interpretation.basis .sphere 8 135 0) (I.interpretation.basis .sphere 10 136 1) := t_incoming_t_incoming4_zero_h256 I
  have h257 : HasDifferential E 2 (8,135) (10,136)
      (I.interpretation.basis .sphere 8 135 4) (I.interpretation.basis .sphere 10 136 3) := t_incoming_t_incoming4_zero_h257 I
  have h258 : HasDifferential E 2 (8,135) (10,136)
      (I.interpretation.basis .sphere 8 135 6) (I.interpretation.basis .sphere 10 136 4) := t_incoming_t_incoming4_zero_h258 I
  have h260 : HasDifferential E 2 (10,136) (12,137)
      (I.interpretation.basis .sphere 10 136 0) (I.interpretation.basis .sphere 12 137 2) := t_incoming_t_incoming4_zero_h260 I
  have h259 : ReachesPage E 1000 (10,136) (I.interpretation.basis .sphere 10 136 2) := t_incoming_t_incoming4_zero_h259 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,136,["419,1", "0,1,414,1", "0,2,394,1", "0,2,392,1", "0,8,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 183) (by rfl))
  change E.Page 2 (10,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 136 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 10 136 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 10 136 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 10 136 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 10 136 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 10 136 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,12,137,["426,1", "425,1", "0,1,69,1,89,1", "0,3,391,1", "0,4,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  change E.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 137 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 12 137 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 12 137 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 12 137 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 12 137 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 12 137 4 := hf 4
  have hr2 : ReachesPage E 5 (10,136) (I.interpretation.basis .sphere 10 136 2) := by
    obtain ⟨a,ha⟩ := h259
    exact represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤1000) ha
  have hr1 : ReachesPage E 5 (10,136) (I.interpretation.basis .sphere 10 136 1) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h256⟩
  have hr3 : ReachesPage E 5 (10,136) (I.interpretation.basis .sphere 10 136 3) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h257⟩
  have hr4 : ReachesPage E 5 (10,136) (I.interpretation.basis .sphere 10 136 4) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h258⟩
  have dz {x : E.Page 2 (10,136)} (hx : ReachesPage E 5 (10,136) x) : E.d 2 (10,136) x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) ha
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) ha2 ⟨a,ha⟩
    simpa only [ha2.eq_on_page_two] using h
  have hd0 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 0)=I.interpretation.basis .sphere 12 137 2 := h260.eq_on_page_two.2
  have hd1 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 1)=0 := dz hr1
  have hd2 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 2)=0 := dz hr2
  have hd3 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 3)=0 := dz hr3
  have hd4 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 4)=0 := dz hr4
  have coord0 (x : E.Page 2 (10,136)) : f (E.d 2 (10,136) x) 2=e x 0 := by
    have hall (c : Fin 5 →₀ F2) : f (E.d 2 (10,136) (e.symm c)) 2=c 0 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,Finsupp.add_apply,ih]
        congr 1
        fin_cases c
        · simp
        · change f (E.d 2 (10,136) (e.symm (Finsupp.single i 1))) 2=(Finsupp.single i (1:F2)) 0
          rw [he i]
          fin_cases i
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 0)) 2=(Finsupp.single (0:Fin 5) (1:F2)) 0
            rw [hd0,←hf2,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 1)) 2=(Finsupp.single (1:Fin 5) (1:F2)) 0
            rw [hd1,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 2)) 2=(Finsupp.single (2:Fin 5) (1:F2)) 0
            rw [hd2,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 3)) 2=(Finsupp.single (3:Fin 5) (1:F2)) 0
            rw [hd3,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 4)) 2=(Finsupp.single (4:Fin 5) (1:F2)) 0
            rw [hd4,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)
  apply d_zero_of_second_kernel_extends (by change (2:ℤ)≤2; omega) (by decide : (3:ℤ)≤4)
  intro x hx
  have hc0 : e x 0=0 := by
    have h := coord0 x
    rw [hx,f.map_zero,Finsupp.zero_apply] at h
    exact h.symm
  apply reaches_from_support (by decide : (2:ℤ)≤5) e x
  intro i hi
  rw [he i]
  fin_cases i
  · change e x 0≠0 at hi
    exact False.elim (hi hc0)
  · exact hr1
  · exact hr2
  · exact hr3
  · exact hr4


private theorem t_incoming_t_source10_d3_zero_h256 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.interpretation.basis .sphere 8 135 0) (I.interpretation.basis .sphere 10 136 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,135,[0],10,136,[1],"S0_AdamsE2_ss",2855⟩ (by
    exact List.mem_of_getElem? (i := 256) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_source10_d3_zero_h257 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.interpretation.basis .sphere 8 135 4) (I.interpretation.basis .sphere 10 136 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,135,[4],10,136,[3],"S0_AdamsE2_ss",2856⟩ (by
    exact List.mem_of_getElem? (i := 257) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_source10_d3_zero_h258 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.interpretation.basis .sphere 8 135 6) (I.interpretation.basis .sphere 10 136 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,135,[6],10,136,[4],"S0_AdamsE2_ss",2857⟩ (by
    exact List.mem_of_getElem? (i := 258) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [6] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_source10_d3_zero_h260 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,136) (12,137)
    (I.interpretation.basis .sphere 10 136 0) (I.interpretation.basis .sphere 12 137 2) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_source10_d3_zero_h259 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (10,136) (I.interpretation.basis .sphere 10 136 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,1000,10,136,[2],10,136,[],"S0_AdamsE2_ss",2858⟩ (by
    exact List.mem_of_getElem? (i := 259) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (10,136) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_source10_d3_zero (I : AdamsComputationTheorems D L G) : (sequence D .sphere).d 3 (10,136)=0 := by
  classical
  let E := sequence D .sphere
  have h256 : HasDifferential E 2 (8,135) (10,136)
      (I.interpretation.basis .sphere 8 135 0) (I.interpretation.basis .sphere 10 136 1) := t_incoming_t_source10_d3_zero_h256 I
  have h257 : HasDifferential E 2 (8,135) (10,136)
      (I.interpretation.basis .sphere 8 135 4) (I.interpretation.basis .sphere 10 136 3) := t_incoming_t_source10_d3_zero_h257 I
  have h258 : HasDifferential E 2 (8,135) (10,136)
      (I.interpretation.basis .sphere 8 135 6) (I.interpretation.basis .sphere 10 136 4) := t_incoming_t_source10_d3_zero_h258 I
  have h260 : HasDifferential E 2 (10,136) (12,137)
      (I.interpretation.basis .sphere 10 136 0) (I.interpretation.basis .sphere 12 137 2) := t_incoming_t_source10_d3_zero_h260 I
  have h259 : ReachesPage E 1000 (10,136) (I.interpretation.basis .sphere 10 136 2) := t_incoming_t_source10_d3_zero_h259 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,136,["419,1", "0,1,414,1", "0,2,394,1", "0,2,392,1", "0,8,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 183) (by rfl))
  change E.Page 2 (10,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 136 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 10 136 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 10 136 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 10 136 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 10 136 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 10 136 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,12,137,["426,1", "425,1", "0,1,69,1,89,1", "0,3,391,1", "0,4,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  change E.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 137 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 12 137 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 12 137 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 12 137 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 12 137 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 12 137 4 := hf 4
  have hr2 : ReachesPage E 4 (10,136) (I.interpretation.basis .sphere 10 136 2) := by
    obtain ⟨a,ha⟩ := h259
    exact represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) ha
  have hr1 : ReachesPage E 4 (10,136) (I.interpretation.basis .sphere 10 136 1) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h256⟩
  have hr3 : ReachesPage E 4 (10,136) (I.interpretation.basis .sphere 10 136 3) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h257⟩
  have hr4 : ReachesPage E 4 (10,136) (I.interpretation.basis .sphere 10 136 4) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h258⟩
  have dz {x : E.Page 2 (10,136)} (hx : ReachesPage E 4 (10,136) x) : E.d 2 (10,136) x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) ha
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) ha2 ⟨a,ha⟩
    simpa only [ha2.eq_on_page_two] using h
  have hd0 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 0)=I.interpretation.basis .sphere 12 137 2 := h260.eq_on_page_two.2
  have hd1 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 1)=0 := dz hr1
  have hd2 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 2)=0 := dz hr2
  have hd3 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 3)=0 := dz hr3
  have hd4 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 4)=0 := dz hr4
  have coord0 (x : E.Page 2 (10,136)) : f (E.d 2 (10,136) x) 2=e x 0 := by
    have hall (c : Fin 5 →₀ F2) : f (E.d 2 (10,136) (e.symm c)) 2=c 0 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,Finsupp.add_apply,ih]
        congr 1
        fin_cases c
        · simp
        · change f (E.d 2 (10,136) (e.symm (Finsupp.single i 1))) 2=(Finsupp.single i (1:F2)) 0
          rw [he i]
          fin_cases i
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 0)) 2=(Finsupp.single (0:Fin 5) (1:F2)) 0
            rw [hd0,←hf2,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 1)) 2=(Finsupp.single (1:Fin 5) (1:F2)) 0
            rw [hd1,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 2)) 2=(Finsupp.single (2:Fin 5) (1:F2)) 0
            rw [hd2,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 3)) 2=(Finsupp.single (3:Fin 5) (1:F2)) 0
            rw [hd3,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 4)) 2=(Finsupp.single (4:Fin 5) (1:F2)) 0
            rw [hd4,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)
  apply d_zero_of_second_kernel_extends (by change (2:ℤ)≤2; omega) (by decide : (3:ℤ)≤3)
  intro x hx
  have hc0 : e x 0=0 := by
    have h := coord0 x
    rw [hx,f.map_zero,Finsupp.zero_apply] at h
    exact h.symm
  apply reaches_from_support (by decide : (2:ℤ)≤4) e x
  intro i hi
  rw [he i]
  fin_cases i
  · change e x 0≠0 at hi
    exact False.elim (hi hc0)
  · exact hr1
  · exact hr2
  · exact hr3
  · exact hr4


private theorem t_incoming_t_d3_targets_independent_h256 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.interpretation.basis .sphere 8 135 0) (I.interpretation.basis .sphere 10 136 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,135,[0],10,136,[1],"S0_AdamsE2_ss",2855⟩ (by
    exact List.mem_of_getElem? (i := 256) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d3_targets_independent_h257 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.interpretation.basis .sphere 8 135 4) (I.interpretation.basis .sphere 10 136 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,135,[4],10,136,[3],"S0_AdamsE2_ss",2856⟩ (by
    exact List.mem_of_getElem? (i := 257) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d3_targets_independent_h258 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,135) (10,136)
    (I.interpretation.basis .sphere 8 135 6) (I.interpretation.basis .sphere 10 136 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,135,[6],10,136,[4],"S0_AdamsE2_ss",2857⟩ (by
    exact List.mem_of_getElem? (i := 258) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (8,135) (10,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 135 [6] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 136 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d3_targets_independent_h260 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (10,136) (12,137)
    (I.interpretation.basis .sphere 10 136 0) (I.interpretation.basis .sphere 12 137 2) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d3_targets_independent_h259 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (10,136) (I.interpretation.basis .sphere 10 136 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,1000,10,136,[2],10,136,[],"S0_AdamsE2_ss",2858⟩ (by
    exact List.mem_of_getElem? (i := 259) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (10,136) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 136 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d3_targets_independent (I : AdamsComputationTheorems D L G)
    (a b : (sequence D .sphere).Page 3 (12,137))
    (ha : RepresentsOnPage (sequence D .sphere) 3 (12,137)
      (I.interpretation.basis .sphere 12 137 3+I.interpretation.basis .sphere 12 137 4) a)
    (hb : RepresentsOnPage (sequence D .sphere) 3 (12,137) (I.interpretation.basis .sphere 12 137 3) b) :
    a≠0 ∧ b≠0 ∧ a+b≠0 := by
  classical
  let E := sequence D .sphere
  have h256 : HasDifferential E 2 (8,135) (10,136)
      (I.interpretation.basis .sphere 8 135 0) (I.interpretation.basis .sphere 10 136 1) := t_incoming_t_d3_targets_independent_h256 I
  have h257 : HasDifferential E 2 (8,135) (10,136)
      (I.interpretation.basis .sphere 8 135 4) (I.interpretation.basis .sphere 10 136 3) := t_incoming_t_d3_targets_independent_h257 I
  have h258 : HasDifferential E 2 (8,135) (10,136)
      (I.interpretation.basis .sphere 8 135 6) (I.interpretation.basis .sphere 10 136 4) := t_incoming_t_d3_targets_independent_h258 I
  have h260 : HasDifferential E 2 (10,136) (12,137)
      (I.interpretation.basis .sphere 10 136 0) (I.interpretation.basis .sphere 12 137 2) := t_incoming_t_d3_targets_independent_h260 I
  have h259 : ReachesPage E 1000 (10,136) (I.interpretation.basis .sphere 10 136 2) := t_incoming_t_d3_targets_independent_h259 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,136,["419,1", "0,1,414,1", "0,2,394,1", "0,2,392,1", "0,8,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 183) (by rfl))
  change E.Page 2 (10,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 136 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 10 136 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 10 136 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 10 136 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 10 136 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 10 136 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,12,137,["426,1", "425,1", "0,1,69,1,89,1", "0,3,391,1", "0,4,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 201) (by rfl))
  change E.Page 2 (12,137) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 137 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 12 137 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 12 137 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 12 137 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 12 137 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 12 137 4 := hf 4
  have hr2 : ReachesPage E 5 (10,136) (I.interpretation.basis .sphere 10 136 2) := by
    obtain ⟨a,ha⟩ := h259
    exact represents_before (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤1000) ha
  have hr1 : ReachesPage E 5 (10,136) (I.interpretation.basis .sphere 10 136 1) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h256⟩
  have hr3 : ReachesPage E 5 (10,136) (I.interpretation.basis .sphere 10 136 3) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h257⟩
  have hr4 : ReachesPage E 5 (10,136) (I.interpretation.basis .sphere 10 136 4) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h258⟩
  have dz {x : E.Page 2 (10,136)} (hx : ReachesPage E 5 (10,136) x) : E.d 2 (10,136) x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) ha
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) ha2 ⟨a,ha⟩
    simpa only [ha2.eq_on_page_two] using h
  have hd0 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 0)=I.interpretation.basis .sphere 12 137 2 := h260.eq_on_page_two.2
  have hd1 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 1)=0 := dz hr1
  have hd2 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 2)=0 := dz hr2
  have hd3 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 3)=0 := dz hr3
  have hd4 : E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 4)=0 := dz hr4
  have hin (j : Fin 5) (hj : j≠2) (x : E.Page 2 (10,136)) : f (E.d 2 (10,136) x) j=0 := by
    have hall (c : Fin 5 →₀ F2) : f (E.d 2 (10,136) (e.symm c)) j=0 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change f (E.d 2 (10,136) (e.symm (Finsupp.single i 1))) j=0
          rw [he i]
          fin_cases i
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 0)) j=0
            rw [hd0,←hf2,LinearEquiv.apply_symm_apply]
            simp [Ne.symm hj]
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 1)) j=0
            rw [hd1,f.map_zero]
            rfl
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 2)) j=0
            rw [hd2,f.map_zero]
            rfl
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 3)) j=0
            rw [hd3,f.map_zero]
            rfl
          · change f (E.d 2 (10,136) (I.interpretation.basis .sphere 10 136 4)) j=0
            rw [hd4,f.map_zero]
            rfl
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)

  have nz {x : E.Page 2 (12,137)} {v : E.Page 3 (12,137)} (hv : RepresentsOnPage E 3 (12,137) x v)
      (j : Fin 5) (hj : j≠2) (hx : f x j=1) : v≠0 := by
    obtain ⟨_,z,hz2,hz3⟩ := hv
    intro hzero
    obtain ⟨u,hu⟩ := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (10,136) z).mp (hz3.trans hzero)
    have he : E.d 2 (10,136) u=x := hu.trans hz2
    have hh := hin j hj u
    rw [he,hx] at hh
    exact one_ne_zero hh
  refine ⟨nz ha 4 (by decide) ?_,nz hb 3 (by decide) ?_,nz (represents_add_tail ha hb) 4 (by decide) ?_⟩ <;>
    simp only [map_add,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply] <;>
    norm_num [Finsupp.single_apply,Fin.ext_iff]


private theorem t_incoming_t_d4_targets_independent_h284 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (9,136) (11,137)
    (I.interpretation.basis .sphere 9 136 2) (I.interpretation.basis .sphere 11 137 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,9,136,[2],11,137,[4],"S0_AdamsE2_ss",2923⟩ (by
    exact List.mem_of_getElem? (i := 284) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,136) (11,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 136 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 137 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d4_targets_independent_h285 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (9,136) (11,137)
    (I.interpretation.basis .sphere 9 136 4) (I.interpretation.basis .sphere 11 137 5) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,9,136,[4],11,137,[5],"S0_AdamsE2_ss",2924⟩ (by
    exact List.mem_of_getElem? (i := 285) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (9,136) (11,137) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 136 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 137 [5] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d4_targets_independent_h287 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (11,137) (15,140)
    (I.interpretation.basis .sphere 11 137 2) (I.interpretation.basis .sphere 15 140 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,11,137,[2],15,140,[1],"S0_AdamsE2_ss",2926⟩ (by
    exact List.mem_of_getElem? (i := 287) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (11,137) (15,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 140 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d4_targets_independent_h288 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    (I.interpretation.basis .sphere 11 137 0) (I.interpretation.basis .sphere 13 138 3) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d4_targets_independent_h289 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (11,137) (13,138)
    (I.interpretation.basis .sphere 11 137 3) (I.interpretation.basis .sphere 13 138 4) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d4_targets_independent_h286 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 1000 (11,137) (I.interpretation.basis .sphere 11 137 1 + I.interpretation.basis .sphere 11 137 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,1000,11,137,[1, 2],11,137,[],"S0_AdamsE2_ss",2925⟩ (by
    exact List.mem_of_getElem? (i := 286) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 1000 (11,137) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 137 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_d4_targets_independent (I : AdamsComputationTheorems D L G)
    (a b : (sequence D .sphere).Page 4 (13,138))
    (ha : RepresentsOnPage (sequence D .sphere) 4 (13,138) (I.interpretation.basis .sphere 13 138 2) a)
    (hb : RepresentsOnPage (sequence D .sphere) 4 (13,138) (I.interpretation.basis .sphere 13 138 0) b) :
    a≠0 ∧ b≠0 ∧ a+b≠0 := by
  classical
  let E := sequence D .sphere
  have h284 : HasDifferential E 2 (9,136) (11,137)
      (I.interpretation.basis .sphere 9 136 2) (I.interpretation.basis .sphere 11 137 4) := t_incoming_t_d4_targets_independent_h284 I
  have h285 : HasDifferential E 2 (9,136) (11,137)
      (I.interpretation.basis .sphere 9 136 4) (I.interpretation.basis .sphere 11 137 5) := t_incoming_t_d4_targets_independent_h285 I
  have h287 : HasDifferential E 4 (11,137) (15,140)
      (I.interpretation.basis .sphere 11 137 2) (I.interpretation.basis .sphere 15 140 1) := t_incoming_t_d4_targets_independent_h287 I
  have h288 : HasDifferential E 2 (11,137) (13,138)
      (I.interpretation.basis .sphere 11 137 0) (I.interpretation.basis .sphere 13 138 3) := t_incoming_t_d4_targets_independent_h288 I
  have h289 : HasDifferential E 2 (11,137) (13,138)
      (I.interpretation.basis .sphere 11 137 3) (I.interpretation.basis .sphere 13 138 4) := t_incoming_t_d4_targets_independent_h289 I
  have h286 : ReachesPage E 1000 (11,137) (I.interpretation.basis .sphere 11 137 1 + I.interpretation.basis .sphere 11 137 2) := t_incoming_t_d4_targets_independent_h286 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,11,137,["427,1", "1,1,413,1", "1,1,412,1", "0,1,419,1", "0,2,414,1", "0,9,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 193) (by rfl))
  change E.Page 2 (11,137) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 137 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 6) 1) = I.interpretation.basis .sphere 11 137 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 6) 1) = I.interpretation.basis .sphere 11 137 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 6) 1) = I.interpretation.basis .sphere 11 137 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 6) 1) = I.interpretation.basis .sphere 11 137 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 6) 1) = I.interpretation.basis .sphere 11 137 4 := he 4
  have he5 : e.symm (Finsupp.single (5:Fin 6) 1) = I.interpretation.basis .sphere 11 137 5 := he 5
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 209) (by rfl))
  change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 138 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 13 138 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 13 138 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 13 138 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 13 138 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 13 138 4 := hf 4
  have hr2 : ReachesPage E 4 (11,137) (I.interpretation.basis .sphere 11 137 2) := by
    obtain ⟨_,a,b,ha,_,_⟩ := h287
    exact ⟨a,ha⟩
  have hr1 : ReachesPage E 4 (11,137) (I.interpretation.basis .sphere 11 137 1) := by
    obtain ⟨a1000,ha1000⟩ := h286
    obtain ⟨a,ha⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤1000) ha1000
    obtain ⟨b,hb⟩ := hr2
    have hab := represents_add_tail ha hb
    have heq : (I.interpretation.basis .sphere 11 137 1+I.interpretation.basis .sphere 11 137 2)+I.interpretation.basis .sphere 11 137 2=I.interpretation.basis .sphere 11 137 1 := by
      apply e.injective
      simp only [map_add,←he1,←he2,LinearEquiv.apply_symm_apply]
      apply Finsupp.ext
      intro i
      fin_cases i <;> norm_num [Finsupp.add_apply,Finsupp.single_apply,Fin.ext_iff]; decide
    exact ⟨a+b,by simpa only [heq] using hab⟩
  have hr4 : ReachesPage E 4 (11,137) (I.interpretation.basis .sphere 11 137 4) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h284⟩
  have hr5 : ReachesPage E 4 (11,137) (I.interpretation.basis .sphere 11 137 5) :=
    ⟨0,differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h285⟩
  have dz {x : E.Page 2 (11,137)} (hx : ReachesPage E 4 (11,137) x) : E.d 2 (11,137) x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) ha
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) ha2 ⟨a,ha⟩
    simpa only [ha2.eq_on_page_two] using h
  have hd0 : E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 0)=I.interpretation.basis .sphere 13 138 3 := h288.eq_on_page_two.2
  have hd3 : E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 3)=I.interpretation.basis .sphere 13 138 4 := h289.eq_on_page_two.2
  have hd1 : E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 1)=0 := dz hr1
  have hd2 : E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 2)=0 := dz hr2
  have hd4 : E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 4)=0 := dz hr4
  have hd5 : E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 5)=0 := dz hr5
  have hin (j : Fin 5) (hj : j≠3 ∧ j≠4) (x : E.Page 2 (11,137)) : f (E.d 2 (11,137) x) j=0 := by
    have hall (c : Fin 6 →₀ F2) : f (E.d 2 (11,137) (e.symm c)) j=0 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change f (E.d 2 (11,137) (e.symm (Finsupp.single i 1))) j=0
          rw [he i]
          fin_cases i
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 0)) j=0
            rw [hd0,←hf3,LinearEquiv.apply_symm_apply]
            simp [Ne.symm hj.1]
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 1)) j=0
            rw [hd1,f.map_zero]
            rfl
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 2)) j=0
            rw [hd2,f.map_zero]
            rfl
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 3)) j=0
            rw [hd3,←hf4,LinearEquiv.apply_symm_apply]
            simp [Ne.symm hj.2]
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 4)) j=0
            rw [hd4,f.map_zero]
            rfl
          · change f (E.d 2 (11,137) (I.interpretation.basis .sphere 11 137 5)) j=0
            rw [hd5,f.map_zero]
            rfl
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)

  have nz3 {x : E.Page 2 (13,138)} {v : E.Page 3 (13,138)} (hv : RepresentsOnPage E 3 (13,138) x v)
      (j : Fin 5) (hj : j≠3 ∧ j≠4) (hx : f x j=1) : v≠0 := by
    obtain ⟨_,z,hz2,hz3⟩ := hv
    intro hzero
    obtain ⟨u,hu⟩ := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (11,137) z).mp (hz3.trans hzero)
    have he : E.d 2 (11,137) u=x := hu.trans hz2
    have hh := hin j hj u
    rw [he,hx] at hh
    exact one_ne_zero hh
  have nz4 {x : E.Page 2 (13,138)} {v : E.Page 4 (13,138)} (hv : RepresentsOnPage E 4 (13,138) x v)
      (j : Fin 5) (hj : j≠3 ∧ j≠4) (hx : f x j=1) : v≠0 := by
    obtain ⟨v3,hv3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hv
    exact represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤3; omega)
      (by decide : (2:ℤ)≤3) (by exact t_incoming_t_source10_d3_zero I) hv hv3 (nz3 hv3 j hj hx)
  refine ⟨nz4 ha 2 (by decide) ?_,nz4 hb 0 (by decide) ?_,nz4 (represents_add_tail ha hb) 2 (by decide) ?_⟩ <;>
    simp only [map_add,←hf0,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply] <;>
    norm_num [Finsupp.single_apply,Fin.ext_iff]


private theorem t_incoming_t_incoming5_source_five_h229 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (7,134) (9,135)
    (I.interpretation.basis .sphere 7 134 1) (I.interpretation.basis .sphere 9 135 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,7,134,[1],9,135,[4],"S0_AdamsE2_ss",2788⟩ (by
    exact List.mem_of_getElem? (i := 229) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (7,134) (9,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming5_source_five_h230 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (7,134) (9,135)
    (I.interpretation.basis .sphere 7 134 4) (I.interpretation.basis .sphere 9 135 5) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,7,134,[4],9,135,[5],"S0_AdamsE2_ss",2789⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (7,134) (9,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 134 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 9 135 [5] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming5_source_five_h231 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    (I.interpretation.basis .sphere 9 135 2) (I.interpretation.basis .sphere 13 138 0) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming5_source_five_h232 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (9,135) (13,138)
    (I.interpretation.basis .sphere 9 135 1) (I.interpretation.basis .sphere 13 138 2) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming5_source_five_h233 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    (I.interpretation.basis .sphere 9 135 0) (I.interpretation.basis .sphere 12 137 3 + I.interpretation.basis .sphere 12 137 4) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming5_source_five_h234 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (9,135) (12,137)
    (I.interpretation.basis .sphere 9 135 3) (I.interpretation.basis .sphere 12 137 3) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming5_source_five (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (9,135)) := by
  classical
  let E := sequence D .sphere
  have h229 : HasDifferential E 2 (7,134) (9,135)
      (I.interpretation.basis .sphere 7 134 1) (I.interpretation.basis .sphere 9 135 4) := t_incoming_t_incoming5_source_five_h229 I
  have h230 : HasDifferential E 2 (7,134) (9,135)
      (I.interpretation.basis .sphere 7 134 4) (I.interpretation.basis .sphere 9 135 5) := t_incoming_t_incoming5_source_five_h230 I
  have h231 : HasDifferential E 4 (9,135) (13,138)
      (I.interpretation.basis .sphere 9 135 2) (I.interpretation.basis .sphere 13 138 0) := t_incoming_t_incoming5_source_five_h231 I
  have h232 : HasDifferential E 4 (9,135) (13,138)
      (I.interpretation.basis .sphere 9 135 1) (I.interpretation.basis .sphere 13 138 2) := t_incoming_t_incoming5_source_five_h232 I
  have h233 : HasDifferential E 3 (9,135) (12,137)
      (I.interpretation.basis .sphere 9 135 0) (I.interpretation.basis .sphere 12 137 3 + I.interpretation.basis .sphere 12 137 4) := t_incoming_t_incoming5_source_five_h233 I
  have h234 : HasDifferential E 3 (9,135) (12,137)
      (I.interpretation.basis .sphere 9 135 3) (I.interpretation.basis .sphere 12 137 3) := t_incoming_t_incoming5_source_five_h234 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,9,135,["414,1", "1,1,376,1", "1,1,375,1", "0,1,394,1", "0,1,392,1", "0,7,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 174) (by rfl))
  change E.Page 2 (9,135) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 9 135 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 6) 1) = I.interpretation.basis .sphere 9 135 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 6) 1) = I.interpretation.basis .sphere 9 135 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 6) 1) = I.interpretation.basis .sphere 9 135 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 6) 1) = I.interpretation.basis .sphere 9 135 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 6) 1) = I.interpretation.basis .sphere 9 135 4 := he 4
  have he5 : e.symm (Finsupp.single (5:Fin 6) 1) = I.interpretation.basis .sphere 9 135 5 := he 5
  obtain ⟨_,a0,y0,ha0,hy0,hd0⟩ := h233
  obtain ⟨_,a3,y3,ha3,hy3,hd3⟩ := h234
  obtain ⟨_,a1,y1,ha1,hy1,hd1⟩ := h232
  obtain ⟨_,a2,y2,ha2,hy2,hd2⟩ := h231
  have d0 : E.d 3 (9,135) a0=y0 := hd0
  have d3 : E.d 3 (9,135) a3=y3 := hd3
  have d1 : E.d 4 (9,135) a1=y1 := hd1
  have d2 : E.d 4 (9,135) a2=y2 := hd2
  obtain ⟨b1,hb1⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha1
  obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha2
  have db1 : E.d 3 (9,135) b1=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) hb1 ⟨a1,ha1⟩
  have db2 : E.d 3 (9,135) b2=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) hb2 ⟨a2,ha2⟩
  obtain ⟨ny0,ny3,nys⟩ := t_incoming_t_d3_targets_independent I y0 y3 hy0 hy3
  obtain ⟨ny1,ny2,nyt⟩ := t_incoming_t_d4_targets_independent I y1 y2 hy1 hy2
  have hz4 : RepresentsOnPage E 5 (9,135) (I.interpretation.basis .sphere 9 135 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h229
  have hz5 : RepresentsOnPage E 5 (9,135) (I.interpretation.basis .sphere 9 135 5) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h230
  have hall (z : E.Page 5 (9,135)) : z=0 := by
    obtain ⟨x,hx⟩ := page_has_representative (by decide : (2:ℤ)≤5) z
    have hcb : RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 4 (e x 4)+Finsupp.single 5 (e x 5))) 0 := by
      generalize e x 4=c4,e x 5=c5
      fin_cases c4 <;> fin_cases c5
      · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 4 (0:F2)+Finsupp.single 5 (0:F2))) 0
        simpa only [Finsupp.single_zero,zero_add,add_zero,map_zero,map_add,he4,he5] using RepresentsOnPage.zero (by decide : (2:ℤ)≤5)
      · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 4 (0:F2)+Finsupp.single 5 (1:F2))) 0
        simpa only [Finsupp.single_zero,zero_add,add_zero,map_zero,map_add,he4,he5] using hz5
      · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 4 (1:F2)+Finsupp.single 5 (0:F2))) 0
        simpa only [Finsupp.single_zero,zero_add,add_zero,map_zero,map_add,he4,he5] using hz4
      · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 4 (1:F2)+Finsupp.single 5 (1:F2))) 0
        simpa only [Finsupp.single_zero,zero_add,add_zero,map_zero,map_add,he4,he5] using represents_add_tail hz4 hz5
    have hclean : x-e.symm (Finsupp.single 4 (e x 4)+Finsupp.single 5 (e x 5)) =
        e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)) := by
      apply e.injective
      simp only [map_sub,LinearEquiv.apply_symm_apply]
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp [Finsupp.sub_apply,Finsupp.add_apply,Fin.ext_iff]
    have hz := represents_sub_tail hx hcb
    rw [hclean,sub_zero] at hz
    generalize e x 0=c0,e x 1=c1,e x 2=c2,e x 3=c3 at hz
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,map_zero] at hz
      exact represents_unique hz (RepresentsOnPage.zero (by decide : (2:ℤ)≤5))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,he3] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) ha3 ⟨z,hz⟩
      exact False.elim (ny3 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,he2] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) ha2 ⟨z,hz⟩
      exact False.elim (ny2 (by simpa only [map_add,d1,d2] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he2,he3] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail hb2 ha3) ⟨z,hz⟩
      exact False.elim (ny3 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,he1] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) ha1 ⟨z,hz⟩
      exact False.elim (ny1 (by simpa only [map_add,d1,d2] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he1,he3] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail hb1 ha3) ⟨z,hz⟩
      exact False.elim (ny3 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he1,he2] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) (represents_add_tail ha1 ha2) ⟨z,hz⟩
      exact False.elim (nyt (by simpa only [map_add,d1,d2] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,zero_add,map_add,he1,he2,he3] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail (represents_add_tail hb1 hb2) ha3) ⟨z,hz⟩
      exact False.elim (ny3 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,he0] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) ha0 ⟨z,hz⟩
      exact False.elim (ny0 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,map_add,he0,he3] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail ha0 ha3) ⟨z,hz⟩
      exact False.elim (nys (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,map_add,he0,he2] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail ha0 hb2) ⟨z,hz⟩
      exact False.elim (ny0 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,map_add,he0,he2,he3] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail (represents_add_tail ha0 hb2) ha3) ⟨z,hz⟩
      exact False.elim (nys (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,map_add,he0,he1] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail ha0 hb1) ⟨z,hz⟩
      exact False.elim (ny0 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,map_add,he0,he1,he3] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail (represents_add_tail ha0 hb1) ha3) ⟨z,hz⟩
      exact False.elim (nys (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2))) z at hz
      simp only [Finsupp.single_zero,add_zero,map_add,he0,he1,he2] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail (represents_add_tail ha0 hb1) hb2) ⟨z,hz⟩
      exact False.elim (ny0 (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
    · change RepresentsOnPage E 5 (9,135) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2))) z at hz
      simp only [map_add,he0,he1,he2,he3] at hz
      have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<5) (represents_add_tail (represents_add_tail (represents_add_tail ha0 hb1) hb2) ha3) ⟨z,hz⟩
      exact False.elim (nys (by simpa only [map_add,d0,d3,db1,db2,add_zero,zero_add] using hh))
  exact ⟨fun a b=>(hall a).trans (hall b).symm⟩


private theorem t_incoming_t_incoming6_image_h176 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (6,133) (8,134)
    (I.interpretation.basis .sphere 6 133 1) (I.interpretation.basis .sphere 8 134 5) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,6,133,[1],8,134,[5],"S0_AdamsE2_ss",2634⟩ (by
    exact List.mem_of_getElem? (i := 176) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (6,133) (8,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 8 134 [5] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming6_image_h205 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (8,134) (11,136)
    (I.interpretation.basis .sphere 8 134 3) (I.interpretation.basis .sphere 11 136 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,8,134,[3],11,136,[1],"S0_AdamsE2_ss",2703⟩ (by
    exact List.mem_of_getElem? (i := 205) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,134) (11,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming6_image_h206 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (8,134) (11,136)
    (I.interpretation.basis .sphere 8 134 2) (I.interpretation.basis .sphere 11 136 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,8,134,[2],11,136,[2],"S0_AdamsE2_ss",2704⟩ (by
    exact List.mem_of_getElem? (i := 206) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (8,134) (11,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 136 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming6_image_h207 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (8,134) (10,135)
    (I.interpretation.basis .sphere 8 134 1) (I.interpretation.basis .sphere 10 135 3) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming6_image_h203 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 17 (8,134) (I.interpretation.basis .sphere 8 134 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,17,8,134,[4],8,134,[],"S0_AdamsE2_ss",2701⟩ (by
    exact List.mem_of_getElem? (i := 203) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 17 (8,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming6_image_h204 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 6 (8,134) (I.interpretation.basis .sphere 8 134 0 + I.interpretation.basis .sphere 8 134 3) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,6,8,134,[0, 3],8,134,[],"S0_AdamsE2_ss",2702⟩ (by
    exact List.mem_of_getElem? (i := 204) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 6 (8,134) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 134 [0, 3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming6_image (I : AdamsComputationTheorems D L G) :
    ∃ w : (sequence D .sphere).Page 6 (8,134),
      RepresentsOnPage (sequence D .sphere) 6 (8,134)
        (I.interpretation.basis .sphere 8 134 0+I.interpretation.basis .sphere 8 134 3) w ∧
      ∀ z : (sequence D .sphere).Page 6 (8,134),
        (sequence D .sphere).d 6 (8,134) z=0 ∨
        (sequence D .sphere).d 6 (8,134) z=(sequence D .sphere).d 6 (8,134) w := by
  classical
  let E := sequence D .sphere
  have h176 : HasDifferential E 2 (6,133) (8,134)
      (I.interpretation.basis .sphere 6 133 1) (I.interpretation.basis .sphere 8 134 5) := t_incoming_t_incoming6_image_h176 I
  have h205 : HasDifferential E 3 (8,134) (11,136)
      (I.interpretation.basis .sphere 8 134 3) (I.interpretation.basis .sphere 11 136 1) := t_incoming_t_incoming6_image_h205 I
  have h206 : HasDifferential E 3 (8,134) (11,136)
      (I.interpretation.basis .sphere 8 134 2) (I.interpretation.basis .sphere 11 136 2) := t_incoming_t_incoming6_image_h206 I
  have h207 : HasDifferential E 2 (8,134) (10,135)
      (I.interpretation.basis .sphere 8 134 1) (I.interpretation.basis .sphere 10 135 3) := t_incoming_t_incoming6_image_h207 I
  have h203 : ReachesPage E 17 (8,134) (I.interpretation.basis .sphere 8 134 4) := t_incoming_t_incoming6_image_h203 I
  have h204 : ReachesPage E 6 (8,134) (I.interpretation.basis .sphere 8 134 0 + I.interpretation.basis .sphere 8 134 3) := t_incoming_t_incoming6_image_h204 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,8,134,["395,1", "394,1", "393,1", "392,1", "69,1,85,1", "0,6,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 162) (by rfl))
  change E.Page 2 (8,134) ≃ₗ[ℤ] (Fin 6 →₀ F2) at e
  change ∀ i : Fin 6, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 8 134 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 6) 1) = I.interpretation.basis .sphere 8 134 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 6) 1) = I.interpretation.basis .sphere 8 134 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 6) 1) = I.interpretation.basis .sphere 8 134 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 6) 1) = I.interpretation.basis .sphere 8 134 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 6) 1) = I.interpretation.basis .sphere 8 134 4 := he 4
  have he5 : e.symm (Finsupp.single (5:Fin 6) 1) = I.interpretation.basis .sphere 8 134 5 := he 5
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 135 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 10 135 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 10 135 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 10 135 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 10 135 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 10 135 4 := hf 4
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,11,136,["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 192) (by rfl))
  change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
  change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 136 i.val at hk
  have hk0 : k.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 11 136 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 11 136 1 := hk 1
  have hk2 : k.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 11 136 2 := hk 2
  have hk3 : k.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 11 136 3 := hk 3
  have hk4 : k.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 11 136 4 := hk 4
  obtain ⟨w,hw⟩ := h204
  obtain ⟨b17,hb17⟩ := h203
  obtain ⟨b6,hb6⟩ := represents_before (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤17) hb17
  obtain ⟨w3,hw3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤6) hw
  obtain ⟨b3,hb3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤17) hb17
  obtain ⟨_,a3,y1,ha3,hy1,hda3⟩ := h205
  obtain ⟨_,a2,y2,ha2,hy2,hda2⟩ := h206
  have hd3a : E.d 3 (8,134) a3=y1 := hda3
  have hd2' : E.d 3 (8,134) a2=y2 := hda2
  have hdw3 : E.d 3 (8,134) w3=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hw3 ⟨w,hw⟩
  have hdb3 : E.d 3 (8,134) b3=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<17) hb3 ⟨b17,hb17⟩
  have hdb6 : E.d 6 (8,134) b6=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤6; omega) (by decide : (6:ℤ)<17) hb6 ⟨b17,hb17⟩
  have heq : (I.interpretation.basis .sphere 8 134 0+I.interpretation.basis .sphere 8 134 3)+I.interpretation.basis .sphere 8 134 3=I.interpretation.basis .sphere 8 134 0 := by
    apply e.injective
    simp only [map_add,←he0,←he3,LinearEquiv.apply_symm_apply]
    apply Finsupp.ext
    intro i
    fin_cases i <;> norm_num [Finsupp.add_apply,Finsupp.sub_apply,Finsupp.single_apply,Fin.ext_iff]; decide
  have ha0 : RepresentsOnPage E 3 (8,134) (I.interpretation.basis .sphere 8 134 0) (w3+a3) := by
    simpa only [heq] using represents_add_tail hw3 ha3
  have hd0' : E.d 3 (8,134) (w3+a3)=y1 := by rw [map_add,hdw3,hd3a,zero_add]
  have hz5 : RepresentsOnPage E 6 (8,134) (I.interpretation.basis .sphere 8 134 5) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h176
  have dz {x : E.Page 2 (8,134)} {r : ℤ} (hr : 3≤r) (hx : ReachesPage E r (8,134) x) : E.d 2 (8,134) x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by omega : (2:ℤ)<r) ha2 ⟨a,ha⟩
    simpa only [ha2.eq_on_page_two] using h
  have hd0 : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 0)=0 := dz (by decide) ⟨_,ha0⟩
  have hd1 : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 1)=I.interpretation.basis .sphere 10 135 3 := h207.eq_on_page_two.2
  have hd2 : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 2)=0 := dz (by decide) ⟨_,ha2⟩
  have hd3 : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 3)=0 := dz (by decide) ⟨_,ha3⟩
  have hd4 : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 4)=0 := dz (by decide) ⟨_,hb17⟩
  have hd5 : E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 5)=0 := dz (by decide) ⟨_,hz5⟩
  have coord1 (x : E.Page 2 (8,134)) : f (E.d 2 (8,134) x) 3=e x 1 := by
    have hall (c : Fin 6 →₀ F2) : f (E.d 2 (8,134) (e.symm c)) 3=c 1 := by
      induction c using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,Finsupp.add_apply,ih]
        congr 1
        fin_cases c
        · simp
        · change f (E.d 2 (8,134) (e.symm (Finsupp.single i 1))) 3=(Finsupp.single i (1:F2)) 1
          rw [he i]
          fin_cases i
          · change f (E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 0)) 3=(Finsupp.single (0:Fin 6) (1:F2)) 1
            rw [hd0,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 1)) 3=(Finsupp.single (1:Fin 6) (1:F2)) 1
            rw [hd1,←hf3,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 2)) 3=(Finsupp.single (2:Fin 6) (1:F2)) 1
            rw [hd2,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 3)) 3=(Finsupp.single (3:Fin 6) (1:F2)) 1
            rw [hd3,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 4)) 3=(Finsupp.single (4:Fin 6) (1:F2)) 1
            rw [hd4,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
          · change f (E.d 2 (8,134) (I.interpretation.basis .sphere 8 134 5)) 3=(Finsupp.single (5:Fin 6) (1:F2)) 1
            rw [hd5,f.map_zero]
            norm_num [Finsupp.zero_apply,Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)

  have nonzero3 {x : E.Page 2 (11,136)} {a : E.Page 3 (11,136)} (ha : RepresentsOnPage E 3 (11,136) x a) (hn : x≠0) : a≠0 := by
    obtain ⟨a2,ha2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) ha
    rw [←ha2.eq_on_page_two] at ha2
    exact represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤2; omega)
      (by decide : (2:ℤ)≤2) (by exact t_incoming_y_incoming2_zero I) ha ha2 hn
  refine ⟨w,hw,?_⟩
  intro z
  obtain ⟨x,hx⟩ := page_has_representative (by decide : (2:ℤ)≤6) z
  have hx2 : E.d 2 (8,134) x=0 := dz (by decide) ⟨z,hx⟩
  have hc1 : e x 1=0 := by
    have hh := coord1 x
    rw [hx2,f.map_zero,Finsupp.zero_apply] at hh
    exact hh.symm
  have hcb : RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 5 (e x 5))) 0 := by
    generalize e x 5=c
    fin_cases c
    · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 5 (0:F2))) 0
      simpa only [Finsupp.single_zero,map_zero] using (RepresentsOnPage.zero (by decide) : RepresentsOnPage E 6 (8,134) 0 0)
    · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 5 (1:F2))) 0
      simpa only [he5] using hz5
  have hclean : x-e.symm (Finsupp.single 5 (e x 5)) =
      e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4)) := by
    apply e.injective
    simp only [map_sub,LinearEquiv.apply_symm_apply]
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [Finsupp.sub_apply,Finsupp.add_apply,Fin.ext_iff,hc1]
  have hz := represents_sub_tail hx hcb
  rw [hclean,sub_zero] at hz
  generalize e x 0=c0,e x 2=c2,e x 3=c3,e x 4=c4 at hz
  fin_cases c0 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,map_zero] at hz
    left
    have hz0 := represents_unique hz (RepresentsOnPage.zero (by decide : (2:ℤ)≤6))
    rw [hz0,map_zero]
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,he4] at hz
    left
    have hz' := represents_unique hz hb6
    rw [hz',hdb6]
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,he3] at hz
    have hrep := ha3
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1)≠0 := by
      apply nonzero3 hy1
      intro hez
      have hez' := congrArg (fun t=>k t 1) hez
      simp only [map_zero,←hk1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he3,he4] at hz
    have hrep := (represents_add_tail ha3 hb3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1+0)≠0 := by
      apply nonzero3 (represents_add_tail hy1 (RepresentsOnPage.zero (by decide)))
      intro hez
      have hez' := congrArg (fun t=>k t 1) hez
      simp only [map_add,map_zero,←hk1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,he2] at hz
    have hrep := ha2
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y2)≠0 := by
      apply nonzero3 hy2
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_zero,←hk2,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he2,he4] at hz
    have hrep := (represents_add_tail ha2 hb3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y2+0)≠0 := by
      apply nonzero3 (represents_add_tail hy2 (RepresentsOnPage.zero (by decide)))
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,zero_add,map_add,he2,he3] at hz
    have hrep := (represents_add_tail ha2 ha3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y2+y1)≠0 := by
      apply nonzero3 (represents_add_tail hy2 hy1)
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,zero_add,map_add,he2,he3,he4] at hz
    have hrep := (represents_add_tail (represents_add_tail ha2 ha3) hb3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y2+y1+0)≠0 := by
      apply nonzero3 (represents_add_tail (represents_add_tail hy2 hy1) (RepresentsOnPage.zero (by decide)))
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,he0] at hz
    have hrep := ha0
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1)≠0 := by
      apply nonzero3 hy1
      intro hez
      have hez' := congrArg (fun t=>k t 1) hez
      simp only [map_zero,←hk1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,map_add,he0,he4] at hz
    have hrep := (represents_add_tail ha0 hb3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1+0)≠0 := by
      apply nonzero3 (represents_add_tail hy1 (RepresentsOnPage.zero (by decide)))
      intro hez
      have hez' := congrArg (fun t=>k t 1) hez
      simp only [map_add,map_zero,←hk1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,map_add,he0,he3] at hz
    right
    have hz' := represents_unique hz hw
    rw [hz']
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,map_add,he0,he3,he4] at hz
    right
    have hz' := represents_unique hz (represents_add_tail hw hb6)
    rw [hz',map_add,hdb6,add_zero]
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,map_add,he0,he2] at hz
    have hrep := (represents_add_tail ha0 ha2)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1+y2)≠0 := by
      apply nonzero3 (represents_add_tail hy1 hy2)
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,map_add,he0,he2,he4] at hz
    have hrep := (represents_add_tail (represents_add_tail ha0 ha2) hb3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1+y2+0)≠0 := by
      apply nonzero3 (represents_add_tail (represents_add_tail hy1 hy2) (RepresentsOnPage.zero (by decide)))
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2))) z at hz
    simp only [Finsupp.single_zero,add_zero,map_add,he0,he2,he3] at hz
    have hrep := (represents_add_tail (represents_add_tail ha0 ha2) ha3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1+y2+y1)≠0 := by
      apply nonzero3 (represents_add_tail (represents_add_tail hy1 hy2) hy1)
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))
  · change RepresentsOnPage E 6 (8,134) (e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2))) z at hz
    simp only [map_add,he0,he2,he3,he4] at hz
    have hrep := (represents_add_tail (represents_add_tail (represents_add_tail ha0 ha2) ha3) hb3)
    have hh := represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<6) hrep ⟨z,hz⟩
    have hn : (y1+y2+y1+0)≠0 := by
      apply nonzero3 (represents_add_tail (represents_add_tail (represents_add_tail hy1 hy2) hy1) (RepresentsOnPage.zero (by decide)))
      intro hez
      have hez' := congrArg (fun t=>k t 2) hez
      simp only [map_add,map_zero,←hk1,←hk2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hez'
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hez'
    exact False.elim (hn (by simpa only [map_add,hd0',hd2',hd3a,hdb3] using hh))


private theorem t_incoming_t_incoming7_zero_h186 (I : AdamsComputationTheorems D L G) : ReachesPage (sequence D .sphere) 18 (7,133) (I.interpretation.basis .sphere 7 133 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.reaches,18,7,133,[0],7,133,[],"S0_AdamsE2_ss",2632⟩ (by
    exact List.mem_of_getElem? (i := 186) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,hd⟩ := hrow
  change ReachesPage (sequence D .sphere) 18 (7,133) x at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 133 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
  rw [←hx] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming7_zero_h185 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (5,132) (7,133)
    (I.interpretation.basis .sphere 5 132 0) (I.interpretation.basis .sphere 7 133 1) := by
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
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming7_zero (I : AdamsComputationTheorems D L G) : (sequence D .sphere).d 7 (7,133)=0 := by
  classical
  let E := sequence D .sphere
  have h186 : ReachesPage E 18 (7,133) (I.interpretation.basis .sphere 7 133 0) := t_incoming_t_incoming7_zero_h186 I
  have h185 : HasDifferential E 2 (5,132) (7,133)
      (I.interpretation.basis .sphere 5 132 0) (I.interpretation.basis .sphere 7 133 1) := t_incoming_t_incoming7_zero_h185 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,7,133,["1,1,69,1,76,1", "0,5,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 150) (by rfl))
  change E.Page 2 (7,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 7 133 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 7 133 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 7 133 1 := he 1
  obtain ⟨a18,ha18⟩ := h186
  obtain ⟨a7,ha7⟩ := represents_before (by decide : (2:ℤ)≤7) (by decide : (7:ℤ)≤18) ha18
  have hdz : E.d 7 (7,133) a7=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤7; omega) (by decide : (7:ℤ)<18) ha7 ⟨a18,ha18⟩
  have hz : RepresentsOnPage E 7 (7,133) (I.interpretation.basis .sphere 7 133 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h185
  ext y
  change E.d 7 (7,133) y=0
  obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤7) e
    (fun i=>if i=0 then a7 else 0) (by
      intro i
      rw [he i]
      fin_cases i
      · change RepresentsOnPage E 7 (7,133) (I.interpretation.basis .sphere 7 133 0) a7
        exact ha7
      · change RepresentsOnPage E 7 (7,133) (I.interpretation.basis .sphere 7 133 1) 0
        exact hz) y
  rw [hc,map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs <;> simp [hdz]


private theorem t_incoming_t_incoming9_zero_h164 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (3,130) (5,131)
    (I.interpretation.basis .sphere 3 130 1) (I.interpretation.basis .sphere 5 131 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,3,130,[1],5,131,[0],"S0_AdamsE2_ss",2494⟩ (by
    exact List.mem_of_getElem? (i := 164) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (3,130) (5,131) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 3 130 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 5 131 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming9_zero (I : AdamsComputationTheorems D L G) : (sequence D .sphere).d 9 (5,131)=0 := by
  classical
  let E := sequence D .sphere
  have h164 : HasDifferential E 2 (3,130) (5,131)
      (I.interpretation.basis .sphere 3 130 1) (I.interpretation.basis .sphere 5 131 0) := t_incoming_t_incoming9_zero_h164 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,5,131,["0,3,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 127) (by rfl))
  change E.Page 2 (5,131) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 5 131 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 5 131 0 := he 0
  have hz : RepresentsOnPage E 9 (5,131) (I.interpretation.basis .sphere 5 131 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h164
  have hall (y : E.Page 9 (5,131)) : y=0 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤9) e (fun _=>0) (by
      intro i
      rw [he i]
      fin_cases i
      exact hz) y
    simpa using hc
  ext y
  change E.d 9 (5,131) y=0
  rw [hall y,map_zero]


private theorem t_incoming_t_incoming11_zero_h151 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (1,128) (3,129)
    (I.interpretation.basis .sphere 1 128 0) (I.interpretation.basis .sphere 3 129 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,1,128,[0],3,129,[0],"S0_AdamsE2_ss",2380⟩ (by
    exact List.mem_of_getElem? (i := 151) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (1,128) (3,129) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 1 128 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 3 129 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming11_zero (I : AdamsComputationTheorems D L G) : (sequence D .sphere).d 11 (3,129)=0 := by
  classical
  let E := sequence D .sphere
  have h151 : HasDifferential E 2 (1,128) (3,129)
      (I.interpretation.basis .sphere 1 128 0) (I.interpretation.basis .sphere 3 129 0) := t_incoming_t_incoming11_zero_h151 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,3,129,["0,1,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 108) (by rfl))
  change E.Page 2 (3,129) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 3 129 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 3 129 0 := he 0
  have hz : RepresentsOnPage E 11 (3,129) (I.interpretation.basis .sphere 3 129 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h151
  have hall (y : E.Page 11 (3,129)) : y=0 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤11) e (fun _=>0) (by
      intro i
      rw [he i]
      fin_cases i
      exact hz) y
    simpa using hc
  ext y
  change E.d 11 (3,129) y=0
  rw [hall y,map_zero]


private theorem t_incoming_t_incoming_late_zero (I : AdamsComputationTheorems D L G) (r : ℤ) (hr : 13≤r) :
    (sequence D .sphere).d r ((14,139)-(sequence D .sphere).diffDeg r)=0 := by
  classical
  let E := sequence D .sphere
  have he : Subsingleton (E.Page r ((14,139)-E.diffDeg r)) := by
    by_cases h15 : 15≤r
    · change Subsingleton (E.Page r (14-r,139-(r-1)))
      exact adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum r (14-r) (139-(r-1)) (by omega)
    · have hrs : r=13 ∨ r=14 := by omega
      rcases hrs with rfl|rfl
      · change Subsingleton (E.Page 13 (1,127))
        obtain ⟨e,he⟩ := I.basis ⟨.sphere,1,127,[]⟩ (by
          exact List.mem_of_getElem? (i := 90) (by rfl))
        change E.Page 2 (1,127) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
        change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 1 127 i.val at he
        exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 13 1 127
          (by decide) (by decide) e.injective.subsingleton
      · change Subsingleton (E.Page 14 (0,126))
        obtain ⟨e,he⟩ := I.basis ⟨.sphere,0,126,[]⟩ (by
          exact List.mem_of_getElem? (i := 77) (by rfl))
        change E.Page 2 (0,126) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
        change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 0 126 i.val at he
        exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 14 0 126
          (by decide) (by decide) e.injective.subsingleton
  ext y
  change E.d r ((14,139)-E.diffDeg r) y=0
  rw [he.elim y 0,map_zero]


private theorem t_incoming_t_incoming8_source_four_h173 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (4,131) (6,132)
    (I.interpretation.basis .sphere 4 131 0) (I.interpretation.basis .sphere 6 132 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,4,131,[0],6,132,[1],"S0_AdamsE2_ss",2573⟩ (by
    exact List.mem_of_getElem? (i := 173) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (4,131) (6,132) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 6 132 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming8_source_four (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (6,132)) := by
  classical
  let E := sequence D .sphere
  have h173 : HasDifferential E 2 (4,131) (6,132)
      (I.interpretation.basis .sphere 4 131 0) (I.interpretation.basis .sphere 6 132 1) := t_incoming_t_incoming8_source_four_h173 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,6,132,["368,1", "0,4,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 138) (by rfl))
  change E.Page 2 (6,132) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 6 132 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 6 132 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 6 132 1 := he 1
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
  have hz1 : RepresentsOnPage E 4 (6,132) (I.interpretation.basis .sphere 6 132 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h173
  have hn {a : E.Page 4 (6,132)} (ha : RepresentsOnPage E 4 (6,132) (I.interpretation.basis .sphere 6 132 0) a) : False := by
    obtain ⟨a3,ha3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
    have hd : E.d 3 (6,132) a3=0 := represents_d_zero_of_later
      (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) ha3 ⟨a,ha⟩
    apply n659
    refine ⟨rfl,a3,0,ha3,RepresentsOnPage.zero (by decide),?_⟩
    exact hd
  have hall (a : E.Page 4 (6,132)) : a=0 := by
    let A := E.ssData (6,132)
    haveI : Epi (A.pageπ 2) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 2)).mp inferInstance a
    let x := (Subobject.ofLE (A.Z 2) (A.Z 0) (A.Z_anti (by decide : (0:WithTop ℕ)≤2)) ≫ A.pageπ 0) z
    have hx : RepresentsOnPage E 4 (6,132) x a := ⟨by decide,z,rfl,hz⟩
    have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0=c0 at hxe
    generalize hc1 : e x 1=c1 at hxe
    fin_cases c0 <;> fin_cases c1
    · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,e.symm.map_zero] at hxe
      rw [hxe] at hx
      exact represents_unique hx (RepresentsOnPage.zero (by decide))
    · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,he1] at hxe
      rw [hxe] at hx
      exact represents_unique hx hz1
    · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,he0] at hxe
      rw [hxe] at hx
      exact False.elim (hn hx)
    · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)) at hxe
      simp only [map_add,he0,he1] at hxe
      rw [hxe] at hx
      have hh := represents_add_tail hx hz1
      have heq : (I.interpretation.basis .sphere 6 132 0 + I.interpretation.basis .sphere 6 132 1) + I.interpretation.basis .sphere 6 132 1 = I.interpretation.basis .sphere 6 132 0 := by
        apply e.injective
        simp only [map_add,←he0,←he1,LinearEquiv.apply_symm_apply]
        apply Finsupp.ext
        intro i
        fin_cases i <;> norm_num [Finsupp.add_apply,Finsupp.single_apply,Fin.ext_iff]; decide
      rw [heq,add_zero] at hh
      exact False.elim (hn hh)
  exact ⟨fun a b=>(hall a).trans (hall b).symm⟩


private theorem x1264_d3_coordinate
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I : AdamsComputationTheorems D L G) :
    HasNonzeroDifferential (sequence D .sphere) 3 (4,130) (7,132)
      (I.interpretation.basis .sphere 4 130 0) (I.interpretation.basis .sphere 7 132 0) := by
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
  obtain ⟨hdeg,xr,yr,hxr,hyr,hd⟩ := h655
  refine ⟨hdeg,xr,yr,hxr,hyr,hd,?_⟩
  have bne : I.interpretation.basis .sphere 7 132 0≠0 := by
    rw [show I.interpretation.basis .sphere 7 132 0 = e7_132.symm (Finsupp.single 0 1) from (he7_132 0).symm]
    exact basis_vector_ne_zero e7_132 0
  exact represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)≤2)
    d2_5 hyr (hrep2 _) bne


private theorem t_incoming_t_incoming10_source_four_h156 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (2,129) (4,130)
    (I.interpretation.basis .sphere 2 129 0) (I.interpretation.basis .sphere 4 130 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,2,129,[0],4,130,[1],"S0_AdamsE2_ss",2436⟩ (by
    exact List.mem_of_getElem? (i := 156) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (2,129) (4,130) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 2 129 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 4 130 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem t_incoming_t_incoming10_source_four (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (4,130)) := by
  classical
  let E := sequence D .sphere
  have h156 : HasDifferential E 2 (2,129) (4,130)
      (I.interpretation.basis .sphere 2 129 0) (I.interpretation.basis .sphere 4 130 1) := t_incoming_t_incoming10_source_four_h156 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,4,130,["341,1", "0,2,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 119) (by rfl))
  change E.Page 2 (4,130) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 4 130 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 4 130 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 4 130 1 := he 1
  obtain ⟨_,a3,b3,ha3,hb3,hd,hbn⟩ := x1264_d3_coordinate I
  have hd3 : E.d 3 (4,130) a3=b3 := hd
  have hz1 : RepresentsOnPage E 3 (4,130) (I.interpretation.basis .sphere 4 130 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h156
  have frame (a : E.Page 3 (4,130)) : a=0 ∨ a=a3 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e
      (fun i=>if i=0 then a3 else 0) (by
        intro i
        rw [he i]
        fin_cases i
        · change RepresentsOnPage E 3 (4,130) (I.interpretation.basis .sphere 4 130 0) a3
          exact ha3
        · change RepresentsOnPage E 3 (4,130) (I.interpretation.basis .sphere 4 130 1) 0
          exact hz1) a
    simp only [Fin.sum_univ_two] at hc
    change a=(if c 0=0 then 0 else a3)+(if c 1=0 then 0 else 0) at hc
    simp only [ite_self,add_zero] at hc
    by_cases hc0 : c 0=0
    · exact Or.inl (by simpa only [hc0,ite_true] using hc)
    · exact Or.inr (by simpa only [hc0,ite_false] using hc)
  have ker0 (a : E.Page 3 (4,130)) (ha : E.d 3 (4,130) a=0) : a=0 := by
    rcases frame a with h|rfl
    · exact h
    · exact False.elim (hbn (hd3.symm.trans ha))
  have hall (a : E.Page 4 (4,130)) : a=0 := by
    have h := next_page_two_of_kernel E 3 (by change (2:ℤ)≤3; omega) (4,130) 0
      (fun b hb=>Or.inl (ker0 b hb)) a
    rcases h with h|h
    · exact h
    · simpa only [map_zero] using h
  exact ⟨fun a b=>(hall a).trans (hall b).symm⟩


private theorem t_incoming_t_incoming12 (I : AdamsComputationTheorems D L G)
    (hit : HitOnPage (sequence D .sphere) 12 (14,139) (I.interpretation.sphere 14 139 T)) :
    Derived.Differential I.interpretation 12 dataH6Sq T := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,2,128,["69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 100) (by rfl))
  change E.Page 2 (2,128) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 2 128 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 2 128 0 := he 0
  have label : I.interpretation.sphere 2 128 dataH6Sq=I.interpretation.basis .sphere 2 128 0 := by
    have hc := I.monomials (⟨.sphere,2,128,["69,2"]⟩ : Raw.Degree) (by
      exact List.mem_of_getElem? (i := 100) (by rfl)) rfl
    obtain ⟨z,hz,he⟩ := hc (0 : Fin 1)
    have heq : dataH6Sq=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨69,by decide⟩ ^ 2 = projection (monomialOfString "69,2")
      have hs : "69,2"≠"" := by decide
      have hp : (("69,2".splitOn ",").map (fun n=>n.toNat?.getD 0))=[69,2] := by
        have split : "69,2".splitOn ","=["69","2"] := by simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString,if_neg hs,hp]
      norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,map_pow,pow_two]
    rw [heq]
    exact he
  obtain ⟨p,hp,z,y,hy,hyn,hd⟩ := hit
  have hq : p=(2,128) := add_right_cancel (hp.trans (show (14,139)=(2,128)+E.diffDeg 12 from rfl))
  subst p
  have hd' : E.d 12 (2,128) z=y := hd
  let A := E.ssData (2,128)
  haveI : Epi (A.pageπ 10) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨c,hc⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 10)).mp inferInstance z
  let x := (Subobject.ofLE (A.Z 10) (A.Z 0) (A.Z_anti (by decide : (0:WithTop ℕ)≤10)) ≫ A.pageπ 0) c
  have hx : RepresentsOnPage E 12 (2,128) x z := ⟨by decide,c,rfl,hc⟩
  have hcases : x=0 ∨ x=I.interpretation.basis .sphere 2 128 0 := by
    have h : e x 0=0 ∨ e x 0=1 := by generalize e x 0=a; fin_cases a <;> simp
    rcases h with h|h
    · left
      apply e.injective
      apply Finsupp.ext
      intro i
      fin_cases i
      simpa using h
    · right
      rw [←he0]
      apply e.injective
      apply Finsupp.ext
      intro i
      fin_cases i
      simpa using h
  rcases hcases with h|h
  · rw [h] at hx
    have hz : z=0 := represents_unique hx (RepresentsOnPage.zero (by decide))
    exact False.elim (hyn (hd'.symm.trans (by rw [hz,map_zero])))
  · rw [h] at hx
    refine ⟨rfl,z,y,?_,hy,hd,hyn⟩
    rw [label]
    exact hx

private theorem t_only_incoming_h153 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (3,130) (5,131) (I.interpretation.basis .sphere 3 130 1) (I.interpretation.basis .sphere 5 131 0) := by
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

private theorem t_only_incoming_h655 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (4,130) (7,132) (I.interpretation.basis .sphere 4 130 0) (I.interpretation.basis .sphere 7 132 0) := by
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

private theorem t_only_incoming (I : AdamsComputationTheorems D L G) : Derived.OnlyIncomingT I.interpretation := by
  classical


  let E := sequence D .sphere
  have nohit (r : ℤ) (hd : E.d r ((14,139)-E.diffDeg r)=0) :
      ¬HitOnPage E r (14,139) (I.interpretation.sphere 14 139 T) := by
    rintro ⟨p,hp,z,y,hy,hyn,hzy⟩
    have he : p=(14,139)-E.diffDeg r := eq_sub_iff_add_eq.mpr hp
    subst p
    rw [hd] at hzy
    have hez : y=0 := by simpa using hzy.symm
    exact hyn hez
  have h6 (hit : HitOnPage E 6 (14,139) (I.interpretation.sphere 14 139 T)) :
      Derived.Differential I.interpretation 6 W T := by
    obtain ⟨p,hp,z,y,hy,hyn,hd⟩ := hit
    have hq : p=(8,134) := add_right_cancel (hp.trans (show (14,139)=(8,134)+E.diffDeg 6 from rfl))
    subst p
    have hd' : E.d 6 (8,134) z=y := hd
    obtain ⟨w,hw,hframe⟩ := t_incoming_t_incoming6_image I
    rcases hframe z with hz|hz
    · exact False.elim (hyn (hd'.symm.trans hz))
    · refine ⟨rfl,w,y,?_,hy,?_,hyn⟩
      · rw [t_incoming_w_label I]
        exact hw
      · change E.d 6 (8,134) w=y
        exact hz.symm.trans hd'
  intro r hit
  have hr : 2≤r := by
    obtain ⟨_,_,_,_,hy,_,_⟩ := hit
    exact hy.1
  by_cases hl : 13≤r
  · exact False.elim (nohit r (t_incoming_t_incoming_late_zero I r hl) hit)
  have hr' : r≤12 := by omega
  interval_cases r
  · exact False.elim (t_incoming_t_incoming2_not_hit I (by simpa only [t_incoming_t_label I] using hit))
  · exact False.elim (nohit 3 (by exact t_incoming_t_incoming3_zero I) hit)
  · exact False.elim (nohit 4 (by exact t_incoming_t_incoming4_zero I) hit)
  · have hs := t_incoming_t_incoming5_source_five I
    apply False.elim (nohit 5 ?_ hit)
    ext x
    change E.d 5 (9,135) x=0
    rw [hs.elim x 0,map_zero]
  · exact Or.inl ⟨rfl,h6 hit⟩
  · exact False.elim (nohit 7 (by exact t_incoming_t_incoming7_zero I) hit)
  · have hs : Subsingleton (E.Page 8 (6,132)) :=
      adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 8 6 132 (by decide) (by decide) (t_incoming_t_incoming8_source_four I)
    apply False.elim (nohit 8 ?_ hit)
    ext x
    change E.d 8 (6,132) x=0
    rw [hs.elim x 0,map_zero]
  · exact False.elim (nohit 9 (by exact t_incoming_t_incoming9_zero I) hit)
  · have hs : Subsingleton (E.Page 10 (4,130)) :=
      adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 10 4 130 (by decide) (by decide) (t_incoming_t_incoming10_source_four I)
    apply False.elim (nohit 10 ?_ hit)
    ext x
    change E.d 10 (4,130) x=0
    rw [hs.elim x 0,map_zero]
  · exact False.elim (nohit 11 (by exact t_incoming_t_incoming11_zero I) hit)
  · exact Or.inr ⟨rfl,t_incoming_t_incoming12 I hit⟩

private theorem sphere_t_incoming_and_survival (I : AdamsComputationTheorems D L G) (V : SphereVanishingLine H) :
    (IsPermanentCycle (sequence D .sphere) (14,139) (I.interpretation.sphere 14 139 T)) ∧
    (Derived.Survival I.interpretation 6 W) ∧
    (DifferentialTargets (sequence D .sphere) 6 (8,134)
        (I.interpretation.sphere 8 134 W) (I.interpretation.sphere 14 139 T)) ∧
    (Derived.OnlyIncomingT I.interpretation) := by
  classical
  exact ⟨t_permanent_cycle I V, w_to_e6 I, w_d6_targets I, t_only_incoming I⟩

end SphereFactsProof

end
end KIP126.Computation.SphereAndCofiber
end
