module

public import KIP126.Main.Computation.SphereAndCofiber.Bounds
public import KIP126.Main.Computation.SphereAndCofiber.Stem125Vanishing

/-! The nonzero filtration-15 and filtration-18 fifth differentials. -/

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
/-- The AF15 source is NONZERO on E5: the selected S0_ss3152 equation is
d5(h1*x124,14)=d0^2*[Delta Delta1 g]. Nonzero follows from reconstruction
of both E5 components, not from the equation alone. In particular it would
be false to extend `stem125_e5_zero_finite` down to all s>=15, s!=25. -/
private theorem af17_three_h387 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (17,142) (19,143)
    (I.interpretation.basis .sphere 17 142 1) (I.interpretation.basis .sphere 19 143 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,17,142,[1],19,143,[1],"S0_AdamsE2_ss",3320⟩ (by
    exact List.mem_of_getElem? (i := 387) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (17,142) (19,143) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 17 142 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 19 143 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af17_three_h386 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (15,141) (17,142)
    (I.interpretation.basis .sphere 15 141 0) (I.interpretation.basis .sphere 17 142 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,15,141,[0],17,142,[0],"S0_AdamsE2_ss",3319⟩ (by
    exact List.mem_of_getElem? (i := 386) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (15,141) (17,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 141 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 142 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af17_three (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 3 (17,142)) := by
  classical
  let E := sequence D .sphere
  have h387 : HasDifferential E 2 (17,142) (19,143)
      (I.interpretation.basis .sphere 17 142 1) (I.interpretation.basis .sphere 19 143 1) := af17_three_h387 I
  have h386 : HasDifferential E 2 (15,141) (17,142)
      (I.interpretation.basis .sphere 15 141 0) (I.interpretation.basis .sphere 17 142 0) := af17_three_h386 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,17,142,["0,2,67,1,107,1", "0,3,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 240) (by rfl))
  change E.Page 2 (17,142) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 17 142 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 17 142 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 17 142 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,19,143,["8,1,293,1", "0,5,440,1"]⟩ (by
    exact List.mem_of_getElem? (i := 251) (by rfl))
  change E.Page 2 (19,143) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 19 143 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 19 143 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 19 143 1 := hf 1
  have hd1 : E.d 2 (17,142) (I.interpretation.basis .sphere 17 142 1) =
      I.interpretation.basis .sphere 19 143 1 := h387.eq_on_page_two.2
  have hz0 : RepresentsOnPage E 3 (17,142) (I.interpretation.basis .sphere 17 142 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h386
  have hd0 : E.d 2 (17,142) (I.interpretation.basis .sphere 17 142 0) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hz0
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz0⟩
  apply third_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (17,142)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  fin_cases c0 <;> fin_cases c1
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(17,142)) (r:=3) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [he1, hd1] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he0]
    simpa only [zero_add] using (hz0)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval


private theorem af16_d4_zero_h369 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (14,140) (16,141)
    (I.interpretation.basis .sphere 14 140 1) (I.interpretation.basis .sphere 16 141 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,14,140,[1],16,141,[2],"S0_AdamsE2_ss",3253⟩ (by
    exact List.mem_of_getElem? (i := 369) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,140) (16,141) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 140 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af16_d4_zero_h370 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (12,138) (16,141)
    (I.interpretation.basis .sphere 12 138 3) (I.interpretation.basis .sphere 16 141 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,12,138,[3],16,141,[1],"S0_AdamsE2_ss",3254⟩ (by
    exact List.mem_of_getElem? (i := 370) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (12,138) (16,141) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af16_d4_zero_h371 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (16,141) (18,142)
    (I.interpretation.basis .sphere 16 141 0) (I.interpretation.basis .sphere 18 142 0 + I.interpretation.basis .sphere 18 142 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,16,141,[0],18,142,[0, 1],"S0_AdamsE2_ss",3255⟩ (by
    exact List.mem_of_getElem? (i := 371) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (16,141) (18,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 16 141 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 142 [0, 1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af16_d4_zero_h372 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (16,141) (18,142)
    (I.interpretation.basis .sphere 16 141 3) (I.interpretation.basis .sphere 18 142 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,16,141,[3],18,142,[1],"S0_AdamsE2_ss",3256⟩ (by
    exact List.mem_of_getElem? (i := 372) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (16,141) (18,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 16 141 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 142 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af16_d4_zero (I : AdamsComputationTheorems D L G) : (sequence D .sphere).d 4 (16,141)=0 := by
  classical
  let E := sequence D .sphere
  have h369 : HasDifferential E 2 (14,140) (16,141)
      (I.interpretation.basis .sphere 14 140 1) (I.interpretation.basis .sphere 16 141 2) := af16_d4_zero_h369 I
  have h370 : HasDifferential E 4 (12,138) (16,141)
      (I.interpretation.basis .sphere 12 138 3) (I.interpretation.basis .sphere 16 141 1) := af16_d4_zero_h370 I
  have h371 : HasDifferential E 2 (16,141) (18,142)
      (I.interpretation.basis .sphere 16 141 0) (I.interpretation.basis .sphere 18 142 0 + I.interpretation.basis .sphere 18 142 1) := af16_d4_zero_h371 I
  have h372 : HasDifferential E 2 (16,141) (18,142)
      (I.interpretation.basis .sphere 16 141 3) (I.interpretation.basis .sphere 18 142 1) := af16_d4_zero_h372 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,16,141,["473,1", "1,1,448,1", "0,1,67,1,107,1", "0,2,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 232) (by rfl))
  change E.Page 2 (16,141) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 141 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 16 141 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 16 141 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 16 141 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 16 141 3 := he 3
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,18,142,["0,1,472,1", "0,4,440,1"]⟩ (by
    exact List.mem_of_getElem? (i := 245) (by rfl))
  change E.Page 2 (18,142) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 18 142 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 18 142 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 18 142 1 := hf 1
  obtain ⟨_,u,v,hu,hv,hd⟩ := h370
  have hd' : E.d 4 (12,138) u=v := hd
  have hdv : E.d 4 (16,141) v=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=4) (p:=(12,138)) ⟨u,hd'⟩
  have hv2 : RepresentsOnPage E 2 (16,141) (I.interpretation.basis .sphere 16 141 1)
      (I.interpretation.basis .sphere 16 141 1) := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hv
    rw [←hb.eq_on_page_two] at hb
    exact hb
  have hd1 : E.d 2 (16,141) (I.interpretation.basis .sphere 16 141 1)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hv2 ⟨v,hv⟩
  have hz2 : RepresentsOnPage E 4 (16,141) (I.interpretation.basis .sphere 16 141 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h369
  have hd2 : E.d 2 (16,141) (I.interpretation.basis .sphere 16 141 2)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hz2
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz2⟩
  have hd0 : E.d 2 (16,141) (I.interpretation.basis .sphere 16 141 0) =
      I.interpretation.basis .sphere 18 142 0 + I.interpretation.basis .sphere 18 142 1 := h371.eq_on_page_two.2
  have hd3 : E.d 2 (16,141) (I.interpretation.basis .sphere 16 141 3) =
      I.interpretation.basis .sphere 18 142 1 := h372.eq_on_page_two.2
  apply fourth_d_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (16,141)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  generalize hc3 : e x 3=c3 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact ⟨0,RepresentsOnPage.zero (by decide),map_zero _⟩
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he3, hd3] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he2]
    exact ⟨0,hz2,map_zero _⟩
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he2, he3, hd2, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    exact ⟨v,hv,hdv⟩
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he3, hd1, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1, he2]
    exact ⟨v+0,represents_add_tail hv hz2,by rw [map_add,hdv,map_zero,add_zero]⟩
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he3, hd0, hd3] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, hd0, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, he3, hd0, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he3, hd0, hd1, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0,←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval


private theorem af15_d5_target_nonzero_h397 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 5 (13,139) (18,143)
    (I.interpretation.basis .sphere 13 139 0) (I.interpretation.basis .sphere 18 143 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,5,13,139,[0],18,143,[0],"S0_AdamsE2_ss",3391⟩ (by
    exact List.mem_of_getElem? (i := 397) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (13,139) (18,143) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 139 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 143 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af15_d5_target_nonzero_h398 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (18,143) (20,144)
    (I.interpretation.basis .sphere 18 143 1) (I.interpretation.basis .sphere 20 144 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,18,143,[1],20,144,[1],"S0_AdamsE2_ss",3392⟩ (by
    exact List.mem_of_getElem? (i := 398) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (18,143) (20,144) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 18 143 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 20 144 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af15_d5_target_nonzero (I : AdamsComputationTheorems D L G)
    (y : (sequence D .sphere).Page 5 (20,144))
    (hy : RepresentsOnPage (sequence D .sphere) 5 (20,144)
      (I.interpretation.basis .sphere 20 144 0) y) : y ≠ 0 := by
  classical
  let E := sequence D .sphere
  have h397 : HasDifferential E 5 (13,139) (18,143)
      (I.interpretation.basis .sphere 13 139 0) (I.interpretation.basis .sphere 18 143 0) := af15_d5_target_nonzero_h397 I
  have h398 : HasDifferential E 2 (18,143) (20,144)
      (I.interpretation.basis .sphere 18 143 1) (I.interpretation.basis .sphere 20 144 1) := af15_d5_target_nonzero_h398 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,18,143,["8,2,209,1", "0,4,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 246) (by rfl))
  change E.Page 2 (18,143) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 18 143 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 18 143 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 18 143 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,20,144,["8,2,212,1", "0,6,440,1"]⟩ (by
    exact List.mem_of_getElem? (i := 256) (by rfl))
  change E.Page 2 (20,144) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 20 144 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 20 144 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 20 144 1 := hf 1
  obtain ⟨_,u,v,hu,hv,hd⟩ := h397
  have hb0 : RepresentsOnPage E 2 (18,143) (I.interpretation.basis .sphere 18 143 0)
      (I.interpretation.basis .sphere 18 143 0) := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hv
    rw [←hb.eq_on_page_two] at hb
    exact hb
  have hd0 : E.d 2 (18,143) (I.interpretation.basis .sphere 18 143 0)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb0 ⟨v,hv⟩
  have hd1 : E.d 2 (18,143) (I.interpretation.basis .sphere 18 143 1)=I.interpretation.basis .sphere 20 144 1 := h398.eq_on_page_two.2
  have hcoord (x : E.Page 2 (18,143)) : f (E.d 2 (18,143) x) 0=0 := by
    have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0=c0 at hxe
    generalize hc1 : e x 1=c1 at hxe
    fin_cases c0 <;> fin_cases c1
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
      rw [hxe]
      simp only [map_zero]
      norm_num [Finsupp.single_apply,Fin.ext_iff]
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add] at hxe
      rw [hxe]
      simp only [he1,hd1,←hf1,LinearEquiv.apply_symm_apply]
      norm_num [Finsupp.single_apply,Fin.ext_iff]
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero] at hxe
      rw [hxe]
      simp only [map_zero,he0,hd0]
      norm_num [Finsupp.single_apply,Fin.ext_iff]
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
      simp only [map_add] at hxe
      rw [hxe]
      simp only [map_add,he0,he1,hd0,hd1,zero_add,←hf1,LinearEquiv.apply_symm_apply]
      norm_num [Finsupp.single_apply,Fin.ext_iff]
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) hy
  have ny3 : y3 ≠ 0 := by
    intro hz
    obtain ⟨_,zz,hzz,hzzy⟩ := hy3
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (18,143) zz).mp (hzzy.trans hz)
    change (Subobject.ofLE _ _ ((E.ssData (20,144)).Z_anti bot_le) ≫ (E.ssData (20,144)).pageπ 0) zz ∈ LinearMap.range (E.d 2 (18,143)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (20,144)).Z_anti bot_le) ≫ (E.ssData (20,144)).pageπ 0) zz = I.interpretation.basis .sphere 20 144 0 at hzz
    rw [hzz] at hh
    obtain ⟨q,hq⟩ := hh
    have hh := hcoord q
    rw [hq,←hf0,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  have in3 : E.d 3 ((20,144)-E.diffDeg 3)=0 := by
    ext a
    change E.d 3 (17,142) a=0
    rw [(af17_three I).elim a 0,map_zero]
  have in4 : E.d 4 ((20,144)-E.diffDeg 4)=0 := af16_d4_zero I
  obtain ⟨y4,hy4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hy
  have ny4 : y4 ≠ 0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) in3 hy4 hy3 ny3
  exact represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤4; omega) (by decide : (2:ℤ)≤4) in4 hy hy4 ny4

private theorem stem125_af15_nonzero_d5_h356 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 5 (15,140) (20,144)
    (I.interpretation.basis .sphere 15 140 2) (I.interpretation.basis .sphere 20 144 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,5,15,140,[2],20,144,[0],"S0_AdamsE2_ss",3152⟩ (by
    exact List.mem_of_getElem? (i := 356) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (15,140) (20,144) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 140 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 20 144 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

theorem stem125_af15_nonzero_d5 (I : AdamsComputationTheorems D L G) :
    ∃ (x : Page D .sphere 15 140) (y : Page D .sphere 20 144),
      I.interpretation.coordinateSum .sphere 15 140 [2] = some x ∧
      I.interpretation.coordinateSum .sphere 20 144 [0] = some y ∧
      HasNonzeroDifferential (sequence D .sphere) 5 (15,140) (20,144) x y := by
  classical

  let E := sequence D .sphere
  have h356 : HasDifferential E 5 (15,140) (20,144)
      (I.interpretation.basis .sphere 15 140 2) (I.interpretation.basis .sphere 20 144 0) := stem125_af15_nonzero_d5_h356 I
  refine ⟨I.interpretation.basis .sphere 15 140 2,I.interpretation.basis .sphere 20 144 0,?_,?_,?_⟩
  · have h : Raw.coordinatesValid Raw.degrees .sphere 15 140 [2] = true := rfl
    simp only [E2Interpretation.coordinateSum,h,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  · have h : Raw.coordinatesValid Raw.degrees .sphere 20 144 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,h,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  · obtain ⟨hp,xr,yr,hxr,hyr,hd⟩ := h356
    exact ⟨hp,xr,yr,hxr,hyr,hd,af15_d5_target_nonzero I yr hyr⟩
end

section
open CategoryTheory.Limits KIP126.Algebra KIP126.Computation.Near126 in
/-- The AF18 target is NONZERO on E5: S0_ss3083/3391 give
d5(h1*x125,12,2)=d0^2*x97,10. It disappears on E6. Its synthetic lifts
require a separate torsion and higher-filtration argument at weight130;
they cannot be discarded by declaring the classical E5 component zero. -/
private theorem af15_three_for_incoming_h359 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (13,140) (15,141)
    ((I.interpretation.basis .sphere 13 140 4)) ((I.interpretation.basis .sphere 15 141 1)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,13,140,[4],15,141,[1],"S0_AdamsE2_ss",3257⟩ (by
    exact List.mem_of_getElem? (i := 359) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (13,140) (15,141) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 140 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 141 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af15_three_for_incoming_h360 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (15,141) (17,142)
    ((I.interpretation.basis .sphere 15 141 0)) ((I.interpretation.basis .sphere 17 142 0)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,15,141,[0],17,142,[0],"S0_AdamsE2_ss",3258⟩ (by
    exact List.mem_of_getElem? (i := 360) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (15,141) (17,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 141 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 142 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af15_three_for_incoming (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 3 (15,141)) := by
  classical
  let E := sequence D .sphere
  have h359 : HasDifferential E 2 (13,140) (15,141)
      ((I.interpretation.basis .sphere 13 140 4)) ((I.interpretation.basis .sphere 15 141 1)) := af15_three_for_incoming_h359 I
  have h360 : HasDifferential E 2 (15,141) (17,142)
      ((I.interpretation.basis .sphere 15 141 0)) ((I.interpretation.basis .sphere 17 142 0)) := af15_three_for_incoming_h360 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,15,141,["0,1,68,1,107,1", "0,13,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 225) (by rfl))
  change E.Page 2 (15,141) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 15 141 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,17,142,["0,2,67,1,107,1", "0,3,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 240) (by rfl))
  change E.Page 2 (17,142) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 17 142 i.val at hf
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 15 141 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 15 141 1 := he 1
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 17 142 0 := hf 0
  have hd0 : E.d 2 (15,141) (I.interpretation.basis .sphere 15 141 0) =
      I.interpretation.basis .sphere 17 142 0 := h360.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 3 (15,141) (I.interpretation.basis .sphere 15 141 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h359
  have hd1 : E.d 2 (15,141) (I.interpretation.basis .sphere 15 141 1)=0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h359
    have hd' : E.d 2 (13,140) x=y := hd
    have heq := hy.eq_on_page_two
    rw [heq]
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(13,140)) ⟨x,hd'⟩
  apply third_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (15,141)
  intro x hx
  have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) := by
    ext i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  fin_cases c0 <;> fin_cases c1
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,zero_add] at hxe
    rw [hxe]
    exact RepresentsOnPage.zero (by decide)
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,he1] at hxe
    rw [hxe]
    exact hz1
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero,he0] at hxe
    rw [hxe,hd0] at hx
    have hh := congrArg (fun y => f y 0) hx
    rw [←hf0,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    rw [map_add,he0,he1] at hxe
    rw [hxe,map_add,hd0,hd1,add_zero] at hx
    have hh := congrArg (fun y => f y 0) hx
    rw [←hf0,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh


private theorem af14_d4_zero_for_incoming_h344 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (12,139) (14,140)
    ((I.interpretation.basis .sphere 12 139 2)) ((I.interpretation.basis .sphere 14 140 3)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,12,139,[2],14,140,[3],"S0_AdamsE2_ss",3155⟩ (by
    exact List.mem_of_getElem? (i := 344) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (12,139) (14,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 139 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 140 [3] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af14_d4_zero_for_incoming_h345 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (10,137) (14,140)
    ((I.interpretation.basis .sphere 10 137 4)) ((I.interpretation.basis .sphere 14 140 0)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,10,137,[4],14,140,[0],"S0_AdamsE2_ss",3156⟩ (by
    exact List.mem_of_getElem? (i := 345) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (10,137) (14,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 137 [4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 140 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af14_d4_zero_for_incoming_h346 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 5 (9,136) (14,140)
    ((I.interpretation.basis .sphere 9 136 0)) ((I.interpretation.basis .sphere 14 140 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,5,9,136,[0],14,140,[2],"S0_AdamsE2_ss",3157⟩ (by
    exact List.mem_of_getElem? (i := 346) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (9,136) (14,140) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 140 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af14_d4_zero_for_incoming_h347 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (14,140) (16,141)
    ((I.interpretation.basis .sphere 14 140 1)) ((I.interpretation.basis .sphere 16 141 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,14,140,[1],16,141,[2],"S0_AdamsE2_ss",3158⟩ (by
    exact List.mem_of_getElem? (i := 347) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,140) (16,141) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 140 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 141 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af14_d4_zero_for_incoming (I : AdamsComputationTheorems D L G) :
    (sequence D .sphere).d 4 (14,140) = 0 := by
  classical
  let E := sequence D .sphere
  have h344 : HasDifferential E 2 (12,139) (14,140)
      ((I.interpretation.basis .sphere 12 139 2)) ((I.interpretation.basis .sphere 14 140 3)) := af14_d4_zero_for_incoming_h344 I
  have h345 : HasDifferential E 4 (10,137) (14,140)
      ((I.interpretation.basis .sphere 10 137 4)) ((I.interpretation.basis .sphere 14 140 0)) := af14_d4_zero_for_incoming_h345 I
  have h346 : HasDifferential E 5 (9,136) (14,140)
      ((I.interpretation.basis .sphere 9 136 0)) ((I.interpretation.basis .sphere 14 140 2)) := af14_d4_zero_for_incoming_h346 I
  have h347 : HasDifferential E 2 (14,140) (16,141)
      ((I.interpretation.basis .sphere 14 140 1)) ((I.interpretation.basis .sphere 16 141 2)) := af14_d4_zero_for_incoming_h347 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,14,140,["457,1", "68,1,107,1", "1,1,3,1,335,1", "0,12,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 218) (by rfl))
  change E.Page 2 (14,140) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 140 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,16,141,["473,1", "1,1,448,1", "0,1,67,1,107,1", "0,2,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 232) (by rfl))
  change E.Page 2 (16,141) ≃ₗ[ℤ] (Fin 4 →₀ F2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 141 i.val at hf
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 14 140 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 14 140 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 14 140 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 14 140 3 := he 3
  have hf0 : f.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 16 141 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 16 141 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 16 141 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 16 141 3 := hf 3
  obtain ⟨_,u0,v0,hu0,hv0,hd0'⟩ := h345
  have hd0'': E.d 4 (10,137) u0=v0 := hd0'
  have hv0d : E.d 4 (14,140) v0=0 := IsPageBoundary.d_eq_zero (E:=E) (r:=4) (p:=(10,137)) ⟨u0,hd0''⟩
  obtain ⟨_,u2,v2,hu2,hv2,hd2'⟩ := h346
  obtain ⟨v24,hv24⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hv2
  have hv24d : E.d 4 (14,140) v24=0 := represents_d_zero_of_later
    (by change (2:ℤ)≤4; omega) (by decide) hv24 ⟨v2,hv2⟩
  have hz3 : RepresentsOnPage E 4 (14,140) (I.interpretation.basis .sphere 14 140 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h344
  have hd0 : E.d 2 (14,140) (I.interpretation.basis .sphere 14 140 0)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hv0
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨v0,hv0⟩
  have hd2 : E.d 2 (14,140) (I.interpretation.basis .sphere 14 140 2)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hv2
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨v2,hv2⟩
  have hd3 : E.d 2 (14,140) (I.interpretation.basis .sphere 14 140 3)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hz3
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz3⟩
  have hd1 : E.d 2 (14,140) (I.interpretation.basis .sphere 14 140 1) =
      I.interpretation.basis .sphere 16 141 2 := h347.eq_on_page_two.2
  apply fourth_d_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (14,140)
  intro x hx
  have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) := by
    ext i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  generalize hc3 : e x 3=c3 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe]
    exact ⟨0,RepresentsOnPage.zero (by decide),map_zero _⟩
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero,he3] at hxe
    rw [hxe]
    exact ⟨0,hz3,map_zero _⟩
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero,he2] at hxe
    rw [hxe]
    exact ⟨v24,hv24,hv24d⟩
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero,he2,he3] at hxe
    rw [hxe]
    exact ⟨v24 + 0,(represents_add_tail hv24 hz3),by simp only [hv24d,add_zero]⟩
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero,he1] at hxe
    rw [hxe] at hx
    simp only [hd1] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero,he1,he3] at hxe
    rw [hxe] at hx
    simp only [map_add,hd1,hd3,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero,he1,he2] at hxe
    rw [hxe] at hx
    simp only [map_add,hd1,hd2,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,he1,he2,he3] at hxe
    rw [hxe] at hx
    simp only [map_add,hd1,hd2,hd3,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,add_zero,he0] at hxe
    rw [hxe]
    exact ⟨v0,hv0,hv0d⟩
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero,he0,he3] at hxe
    rw [hxe]
    exact ⟨v0 + 0,(represents_add_tail hv0 hz3),by simp only [hv0d,add_zero]⟩
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero,he0,he2] at hxe
    rw [hxe]
    exact ⟨v0 + v24,(represents_add_tail hv0 hv24),by simp only [map_add,hv0d, hv24d,add_zero]⟩
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero,he0,he2,he3] at hxe
    rw [hxe]
    exact ⟨v0 + v24 + 0,(represents_add_tail (represents_add_tail hv0 hv24) hz3),by simp only [map_add,hv0d, hv24d,add_zero]⟩
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero,he0,he1] at hxe
    rw [hxe] at hx
    simp only [map_add,hd0,hd1,zero_add] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero,he0,he1,he3] at hxe
    rw [hxe] at hx
    simp only [map_add,hd0,hd1,hd3,zero_add,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero,he0,he1,he2] at hxe
    rw [hxe] at hx
    simp only [map_add,hd0,hd1,hd2,zero_add,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    simp only [map_add,he0,he1,he2,he3] at hxe
    rw [hxe] at hx
    simp only [map_add,hd0,hd1,hd2,hd3,zero_add,add_zero] at hx
    have hh := congrArg (fun y => f y 2) hx
    rw [←hf2,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh


private theorem af18_d5_target_nonzero_h373 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (14,141) (16,142)
    ((I.interpretation.basis .sphere 14 141 2)) ((I.interpretation.basis .sphere 16 142 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,14,141,[2],16,142,[2],"S0_AdamsE2_ss",3321⟩ (by
    exact List.mem_of_getElem? (i := 373) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (14,141) (16,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 141 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 142 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af18_d5_target_nonzero_h374 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (13,140) (16,142)
    ((I.interpretation.basis .sphere 13 140 0)) ((I.interpretation.basis .sphere 16 142 1)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,13,140,[0],16,142,[1],"S0_AdamsE2_ss",3322⟩ (by
    exact List.mem_of_getElem? (i := 374) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (13,140) (16,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 140 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 142 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af18_d5_target_nonzero_h375 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 6 (10,137) (16,142)
    ((I.interpretation.basis .sphere 10 137 2) + (I.interpretation.basis .sphere 10 137 4)) ((I.interpretation.basis .sphere 16 142 0)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,6,10,137,[2, 4],16,142,[0],"S0_AdamsE2_ss",3323⟩ (by
    exact List.mem_of_getElem? (i := 375) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 6 (10,137) (16,142) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 137 [2, 4] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 142 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem af18_d5_target_nonzero (I : AdamsComputationTheorems D L G)
    (y : (sequence D .sphere).Page 5 (18,143))
    (hy : RepresentsOnPage (sequence D .sphere) 5 (18,143)
      (I.interpretation.basis .sphere 18 143 0) y) : y ≠ 0 := by
  classical
  let E := sequence D .sphere
  have h373 : HasDifferential E 2 (14,141) (16,142)
      ((I.interpretation.basis .sphere 14 141 2)) ((I.interpretation.basis .sphere 16 142 2)) := af18_d5_target_nonzero_h373 I
  have h374 : HasDifferential E 3 (13,140) (16,142)
      ((I.interpretation.basis .sphere 13 140 0)) ((I.interpretation.basis .sphere 16 142 1)) := af18_d5_target_nonzero_h374 I
  have h375 : HasDifferential E 6 (10,137) (16,142)
      ((I.interpretation.basis .sphere 10 137 2) + (I.interpretation.basis .sphere 10 137 4)) ((I.interpretation.basis .sphere 16 142 0)) := af18_d5_target_nonzero_h375 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,16,142,["1,2,439,1", "0,2,68,1,107,1", "0,14,69,2"]⟩ (by
    exact List.mem_of_getElem? (i := 233) (by rfl))
  change E.Page 2 (16,142) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 142 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,18,143,["8,2,209,1", "0,4,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 246) (by rfl))
  change E.Page 2 (18,143) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 18 143 i.val at hf
  have hd0 : E.d 2 (16,142) (I.interpretation.basis .sphere 16 142 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h375
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hy
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hy⟩
  have hd1 : E.d 2 (16,142) (I.interpretation.basis .sphere 16 142 1) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h374
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hy
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hy⟩
  have hd2 : E.d 2 (16,142) (I.interpretation.basis .sphere 16 142 2)=0 := by
    have hd : E.d 2 (14,141) (I.interpretation.basis .sphere 14 141 2)=
      I.interpretation.basis .sphere 16 142 2 := h373.eq_on_page_two.2
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(14,141)) ⟨_,hd⟩
  have in2 : E.d 2 ((18,143)-E.diffDeg 2)=0 := by
    have hall (a : Fin 3 →₀ F2) : E.d 2 (16,142) (e.symm a)=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,ih,add_zero]
        fin_cases c
        · simp
        · change E.d 2 (16,142) (e.symm (Finsupp.single i 1))=0
          rw [he i]
          fin_cases i
          · exact hd0
          · exact hd1
          · exact hd2
    ext x
    change E.d 2 (16,142) x=0
    simpa only [LinearEquiv.symm_apply_apply] using hall (e x)
  have in3 : E.d 3 ((18,143)-E.diffDeg 3)=0 := by
    ext x
    change E.d 3 (15,141) x=0
    rw [(af15_three_for_incoming I).elim x 0,map_zero]
  have in4 : E.d 4 ((18,143)-E.diffDeg 4)=0 := af14_d4_zero_for_incoming I
  have n2 : I.interpretation.basis .sphere 18 143 0 ≠ 0 := by
    have hh : f.symm (Finsupp.single (0:Fin 2) 1)=I.interpretation.basis .sphere 18 143 0 := hf 0
    rw [←hh]
    intro hz
    have hh := congrArg (fun x => f x 0) hz
    norm_num [Finsupp.single_apply] at hh
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) hy
  obtain ⟨y4,hy4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hy
  have hy2 : RepresentsOnPage E 2 (18,143) (I.interpretation.basis .sphere 18 143 0) (I.interpretation.basis .sphere 18 143 0) := by
    obtain ⟨y2,hy2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hy
    rw [←hy2.eq_on_page_two] at hy2
    exact hy2
  have n3 := represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤2; omega)
    (by decide : (2:ℤ)≤2) in2 hy3 hy2 n2
  have n4 := represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤3; omega)
    (by decide : (2:ℤ)≤3) in3 hy4 hy3 n3
  exact represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤4; omega)
    (by decide : (2:ℤ)≤4) in4 hy hy4 n4

private theorem stem125_af18_nonzero_incoming_d5_h397 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 5 (13,139) (18,143)
    ((I.interpretation.basis .sphere 13 139 0)) ((I.interpretation.basis .sphere 18 143 0)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,5,13,139,[0],18,143,[0],"S0_AdamsE2_ss",3391⟩ (by
    exact List.mem_of_getElem? (i := 397) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 5 (13,139) (18,143) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 139 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 143 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

theorem stem125_af18_nonzero_incoming_d5 (I : AdamsComputationTheorems D L G) :
    ∃ (x : Page D .sphere 13 139) (y : Page D .sphere 18 143),
      I.interpretation.coordinateSum .sphere 13 139 [0] = some x ∧
      I.interpretation.coordinateSum .sphere 18 143 [0] = some y ∧
      HasNonzeroDifferential (sequence D .sphere) 5 (13,139) (18,143) x y := by
  classical

  let E := sequence D .sphere
  have h397 : HasDifferential E 5 (13,139) (18,143)
      ((I.interpretation.basis .sphere 13 139 0)) ((I.interpretation.basis .sphere 18 143 0)) := stem125_af18_nonzero_incoming_d5_h397 I
  refine ⟨I.interpretation.basis .sphere 13 139 0,I.interpretation.basis .sphere 18 143 0,?_,?_,?_⟩
  · have vx : Raw.coordinatesValid Raw.degrees .sphere 13 139 [0]=true := rfl
    simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  · have vy : Raw.coordinatesValid Raw.degrees .sphere 18 143 [0]=true := rfl
    simp only [E2Interpretation.coordinateSum,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  · obtain ⟨hp,xr,yr,hx,hy,hd⟩ := h397
    refine ⟨hp,xr,yr,hx,hy,hd,?_⟩
    exact af18_d5_target_nonzero I yr hy
end


end
end KIP126.Computation.SphereAndCofiber
end
