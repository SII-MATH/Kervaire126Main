module

public import KIP126.Computation.LinCoordinates.Certificates.SphereAndCofiber.Bounds

/-! Finite stem-125 vanishing in high filtration. -/

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

private theorem tail_af26_h469 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (26,151) (28,152)
    (I.interpretation.basis .sphere 26 151 0) (I.interpretation.basis .sphere 28 152 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,26,151,[0],28,152,[1],"S0_AdamsE2_ss",4092⟩ (by
    exact List.mem_of_getElem? (i := 469) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (26,151) (28,152) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 26 151 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 28 152 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af26 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (26,151)) := by
  classical
  let E := sequence D .sphere
  have h469 : HasDifferential E 2 (26,151) (28,152)
      (I.interpretation.basis .sphere 26 151 0) (I.interpretation.basis .sphere 28 152 1) := tail_af26_h469 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,26,151,["0,1,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 286) (by rfl))
  change E.Page 2 (26,151) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 26 151 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 26 151 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,28,152,["8,3,166,1", "0,3,17,1,260,1"]⟩ (by
    exact List.mem_of_getElem? (i := 294) (by rfl))
  change E.Page 2 (28,152) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 28 152 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 28 152 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 28 152 1 := hf 1
  have hd0 : E.d 2 (26,151) (I.interpretation.basis .sphere 26 151 0) =
      I.interpretation.basis .sphere 28 152 1 := h469.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (26,151)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i; simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(26,151)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af26 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (26,151)) := by
  classical
  exact tail_af26 I

private theorem tail_af27_h480 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (27,152) (29,153)
    (I.interpretation.basis .sphere 27 152 0) (I.interpretation.basis .sphere 29 153 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,27,152,[0],29,153,[0],"S0_AdamsE2_ss",4163⟩ (by
    exact List.mem_of_getElem? (i := 480) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (27,152) (29,153) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 27 152 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 29 153 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af27_h479 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (27,152) (29,153)
    (I.interpretation.basis .sphere 27 152 1) (I.interpretation.basis .sphere 29 153 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,27,152,[1],29,153,[2],"S0_AdamsE2_ss",4162⟩ (by
    exact List.mem_of_getElem? (i := 479) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (27,152) (29,153) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 27 152 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 29 153 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af27 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (27,152)) := by
  classical
  let E := sequence D .sphere
  have h480 : HasDifferential E 2 (27,152) (29,153)
      (I.interpretation.basis .sphere 27 152 0) (I.interpretation.basis .sphere 29 153 0) := tail_af27_h480 I
  have h479 : HasDifferential E 2 (27,152) (29,153)
      (I.interpretation.basis .sphere 27 152 1) (I.interpretation.basis .sphere 29 153 2) := tail_af27_h479 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,27,152,["8,3,167,1", "0,2,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 290) (by rfl))
  change E.Page 2 (27,152) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 27 152 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 27 152 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 27 152 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,29,153,["8,3,9,1,13,1,51,1", "8,4,118,1", "0,4,17,1,260,1"]⟩ (by
    exact List.mem_of_getElem? (i := 298) (by rfl))
  change E.Page 2 (29,153) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 29 153 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 29 153 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 29 153 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 29 153 2 := hf 2
  have hd0 : E.d 2 (27,152) (I.interpretation.basis .sphere 27 152 0) =
      I.interpretation.basis .sphere 29 153 0 := h480.eq_on_page_two.2
  have hd1 : E.d 2 (27,152) (I.interpretation.basis .sphere 27 152 1) =
      I.interpretation.basis .sphere 29 153 2 := h479.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (27,152)
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
    exact RepresentsOnPage.zero (E:=E) (p:=(27,152)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [he1, hd1] at hx
    have hval := congrArg (fun y => f y 2) hx
    simp only [map_zero, ←hf2, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, ←hf2, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af27 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (27,152)) := by
  classical
  exact tail_af27 I

private theorem tail_af28_h492 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (28,153) (30,154)
    (I.interpretation.basis .sphere 28 153 0) (I.interpretation.basis .sphere 30 154 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,28,153,[0],30,154,[0],"S0_AdamsE2_ss",4266⟩ (by
    exact List.mem_of_getElem? (i := 492) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (28,153) (30,154) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 28 153 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 30 154 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af28_h491 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (28,153) (30,154)
    (I.interpretation.basis .sphere 28 153 3) (I.interpretation.basis .sphere 30 154 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,28,153,[3],30,154,[1],"S0_AdamsE2_ss",4265⟩ (by
    exact List.mem_of_getElem? (i := 491) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (28,153) (30,154) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 28 153 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 30 154 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af28_h490 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (26,152) (28,153)
    (I.interpretation.basis .sphere 26 152 1) (I.interpretation.basis .sphere 28 153 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,26,152,[1],28,153,[1],"S0_AdamsE2_ss",4264⟩ (by
    exact List.mem_of_getElem? (i := 490) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (26,152) (28,153) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 26 152 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 28 153 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af28_h489 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (26,152) (28,153)
    (I.interpretation.basis .sphere 26 152 0) (I.interpretation.basis .sphere 28 153 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,26,152,[0],28,153,[2],"S0_AdamsE2_ss",4263⟩ (by
    exact List.mem_of_getElem? (i := 489) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (26,152) (28,153) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 26 152 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 28 153 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af28 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (28,153)) := by
  classical
  let E := sequence D .sphere
  have h492 : HasDifferential E 2 (28,153) (30,154)
      (I.interpretation.basis .sphere 28 153 0) (I.interpretation.basis .sphere 30 154 0) := tail_af28_h492 I
  have h491 : HasDifferential E 2 (28,153) (30,154)
      (I.interpretation.basis .sphere 28 153 3) (I.interpretation.basis .sphere 30 154 1) := tail_af28_h491 I
  have h490 : HasDifferential E 2 (26,152) (28,153)
      (I.interpretation.basis .sphere 26 152 1) (I.interpretation.basis .sphere 28 153 1) := tail_af28_h490 I
  have h489 : HasDifferential E 2 (26,152) (28,153)
      (I.interpretation.basis .sphere 26 152 0) (I.interpretation.basis .sphere 28 153 2) := tail_af28_h489 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,28,153,["64,1,146,1", "8,2,9,1,13,4", "8,3,17,1,80,1", "0,3,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 295) (by rfl))
  change E.Page 2 (28,153) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 28 153 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = I.interpretation.basis .sphere 28 153 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = I.interpretation.basis .sphere 28 153 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = I.interpretation.basis .sphere 28 153 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = I.interpretation.basis .sphere 28 153 3 := he 3
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,30,154,["1,2,64,1,137,1", "0,5,17,1,260,1"]⟩ (by
    exact List.mem_of_getElem? (i := 302) (by rfl))
  change E.Page 2 (30,154) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 30 154 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 30 154 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 30 154 1 := hf 1
  have hd0 : E.d 2 (28,153) (I.interpretation.basis .sphere 28 153 0) =
      I.interpretation.basis .sphere 30 154 0 := h492.eq_on_page_two.2
  have hd3 : E.d 2 (28,153) (I.interpretation.basis .sphere 28 153 3) =
      I.interpretation.basis .sphere 30 154 1 := h491.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 5 (28,153) (I.interpretation.basis .sphere 28 153 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h490
  have hd1 : E.d 2 (28,153) (I.interpretation.basis .sphere 28 153 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz1⟩
  have hz2 : RepresentsOnPage E 5 (28,153) (I.interpretation.basis .sphere 28 153 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h489
  have hd2 : E.d 2 (28,153) (I.interpretation.basis .sphere 28 153 2) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz2
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz2⟩
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (28,153)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  generalize hc2 : e x 2 = c2 at hxe
  generalize hc3 : e x 3 = c3 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(28,153)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he3, hd3] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he2]
    simpa only [zero_add] using (hz2)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he2, he3, hd2, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [zero_add] using (hz1)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he3, hd1, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1, he2]
    simpa only [zero_add] using (represents_add_tail (hz1) hz2)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he3, hd0, hd3] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, hd0, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, he3, hd0, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he3, hd0, hd1, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, LinearEquiv.apply_symm_apply, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af28 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (28,153)) := by
  classical
  exact tail_af28 I

private theorem stem125_af29_four_h498 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (27,153) (29,154)
    (I.interpretation.basis .sphere 27 153 0) (I.interpretation.basis .sphere 29 154 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,27,153,[0],29,154,[0],"S0_AdamsE2_ss",4337⟩ (by
    exact List.mem_of_getElem? (i := 498) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (27,153) (29,154) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 27 153 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 29 154 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af29_four_h499 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (29,154) (32,156)
    (I.interpretation.basis .sphere 29 154 1) (I.interpretation.basis .sphere 32 156 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,29,154,[1],32,156,[0],"S0_AdamsE2_ss",4338⟩ (by
    exact List.mem_of_getElem? (i := 499) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (29,154) (32,156) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 29 154 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 32 156 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af29_four_h506 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (28,154) (30,155)
    (I.interpretation.basis .sphere 28 154 0) (I.interpretation.basis .sphere 30 155 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,28,154,[0],30,155,[1],"S0_AdamsE2_ss",4411⟩ (by
    exact List.mem_of_getElem? (i := 506) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (28,154) (30,155) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 28 154 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 30 155 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af29_four_h507 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (30,155) (32,156)
    (I.interpretation.basis .sphere 30 155 0) (I.interpretation.basis .sphere 32 156 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,30,155,[0],32,156,[1],"S0_AdamsE2_ss",4412⟩ (by
    exact List.mem_of_getElem? (i := 507) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (30,155) (32,156) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 30 155 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 32 156 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af29_four (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (29,154)) := by
  classical
  let E := sequence D .sphere
  have h498 : HasDifferential E 2 (27,153) (29,154)
      (I.interpretation.basis .sphere 27 153 0) (I.interpretation.basis .sphere 29 154 0) := stem125_af29_four_h498 I
  have h499 : HasDifferential E 3 (29,154) (32,156)
      (I.interpretation.basis .sphere 29 154 1) (I.interpretation.basis .sphere 32 156 0) := stem125_af29_four_h499 I
  have h506 : HasDifferential E 2 (28,154) (30,155)
      (I.interpretation.basis .sphere 28 154 0) (I.interpretation.basis .sphere 30 155 1) := stem125_af29_four_h506 I
  have h507 : HasDifferential E 2 (30,155) (32,156)
      (I.interpretation.basis .sphere 30 155 0) (I.interpretation.basis .sphere 32 156 1) := stem125_af29_four_h507 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,29,154,["0,1,64,1,146,1", "0,4,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 299) (by rfl))
  change E.Page 2 (29,154) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 29 154 i.val at he
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,30,155,["8,2,258,1", "0,5,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 303) (by rfl))
  change E.Page 2 (30,155) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 30 155 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,32,156,["8,2,17,1,147,1", "8,6,13,2"]⟩ (by
    exact List.mem_of_getElem? (i := 310) (by rfl))
  change E.Page 2 (32,156) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 32 156 i.val at hg
  have d20 : E.d 2 (30,155) (I.interpretation.basis .sphere 30 155 0) =
      I.interpretation.basis .sphere 32 156 1 := h507.eq_on_page_two.2
  have d21 : E.d 2 (30,155) (I.interpretation.basis .sphere 30 155 1) = 0 := by
    have hd : E.d 2 (28,154) (I.interpretation.basis .sphere 28 154 0) =
      I.interpretation.basis .sphere 30 155 1 := h506.eq_on_page_two.2
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(28,154)) ⟨_,hd⟩
  have hc (x : E.Page 2 (30,155)) : g (E.d 2 (30,155) x) 0 = 0 := by
    have hall (a : Fin 2 →₀ F2) : g (E.d 2 (30,155) (f.symm a)) 0 = 0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (30,155) (f.symm (Finsupp.single i 1))) 0 = 0
          rw [hf i]
          fin_cases i
          · rw [d20]
            rw [show I.interpretation.basis .sphere 32 156 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm, LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
          · rw [d21]
            exact congrArg (fun z : Fin 2 →₀ F2 => z 0) g.map_zero
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h499
  have hd' : E.d 3 (29,154) a = b := hd
  have hbne : b ≠ 0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (30,155) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (32,156)).Z_anti bot_le) ≫
      (E.ssData (32,156)).pageπ 0) z ∈ LinearMap.range (E.d 2 (30,155)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (32,156)).Z_anti bot_le) ≫
      (E.ssData (32,156)).pageπ 0) z = I.interpretation.basis .sphere 32 156 0 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := hc u
    rw [hu] at hzero
    rw [show I.interpretation.basis .sphere 32 156 0 = g.symm (Finsupp.single 0 1) from (hg 0).symm, LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply] at hzero
  have hz : RepresentsOnPage E 3 (29,154) (I.interpretation.basis .sphere 29 154 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h498
  have frame (q : E.Page 3 (29,154)) : q=0 ∨ q=a := by
    let vv : Fin 2 → E.Page 3 (29,154) := ![0,a]
    have hv (i : Fin 2) : RepresentsOnPage E 3 (29,154) (e.symm (Finsupp.single i 1)) (vv i) := by
      rw [he i]
      fin_cases i
      · exact hz
      · exact ha
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e vv hv q
    simp only [Fin.sum_univ_succ] at hc
    change q = (if c 0=0 then 0 else 0) + ((if c 1=0 then 0 else a)+0) at hc
    by_cases h : c 1=0
    · exact Or.inl (by simpa only [h,ite_true,ite_self,add_zero] using hc)
    · exact Or.inr (by simpa only [h,ite_false,ite_self,add_zero,zero_add] using hc)
  have hker (q : E.Page 3 (29,154)) (hq : E.d 3 (29,154) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 3 ((29,154)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [hker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (29,154)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))

private theorem stem125_e5_zero_af29 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (29,154)) := by
  classical
  exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 5 29 154
    (by decide) (by decide) (stem125_af29_four I)

private theorem tail_af30_h507 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (30,155) (32,156)
    (I.interpretation.basis .sphere 30 155 0) (I.interpretation.basis .sphere 32 156 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,30,155,[0],32,156,[1],"S0_AdamsE2_ss",4412⟩ (by
    exact List.mem_of_getElem? (i := 507) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (30,155) (32,156) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 30 155 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 32 156 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af30_h506 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (28,154) (30,155)
    (I.interpretation.basis .sphere 28 154 0) (I.interpretation.basis .sphere 30 155 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,28,154,[0],30,155,[1],"S0_AdamsE2_ss",4411⟩ (by
    exact List.mem_of_getElem? (i := 506) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (28,154) (30,155) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 28 154 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 30 155 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af30 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (30,155)) := by
  classical
  let E := sequence D .sphere
  have h507 : HasDifferential E 2 (30,155) (32,156)
      (I.interpretation.basis .sphere 30 155 0) (I.interpretation.basis .sphere 32 156 1) := tail_af30_h507 I
  have h506 : HasDifferential E 2 (28,154) (30,155)
      (I.interpretation.basis .sphere 28 154 0) (I.interpretation.basis .sphere 30 155 1) := tail_af30_h506 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,30,155,["8,2,258,1", "0,5,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 303) (by rfl))
  change E.Page 2 (30,155) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 30 155 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 30 155 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 30 155 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,32,156,["8,2,17,1,147,1", "8,6,13,2"]⟩ (by
    exact List.mem_of_getElem? (i := 310) (by rfl))
  change E.Page 2 (32,156) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 32 156 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 32 156 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 32 156 1 := hf 1
  have hd0 : E.d 2 (30,155) (I.interpretation.basis .sphere 30 155 0) =
      I.interpretation.basis .sphere 32 156 1 := h507.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 5 (30,155) (I.interpretation.basis .sphere 30 155 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h506
  have hd1 : E.d 2 (30,155) (I.interpretation.basis .sphere 30 155 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz1⟩
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (30,155)
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
    exact RepresentsOnPage.zero (E:=E) (p:=(30,155)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [zero_add] using (hz1)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af30 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (30,155)) := by
  classical
  exact tail_af30 I

private theorem stem125_af31_five_h501 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (29,155) (31,156)
    (I.interpretation.basis .sphere 29 155 0) (I.interpretation.basis .sphere 31 156 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,29,155,[0],31,156,[1],"S0_AdamsE2_ss",4414⟩ (by
    exact List.mem_of_getElem? (i := 501) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (29,155) (31,156) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 29 155 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 31 156 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af31_five_h502 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (29,155) (31,156)
    (I.interpretation.basis .sphere 29 155 1) (I.interpretation.basis .sphere 31 156 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,29,155,[1],31,156,[2],"S0_AdamsE2_ss",4415⟩ (by
    exact List.mem_of_getElem? (i := 502) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (29,155) (31,156) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 29 155 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 31 156 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af31_five_h514 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (31,156) (35,159)
    (I.interpretation.basis .sphere 31 156 0) (I.interpretation.basis .sphere 35 159 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,31,156,[0],35,159,[0],"S0_AdamsE2_ss",4503⟩ (by
    exact List.mem_of_getElem? (i := 514) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (31,156) (35,159) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 31 156 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 35 159 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af31_five_h525 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (33,158) (35,159)
    (I.interpretation.basis .sphere 33 158 0) (I.interpretation.basis .sphere 35 159 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,33,158,[0],35,159,[1],"S0_AdamsE2_ss",4671⟩ (by
    exact List.mem_of_getElem? (i := 525) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (33,158) (35,159) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 33 158 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 35 159 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af31_five_hd3zero
    (I : AdamsComputationTheorems D L G) : (sequence D .sphere).d 3 (32,157) = 0  := by
  classical
  let E := sequence D .sphere
  have h525 : HasDifferential E 2 (33,158) (35,159)
      (I.interpretation.basis .sphere 33 158 0) (I.interpretation.basis .sphere 35 159 1) := stem125_af31_five_h525 I
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,33,158,["8,1,453,1"]⟩ (by
    exact List.mem_of_getElem? (i := 314) (by rfl))
  change E.Page 2 (33,158) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 33 158 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,35,159,["42,1,224,1", "8,7,20,1"]⟩ (by
    exact List.mem_of_getElem? (i := 322) (by rfl))
  change E.Page 2 (35,159) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 35 159 i.val at hg
  obtain ⟨z,hz⟩ := I.basis ⟨.sphere,32,157,[]⟩ (by
    exact List.mem_of_getElem? (i := 311) (by rfl))
  change E.Page 2 (32,157) ≃ₗ[ℤ] (Fin 0 →₀ F2) at z
  change ∀ i : Fin 0, z.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 32 157 i.val at hz
  have d20 : E.d 2 (33,158) (I.interpretation.basis .sphere 33 158 0) =
      I.interpretation.basis .sphere 35 159 1 := h525.eq_on_page_two.2
  have hc (x : E.Page 2 (33,158)) : g (E.d 2 (33,158) x) 0 = 0 := by
    have hall (a : Fin 1 →₀ F2) : g (E.d 2 (33,158) (f.symm a)) 0 = 0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (33,158) (f.symm (Finsupp.single i 1))) 0 = 0
          rw [hf i]
          fin_cases i
          rw [d20]
          rw [show I.interpretation.basis .sphere 35 159 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm, LinearEquiv.apply_symm_apply]
          norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)

  have hp (q : E.Page 3 (32,157)) : q = 0 := by
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) z
      (fun i : Fin 0 => i.elim0) (fun i => i.elim0) q
    simpa only [Fin.sum_univ_zero] using hc
  ext q
  simp only [hp q,map_zero]

private theorem stem125_af31_target_nonzero (I : AdamsComputationTheorems D L G)
    {b : (sequence D .sphere).Page 4 (35,159)}
    (hb : RepresentsOnPage (sequence D .sphere) 4 (35,159)
      (I.interpretation.basis .sphere 35 159 0) b) : b ≠ 0 := by
  classical
  let E := sequence D .sphere
  have h525 : HasDifferential E 2 (33,158) (35,159)
      (I.interpretation.basis .sphere 33 158 0) (I.interpretation.basis .sphere 35 159 1) := stem125_af31_five_h525 I
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,33,158,["8,1,453,1"]⟩ (by
    exact List.mem_of_getElem? (i := 314) (by rfl))
  change E.Page 2 (33,158) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 33 158 i.val at hf
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,35,159,["42,1,224,1", "8,7,20,1"]⟩ (by
    exact List.mem_of_getElem? (i := 322) (by rfl))
  change E.Page 2 (35,159) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 35 159 i.val at hg
  obtain ⟨z,hz⟩ := I.basis ⟨.sphere,32,157,[]⟩ (by
    exact List.mem_of_getElem? (i := 311) (by rfl))
  change E.Page 2 (32,157) ≃ₗ[ℤ] (Fin 0 →₀ F2) at z
  change ∀ i : Fin 0, z.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 32 157 i.val at hz
  have d20 : E.d 2 (33,158) (I.interpretation.basis .sphere 33 158 0) =
      I.interpretation.basis .sphere 35 159 1 := h525.eq_on_page_two.2
  have hc (x : E.Page 2 (33,158)) : g (E.d 2 (33,158) x) 0 = 0 := by
    as_aux_lemma =>
      have hall (a : Fin 1 →₀ F2) : g (E.d 2 (33,158) (f.symm a)) 0 = 0 := by
        as_aux_lemma =>
          induction a using Finsupp.induction with
          | zero => simp
          | @single_add i c a hi hci ih =>
            rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
            fin_cases c
            · simp
            · change g (E.d 2 (33,158) (f.symm (Finsupp.single i 1))) 0 = 0
              rw [hf i]
              fin_cases i
              rw [d20]
              rw [show I.interpretation.basis .sphere 35 159 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm, LinearEquiv.apply_symm_apply]
              norm_num [Finsupp.single_apply,Fin.ext_iff]
      simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  have hd3zero : E.d 3 (32,157) = 0  := stem125_af31_five_hd3zero I
  obtain ⟨b3,hb3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hb
  have hb3ne : b3 ≠ 0 := by
    apply represents_next_nonzero_of_not_incoming_at
      (r := 2) (p := (35,159)) (q := (33,158)) (by rfl)
      (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)≤2) hb3 (represents_two_self _)
    intro u hu
    change E.d 2 (33,158) u=I.interpretation.basis .sphere 35 159 0 at hu
    have hzero := hc u
    rw [hu] at hzero
    rw [show I.interpretation.basis .sphere 35 159 0 = g.symm (Finsupp.single 0 1) from (hg 0).symm,
      LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply] at hzero
  exact represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) hd3zero hb hb3 hb3ne

private theorem stem125_af31_five (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (31,156)) := by
  classical
  let E := sequence D .sphere
  have h501 : HasDifferential E 2 (29,155) (31,156)
      (I.interpretation.basis .sphere 29 155 0) (I.interpretation.basis .sphere 31 156 1) := stem125_af31_five_h501 I
  have h502 : HasDifferential E 2 (29,155) (31,156)
      (I.interpretation.basis .sphere 29 155 1) (I.interpretation.basis .sphere 31 156 2) := stem125_af31_five_h502 I
  have h514 : HasDifferential E 4 (31,156) (35,159)
      (I.interpretation.basis .sphere 31 156 0) (I.interpretation.basis .sphere 35 159 0) := stem125_af31_five_h514 I
  have h525 : HasDifferential E 2 (33,158) (35,159)
      (I.interpretation.basis .sphere 33 158 0) (I.interpretation.basis .sphere 35 159 1) := stem125_af31_five_h525 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,31,156,["8,1,17,2,113,1", "8,5,13,1,32,1", "0,6,558,1"]⟩ (by
    exact List.mem_of_getElem? (i := 307) (by rfl))
  change E.Page 2 (31,156) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 31 156 i.val at he
  obtain ⟨_,a,b,ha,hb,hd⟩ := h514
  have hd' : E.d 4 (31,156) a = b := hd
  have hbne : b ≠ 0 := stem125_af31_target_nonzero I hb
  have hz1 : RepresentsOnPage E 4 (31,156) (I.interpretation.basis .sphere 31 156 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h501
  have hz2 : RepresentsOnPage E 4 (31,156) (I.interpretation.basis .sphere 31 156 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4) h502
  have frame (q : E.Page 4 (31,156)) : q=0 ∨ q=a := by
    as_aux_lemma =>
      let vv : Fin 3 → E.Page 4 (31,156) := ![a,0,0]
      have hv (i : Fin 3) : RepresentsOnPage E 4 (31,156) (e.symm (Finsupp.single i 1)) (vv i) := by
        as_aux_lemma =>
          rw [he i]
          fin_cases i
          · exact ha
          · exact hz1
          · exact hz2
      obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤4) e vv hv q
      simp only [Fin.sum_univ_succ] at hc
      change q = (if c 0=0 then 0 else a) + ((if c 1=0 then 0 else 0)+((if c 2=0 then 0 else 0)+0)) at hc
      by_cases h : c 0=0
      · exact Or.inl (by simpa only [h,ite_true,ite_self,add_zero] using hc)
      · exact Or.inr (by simpa only [h,ite_false,ite_self,add_zero,zero_add] using hc)
  exact choice_next_zero_of_single_frame_nonzero_differential
    (E := E) (r := 4) (by decide) (by change (2:ℤ)≤4; omega)
    a (fun h => hbne (hd'.symm.trans h)) frame

private theorem stem125_e5_zero_af31 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (31,156)) := by
  classical
  exact stem125_af31_five I

private theorem tail_af32 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (32,157)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,32,157,[]⟩ (by
    exact List.mem_of_getElem? (i := 311) (by rfl))
  change E.Page 2 (32,157) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 32 157 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af32 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (32,157)) := by
  classical
  exact tail_af32 I

private theorem tail_af33_h525 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (33,158) (35,159)
    (I.interpretation.basis .sphere 33 158 0) (I.interpretation.basis .sphere 35 159 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,33,158,[0],35,159,[1],"S0_AdamsE2_ss",4671⟩ (by
    exact List.mem_of_getElem? (i := 525) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (33,158) (35,159) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 33 158 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 35 159 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af33 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (33,158)) := by
  classical
  let E := sequence D .sphere
  have h525 : HasDifferential E 2 (33,158) (35,159)
      (I.interpretation.basis .sphere 33 158 0) (I.interpretation.basis .sphere 35 159 1) := tail_af33_h525 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,33,158,["8,1,453,1"]⟩ (by
    exact List.mem_of_getElem? (i := 314) (by rfl))
  change E.Page 2 (33,158) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 33 158 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 33 158 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,35,159,["42,1,224,1", "8,7,20,1"]⟩ (by
    exact List.mem_of_getElem? (i := 322) (by rfl))
  change E.Page 2 (35,159) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 35 159 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 35 159 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 35 159 1 := hf 1
  have hd0 : E.d 2 (33,158) (I.interpretation.basis .sphere 33 158 0) =
      I.interpretation.basis .sphere 35 159 1 := h525.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (33,158)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i; simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(33,158)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af33 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (33,158)) := by
  classical
  exact tail_af33 I

private theorem tail_af34_h531 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (31,157) (34,159)
    (I.interpretation.basis .sphere 31 157 0) (I.interpretation.basis .sphere 34 159 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,31,157,[0],34,159,[0],"S0_AdamsE2_ss",4764⟩ (by
    exact List.mem_of_getElem? (i := 531) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (31,157) (34,159) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 31 157 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 34 159 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af34_h530 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (32,158) (34,159)
    (I.interpretation.basis .sphere 32 158 0) (I.interpretation.basis .sphere 34 159 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,32,158,[0],34,159,[1],"S0_AdamsE2_ss",4763⟩ (by
    exact List.mem_of_getElem? (i := 530) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (32,158) (34,159) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 32 158 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 34 159 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af34 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (34,159)) := by
  classical
  let E := sequence D .sphere
  have h531 : HasDifferential E 3 (31,157) (34,159)
      (I.interpretation.basis .sphere 31 157 0) (I.interpretation.basis .sphere 34 159 0) := tail_af34_h531 I
  have h530 : HasDifferential E 2 (32,158) (34,159)
      (I.interpretation.basis .sphere 32 158 0) (I.interpretation.basis .sphere 34 159 1) := tail_af34_h530 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,34,159,["8,4,137,1", "8,6,45,1"]⟩ (by
    exact List.mem_of_getElem? (i := 318) (by rfl))
  change E.Page 2 (34,159) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 34 159 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 34 159 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 34 159 1 := he 1
  apply fifth_zero_of_all_basis e
  intro i
  rw [he i]
  fin_cases i
  · exact differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide) h531
  · exact differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h530

private theorem stem125_e5_zero_af34 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (34,159)) := by
  classical
  exact tail_af34 I

private theorem tail_af35 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (35,160)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,35,160,[]⟩ (by
    exact List.mem_of_getElem? (i := 323) (by rfl))
  change E.Page 2 (35,160) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 35 160 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af35 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (35,160)) := by
  classical
  exact tail_af35 I

private theorem tail_af36_h541 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (36,161) (38,162)
    (I.interpretation.basis .sphere 36 161 0) (I.interpretation.basis .sphere 38 162 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,36,161,[0],38,162,[1],"S0_AdamsE2_ss",4930⟩ (by
    exact List.mem_of_getElem? (i := 541) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (36,161) (38,162) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 36 161 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 38 162 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af36_h540 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (33,159) (36,161)
    (I.interpretation.basis .sphere 33 159 0) (I.interpretation.basis .sphere 36 161 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,33,159,[0],36,161,[1],"S0_AdamsE2_ss",4929⟩ (by
    exact List.mem_of_getElem? (i := 540) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (33,159) (36,161) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 33 159 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 36 161 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af36 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (36,161)) := by
  classical
  let E := sequence D .sphere
  have h541 : HasDifferential E 2 (36,161) (38,162)
      (I.interpretation.basis .sphere 36 161 0) (I.interpretation.basis .sphere 38 162 1) := tail_af36_h541 I
  have h540 : HasDifferential E 3 (33,159) (36,161)
      (I.interpretation.basis .sphere 33 159 0) (I.interpretation.basis .sphere 36 161 1) := tail_af36_h540 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,36,161,["8,1,488,1", "1,1,42,1,224,1"]⟩ (by
    exact List.mem_of_getElem? (i := 326) (by rfl))
  change E.Page 2 (36,161) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 36 161 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 36 161 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 36 161 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,38,162,["8,2,297,1", "8,4,16,1,17,2"]⟩ (by
    exact List.mem_of_getElem? (i := 334) (by rfl))
  change E.Page 2 (38,162) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 38 162 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 38 162 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 38 162 1 := hf 1
  have hd0 : E.d 2 (36,161) (I.interpretation.basis .sphere 36 161 0) =
      I.interpretation.basis .sphere 38 162 1 := h541.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 5 (36,161) (I.interpretation.basis .sphere 36 161 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide) h540
  have hd1 : E.d 2 (36,161) (I.interpretation.basis .sphere 36 161 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz1⟩
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (36,161)
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
    exact RepresentsOnPage.zero (E:=E) (p:=(36,161)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [zero_add] using (hz1)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af36 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (36,161)) := by
  classical
  exact tail_af36 I

private theorem tail_af37_h547 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (37,162) (39,163)
    (I.interpretation.basis .sphere 37 162 0) (I.interpretation.basis .sphere 39 163 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,37,162,[0],39,163,[0],"S0_AdamsE2_ss",5028⟩ (by
    exact List.mem_of_getElem? (i := 547) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (37,162) (39,163) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 37 162 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 39 163 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af37_h546 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (35,161) (37,162)
    (I.interpretation.basis .sphere 35 161 0) (I.interpretation.basis .sphere 37 162 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,35,161,[0],37,162,[1],"S0_AdamsE2_ss",5027⟩ (by
    exact List.mem_of_getElem? (i := 546) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (35,161) (37,162) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 35 161 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 37 162 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af37 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (37,162)) := by
  classical
  let E := sequence D .sphere
  have h547 : HasDifferential E 2 (37,162) (39,163)
      (I.interpretation.basis .sphere 37 162 0) (I.interpretation.basis .sphere 39 163 0) := tail_af37_h547 I
  have h546 : HasDifferential E 2 (35,161) (37,162)
      (I.interpretation.basis .sphere 35 161 0) (I.interpretation.basis .sphere 37 162 1) := tail_af37_h546 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,37,162,["8,2,298,1", "8,5,88,1"]⟩ (by
    exact List.mem_of_getElem? (i := 330) (by rfl))
  change E.Page 2 (37,162) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 37 162 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 37 162 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 37 162 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,39,163,["0,1,8,2,297,1"]⟩ (by
    exact List.mem_of_getElem? (i := 339) (by rfl))
  change E.Page 2 (39,163) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 39 163 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 39 163 0 := hf 0
  have hd0 : E.d 2 (37,162) (I.interpretation.basis .sphere 37 162 0) =
      I.interpretation.basis .sphere 39 163 0 := h547.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 5 (37,162) (I.interpretation.basis .sphere 37 162 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h546
  have hd1 : E.d 2 (37,162) (I.interpretation.basis .sphere 37 162 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz1⟩
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (37,162)
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
    exact RepresentsOnPage.zero (E:=E) (p:=(37,162)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [zero_add] using (hz1)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af37 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (37,162)) := by
  classical
  exact tail_af37 I

private theorem stem125_e5_zero_26_to_37 (I : AdamsComputationTheorems D L G)
    (s : ℕ) (hs : 26 ≤ s) (hs' : s ≤ 37) :
    Subsingleton ((sequence D .sphere).Page 5 (s,(s : ℤ)+125)) := by
  classical

  interval_cases s
  · exact stem125_e5_zero_af26 I
  · exact stem125_e5_zero_af27 I
  · exact stem125_e5_zero_af28 I
  · exact stem125_e5_zero_af29 I
  · exact stem125_e5_zero_af30 I
  · exact stem125_e5_zero_af31 I
  · exact stem125_e5_zero_af32 I
  · exact stem125_e5_zero_af33 I
  · exact stem125_e5_zero_af34 I
  · exact stem125_e5_zero_af35 I
  · exact stem125_e5_zero_af36 I
  · exact stem125_e5_zero_af37 I

private theorem stem125_af38_four_h552 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (38,163) (41,165)
    ((I.interpretation.basis .sphere 38 163 0)) ((I.interpretation.basis .sphere 41 165 1) + (I.interpretation.basis .sphere 41 165 2)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,38,163,[0],41,165,[1, 2],"S0_AdamsE2_ss",5143⟩ (by
    exact List.mem_of_getElem? (i := 552) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (38,163) (41,165) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 38 163 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 41 165 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af38_four_h557 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (39,164) (43,167)
    ((I.interpretation.basis .sphere 39 164 0)) ((I.interpretation.basis .sphere 43 167 0)) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,39,164,[0],43,167,[0],"S0_AdamsE2_ss",5217⟩ (by
    exact List.mem_of_getElem? (i := 557) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (39,164) (43,167) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 39 164 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 43 167 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem stem125_af38_four_hd2zero
    (I : AdamsComputationTheorems D L G) : (sequence D .sphere).d 2 (39,164) = 0  := by
  classical
  let E := sequence D .sphere
  have h557 : HasDifferential E 4 (39,164) (43,167)
      ((I.interpretation.basis .sphere 39 164 0)) ((I.interpretation.basis .sphere 43 167 0)) := stem125_af38_four_h557 I
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,39,164,["0,2,8,2,298,1"]⟩ (by
    exact List.mem_of_getElem? (i := 340) (by rfl))
  change E.Page 2 (39,164) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 39 164 i.val at hf
  have d20 : E.d 2 (39,164) (I.interpretation.basis .sphere 39 164 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h557
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hx
    rw [← hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide : (2:ℤ)<4) hx2 ⟨x,hx⟩

  have hall (a : Fin 1 →₀ F2) : E.d 2 (39,164) (f.symm a) = 0 := by
    induction a using Finsupp.induction with
    | zero => simp
    | @single_add i c a hi hci ih =>
      rw [map_add,map_add,ih,add_zero]
      fin_cases c
      · simp
      · change E.d 2 (39,164) (f.symm (Finsupp.single i 1)) = 0
        rw [hf i]
        fin_cases i
        exact d20
  ext x
  change E.d 2 (39,164) x = 0
  simpa only [LinearEquiv.symm_apply_apply] using hall (f x)

private theorem stem125_af38_four (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (38,163)) := by
  classical
  let E := sequence D .sphere
  have h552 : HasDifferential E 3 (38,163) (41,165)
      ((I.interpretation.basis .sphere 38 163 0)) ((I.interpretation.basis .sphere 41 165 1) + (I.interpretation.basis .sphere 41 165 2)) := stem125_af38_four_h552 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,38,163,["0,1,8,2,298,1"]⟩ (by
    exact List.mem_of_getElem? (i := 335) (by rfl))
  change E.Page 2 (38,163) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 38 163 i.val at he
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,41,165,["16,1,403,1", "8,3,223,1", "0,1,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 347) (by rfl))
  change E.Page 2 (41,165) ≃ₗ[ℤ] (Fin 3 →₀ F2) at g
  change ∀ i : Fin 3, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 41 165 i.val at hg
  have hd2zero : E.d 2 (39,164) = 0  := stem125_af38_four_hd2zero I
  obtain ⟨_,a,b,ha,hb,hd⟩ := h552
  have hd' : E.d 3 (38,163) a = b := hd
  obtain ⟨b2,hb2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hb
  have hb2ne : b2 ≠ 0 := by
    as_aux_lemma =>
      intro hb0
      have hh := hb2.eq_on_page_two
      rw [hb0] at hh
      have ht := congrArg (fun x => g x 1) hh
      rw [map_add,Finsupp.add_apply] at ht
      rw [show I.interpretation.basis .sphere 41 165 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm,
        show I.interpretation.basis .sphere 41 165 2 = g.symm (Finsupp.single 2 1) from (hg 2).symm,
        LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at ht
      norm_num [Finsupp.single_apply,Fin.ext_iff] at ht
  have hbne : b ≠ 0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)≤2) hd2zero hb hb2 hb2ne
  have frame (q : E.Page 3 (38,163)) : q=0 ∨ q=a := by
    as_aux_lemma =>
      apply generated_one (by decide : (2:ℤ)≤3) e a
      rw [he 0]
      change RepresentsOnPage E 3 (38,163) (I.interpretation.basis .sphere 38 163 0) a
      exact ha
  exact choice_next_zero_of_single_frame_nonzero_differential
    (E := E) (r := 3) (by decide) (by change (2:ℤ)≤3; omega)
    a (fun h => hbne (hd'.symm.trans h)) frame

private theorem stem125_e5_zero_af38 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (38,163)) := by
  classical
  exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 5 38 163
    (by decide) (by decide) (stem125_af38_four I)

private theorem tail_af40_three_h563 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (40,165) (42,166)
    (I.interpretation.basis .sphere 40 165 0) (I.interpretation.basis .sphere 42 166 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,40,165,[0],42,166,[1],"S0_AdamsE2_ss",5327⟩ (by
    exact List.mem_of_getElem? (i := 563) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (40,165) (42,166) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 40 165 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 42 166 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af40_three_h562 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (38,164) (40,165)
    (I.interpretation.basis .sphere 38 164 0) (I.interpretation.basis .sphere 40 165 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,38,164,[0],40,165,[1],"S0_AdamsE2_ss",5326⟩ (by
    exact List.mem_of_getElem? (i := 562) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (38,164) (40,165) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 38 164 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 40 165 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af40_three (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 3 (40,165)) := by
  classical
  let E := sequence D .sphere
  have h563 : HasDifferential E 2 (40,165) (42,166)
      (I.interpretation.basis .sphere 40 165 0) (I.interpretation.basis .sphere 42 166 1) := tail_af40_three_h563 I
  have h562 : HasDifferential E 2 (38,164) (40,165)
      (I.interpretation.basis .sphere 38 164 0) (I.interpretation.basis .sphere 40 165 1) := tail_af40_three_h562 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,40,165,["17,1,403,1", "8,6,55,1"]⟩ (by
    exact List.mem_of_getElem? (i := 343) (by rfl))
  change E.Page 2 (40,165) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 40 165 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 40 165 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 40 165 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,42,166,["0,1,16,1,403,1", "0,2,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 352) (by rfl))
  change E.Page 2 (42,166) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 42 166 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 42 166 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 42 166 1 := hf 1
  have hd0 : E.d 2 (40,165) (I.interpretation.basis .sphere 40 165 0) =
      I.interpretation.basis .sphere 42 166 1 := h563.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 3 (40,165) (I.interpretation.basis .sphere 40 165 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h562
  have hd1 : E.d 2 (40,165) (I.interpretation.basis .sphere 40 165 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hz1
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz1⟩
  apply third_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (40,165)
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
    exact RepresentsOnPage.zero (E:=E) (p:=(40,165)) (r:=3) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [zero_add] using (hz1)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem tail_af39_h557 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (39,164) (43,167)
    (I.interpretation.basis .sphere 39 164 0) (I.interpretation.basis .sphere 43 167 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,39,164,[0],43,167,[0],"S0_AdamsE2_ss",5217⟩ (by
    exact List.mem_of_getElem? (i := 557) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (39,164) (43,167) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 39 164 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 43 167 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af39_h567 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (41,166) (44,168)
    (I.interpretation.basis .sphere 41 166 0) (I.interpretation.basis .sphere 44 168 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,41,166,[0],44,168,[0],"S0_AdamsE2_ss",5441⟩ (by
    exact List.mem_of_getElem? (i := 567) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (41,166) (44,168) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 41 166 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 44 168 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af39_h568 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (41,166) (43,167)
    (I.interpretation.basis .sphere 41 166 1) (I.interpretation.basis .sphere 43 167 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,41,166,[1],43,167,[1],"S0_AdamsE2_ss",5442⟩ (by
    exact List.mem_of_getElem? (i := 568) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (41,166) (43,167) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 41 166 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 43 167 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af39 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (39,164)) := by
  classical
  let E := sequence D .sphere
  have h557 : HasDifferential E 4 (39,164) (43,167)
      (I.interpretation.basis .sphere 39 164 0) (I.interpretation.basis .sphere 43 167 0) := tail_af39_h557 I
  have h567 : HasDifferential E 3 (41,166) (44,168)
      (I.interpretation.basis .sphere 41 166 0) (I.interpretation.basis .sphere 44 168 0) := tail_af39_h567 I
  have h568 : HasDifferential E 2 (41,166) (43,167)
      (I.interpretation.basis .sphere 41 166 1) (I.interpretation.basis .sphere 43 167 1) := tail_af39_h568 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,39,164,["0,2,8,2,298,1"]⟩ (by
    exact List.mem_of_getElem? (i := 340) (by rfl))
  change E.Page 2 (39,164) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 39 164 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 39 164 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,41,166,["1,1,685,1", "0,1,17,1,403,1"]⟩ (by
    exact List.mem_of_getElem? (i := 348) (by rfl))
  change E.Page 2 (41,166) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 41 166 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 41 166 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 41 166 1 := hf 1
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,43,167,["0,2,16,1,403,1", "0,3,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 356) (by rfl))
  change E.Page 2 (43,167) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 43 167 i.val at hg
  have hg0 : g.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 43 167 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 43 167 1 := hg 1
  have d21 : E.d 2 (41,166) (I.interpretation.basis .sphere 41 166 1) =
      I.interpretation.basis .sphere 43 167 1 := h568.eq_on_page_two.2
  have d20 : E.d 2 (41,166) (I.interpretation.basis .sphere 41 166 0) = 0 := by
    obtain ⟨_,xr,yr,hxr,_,_⟩ := h567
    obtain ⟨z,hz⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hxr
    rw [←hz.eq_on_page_two] at hz
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hz ⟨xr,hxr⟩
  have incoming_zero (x : E.Page 2 (41,166)) : g (E.d 2 (41,166) x) 0 = 0 := by
    have hall (a : Fin 2 →₀ F2) : g (E.d 2 (41,166) (f.symm a)) 0 = 0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (41,166) (f.symm (Finsupp.single i 1))) 0 = 0
          fin_cases i
          · change g (E.d 2 (41,166) (f.symm (Finsupp.single 0 1))) 0 = 0
            simp only [hf0,d20,map_zero,Finsupp.zero_apply]
          · change g (E.d 2 (41,166) (f.symm (Finsupp.single 1 1))) 0 = 0
            rw [hf1,d21,←hg1,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h557
  have hd' : E.d 4 (39,164) a = b := hd
  obtain ⟨b3,hb3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hb
  have hb3ne : b3 ≠ 0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb3
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (41,166) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (43,167)).Z_anti bot_le) ≫
      (E.ssData (43,167)).pageπ 0) z ∈ LinearMap.range (E.d 2 (41,166)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (43,167)).Z_anti bot_le) ≫
      (E.ssData (43,167)).pageπ 0) z = I.interpretation.basis .sphere 43 167 0 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming_zero u
    rw [hu,←hg0,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply] at hzero
  have in3 : E.d 3 ((43,167)-E.diffDeg 3) = 0 := by
    ext x
    change E.d 3 (40,165) x = 0
    rw [(tail_af40_three I).elim x 0,map_zero]
  have hbne : b ≠ 0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤3; omega) (by decide) in3 hb hb3 hb3ne
  have frame (q : E.Page 4 (39,164)) : q=0 ∨ q=a := by
    have hv (i : Fin 1) : RepresentsOnPage E 4 (39,164) (e.symm (Finsupp.single i 1)) a := by
      rw [he i]
      fin_cases i
      exact ha
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤4) e (fun _=>a) hv q
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hc
    by_cases hz : c 0=0
    · exact Or.inl (by simpa only [hz,ite_true] using hc)
    · exact Or.inr (by simpa only [hz,ite_false] using hc)
  have ker (q : E.Page 4 (39,164)) (hq : E.d 4 (39,164) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 4 ((39,164)-E.diffDeg 4)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [ker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 4 (39,164)
    (by change (2:ℤ)≤4; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))

private theorem stem125_e5_zero_af39 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (39,164)) := by
  classical
  exact tail_af39 I

private theorem tail_af40_h563 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (40,165) (42,166)
    (I.interpretation.basis .sphere 40 165 0) (I.interpretation.basis .sphere 42 166 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,40,165,[0],42,166,[1],"S0_AdamsE2_ss",5327⟩ (by
    exact List.mem_of_getElem? (i := 563) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (40,165) (42,166) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 40 165 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 42 166 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af40_h562 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (38,164) (40,165)
    (I.interpretation.basis .sphere 38 164 0) (I.interpretation.basis .sphere 40 165 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,38,164,[0],40,165,[1],"S0_AdamsE2_ss",5326⟩ (by
    exact List.mem_of_getElem? (i := 562) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (38,164) (40,165) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 38 164 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 40 165 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af40 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (40,165)) := by
  classical
  let E := sequence D .sphere
  have h563 : HasDifferential E 2 (40,165) (42,166)
      (I.interpretation.basis .sphere 40 165 0) (I.interpretation.basis .sphere 42 166 1) := tail_af40_h563 I
  have h562 : HasDifferential E 2 (38,164) (40,165)
      (I.interpretation.basis .sphere 38 164 0) (I.interpretation.basis .sphere 40 165 1) := tail_af40_h562 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,40,165,["17,1,403,1", "8,6,55,1"]⟩ (by
    exact List.mem_of_getElem? (i := 343) (by rfl))
  change E.Page 2 (40,165) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 40 165 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 40 165 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 40 165 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,42,166,["0,1,16,1,403,1", "0,2,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 352) (by rfl))
  change E.Page 2 (42,166) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 42 166 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 42 166 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 42 166 1 := hf 1
  have hd0 : E.d 2 (40,165) (I.interpretation.basis .sphere 40 165 0) =
      I.interpretation.basis .sphere 42 166 1 := h563.eq_on_page_two.2
  have hz1 : RepresentsOnPage E 5 (40,165) (I.interpretation.basis .sphere 40 165 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h562
  have hd1 : E.d 2 (40,165) (I.interpretation.basis .sphere 40 165 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    have hx' := hx.eq_on_page_two
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
      (by simpa only [hx'] using hx) ⟨0,hz1⟩
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (40,165)
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
    exact RepresentsOnPage.zero (E:=E) (p:=(40,165)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [zero_add] using (hz1)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af40 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (40,165)) := by
  classical
  exact tail_af40 I

private theorem tail_af41_four_h567 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (41,166) (44,168)
    (I.interpretation.basis .sphere 41 166 0) (I.interpretation.basis .sphere 44 168 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,41,166,[0],44,168,[0],"S0_AdamsE2_ss",5441⟩ (by
    exact List.mem_of_getElem? (i := 567) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (41,166) (44,168) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 41 166 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 44 168 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af41_four_h568 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (41,166) (43,167)
    (I.interpretation.basis .sphere 41 166 1) (I.interpretation.basis .sphere 43 167 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,41,166,[1],43,167,[1],"S0_AdamsE2_ss",5442⟩ (by
    exact List.mem_of_getElem? (i := 568) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (41,166) (43,167) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 41 166 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 43 167 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af41_four_h574 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (42,167) (44,168)
    (I.interpretation.basis .sphere 42 167 0) (I.interpretation.basis .sphere 44 168 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,42,167,[0],44,168,[1],"S0_AdamsE2_ss",5540⟩ (by
    exact List.mem_of_getElem? (i := 574) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (42,167) (44,168) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 42 167 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 44 168 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af41_four (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 4 (41,166)) := by
  classical
  let E := sequence D .sphere
  have h567 : HasDifferential E 3 (41,166) (44,168)
      (I.interpretation.basis .sphere 41 166 0) (I.interpretation.basis .sphere 44 168 0) := tail_af41_four_h567 I
  have h568 : HasDifferential E 2 (41,166) (43,167)
      (I.interpretation.basis .sphere 41 166 1) (I.interpretation.basis .sphere 43 167 1) := tail_af41_four_h568 I
  have h574 : HasDifferential E 2 (42,167) (44,168)
      (I.interpretation.basis .sphere 42 167 0) (I.interpretation.basis .sphere 44 168 1) := tail_af41_four_h574 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,41,166,["1,1,685,1", "0,1,17,1,403,1"]⟩ (by
    exact List.mem_of_getElem? (i := 348) (by rfl))
  change E.Page 2 (41,166) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 41 166 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 41 166 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 41 166 1 := he 1
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,42,167,["0,2,17,1,403,1"]⟩ (by
    exact List.mem_of_getElem? (i := 353) (by rfl))
  change E.Page 2 (42,167) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 42 167 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 42 167 0 := hf 0
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,44,168,["8,5,110,1", "0,4,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 360) (by rfl))
  change E.Page 2 (44,168) ≃ₗ[ℤ] (Fin 2 →₀ F2) at g
  change ∀ i : Fin 2, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 44 168 i.val at hg
  have hg0 : g.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 44 168 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 44 168 1 := hg 1
  obtain ⟨k,hk⟩ := I.basis ⟨.sphere,43,167,["0,2,16,1,403,1", "0,3,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 356) (by rfl))
  change E.Page 2 (43,167) ≃ₗ[ℤ] (Fin 2 →₀ F2) at k
  change ∀ i : Fin 2, k.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 43 167 i.val at hk
  have hk0 : k.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 43 167 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 43 167 1 := hk 1
  have d20 : E.d 2 (42,167) (I.interpretation.basis .sphere 42 167 0) =
      I.interpretation.basis .sphere 44 168 1 := h574.eq_on_page_two.2
  have incoming_zero (x : E.Page 2 (42,167)) : g (E.d 2 (42,167) x) 0 = 0 := by
    have hall (a : Fin 1 →₀ F2) : g (E.d 2 (42,167) (f.symm a)) 0 = 0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · fin_cases i
          change g (E.d 2 (42,167) (f.symm (Finsupp.single 0 1))) 0 = 0
          rw [hf0,d20,←hg1,LinearEquiv.apply_symm_apply]
          norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h567
  have hd' : E.d 3 (41,166) a = b := hd
  have hbne : b ≠ 0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (42,167) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (44,168)).Z_anti bot_le) ≫
      (E.ssData (44,168)).pageπ 0) z ∈ LinearMap.range (E.d 2 (42,167)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (44,168)).Z_anti bot_le) ≫
      (E.ssData (44,168)).pageπ 0) z = I.interpretation.basis .sphere 44 168 0 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming_zero u
    rw [hu,←hg0,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply] at hzero
  have hn : E.d 2 (41,166) (e.symm (Finsupp.single 1 1)) ≠ 0 := by
    rw [he1]
    have hh : E.d 2 (41,166) (I.interpretation.basis .sphere 41 166 1) =
      I.interpretation.basis .sphere 43 167 1 := h568.eq_on_page_two.2
    rw [hh,←hk1]
    intro hz
    have hz' := congrArg k hz
    simp at hz'
  have frame : ∀ q : E.Page 3 (41,166), q=0 ∨ q=a :=
    frame_after_second (by change (2:ℤ)≤2; omega) (by decide) e (he0.symm ▸ ha) hn
  have ker (q : E.Page 3 (41,166)) (hq : E.d 3 (41,166) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 3 ((41,166)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [ker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (41,166)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))

private theorem stem125_e5_zero_af41 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (41,166)) := by
  classical
  exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 5 41 166
    (by decide) (by decide) (tail_af41_four I)

private theorem tail_af42_h574 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (42,167) (44,168)
    (I.interpretation.basis .sphere 42 167 0) (I.interpretation.basis .sphere 44 168 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,42,167,[0],44,168,[1],"S0_AdamsE2_ss",5540⟩ (by
    exact List.mem_of_getElem? (i := 574) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (42,167) (44,168) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 42 167 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 44 168 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af42 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (42,167)) := by
  classical
  let E := sequence D .sphere
  have h574 : HasDifferential E 2 (42,167) (44,168)
      (I.interpretation.basis .sphere 42 167 0) (I.interpretation.basis .sphere 44 168 1) := tail_af42_h574 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,42,167,["0,2,17,1,403,1"]⟩ (by
    exact List.mem_of_getElem? (i := 353) (by rfl))
  change E.Page 2 (42,167) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 42 167 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 42 167 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,44,168,["8,5,110,1", "0,4,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 360) (by rfl))
  change E.Page 2 (44,168) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 44 168 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = I.interpretation.basis .sphere 44 168 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = I.interpretation.basis .sphere 44 168 1 := hf 1
  have hd0 : E.d 2 (42,167) (I.interpretation.basis .sphere 42 167 0) =
      I.interpretation.basis .sphere 44 168 1 := h574.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (42,167)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i; simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(42,167)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af42 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (42,167)) := by
  classical
  exact tail_af42 I

private theorem stem125_af43 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (43,168)) := by
  classical
  let E := sequence D .sphere
  have one_cases {p : ℤ × ℤ} (e : E.Page 2 p ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2))
      (a : E.Page 2 p) : a=0 ∨ a=e.symm (Finsupp.single 0 1) := by
    have hc : e a = Finsupp.single 0 (e a 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    have ht : e a 0 = 0 ∨ e a 0 = 1 := by
      generalize e a 0 = c
      fin_cases c <;> simp
    rcases ht with ht|ht
    · left
      apply e.injective
      rw [hc]
      simp only [ht,Finsupp.single_zero,map_zero]
    · right
      apply e.injective
      rw [hc]
      simp only [ht,LinearEquiv.apply_symm_apply]
  have two_cases {p : ℤ × ℤ} (e : E.Page 2 p ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Algebra.F2))
      (a : E.Page 2 p) : a=0 ∨ a=e.symm (Finsupp.single 0 1) ∨
        a=e.symm (Finsupp.single 1 1) ∨ a=e.symm (Finsupp.single 0 1)+e.symm (Finsupp.single 1 1) := by
    have hc : e a = Finsupp.single 0 (e a 0) + Finsupp.single 1 (e a 1) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have h0 : e a 0 = 0 ∨ e a 0 = 1 := by generalize e a 0=c; fin_cases c <;> simp
    have h1 : e a 1 = 0 ∨ e a 1 = 1 := by generalize e a 1=c; fin_cases c <;> simp
    rcases h0 with h0|h0 <;> rcases h1 with h1|h1
    · left
      apply e.injective
      rw [hc]
      simp only [h0,h1,Finsupp.single_zero,add_zero,map_zero]
    · right; right; left
      apply e.injective
      rw [hc]
      simp only [h0,h1,Finsupp.single_zero,zero_add,LinearEquiv.apply_symm_apply]
    · right; left
      apply e.injective
      rw [hc]
      simp only [h0,h1,Finsupp.single_zero,add_zero,LinearEquiv.apply_symm_apply]
    · right; right; right
      apply e.injective
      rw [hc]
      simp only [h0,h1,map_add,LinearEquiv.apply_symm_apply]
  have nonzero_basis {p : ℤ × ℤ} {n : ℕ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin n →₀ KIP126.Algebra.F2)) (i : Fin n) :
      e.symm (Finsupp.single i 1) ≠ 0 := by
    intro hz
    have hh := congrArg (fun z => e z i) hz
    simp at hh
  have at_two {p : ℤ × ℤ} {r : ℤ} {a : E.Page 2 p} {b : E.Page r p}
      (hr : 2≤r) (hb : RepresentsOnPage E r p a b) : RepresentsOnPage E 2 p a a := by
    obtain ⟨c,hc⟩ := represents_before (by decide : (2:ℤ)≤2) hr hb
    rw [←hc.eq_on_page_two] at hc
    exact hc
  have row578 : HasDifferential E 3 (42,168) (45,170)
      (I.interpretation.basis .sphere 42 168 0) (I.interpretation.basis .sphere 45 170 0) := by
    have hh := I.adamsStatements _ (List.mem_of_getElem? (i := 578) (by rfl))
    dsimp only [AdamsStatement] at hh
    obtain ⟨u,hu,v,hv,h⟩ := hh
    change HasDifferential E 3 (42,168) (45,170) u v at h
    change I.interpretation.coordinateSum .sphere 42 168 [0] = some u at hu
    change I.interpretation.coordinateSum .sphere 45 170 [0] = some v at hv
    have vx : Raw.coordinatesValid Raw.degrees .sphere 42 168 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 45 170 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hu hv
    rw [←hu,←hv] at h
    exact h
  have row582 : HasDifferential E 4 (43,168) (47,171)
      (I.interpretation.basis .sphere 43 168 0) (I.interpretation.basis .sphere 47 171 0) := by
    have hh := I.adamsStatements _ (List.mem_of_getElem? (i := 582) (by rfl))
    dsimp only [AdamsStatement] at hh
    obtain ⟨u,hu,v,hv,h⟩ := hh
    change HasDifferential E 4 (43,168) (47,171) u v at h
    change I.interpretation.coordinateSum .sphere 43 168 [0] = some u at hu
    change I.interpretation.coordinateSum .sphere 47 171 [0] = some v at hv
    have vx : Raw.coordinatesValid Raw.degrees .sphere 43 168 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 47 171 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hu hv
    rw [←hu,←hv] at h
    exact h
  have row583 : HasDifferential E 2 (43,168) (45,169)
      (I.interpretation.basis .sphere 43 168 1) (I.interpretation.basis .sphere 45 169 0) := by
    have hh := I.adamsStatements _ (List.mem_of_getElem? (i := 583) (by rfl))
    dsimp only [AdamsStatement] at hh
    obtain ⟨u,hu,v,hv,h⟩ := hh
    change HasDifferential E 2 (43,168) (45,169) u v at h
    change I.interpretation.coordinateSum .sphere 43 168 [1] = some u at hu
    change I.interpretation.coordinateSum .sphere 45 169 [0] = some v at hv
    have vx : Raw.coordinatesValid Raw.degrees .sphere 43 168 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 45 169 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hu hv
    rw [←hu,←hv] at h
    exact h
  have row589 : HasDifferential E 2 (44,169) (46,170)
      (I.interpretation.basis .sphere 44 169 0) (I.interpretation.basis .sphere 46 170 0) := by
    have hh := I.adamsStatements _ (List.mem_of_getElem? (i := 589) (by rfl))
    dsimp only [AdamsStatement] at hh
    obtain ⟨u,hu,v,hv,h⟩ := hh
    change HasDifferential E 2 (44,169) (46,170) u v at h
    change I.interpretation.coordinateSum .sphere 44 169 [0] = some u at hu
    change I.interpretation.coordinateSum .sphere 46 170 [0] = some v at hv
    have vx : Raw.coordinatesValid Raw.degrees .sphere 44 169 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 46 170 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hu hv
    rw [←hu,←hv] at h
    exact h
  obtain ⟨e43_168,h43_168⟩ := I.basis ⟨.sphere,43,168,["8,5,111,1", "0,3,17,1,403,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (43,168) ≃ₗ[ℤ] (Fin 2 →₀ KIP126.Algebra.F2) at e43_168
  change ∀i : Fin 2, e43_168.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 43 168 i.val at h43_168
  obtain ⟨e44_169,h44_169⟩ := I.basis ⟨.sphere,44,169,["0,4,17,1,403,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (44,169) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e44_169
  change ∀i : Fin 1, e44_169.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 44 169 i.val at h44_169
  obtain ⟨e45_169,h45_169⟩ := I.basis ⟨.sphere,45,169,["0,5,685,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (45,169) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e45_169
  change ∀i : Fin 1, e45_169.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 45 169 i.val at h45_169
  obtain ⟨e45_170,h45_170⟩ := I.basis ⟨.sphere,45,170,["0,5,17,1,403,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (45,170) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e45_170
  change ∀i : Fin 1, e45_170.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 45 170 i.val at h45_170
  obtain ⟨e46_170,h46_170⟩ := I.basis ⟨.sphere,46,170,["0,6,685,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (46,170) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e46_170
  change ∀i : Fin 1, e46_170.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 46 170 i.val at h46_170
  obtain ⟨e47_171,h47_171⟩ := I.basis ⟨.sphere,47,171,["8,3,253,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (47,171) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e47_171
  change ∀i : Fin 1, e47_171.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 47 171 i.val at h47_171
  have h43_168_0 : e43_168.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 43 168 0 := h43_168 0
  have h43_168_1 : e43_168.symm (Finsupp.single 1 1) = I.interpretation.basis .sphere 43 168 1 := h43_168 1
  have h44_169_0 : e44_169.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 44 169 0 := h44_169 0
  have h45_169_0 : e45_169.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 45 169 0 := h45_169 0
  have h45_170_0 : e45_170.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 45 170 0 := h45_170 0
  have h46_170_0 : e46_170.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 46 170 0 := h46_170 0
  have h47_171_0 : e47_171.symm (Finsupp.single 0 1) = I.interpretation.basis .sphere 47 171 0 := h47_171 0
  have d44 : E.d 2 (44,169) (I.interpretation.basis .sphere 44 169 0) = I.interpretation.basis .sphere 46 170 0 := row589.eq_on_page_two.choose_spec
  have n46 : I.interpretation.basis .sphere 46 170 0 ≠ 0 := by
    rw [←h46_170_0]
    exact nonzero_basis e46_170 0
  have zero44 : Subsingleton (E.Page 3 (44,169)) := by
    have ker (a : E.Page 2 (44,169)) (ha : E.d 2 (44,169) a=0) : a=0 := by
      rcases one_cases e44_169 a with hz|hz
      · exact hz
      · rw [h44_169_0] at hz
        exact (n46 (by simpa only [hz,d44] using ha)).elim
    let S := E.pageShortComplex 2 ((44,169)-E.diffDeg 2)
    have hex : S.Exact := S.moduleCat_exact_iff.mpr (by
      intro a ha
      exact ⟨0,by rw [ker a ha,map_zero]⟩)
    exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 2 (44,169)
      (by change (2:ℤ)≤2; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hex))
  obtain ⟨_,u3,v3,hu3,hv3,huv3⟩ := row578
  have d45 : E.d 2 (45,170) (I.interpretation.basis .sphere 45 170 0) = 0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      (at_two (by decide) hv3) ⟨v3,hv3⟩
  have in2 : E.d 2 ((47,171)-E.diffDeg 2) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change E.d 2 (45,170) a=0
    rcases one_cases e45_170 a with ha|ha
    · rw [ha,map_zero]
    · rw [ha,h45_170_0,d45]
  have in3 : E.d 3 ((47,171)-E.diffDeg 3) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change E.d 3 (44,169) a=0
    rw [zero44.elim a 0,map_zero]
  obtain ⟨_,x4,y4,hx4,hy4,hxy4⟩ := row582
  have hxy : E.d 4 (43,168) x4=y4 := hxy4
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hy4
  have n47 : I.interpretation.basis .sphere 47 171 0 ≠ 0 := by
    rw [←h47_171_0]
    exact nonzero_basis e47_171 0
  have ny3 : y3 ≠ 0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)≤2) in2 hy3 (at_two (by decide) hy4) n47
  have ny4 : y4 ≠ 0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) in3 hy4 hy3 ny3
  have dx0 : E.d 2 (43,168) (I.interpretation.basis .sphere 43 168 0)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<4)
      (at_two (by decide) hx4) ⟨x4,hx4⟩
  have dx1 : E.d 2 (43,168) (I.interpretation.basis .sphere 43 168 1) = I.interpretation.basis .sphere 45 169 0 := row583.eq_on_page_two.choose_spec
  have nx1 : I.interpretation.basis .sphere 45 169 0 ≠ 0 := by
    rw [←h45_169_0]
    exact nonzero_basis e45_169 0
  have ker2 (a : E.Page 2 (43,168)) (ha : E.d 2 (43,168) a=0) :
      a=0 ∨ a=I.interpretation.basis .sphere 43 168 0 := by
    rcases two_cases e43_168 a with hz|hz|hz|hz
    · exact Or.inl hz
    · exact Or.inr (hz.trans h43_168_0)
    · rw [h43_168_1] at hz
      exact (nx1 (by simpa only [hz,dx1] using ha)).elim
    · rw [h43_168_0,h43_168_1] at hz
      exact (nx1 (by simpa only [hz,map_add,dx0,dx1,zero_add] using ha)).elim
  obtain ⟨_,z4,hz4,hz4x⟩ := hx4
  let A := E.ssData (43,168)
  let z3 := (Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide))) z4
  let x3 := A.pageπ 1 z3
  have hdown : (Subobject.ofLE (A.Z 1) (A.Z 0) (A.Z_anti (by decide)) ≫ A.pageπ 0) z3 = I.interpretation.basis .sphere 43 168 0 := by
    change ((Subobject.ofLE (A.Z 2) (A.Z 1) _) ≫ Subobject.ofLE (A.Z 1) (A.Z 0) _ ≫ A.pageπ 0) z4 = _
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz4
  have hz3 : RepresentsOnPage E 3 (43,168) (I.interpretation.basis .sphere 43 168 0) x3 := by
    exact ⟨by decide,z3,hdown,rfl⟩
  have frame3 (a : E.Page 3 (43,168)) : a=0 ∨ a=x3 := by
    apply next_page_two_of_kernel E 2 (by change (2:ℤ)≤2; omega) (43,168) z3
    intro q hq
    have hc := ker2 q hq
    change q=0 ∨ q=(Subobject.ofLE (A.Z 1) (A.Z 0) _ ≫ A.pageπ 0) z3
    rwa [hdown]
  have frame4 (a : E.Page 4 (43,168)) : a=0 ∨ a=x4 := by
    have h := next_page_two_of_kernel E 3 (by change (2:ℤ)≤3; omega) (43,168) z4 (by
      intro q hq
      exact frame3 q) a
    change a=0 ∨ a=A.pageπ 2 z4 at h
    change A.pageπ 2 z4=x4 at hz4x
    rwa [hz4x] at h
  have ker4 (a : E.Page 4 (43,168)) (ha : E.d 4 (43,168) a=0) : a=0 := by
    rcases frame4 a with hz|hz
    · exact hz
    · exact (ny4 (by simpa only [hz,hxy] using ha)).elim
  let S := E.pageShortComplex 4 ((43,168)-E.diffDeg 4)
  have hex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro a ha
    exact ⟨0,by rw [ker4 a ha,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 4 (43,168)
    (by change (2:ℤ)≤4; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hex))

private theorem stem125_e5_zero_af43 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (43,168)) := by
  classical
  exact stem125_af43 I

private theorem tail_af44_h589 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (44,169) (46,170)
    (I.interpretation.basis .sphere 44 169 0) (I.interpretation.basis .sphere 46 170 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,44,169,[0],46,170,[0],"S0_AdamsE2_ss",5772⟩ (by
    exact List.mem_of_getElem? (i := 589) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (44,169) (46,170) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 44 169 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 46 170 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af44 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (44,169)) := by
  classical
  let E := sequence D .sphere
  have h589 : HasDifferential E 2 (44,169) (46,170)
      (I.interpretation.basis .sphere 44 169 0) (I.interpretation.basis .sphere 46 170 0) := tail_af44_h589 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,44,169,["0,4,17,1,403,1"]⟩ (by
    exact List.mem_of_getElem? (i := 361) (by rfl))
  change E.Page 2 (44,169) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 44 169 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 44 169 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,46,170,["0,6,685,1"]⟩ (by
    exact List.mem_of_getElem? (i := 368) (by rfl))
  change E.Page 2 (46,170) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 46 170 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 46 170 0 := hf 0
  have hd0 : E.d 2 (44,169) (I.interpretation.basis .sphere 44 169 0) =
      I.interpretation.basis .sphere 46 170 0 := h589.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (44,169)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i; simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(44,169)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af44 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (44,169)) := by
  classical
  exact tail_af44 I

private theorem tail_af45_h594 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (42,168) (45,170)
    (I.interpretation.basis .sphere 42 168 0) (I.interpretation.basis .sphere 45 170 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,42,168,[0],45,170,[0],"S0_AdamsE2_ss",5862⟩ (by
    exact List.mem_of_getElem? (i := 594) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (42,168) (45,170) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 42 168 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 45 170 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af45 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (45,170)) := by
  classical
  let E := sequence D .sphere
  have h594 : HasDifferential E 3 (42,168) (45,170)
      (I.interpretation.basis .sphere 42 168 0) (I.interpretation.basis .sphere 45 170 0) := tail_af45_h594 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,45,170,["0,5,17,1,403,1"]⟩ (by
    exact List.mem_of_getElem? (i := 365) (by rfl))
  change E.Page 2 (45,170) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 45 170 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 45 170 0 := he 0
  apply fifth_zero_of_all_basis e
  intro i
  rw [he i]
  fin_cases i
  · exact differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide) h594

private theorem stem125_e5_zero_af45 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (45,170)) := by
  classical
  exact tail_af45 I

private theorem tail_af46_h598 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (42,168) (46,171)
    (I.interpretation.basis .sphere 42 168 2) (I.interpretation.basis .sphere 46 171 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,42,168,[2],46,171,[0],"S0_AdamsE2_ss",5977⟩ (by
    exact List.mem_of_getElem? (i := 598) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (42,168) (46,171) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 42 168 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 46 171 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af46 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (46,171)) := by
  classical
  let E := sequence D .sphere
  have h598 : HasDifferential E 4 (42,168) (46,171)
      (I.interpretation.basis .sphere 42 168 2) (I.interpretation.basis .sphere 46 171 0) := tail_af46_h598 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,46,171,["8,2,17,1,200,1"]⟩ (by
    exact List.mem_of_getElem? (i := 369) (by rfl))
  change E.Page 2 (46,171) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 46 171 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 46 171 0 := he 0
  apply fifth_zero_of_all_basis e
  intro i
  rw [he i]
  fin_cases i
  · exact differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h598

private theorem stem125_e5_zero_af46 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (46,171)) := by
  classical
  exact tail_af46 I

private theorem stem125_e5_zero_38_to_46 (I : AdamsComputationTheorems D L G)
    (s : ℕ) (hs : 38 ≤ s) (hs' : s ≤ 46) :
    Subsingleton ((sequence D .sphere).Page 5 (s,(s : ℤ)+125)) := by
  classical

  interval_cases s
  · exact stem125_e5_zero_af38 I
  · exact stem125_e5_zero_af39 I
  · exact stem125_e5_zero_af40 I
  · exact stem125_e5_zero_af41 I
  · exact stem125_e5_zero_af42 I
  · exact stem125_e5_zero_af43 I
  · exact stem125_e5_zero_af44 I
  · exact stem125_e5_zero_af45 I
  · exact stem125_e5_zero_af46 I

private theorem tail_af47 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (47,172)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,47,172,[]⟩ (by
    exact List.mem_of_getElem? (i := 374) (by rfl))
  change E.Page 2 (47,172) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 47 172 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af47 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (47,172)) := by
  classical
  exact tail_af47 I

private theorem tail_af48 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (48,173)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,48,173,[]⟩ (by
    exact List.mem_of_getElem? (i := 377) (by rfl))
  change E.Page 2 (48,173) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 48 173 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af48 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (48,173)) := by
  classical
  exact tail_af48 I

private theorem tail_af49_h609 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 4 (45,171) (49,174)
    (I.interpretation.basis .sphere 45 171 0) (I.interpretation.basis .sphere 49 174 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,45,171,[0],49,174,[0],"S0_AdamsE2_ss",6296⟩ (by
    exact List.mem_of_getElem? (i := 609) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 4 (45,171) (49,174) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 45 171 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 49 174 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af49 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (49,174)) := by
  classical
  let E := sequence D .sphere
  have h609 : HasDifferential E 4 (45,171) (49,174)
      (I.interpretation.basis .sphere 45 171 0) (I.interpretation.basis .sphere 49 174 0) := tail_af49_h609 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,49,174,["8,1,607,1"]⟩ (by
    exact List.mem_of_getElem? (i := 380) (by rfl))
  change E.Page 2 (49,174) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 49 174 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 49 174 0 := he 0
  apply fifth_zero_of_all_basis e
  intro i
  rw [he i]
  fin_cases i
  · exact differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h609

private theorem stem125_e5_zero_af49 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (49,174)) := by
  classical
  exact tail_af49 I

private theorem tail_af50 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (50,175)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,50,175,[]⟩ (by
    exact List.mem_of_getElem? (i := 384) (by rfl))
  change E.Page 2 (50,175) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 50 175 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af50 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (50,175)) := by
  classical
  exact tail_af50 I

private theorem tail_af51 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (51,176)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,51,176,[]⟩ (by
    exact List.mem_of_getElem? (i := 387) (by rfl))
  change E.Page 2 (51,176) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 51 176 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af51 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (51,176)) := by
  classical
  exact tail_af51 I

private theorem stem125_af52 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (52,177)) := by
  classical
  let E := sequence D .sphere
  have empty (s t : ℕ) (hd : (⟨.sphere,s,t,[]⟩ : Raw.Degree) ∈ Raw.degrees)
      (r : ℤ) (hr : 2 ≤ r) : Subsingleton (E.Page r (s,t)) := by
    obtain ⟨e,_⟩ := I.basis _ hd
    change E.Page 2 (s,t) ≃ₗ[ℤ] (Fin 0 →₀ KIP126.Algebra.F2) at e
    have he : Subsingleton (E.Page 2 (s,t)) := e.injective.subsingleton
    exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 2 r s t
      (by decide) hr he
  have h54 : Subsingleton (E.Page 2 (54,179)) :=
    empty 54 179 (by simp [Raw.degrees]) 2 (by decide)
  have h53 : Subsingleton (E.Page 3 (53,178)) :=
    empty 53 178 (by simp [Raw.degrees]) 3 (by decide)
  have in2 : E.d 2 ((56,180)-E.diffDeg 2) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change E.d 2 (54,179) x=0
    rw [h54.elim x 0,map_zero]
  have in3 : E.d 3 ((56,180)-E.diffDeg 3) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change E.d 3 (53,178) x=0
    rw [h53.elim x 0,map_zero]
  have hrow := I.adamsStatements _ (List.mem_of_getElem? (i := 618) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential E 4 (52,177) (56,180) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 52 177 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 56 180 [0] = true := rfl
  change I.interpretation.coordinateSum .sphere 52 177 [0] = some a at ha
  change I.interpretation.coordinateSum .sphere 56 180 [0] = some b at hb
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  obtain ⟨_,x,y,hx,hy,hxy⟩ := h
  have hxy' : E.d 4 (52,177) x=y := hxy
  obtain ⟨eT,heT⟩ := I.basis ⟨.sphere,56,180,["8,1,661,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (56,180) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at eT
  change ∀i : Fin 1, eT.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 56 180 i.val at heT
  have hn : I.interpretation.basis .sphere 56 180 0 ≠ 0 := by
    have h0 := heT (0 : Fin 1)
    change eT.symm (Finsupp.single (0 : Fin 1) 1) = I.interpretation.basis .sphere 56 180 0 at h0
    rw [←h0]
    intro hz
    have hc := congrArg (fun z => eT z (0 : Fin 1)) hz
    simp at hc
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hy
  have hy2 : RepresentsOnPage E 2 (56,180)
      (I.interpretation.basis .sphere 56 180 0) (I.interpretation.basis .sphere 56 180 0) := by
    obtain ⟨y2,hy2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hy
    rw [←hy2.eq_on_page_two] at hy2
    exact hy2
  have hn3 : y3 ≠ 0 := represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤2; omega)
    (by decide : (2:ℤ)≤2) in2 hy3 hy2 hn
  have hn4 : y ≠ 0 := represents_next_nonzero_of_incoming_zero_at (by change (2:ℤ)≤3; omega)
    (by decide : (2:ℤ)≤3) in3 hy hy3 hn3
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,52,177,["8,2,469,1"]⟩ (by simp [Raw.degrees])
  change E.Page 2 (52,177) ≃ₗ[ℤ] (Fin 1 →₀ KIP126.Algebra.F2) at e
  change ∀i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 52 177 i.val at he
  have frame (a : E.Page 4 (52,177)) : a=0 ∨ a=x := by
    have hv (i : Fin 1) : RepresentsOnPage E 4 (52,177) (e.symm (Finsupp.single i 1)) x := by
      rw [he i]
      fin_cases i
      exact hx
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤4) e (fun _ => x) hv a
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hc
    by_cases hcz : c 0=0
    · exact Or.inl (by simpa only [hcz,ite_true] using hc)
    · exact Or.inr (by simpa only [hcz,ite_false] using hc)
  have ker (a : E.Page 4 (52,177)) (ha : E.d 4 (52,177) a=0) : a=0 := by
    rcases frame a with hz|hz
    · exact hz
    · exact (hn4 (by simpa only [hz,hxy'] using ha)).elim
  let S := E.pageShortComplex 4 ((52,177)-E.diffDeg 4)
  have hex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro a ha
    exact ⟨0,by rw [ker a ha,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 4 (52,177)
    (by change (2:ℤ)≤4; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hex))

private theorem stem125_e5_zero_af52 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (52,177)) := by
  classical
  exact stem125_af52 I

private theorem tail_af53 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (53,178)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,53,178,[]⟩ (by
    exact List.mem_of_getElem? (i := 393) (by rfl))
  change E.Page 2 (53,178) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 53 178 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af53 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (53,178)) := by
  classical
  exact tail_af53 I

private theorem tail_af54 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (54,179)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,54,179,[]⟩ (by
    exact List.mem_of_getElem? (i := 396) (by rfl))
  change E.Page 2 (54,179) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 54 179 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af54 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (54,179)) := by
  classical
  exact tail_af54 I

private theorem tail_af55_h626 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (55,180) (57,181)
    (I.interpretation.basis .sphere 55 180 0) (I.interpretation.basis .sphere 57 181 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,55,180,[0],57,181,[0],"S0_AdamsE2_ss",7007⟩ (by
    exact List.mem_of_getElem? (i := 626) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (55,180) (57,181) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 55 180 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 57 181 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af55 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (55,180)) := by
  classical
  let E := sequence D .sphere
  have h626 : HasDifferential E 2 (55,180) (57,181)
      (I.interpretation.basis .sphere 55 180 0) (I.interpretation.basis .sphere 57 181 0) := tail_af55_h626 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,55,180,["16,1,554,1"]⟩ (by
    exact List.mem_of_getElem? (i := 399) (by rfl))
  change E.Page 2 (55,180) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 55 180 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 55 180 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,57,181,["0,1,8,1,661,1"]⟩ (by
    exact List.mem_of_getElem? (i := 408) (by rfl))
  change E.Page 2 (57,181) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 57 181 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 57 181 0 := hf 0
  have hd0 : E.d 2 (55,180) (I.interpretation.basis .sphere 55 180 0) =
      I.interpretation.basis .sphere 57 181 0 := h626.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (55,180)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i; simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(55,180)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af55 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (55,180)) := by
  classical
  exact tail_af55 I

private theorem tail_af56_h629 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 2 (56,181) (58,182)
    (I.interpretation.basis .sphere 56 181 0) (I.interpretation.basis .sphere 58 182 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,56,181,[0],58,182,[0],"S0_AdamsE2_ss",7162⟩ (by
    exact List.mem_of_getElem? (i := 629) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 2 (56,181) (58,182) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 56 181 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 58 182 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af56 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (56,181)) := by
  classical
  let E := sequence D .sphere
  have h629 : HasDifferential E 2 (56,181) (58,182)
      (I.interpretation.basis .sphere 56 181 0) (I.interpretation.basis .sphere 58 182 0) := tail_af56_h629 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,56,181,["0,1,16,1,554,1"]⟩ (by
    exact List.mem_of_getElem? (i := 404) (by rfl))
  change E.Page 2 (56,181) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 56 181 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 56 181 0 := he 0
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,58,182,["0,2,8,1,661,1"]⟩ (by
    exact List.mem_of_getElem? (i := 413) (by rfl))
  change E.Page 2 (58,182) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 58 182 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 58 182 0 := hf 0
  have hd0 : E.d 2 (56,181) (I.interpretation.basis .sphere 56 181 0) =
      I.interpretation.basis .sphere 58 182 0 := h629.eq_on_page_two.2
  apply fifth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (56,181)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0)) := by
    apply Finsupp.ext
    intro i
    fin_cases i; simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  fin_cases c0
  · change x = e.symm (Finsupp.single 0 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(56,181)) (r:=5) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply, Fin.ext_iff] at hval

private theorem stem125_e5_zero_af56 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (56,181)) := by
  classical
  exact tail_af56 I

private theorem tail_af57_h633 (I : AdamsComputationTheorems D L G) : HasDifferential (sequence D .sphere) 3 (54,180) (57,182)
    (I.interpretation.basis .sphere 54 180 0) (I.interpretation.basis .sphere 57 182 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,54,180,[0],57,182,[0],"S0_AdamsE2_ss",7247⟩ (by
    exact List.mem_of_getElem? (i := 633) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D .sphere) 3 (54,180) (57,182) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 54 180 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 57 182 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem tail_af57 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (57,182)) := by
  classical
  let E := sequence D .sphere
  have h633 : HasDifferential E 3 (54,180) (57,182)
      (I.interpretation.basis .sphere 54 180 0) (I.interpretation.basis .sphere 57 182 0) := tail_af57_h633 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,57,182,["0,2,16,1,554,1"]⟩ (by
    exact List.mem_of_getElem? (i := 409) (by rfl))
  change E.Page 2 (57,182) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 57 182 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 57 182 0 := he 0
  apply fifth_zero_of_all_basis e
  intro i
  rw [he i]
  fin_cases i
  · exact differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide) h633

private theorem stem125_e5_zero_af57 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (57,182)) := by
  classical
  exact tail_af57 I

private theorem tail_af58 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (58,183)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,58,183,[]⟩ (by
    exact List.mem_of_getElem? (i := 414) (by rfl))
  change E.Page 2 (58,183) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 58 183 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af58 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (58,183)) := by
  classical
  exact tail_af58 I

private theorem tail_af59 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (59,184)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,59,184,[]⟩ (by
    exact List.mem_of_getElem? (i := 417) (by rfl))
  change E.Page 2 (59,184) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 59 184 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af59 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (59,184)) := by
  classical
  exact tail_af59 I

private theorem tail_af60 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (60,185)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,60,185,[]⟩ (by
    exact List.mem_of_getElem? (i := 420) (by rfl))
  change E.Page 2 (60,185) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 60 185 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af60 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (60,185)) := by
  classical
  exact tail_af60 I

private theorem tail_af61 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (61,186)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,61,186,[]⟩ (by
    exact List.mem_of_getElem? (i := 423) (by rfl))
  change E.Page 2 (61,186) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 61 186 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af61 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (61,186)) := by
  classical
  exact tail_af61 I

private theorem tail_af62 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (62,187)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,62,187,[]⟩ (by
    exact List.mem_of_getElem? (i := 426) (by rfl))
  change E.Page 2 (62,187) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 62 187 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af62 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (62,187)) := by
  classical
  exact tail_af62 I

private theorem tail_af63 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (63,188)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,63,188,[]⟩ (by
    exact List.mem_of_getElem? (i := 429) (by rfl))
  change E.Page 2 (63,188) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 63 188 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af63 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (63,188)) := by
  classical
  exact tail_af63 I

private theorem tail_af64 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (64,189)) := by
  classical
  let E := sequence D .sphere
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,64,189,[]⟩ (by
    exact List.mem_of_getElem? (i := 432) (by rfl))
  change E.Page 2 (64,189) ≃ₗ[ℤ] (Fin 0 →₀ F2) at e
  change ∀ i : Fin 0, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 64 189 i.val at he
  apply fifth_zero_of_all_basis e
  intro i
  exact Fin.elim0 i

private theorem stem125_e5_zero_af64 (I : AdamsComputationTheorems D L G) :
    Subsingleton ((sequence D .sphere).Page 5 (64,189)) := by
  classical
  exact tail_af64 I

private theorem stem125_e5_zero_47_to_64 (I : AdamsComputationTheorems D L G)
    (s : ℕ) (hs : 47 ≤ s) (hs' : s ≤ 64) :
    Subsingleton ((sequence D .sphere).Page 5 (s,(s : ℤ)+125)) := by
  classical

  interval_cases s
  · exact stem125_e5_zero_af47 I
  · exact stem125_e5_zero_af48 I
  · exact stem125_e5_zero_af49 I
  · exact stem125_e5_zero_af50 I
  · exact stem125_e5_zero_af51 I
  · exact stem125_e5_zero_af52 I
  · exact stem125_e5_zero_af53 I
  · exact stem125_e5_zero_af54 I
  · exact stem125_e5_zero_af55 I
  · exact stem125_e5_zero_af56 I
  · exact stem125_e5_zero_af57 I
  · exact stem125_e5_zero_af58 I
  · exact stem125_e5_zero_af59 I
  · exact stem125_e5_zero_af60 I
  · exact stem125_e5_zero_af61 I
  · exact stem125_e5_zero_af62 I
  · exact stem125_e5_zero_af63 I
  · exact stem125_e5_zero_af64 I

/-- This is a finite, record-derived assertion.  There are 38 staircase
rows in this range, all at levels 2,3,4,9996,9997,9998; certification must
prove their equations and local basis completeness before deriving this.
Empty components use `I.basis` on explicitly included empty degrees. -/
theorem stem125_e5_zero_finite (I : AdamsComputationTheorems D L G)
    (s : ℕ) (hs : 26 ≤ s) (hs' : s ≤ 64) :
    Subsingleton ((sequence D .sphere).Page 5 (s,(s : ℤ)+125)) := by
  by_cases h37 : s ≤ 37
  · exact stem125_e5_zero_26_to_37 I s hs h37
  · by_cases h46 : s ≤ 46
    · exact stem125_e5_zero_38_to_46 I s (by omega) h46
    · exact stem125_e5_zero_47_to_64 I s (by omega) hs'
end

end
end KIP126.Computation.SphereAndCofiber
end
