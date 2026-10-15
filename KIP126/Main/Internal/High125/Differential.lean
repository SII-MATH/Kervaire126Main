module
public import KIP126.Main.Conditions
import all KIP126.Main.Internal.Selected.NormalizedTable
import all KIP126.Main.Internal.PageCalculus
/-! Original finite-page proofs from the pinned Main/Solution/Computation
baseline bbac1fc05843 (MIT), transported along a proved equality with the
same actual Adams sequence. No additional mathematical input. -/
@[expose] section
namespace KIP126.Main.Internal.High125
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Main.Internal KIP126.Computation.Table.Raw
open KIP126.Main.Internal.Selected.Normalized
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
private theorem af17_three_h387  : HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 2 (17,142) (19,143)
    (basis .sphere 17 142 1) (basis .sphere 19 143 1) := by
  classical
  have hrow := result ⟨.sphere,.equation,2,17,142,[1],19,143,[1],"S0_AdamsE2_ss",3320⟩ (by
    exact List.mem_of_getElem? (i := 387) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 2 (17,142) (19,143) x y at hd
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 17 142 [1] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 19 143 [1] = true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af17_three_h386  : HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 2 (15,141) (17,142)
    (basis .sphere 15 141 0) (basis .sphere 17 142 0) := by
  classical
  have hrow := result ⟨.sphere,.equation,2,15,141,[0],17,142,[0],"S0_AdamsE2_ss",3319⟩ (by
    exact List.mem_of_getElem? (i := 386) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 2 (15,141) (17,142) x y at hd
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 141 [0] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 17 142 [0] = true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af17_three  :
    Subsingleton ((KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 3 (17,142)) := by
  classical
  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h387 : HasDifferential E 2 (17,142) (19,143)
      (basis .sphere 17 142 1) (basis .sphere 19 143 1) := af17_three_h387
  have h386 : HasDifferential E 2 (15,141) (17,142)
      (basis .sphere 15 141 0) (basis .sphere 17 142 0) := af17_three_h386
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,17,142,["0,2,67,1,107,1", "0,3,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 240) (by rfl))
  change E.Page 2 (17,142) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = basis .sphere 17 142 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = basis .sphere 17 142 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = basis .sphere 17 142 1 := he 1
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,19,143,["8,1,293,1", "0,5,440,1"]⟩ (by
    exact List.mem_of_getElem? (i := 251) (by rfl))
  change E.Page 2 (19,143) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = basis .sphere 19 143 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = basis .sphere 19 143 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = basis .sphere 19 143 1 := hf 1
  have hd1 : E.d 2 (17,142) (basis .sphere 17 142 1) =
      basis .sphere 19 143 1 := h387.eq_on_page_two.2
  have hz0 : RepresentsOnPage E 3 (17,142) (basis .sphere 17 142 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h386
  have hd0 : E.d 2 (17,142) (basis .sphere 17 142 0) = 0 := by
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


private theorem af16_d4_zero_h369  : HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 2 (14,140) (16,141)
    (basis .sphere 14 140 1) (basis .sphere 16 141 2) := by
  classical
  have hrow := result ⟨.sphere,.equation,2,14,140,[1],16,141,[2],"S0_AdamsE2_ss",3253⟩ (by
    exact List.mem_of_getElem? (i := 369) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 2 (14,140) (16,141) x y at hd
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 14 140 [1] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [2] = true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af16_d4_zero_h370  : HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 4 (12,138) (16,141)
    (basis .sphere 12 138 3) (basis .sphere 16 141 1) := by
  classical
  have hrow := result ⟨.sphere,.equation,4,12,138,[3],16,141,[1],"S0_AdamsE2_ss",3254⟩ (by
    exact List.mem_of_getElem? (i := 370) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 4 (12,138) (16,141) x y at hd
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 138 [3] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [1] = true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af16_d4_zero_h371  : HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 2 (16,141) (18,142)
    (basis .sphere 16 141 0) (basis .sphere 18 142 0 + basis .sphere 18 142 1) := by
  classical
  have hrow := result ⟨.sphere,.equation,2,16,141,[0],18,142,[0, 1],"S0_AdamsE2_ss",3255⟩ (by
    exact List.mem_of_getElem? (i := 371) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 2 (16,141) (18,142) x y at hd
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [0] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 142 [0, 1] = true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af16_d4_zero_h372  : HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 2 (16,141) (18,142)
    (basis .sphere 16 141 3) (basis .sphere 18 142 1) := by
  classical
  have hrow := result ⟨.sphere,.equation,2,16,141,[3],18,142,[1],"S0_AdamsE2_ss",3256⟩ (by
    exact List.mem_of_getElem? (i := 372) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 2 (16,141) (18,142) x y at hd
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [3] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 142 [1] = true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af16_d4_zero  : (KIP126.Main.Internal.Selected.Normalized.sequence .sphere).d 4 (16,141)=0 := by
  classical
  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h369 : HasDifferential E 2 (14,140) (16,141)
      (basis .sphere 14 140 1) (basis .sphere 16 141 2) := af16_d4_zero_h369
  have h370 : HasDifferential E 4 (12,138) (16,141)
      (basis .sphere 12 138 3) (basis .sphere 16 141 1) := af16_d4_zero_h370
  have h371 : HasDifferential E 2 (16,141) (18,142)
      (basis .sphere 16 141 0) (basis .sphere 18 142 0 + basis .sphere 18 142 1) := af16_d4_zero_h371
  have h372 : HasDifferential E 2 (16,141) (18,142)
      (basis .sphere 16 141 3) (basis .sphere 18 142 1) := af16_d4_zero_h372
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,16,141,["473,1", "1,1,448,1", "0,1,67,1,107,1", "0,2,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 232) (by rfl))
  change E.Page 2 (16,141) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = basis .sphere 16 141 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = basis .sphere 16 141 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = basis .sphere 16 141 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = basis .sphere 16 141 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = basis .sphere 16 141 3 := he 3
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,18,142,["0,1,472,1", "0,4,440,1"]⟩ (by
    exact List.mem_of_getElem? (i := 245) (by rfl))
  change E.Page 2 (18,142) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = basis .sphere 18 142 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = basis .sphere 18 142 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = basis .sphere 18 142 1 := hf 1
  obtain ⟨_,u,v,hu,hv,hd⟩ := h370
  have hd' : E.d 4 (12,138) u=v := hd
  have hdv : E.d 4 (16,141) v=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=4) (p:=(12,138)) ⟨u,hd'⟩
  have hv2 : RepresentsOnPage E 2 (16,141) (basis .sphere 16 141 1)
      (basis .sphere 16 141 1) := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hv
    rw [←hb.eq_on_page_two] at hb
    exact hb
  have hd1 : E.d 2 (16,141) (basis .sphere 16 141 1)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hv2 ⟨v,hv⟩
  have hz2 : RepresentsOnPage E 4 (16,141) (basis .sphere 16 141 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h369
  have hd2 : E.d 2 (16,141) (basis .sphere 16 141 2)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hz2
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz2⟩
  have hd0 : E.d 2 (16,141) (basis .sphere 16 141 0) =
      basis .sphere 18 142 0 + basis .sphere 18 142 1 := h371.eq_on_page_two.2
  have hd3 : E.d 2 (16,141) (basis .sphere 16 141 3) =
      basis .sphere 18 142 1 := h372.eq_on_page_two.2
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


private theorem af15_d5_target_nonzero_h397  : HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 5 (13,139) (18,143)
    (basis .sphere 13 139 0) (basis .sphere 18 143 0) := by
  classical
  have hrow := result ⟨.sphere,.equation,5,13,139,[0],18,143,[0],"S0_AdamsE2_ss",3391⟩ (by
    exact List.mem_of_getElem? (i := 397) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 5 (13,139) (18,143) x y at hd
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 139 [0] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 143 [0] = true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af15_d5_target_nonzero_h398  : HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 2 (18,143) (20,144)
    (basis .sphere 18 143 1) (basis .sphere 20 144 1) := by
  classical
  have hrow := result ⟨.sphere,.equation,2,18,143,[1],20,144,[1],"S0_AdamsE2_ss",3392⟩ (by
    exact List.mem_of_getElem? (i := 398) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 2 (18,143) (20,144) x y at hd
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 143 [1] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 20 144 [1] = true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem af15_d5_target_nonzero
    (y : (KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 5 (20,144))
    (hy : RepresentsOnPage (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 5 (20,144)
      (basis .sphere 20 144 0) y) : y ≠ 0 := by
  classical
  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h397 : HasDifferential E 5 (13,139) (18,143)
      (basis .sphere 13 139 0) (basis .sphere 18 143 0) := af15_d5_target_nonzero_h397
  have h398 : HasDifferential E 2 (18,143) (20,144)
      (basis .sphere 18 143 1) (basis .sphere 20 144 1) := af15_d5_target_nonzero_h398
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,18,143,["8,2,209,1", "0,4,449,1"]⟩ (by
    exact List.mem_of_getElem? (i := 246) (by rfl))
  change E.Page 2 (18,143) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = basis .sphere 18 143 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = basis .sphere 18 143 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = basis .sphere 18 143 1 := he 1
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,20,144,["8,2,212,1", "0,6,440,1"]⟩ (by
    exact List.mem_of_getElem? (i := 256) (by rfl))
  change E.Page 2 (20,144) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = basis .sphere 20 144 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = basis .sphere 20 144 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = basis .sphere 20 144 1 := hf 1
  obtain ⟨_,u,v,hu,hv,hd⟩ := h397
  have hb0 : RepresentsOnPage E 2 (18,143) (basis .sphere 18 143 0)
      (basis .sphere 18 143 0) := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hv
    rw [←hb.eq_on_page_two] at hb
    exact hb
  have hd0 : E.d 2 (18,143) (basis .sphere 18 143 0)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb0 ⟨v,hv⟩
  have hd1 : E.d 2 (18,143) (basis .sphere 18 143 1)=basis .sphere 20 144 1 := h398.eq_on_page_two.2
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
    change (Subobject.ofLE _ _ ((E.ssData (20,144)).Z_anti bot_le) ≫ (E.ssData (20,144)).pageπ 0) zz = basis .sphere 20 144 0 at hzz
    rw [hzz] at hh
    obtain ⟨q,hq⟩ := hh
    have hh := hcoord q
    rw [hq,←hf0,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  have in3 : E.d 3 ((20,144)-E.diffDeg 3)=0 := by
    ext a
    change E.d 3 (17,142) a=0
    rw [(af17_three ).elim a 0,map_zero]
  have in4 : E.d 4 ((20,144)-E.diffDeg 4)=0 := af16_d4_zero
  obtain ⟨y4,hy4⟩ := represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hy
  have ny4 : y4 ≠ 0 := represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) in3 hy4 hy3 ny3
  exact represents_next_nonzero_of_incoming_zero_at
    (by change (2:ℤ)≤4; omega) (by decide : (2:ℤ)≤4) in4 hy hy4 ny4

private theorem stem125_af15_nonzero_d5_h356  : HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 5 (15,140) (20,144)
    (basis .sphere 15 140 2) (basis .sphere 20 144 0) := by
  classical
  have hrow := result ⟨.sphere,.equation,5,15,140,[2],20,144,[0],"S0_AdamsE2_ss",3152⟩ (by
    exact List.mem_of_getElem? (i := 356) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 5 (15,140) (20,144) x y at hd
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [2] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 20 144 [0] = true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

theorem stem125_af15_nonzero_d5  :
    ∃ (x : Page .sphere 15 140) (y : Page .sphere 20 144),
      decode .sphere 15 140 [2] = some x ∧
      decode .sphere 20 144 [0] = some y ∧
      HasNonzeroDifferential (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 5 (15,140) (20,144) x y := by
  classical

  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h356 : HasDifferential E 5 (15,140) (20,144)
      (basis .sphere 15 140 2) (basis .sphere 20 144 0) := stem125_af15_nonzero_d5_h356
  refine ⟨basis .sphere 15 140 2,basis .sphere 20 144 0,?_,?_,?_⟩
  · have h : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [2] = true := rfl
    simp only [decode,h,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  · have h : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 20 144 [0] = true := rfl
    simp only [decode,h,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  · obtain ⟨hp,xr,yr,hxr,hyr,hd⟩ := h356
    exact ⟨hp,xr,yr,hxr,hyr,hd,af15_d5_target_nonzero  yr hyr⟩
end
end KIP126.Main.Internal.High125
