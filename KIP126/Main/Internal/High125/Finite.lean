module
public import KIP126.Main.Conditions
import all KIP126.Main.Internal.High125.Pages
import all KIP126.Main.Internal.High125.Differential
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
private theorem h125_page15  :
    Subsingleton ((KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 6 (15,140)) := by
  classical
  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h354 : HasDifferential E 2 (13,139) (15,140)
      (basis .sphere 13 139 1) (basis .sphere 15 140 4) := by
    have hrow := result ⟨.sphere,.equation,2,13,139,[1],15,140,[4],"S0_AdamsE2_ss",3150⟩ (by
      exact List.mem_of_getElem? (i := 354) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (13,139) (15,140) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 139 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [4] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h355 : HasDifferential E 4 (11,137) (15,140)
      (basis .sphere 11 137 2) (basis .sphere 15 140 1) := by
    have hrow := result ⟨.sphere,.equation,4,11,137,[2],15,140,[1],"S0_AdamsE2_ss",3151⟩ (by
      exact List.mem_of_getElem? (i := 355) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (11,137) (15,140) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 137 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h357 : HasDifferential E 2 (15,140) (17,141)
      (basis .sphere 15 140 0) (basis .sphere 17 141 3) := by
    have hrow := result ⟨.sphere,.equation,2,15,140,[0],17,141,[3],"S0_AdamsE2_ss",3153⟩ (by
      exact List.mem_of_getElem? (i := 357) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (15,140) (17,141) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 17 141 [3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h358 : HasDifferential E 2 (15,140) (17,141)
      (basis .sphere 15 140 3) (basis .sphere 17 141 1) := by
    have hrow := result ⟨.sphere,.equation,2,15,140,[3],17,141,[1],"S0_AdamsE2_ss",3154⟩ (by
      exact List.mem_of_getElem? (i := 358) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (15,140) (17,141) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 17 141 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,15,140,["456,1", "67,1,107,1", "1,1,439,1", "0,1,449,1", "0,3,425,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 224 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (15,140) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = basis .sphere 15 140 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = basis .sphere 15 140 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = basis .sphere 15 140 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = basis .sphere 15 140 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = basis .sphere 15 140 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = basis .sphere 15 140 4 := he 4
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,17,141,["472,1", "0,2,448,1", "0,3,440,1", "0,3,439,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 239 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (17,141) ≃ₗ[ℤ] (Fin 4 →₀ F2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1) = basis .sphere 17 141 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 4) 1) = basis .sphere 17 141 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 4) 1) = basis .sphere 17 141 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 4) 1) = basis .sphere 17 141 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 4) 1) = basis .sphere 17 141 3 := hf 3
  obtain ⟨x,y,hx,hy,hd⟩ := stem125_af15_nonzero_d5
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [2]=true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 20 144 [0]=true := rfl
  simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  obtain ⟨_,u,v,hu,hv,hd,hn⟩ := hd
  have hd' : E.d 5 (15,140) u=v := hd
  have hz1 : RepresentsOnPage E 5 (15,140) (basis .sphere 15 140 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h355
  have hz4 : RepresentsOnPage E 5 (15,140) (basis .sphere 15 140 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h354
  have hd1 : E.d 2 (15,140) (basis .sphere 15 140 1)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz1⟩
  have hd2 : E.d 2 (15,140) (basis .sphere 15 140 2)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hu
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨u,hu⟩
  have hd4 : E.d 2 (15,140) (basis .sphere 15 140 4)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz4
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz4⟩
  have hd0 : E.d 2 (15,140) (basis .sphere 15 140 0)=basis .sphere 17 141 3 := h357.eq_on_page_two.2
  have hd3 : E.d 2 (15,140) (basis .sphere 15 140 3)=basis .sphere 17 141 1 := h358.eq_on_page_two.2
  have frame : ∀a : E.Page 5 (15,140), a=0 ∨ a=u := by
    apply fifth_frame_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (15,140) u
    intro x hx
    have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) + Finsupp.single 4 (e x 4)) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) + Finsupp.single 4 (e x 4)) := by rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0=c0 at hxe
    generalize hc1 : e x 1=c1 at hxe
    generalize hc2 : e x 2=c2 at hxe
    generalize hc3 : e x 3=c3 at hxe
    generalize hc4 : e x 4=c4 at hxe
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
      rw [hxe] at hx ⊢
      exact ⟨0,RepresentsOnPage.zero (by decide),Or.inl rfl⟩
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he4]
      refine ⟨0,hz4,?_⟩
      left
      simp only []
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [he3, hd3] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he3, he4, hd3, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he2]
      refine ⟨u,hu,?_⟩
      right
      simp only []
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he2, he4]
      refine ⟨u + 0,represents_add_tail (hu) hz4,?_⟩
      right
      simp only [add_zero]
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he2, he3, hd2, hd3, zero_add] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he2, he3, he4, hd2, hd3, hd4, zero_add, add_zero] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he1]
      refine ⟨0,hz1,?_⟩
      left
      simp only []
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he1, he4]
      refine ⟨0 + 0,represents_add_tail (hz1) hz4,?_⟩
      left
      simp only [add_zero]
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he1, he3, hd1, hd3, zero_add] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he1, he3, he4, hd1, hd3, hd4, zero_add, add_zero] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he1, he2]
      refine ⟨0 + u,represents_add_tail (hz1) hu,?_⟩
      right
      simp only [zero_add]
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      rw [he1, he2, he4]
      refine ⟨0 + u + 0,represents_add_tail (represents_add_tail (hz1) hu) hz4,?_⟩
      right
      simp only [zero_add,add_zero]
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add, add_zero] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,zero_add] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he1, he2, he3, he4, hd1, hd2, hd3, hd4, zero_add, add_zero] at hx
      have hval := congrArg (fun y => f y 1) hx
      simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [he0, hd0] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he4, hd0, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he3, hd0, hd3] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he3, he4, hd0, hd3, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he2, hd0, hd2, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he2, he4, hd0, hd2, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he2, he3, hd0, hd2, hd3, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he2, he3, he4, hd0, hd2, hd3, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he4, hd0, hd1, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he3, hd0, hd1, hd3, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he3, he4, hd0, hd1, hd3, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he2, he4, hd0, hd1, hd2, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_zero,←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
    · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      simp only [map_add] at hxe
      rw [hxe] at hx ⊢
      simp only [map_add, he0, he1, he2, he3, he4, hd0, hd1, hd2, hd3, hd4, add_zero] at hx
      have hval := congrArg (fun y => f y 3) hx
      simp only [map_add,map_zero,←hf1,←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  have ker (a : E.Page 5 (15,140)) (ha : E.d 5 (15,140) a=0) : a=0 := by
    rcases frame a with hz|hz
    · exact hz
    · exact (hn (by simpa only [hz,hd'] using ha)).elim
  let S := E.pageShortComplex 5 ((15,140)-E.diffDeg 5)
  have hex : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro a ha
    exact ⟨0,by rw [ker a ha,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 5 (15,140)
    (by change (2:ℤ)≤5; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hex))

private theorem h125_page16  :
    Subsingleton ((KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 6 (16,141)) := by
  classical
  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h371 : HasDifferential E 2 (16,141) (18,142)
      (basis .sphere 16 141 0) (basis .sphere 18 142 0 + basis .sphere 18 142 1) := by
    have hrow := result ⟨.sphere,.equation,2,16,141,[0],18,142,[0, 1],"S0_AdamsE2_ss",3255⟩ (by
      exact List.mem_of_getElem? (i := 371) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (16,141) (18,142) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 142 [0, 1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h372 : HasDifferential E 2 (16,141) (18,142)
      (basis .sphere 16 141 3) (basis .sphere 18 142 1) := by
    have hrow := result ⟨.sphere,.equation,2,16,141,[3],18,142,[1],"S0_AdamsE2_ss",3256⟩ (by
      exact List.mem_of_getElem? (i := 372) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (16,141) (18,142) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 142 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h370 : HasDifferential E 4 (12,138) (16,141)
      (basis .sphere 12 138 3) (basis .sphere 16 141 1) := by
    have hrow := result ⟨.sphere,.equation,4,12,138,[3],16,141,[1],"S0_AdamsE2_ss",3254⟩ (by
      exact List.mem_of_getElem? (i := 370) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (12,138) (16,141) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 138 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h369 : HasDifferential E 2 (14,140) (16,141)
      (basis .sphere 14 140 1) (basis .sphere 16 141 2) := by
    have hrow := result ⟨.sphere,.equation,2,14,140,[1],16,141,[2],"S0_AdamsE2_ss",3253⟩ (by
      exact List.mem_of_getElem? (i := 369) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (14,140) (16,141) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 14 140 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,16,141,["473,1", "1,1,448,1", "0,1,67,1,107,1", "0,2,449,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 232 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (16,141) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = basis .sphere 16 141 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = basis .sphere 16 141 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = basis .sphere 16 141 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = basis .sphere 16 141 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = basis .sphere 16 141 3 := he 3
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,18,142,["0,1,472,1", "0,4,440,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 245 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (18,142) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = basis .sphere 18 142 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = basis .sphere 18 142 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = basis .sphere 18 142 1 := hf 1
  have hd0 : E.d 2 (16,141) (basis .sphere 16 141 0) =
      basis .sphere 18 142 0 + basis .sphere 18 142 1 := h371.eq_on_page_two.2
  have hd3 : E.d 2 (16,141) (basis .sphere 16 141 3) =
      basis .sphere 18 142 1 := h372.eq_on_page_two.2
  have hz370 : RepresentsOnPage E 6 (16,141) (basis .sphere 16 141 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h370
  have hc370 : E.d 2 (16,141) (basis .sphere 16 141 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz370
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz370⟩
  have hd1 := hc370
  have hz369 : RepresentsOnPage E 6 (16,141) (basis .sphere 16 141 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h369
  have hc369 : E.d 2 (16,141) (basis .sphere 16 141 2) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz369
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz369⟩
  have hd2 := hc369
  apply sixth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (16,141)
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
    exact RepresentsOnPage.zero (E:=E) (p:=(16,141)) (r:=6) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he3, hd3] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he2]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz369)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he2, he3, hd2, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz370)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he3, hd1, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1, he2]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (represents_add_tail (hz370) hz369)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he3, hd0, hd3] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, hd0, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, he3, hd0, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he3, hd0, hd1, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

private theorem h125_page17  :
    Subsingleton ((KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 6 (17,142)) := by
  classical
  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h387 : HasDifferential E 2 (17,142) (19,143)
      (basis .sphere 17 142 1) (basis .sphere 19 143 1) := by
    have hrow := result ⟨.sphere,.equation,2,17,142,[1],19,143,[1],"S0_AdamsE2_ss",3320⟩ (by
      exact List.mem_of_getElem? (i := 387) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (17,142) (19,143) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 17 142 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 19 143 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h386 : HasDifferential E 2 (15,141) (17,142)
      (basis .sphere 15 141 0) (basis .sphere 17 142 0) := by
    have hrow := result ⟨.sphere,.equation,2,15,141,[0],17,142,[0],"S0_AdamsE2_ss",3319⟩ (by
      exact List.mem_of_getElem? (i := 386) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (15,141) (17,142) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 141 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 17 142 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,17,142,["0,2,67,1,107,1", "0,3,449,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 240 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (17,142) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = basis .sphere 17 142 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = basis .sphere 17 142 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = basis .sphere 17 142 1 := he 1
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,19,143,["8,1,293,1", "0,5,440,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 251 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (19,143) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = basis .sphere 19 143 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = basis .sphere 19 143 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = basis .sphere 19 143 1 := hf 1
  have hd1 : E.d 2 (17,142) (basis .sphere 17 142 1) =
      basis .sphere 19 143 1 := h387.eq_on_page_two.2
  have hz386 : RepresentsOnPage E 6 (17,142) (basis .sphere 17 142 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h386
  have hc386 : E.d 2 (17,142) (basis .sphere 17 142 0) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz386
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz386⟩
  have hd0 := hc386
  apply sixth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (17,142)
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
    exact RepresentsOnPage.zero (E:=E) (p:=(17,142)) (r:=6) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [he1, hd1] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he0]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz386)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

private theorem h125_page18  :
    Subsingleton ((KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 6 (18,143)) := by
  classical
  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h398 : HasDifferential E 2 (18,143) (20,144)
      (basis .sphere 18 143 1) (basis .sphere 20 144 1) := by
    have hrow := result ⟨.sphere,.equation,2,18,143,[1],20,144,[1],"S0_AdamsE2_ss",3392⟩ (by
      exact List.mem_of_getElem? (i := 398) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (18,143) (20,144) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 143 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 20 144 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h397 : HasDifferential E 5 (13,139) (18,143)
      (basis .sphere 13 139 0) (basis .sphere 18 143 0) := by
    have hrow := result ⟨.sphere,.equation,5,13,139,[0],18,143,[0],"S0_AdamsE2_ss",3391⟩ (by
      exact List.mem_of_getElem? (i := 397) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 5 (13,139) (18,143) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 139 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 143 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,18,143,["8,2,209,1", "0,4,449,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 246 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (18,143) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = basis .sphere 18 143 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = basis .sphere 18 143 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = basis .sphere 18 143 1 := he 1
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,20,144,["8,2,212,1", "0,6,440,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 256 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (20,144) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = basis .sphere 20 144 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = basis .sphere 20 144 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = basis .sphere 20 144 1 := hf 1
  have hd1 : E.d 2 (18,143) (basis .sphere 18 143 1) =
      basis .sphere 20 144 1 := h398.eq_on_page_two.2
  have hz397 : RepresentsOnPage E 6 (18,143) (basis .sphere 18 143 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤5; omega) (by decide) h397
  have hc397 : E.d 2 (18,143) (basis .sphere 18 143 0) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz397
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz397⟩
  have hd0 := hc397
  apply sixth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (18,143)
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
    exact RepresentsOnPage.zero (E:=E) (p:=(18,143)) (r:=6) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [he1, hd1] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he0]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz397)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

private theorem h125_page19  :
    Subsingleton ((KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 6 (19,144)) := by
  classical
  apply page_subsingleton_of_le (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 4 6 19 144 (by decide) (by decide)
  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h408 : HasDifferential E 3 (19,144) (22,146)
      ((basis .sphere 19 144 0)) ((basis .sphere 22 146 1)) := by
    have hrow := result ⟨.sphere,.equation,3,19,144,[0],22,146,[1],"S0_AdamsE2_ss",3486⟩ (by
      exact List.mem_of_getElem? (i := 408) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (19,144) (22,146) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 19 144 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 22 146 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h409 : HasDifferential E 2 (19,144) (21,145)
      ((basis .sphere 19 144 2)) ((basis .sphere 21 145 1)) := by
    have hrow := result ⟨.sphere,.equation,2,19,144,[2],21,145,[1],"S0_AdamsE2_ss",3487⟩ (by
      exact List.mem_of_getElem? (i := 409) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (19,144) (21,145) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 19 144 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 21 145 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h410 : HasDifferential E 2 (19,144) (21,145)
      ((basis .sphere 19 144 1)) ((basis .sphere 21 145 0)) := by
    have hrow := result ⟨.sphere,.equation,2,19,144,[1],21,145,[0],"S0_AdamsE2_ss",3488⟩ (by
      exact List.mem_of_getElem? (i := 410) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (19,144) (21,145) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 19 144 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 21 145 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h418 : HasDifferential E 2 (18,144) (20,145)
      ((basis .sphere 18 144 0)) ((basis .sphere 20 145 1)) := by
    have hrow := result ⟨.sphere,.equation,2,18,144,[0],20,145,[1],"S0_AdamsE2_ss",3556⟩ (by
      exact List.mem_of_getElem? (i := 418) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (18,144) (20,145) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 144 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 20 145 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h419 : HasDifferential E 3 (20,145) (23,147)
      ((basis .sphere 20 145 0)) ((basis .sphere 23 147 2)) := by
    have hrow := result ⟨.sphere,.equation,3,20,145,[0],23,147,[2],"S0_AdamsE2_ss",3557⟩ (by
      exact List.mem_of_getElem? (i := 419) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (20,145) (23,147) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 20 145 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 23 147 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h420 : HasDifferential E 2 (20,145) (22,146)
      ((basis .sphere 20 145 2)) ((basis .sphere 22 146 3)) := by
    have hrow := result ⟨.sphere,.equation,2,20,145,[2],22,146,[3],"S0_AdamsE2_ss",3558⟩ (by
      exact List.mem_of_getElem? (i := 420) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (20,145) (22,146) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 20 145 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 22 146 [3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,19,144,["13,1,266,1", "8,1,13,1,188,1", "0,5,449,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 252 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (19,144) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = basis .sphere 19 144 i.val at he
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,20,145,["510,1", "0,1,8,1,13,1,188,1", "0,6,449,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 257 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (20,145) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = basis .sphere 20 145 i.val at hf
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere,22,146,["517,1", "13,2,168,1", "8,1,316,1", "0,8,440,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 265 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (22,146) ≃ₗ[ℤ] (Fin 4 →₀ F2) at g
  change ∀ i : Fin 4, g.symm (Finsupp.single i 1) = basis .sphere 22 146 i.val at hg
  obtain ⟨k,hk⟩ := basis_correct ⟨.sphere,21,145,["0,1,8,2,212,1", "0,7,440,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 260 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (21,145) ≃ₗ[ℤ] (Fin 2 →₀ F2) at k
  change ∀ i : Fin 2, k.symm (Finsupp.single i 1) = basis .sphere 21 145 i.val at hk
  have d20 : E.d 2 (19,144) (basis .sphere 19 144 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h408
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d21 : E.d 2 (19,144) (basis .sphere 19 144 1) =
      basis .sphere 21 145 0 := h410.eq_on_page_two.2
  have d22 : E.d 2 (19,144) (basis .sphere 19 144 2) =
      basis .sphere 21 145 1 := h409.eq_on_page_two.2
  have df0 : E.d 2 (20,145) (basis .sphere 20 145 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h419
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have df1 : E.d 2 (20,145) (basis .sphere 20 145 1) = 0 := by
    have hd : E.d 2 (18,144) (basis .sphere 18 144 0) =
      basis .sphere 20 145 1 := h418.eq_on_page_two.2
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(18,144)) ⟨_,hd⟩
  have df2 : E.d 2 (20,145) (basis .sphere 20 145 2) =
      basis .sphere 22 146 3 := h420.eq_on_page_two.2
  have incoming (x : E.Page 2 (20,145)) : g (E.d 2 (20,145) x) 1 = 0 := by
    have hall (a : Fin 3 →₀ F2) : g (E.d 2 (20,145) (f.symm a)) 1 = 0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (20,145) (f.symm (Finsupp.single i 1))) 1 = 0
          rw [hf i]
          fin_cases i
          · rw [df0]; exact congrArg (fun z : Fin 4 →₀ F2 => z 1) g.map_zero
          · rw [df1]; exact congrArg (fun z : Fin 4 →₀ F2 => z 1) g.map_zero
          · rw [df2]
            rw [show basis .sphere 22 146 3 = g.symm (Finsupp.single 3 1) from (hg 3).symm,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h408
  have hd' : E.d 3 (19,144) a = b := hd
  have hbne : b ≠ 0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (20,145) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (22,146)).Z_anti bot_le) ≫
      (E.ssData (22,146)).pageπ 0) z ∈ LinearMap.range (E.d 2 (20,145)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (22,146)).Z_anti bot_le) ≫
      (E.ssData (22,146)).pageπ 0) z = basis .sphere 22 146 1 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming u
    rw [hu] at hzero
    rw [show basis .sphere 22 146 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hzero
  have frame (q : E.Page 3 (19, 144)) : q=0 ∨ q=a := by
    let A := E.ssData (19, 144)
    haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance q
    let x : E.Page 2 (19, 144) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
    have hx : RepresentsOnPage E 3 (19, 144) x q := ⟨by decide,z,rfl,hz⟩
    have hc : E.d 2 (19, 144) x = 0 := by
      obtain ⟨z,hz⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hx
      rw [←hz.eq_on_page_two] at hz
      exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hz ⟨q,hx⟩
    have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) := by
      ext i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2)) := by
      rw [←heq,LinearEquiv.symm_apply_apply]
    generalize h0 : e x 0 = c0 at hxe
    generalize h1 : e x 1 = c1 at hxe
    generalize h2 : e x 2 = c2 at hxe
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_zero] at hxe
      rw [hxe] at hx
      exact Or.inl (represents_unique hx (RepresentsOnPage.zero (by decide)))
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [show e.symm (Finsupp.single 2 1) = basis .sphere 19 144 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 1) hc
      rw [hxe] at hh
      simp only [d22] at hh
      simp only [show basis .sphere 21 145 1 = k.symm (Finsupp.single 1 1) from (hk 1).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [show e.symm (Finsupp.single 1 1) = basis .sphere 19 144 1 from he 1] at hxe
      have hh := congrArg (fun y => k y 0) hc
      rw [hxe] at hh
      simp only [d21] at hh
      simp only [show basis .sphere 21 145 0 = k.symm (Finsupp.single 0 1) from (hk 0).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,map_add] at hxe
      rw [show e.symm (Finsupp.single 1 1) = basis .sphere 19 144 1 from he 1] at hxe
      rw [show e.symm (Finsupp.single 2 1) = basis .sphere 19 144 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 0) hc
      rw [hxe] at hh
      simp only [map_add,d21,d22] at hh
      simp only [show basis .sphere 21 145 0 = k.symm (Finsupp.single 0 1) from (hk 0).symm, show basis .sphere 21 145 1 = k.symm (Finsupp.single 1 1) from (hk 1).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero] at hxe
      rw [show e.symm (Finsupp.single 0 1) = basis .sphere 19 144 0 from he 0] at hxe
      rw [hxe] at hx
      exact Or.inr (represents_unique hx (by simpa only [he] using ha))
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = basis .sphere 19 144 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 2 1) = basis .sphere 19 144 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 1) hc
      rw [hxe] at hh
      simp only [map_add,d20,d22] at hh
      simp only [show basis .sphere 21 145 1 = k.symm (Finsupp.single 1 1) from (hk 1).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = basis .sphere 19 144 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 1 1) = basis .sphere 19 144 1 from he 1] at hxe
      have hh := congrArg (fun y => k y 0) hc
      rw [hxe] at hh
      simp only [map_add,d20,d21] at hh
      simp only [show basis .sphere 21 145 0 = k.symm (Finsupp.single 0 1) from (hk 0).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = basis .sphere 19 144 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 1 1) = basis .sphere 19 144 1 from he 1] at hxe
      rw [show e.symm (Finsupp.single 2 1) = basis .sphere 19 144 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 0) hc
      rw [hxe] at hh
      simp only [map_add,d20,d21,d22] at hh
      simp only [show basis .sphere 21 145 0 = k.symm (Finsupp.single 0 1) from (hk 0).symm, show basis .sphere 21 145 1 = k.symm (Finsupp.single 1 1) from (hk 1).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have hker (q : E.Page 3 (19,144)) (hq : E.d 3 (19,144) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 3 ((19,144)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [hker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (19,144)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))


private theorem stem125_sixth_pages_15_19
    (s : ℕ) (hs : 15 ≤ s) (hs' : s ≤ 19) :
    Subsingleton ((KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 6 (s,(s:ℤ)+125)) := by
  classical

  interval_cases s
  · exact h125_page15
  · exact h125_page16
  · exact h125_page17
  · exact h125_page18
  · exact h125_page19

private theorem h125_page20  :
    Subsingleton ((KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 6 (20,145)) := by
  classical
  apply page_subsingleton_of_le (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 4 6 20 145 (by decide) (by decide)
  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h418 : HasDifferential E 2 (18,144) (20,145)
      ((basis .sphere 18 144 0)) ((basis .sphere 20 145 1)) := by
    have hrow := result ⟨.sphere,.equation,2,18,144,[0],20,145,[1],"S0_AdamsE2_ss",3556⟩ (by
      exact List.mem_of_getElem? (i := 418) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (18,144) (20,145) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 144 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 20 145 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h419 : HasDifferential E 3 (20,145) (23,147)
      ((basis .sphere 20 145 0)) ((basis .sphere 23 147 2)) := by
    have hrow := result ⟨.sphere,.equation,3,20,145,[0],23,147,[2],"S0_AdamsE2_ss",3557⟩ (by
      exact List.mem_of_getElem? (i := 419) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (20,145) (23,147) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 20 145 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 23 147 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h420 : HasDifferential E 2 (20,145) (22,146)
      ((basis .sphere 20 145 2)) ((basis .sphere 22 146 3)) := by
    have hrow := result ⟨.sphere,.equation,2,20,145,[2],22,146,[3],"S0_AdamsE2_ss",3558⟩ (by
      exact List.mem_of_getElem? (i := 420) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (20,145) (22,146) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 20 145 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 22 146 [3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h426 : HasDifferential E 4 (17,143) (21,146)
      ((basis .sphere 17 143 1)) ((basis .sphere 21 146 0)) := by
    have hrow := result ⟨.sphere,.equation,4,17,143,[1],21,146,[0],"S0_AdamsE2_ss",3629⟩ (by
      exact List.mem_of_getElem? (i := 426) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (17,143) (21,146) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 17 143 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 21 146 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h427 : HasDifferential E 2 (21,146) (23,147)
      ((basis .sphere 21 146 2)) ((basis .sphere 23 147 3)) := by
    have hrow := result ⟨.sphere,.equation,2,21,146,[2],23,147,[3],"S0_AdamsE2_ss",3630⟩ (by
      exact List.mem_of_getElem? (i := 427) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (21,146) (23,147) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 21 146 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 23 147 [3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h428 : HasDifferential E 2 (21,146) (23,147)
      ((basis .sphere 21 146 1)) ((basis .sphere 23 147 1) + (basis .sphere 23 147 2)) := by
    have hrow := result ⟨.sphere,.equation,2,21,146,[1],23,147,[1, 2],"S0_AdamsE2_ss",3631⟩ (by
      exact List.mem_of_getElem? (i := 428) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (21,146) (23,147) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 21 146 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 23 147 [1, 2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,20,145,["510,1", "0,1,8,1,13,1,188,1", "0,6,449,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 257 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (20,145) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = basis .sphere 20 145 i.val at he
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,21,146,["518,1", "9,1,292,1", "0,7,449,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 261 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (21,146) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = basis .sphere 21 146 i.val at hf
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere,23,147,["8,1,327,1", "8,1,13,1,23,1,80,1", "0,1,8,1,316,1", "0,9,440,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 270 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (23,147) ≃ₗ[ℤ] (Fin 4 →₀ F2) at g
  change ∀ i : Fin 4, g.symm (Finsupp.single i 1) = basis .sphere 23 147 i.val at hg
  obtain ⟨k,hk⟩ := basis_correct ⟨.sphere,22,146,["517,1", "13,2,168,1", "8,1,316,1", "0,8,440,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 265 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (22,146) ≃ₗ[ℤ] (Fin 4 →₀ F2) at k
  change ∀ i : Fin 4, k.symm (Finsupp.single i 1) = basis .sphere 22 146 i.val at hk
  have d20 : E.d 2 (20,145) (basis .sphere 20 145 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h419
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d21 : E.d 2 (20,145) (basis .sphere 20 145 1) = 0 := by
    have hd : E.d 2 (18,144) (basis .sphere 18 144 0) =
      basis .sphere 20 145 1 := h418.eq_on_page_two.2
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(18,144)) ⟨_,hd⟩
  have d22 : E.d 2 (20,145) (basis .sphere 20 145 2) =
      basis .sphere 22 146 3 := h420.eq_on_page_two.2
  have df0 : E.d 2 (21,146) (basis .sphere 21 146 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h426
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hy
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hy⟩
  have df1 : E.d 2 (21,146) (basis .sphere 21 146 1) =
      basis .sphere 23 147 1 + basis .sphere 23 147 2 := h428.eq_on_page_two.2
  have df2 : E.d 2 (21,146) (basis .sphere 21 146 2) =
      basis .sphere 23 147 3 := h427.eq_on_page_two.2
  have incoming (x : E.Page 2 (21,146)) : g (E.d 2 (21,146) x) 1 = g (E.d 2 (21,146) x) 2 := by
    have hall (a : Fin 3 →₀ F2) : g (E.d 2 (21,146) (f.symm a)) 1 = g (E.d 2 (21,146) (f.symm a)) 2 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        simp only [map_add,Finsupp.add_apply]
        rw [ih]
        congr 1
        fin_cases c
        · simp
        · change g (E.d 2 (21,146) (f.symm (Finsupp.single i 1))) 1 = g (E.d 2 (21,146) (f.symm (Finsupp.single i 1))) 2
          rw [hf i]
          fin_cases i
          · rw [df0]
            simp only [map_zero,Finsupp.zero_apply]
          · rw [df1,map_add,Finsupp.add_apply,Finsupp.add_apply]
            rw [show basis .sphere 23 147 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm,
              show basis .sphere 23 147 2 = g.symm (Finsupp.single 2 1) from (hg 2).symm]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
          · rw [df2]
            rw [show basis .sphere 23 147 3 = g.symm (Finsupp.single 3 1) from (hg 3).symm]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h419
  have hd' : E.d 3 (20,145) a = b := hd
  have hbne : b ≠ 0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (21,146) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (23,147)).Z_anti bot_le) ≫
      (E.ssData (23,147)).pageπ 0) z ∈ LinearMap.range (E.d 2 (21,146)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (23,147)).Z_anti bot_le) ≫
      (E.ssData (23,147)).pageπ 0) z = basis .sphere 23 147 2 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming u
    rw [hu] at hzero
    rw [show basis .sphere 23 147 2 = g.symm (Finsupp.single 2 1) from (hg 2).symm,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hzero
  have hboundary : RepresentsOnPage E 3 (20,145) (basis .sphere 20 145 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h418
  have hadd {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ)}
      {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    obtain ⟨hr,z,hz,ha⟩ := hx
    obtain ⟨_,w,hw,hb⟩ := hy
    exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,ha,hb]⟩
  have frame (q : E.Page 3 (20, 145)) : q=0 ∨ q=a := by
    let A := E.ssData (20, 145)
    haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance q
    let x : E.Page 2 (20, 145) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
    have hx : RepresentsOnPage E 3 (20, 145) x q := ⟨by decide,z,rfl,hz⟩
    have hc : E.d 2 (20, 145) x = 0 := by
      obtain ⟨z,hz⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hx
      rw [←hz.eq_on_page_two] at hz
      exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hz ⟨q,hx⟩
    have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) := by
      ext i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2)) := by
      rw [←heq,LinearEquiv.symm_apply_apply]
    generalize h0 : e x 0 = c0 at hxe
    generalize h1 : e x 1 = c1 at hxe
    generalize h2 : e x 2 = c2 at hxe
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_zero] at hxe
      rw [hxe] at hx
      exact Or.inl (represents_unique hx (RepresentsOnPage.zero (by decide)))
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [show e.symm (Finsupp.single 2 1) = basis .sphere 20 145 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 3) hc
      rw [hxe] at hh
      simp only [d22] at hh
      simp only [show basis .sphere 22 146 3 = k.symm (Finsupp.single 3 1) from (hk 3).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [show e.symm (Finsupp.single 1 1) = basis .sphere 20 145 1 from he 1] at hxe
      rw [hxe] at hx
      exact Or.inl (represents_unique hx (by simpa only [he] using hboundary))
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add,map_add] at hxe
      rw [show e.symm (Finsupp.single 1 1) = basis .sphere 20 145 1 from he 1] at hxe
      rw [show e.symm (Finsupp.single 2 1) = basis .sphere 20 145 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 3) hc
      rw [hxe] at hh
      simp only [map_add,d21,d22] at hh
      simp only [show basis .sphere 22 146 3 = k.symm (Finsupp.single 3 1) from (hk 3).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero] at hxe
      rw [show e.symm (Finsupp.single 0 1) = basis .sphere 20 145 0 from he 0] at hxe
      rw [hxe] at hx
      exact Or.inr (represents_unique hx (by simpa only [he] using ha))
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = basis .sphere 20 145 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 2 1) = basis .sphere 20 145 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 3) hc
      rw [hxe] at hh
      simp only [map_add,d20,d22] at hh
      simp only [show basis .sphere 22 146 3 = k.symm (Finsupp.single 3 1) from (hk 3).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = basis .sphere 20 145 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 1 1) = basis .sphere 20 145 1 from he 1] at hxe
      rw [hxe] at hx
      exact Or.inr (represents_unique hx (by simpa only [he,add_zero] using hadd ha hboundary))
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
      simp only [map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = basis .sphere 20 145 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 1 1) = basis .sphere 20 145 1 from he 1] at hxe
      rw [show e.symm (Finsupp.single 2 1) = basis .sphere 20 145 2 from he 2] at hxe
      have hh := congrArg (fun y => k y 3) hc
      rw [hxe] at hh
      simp only [map_add,d20,d21,d22] at hh
      simp only [show basis .sphere 22 146 3 = k.symm (Finsupp.single 3 1) from (hk 3).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have hker (q : E.Page 3 (20,145)) (hq : E.d 3 (20,145) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 3 ((20,145)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [hker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (20,145)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))

private theorem h125_page21  :
    Subsingleton ((KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 6 (21,146)) := by
  classical
  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h428 : HasDifferential E 2 (21,146) (23,147)
      (basis .sphere 21 146 1) (basis .sphere 23 147 1 + basis .sphere 23 147 2) := by
    have hrow := result ⟨.sphere,.equation,2,21,146,[1],23,147,[1, 2],"S0_AdamsE2_ss",3631⟩ (by
      exact List.mem_of_getElem? (i := 428) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (21,146) (23,147) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 21 146 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 23 147 [1, 2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h427 : HasDifferential E 2 (21,146) (23,147)
      (basis .sphere 21 146 2) (basis .sphere 23 147 3) := by
    have hrow := result ⟨.sphere,.equation,2,21,146,[2],23,147,[3],"S0_AdamsE2_ss",3630⟩ (by
      exact List.mem_of_getElem? (i := 427) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (21,146) (23,147) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 21 146 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 23 147 [3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h426 : HasDifferential E 4 (17,143) (21,146)
      (basis .sphere 17 143 1) (basis .sphere 21 146 0) := by
    have hrow := result ⟨.sphere,.equation,4,17,143,[1],21,146,[0],"S0_AdamsE2_ss",3629⟩ (by
      exact List.mem_of_getElem? (i := 426) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (17,143) (21,146) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 17 143 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 21 146 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,21,146,["518,1", "9,1,292,1", "0,7,449,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 261 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (21,146) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = basis .sphere 21 146 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = basis .sphere 21 146 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = basis .sphere 21 146 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = basis .sphere 21 146 2 := he 2
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,23,147,["8,1,327,1", "8,1,13,1,23,1,80,1", "0,1,8,1,316,1", "0,9,440,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 270 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (23,147) ≃ₗ[ℤ] (Fin 4 →₀ F2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1) = basis .sphere 23 147 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 4) 1) = basis .sphere 23 147 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 4) 1) = basis .sphere 23 147 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 4) 1) = basis .sphere 23 147 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 4) 1) = basis .sphere 23 147 3 := hf 3
  have hd1 : E.d 2 (21,146) (basis .sphere 21 146 1) =
      basis .sphere 23 147 1 + basis .sphere 23 147 2 := h428.eq_on_page_two.2
  have hd2 : E.d 2 (21,146) (basis .sphere 21 146 2) =
      basis .sphere 23 147 3 := h427.eq_on_page_two.2
  have hz426 : RepresentsOnPage E 6 (21,146) (basis .sphere 21 146 0) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h426
  have hc426 : E.d 2 (21,146) (basis .sphere 21 146 0) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz426
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz426⟩
  have hd0 := hc426
  apply sixth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (21,146)
  intro x hx
  have heq : e x = (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2)) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x = e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0 = c0 at hxe
  generalize hc1 : e x 1 = c1 at hxe
  generalize hc2 : e x 2 = c2 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    exact RepresentsOnPage.zero (E:=E) (p:=(21,146)) (r:=6) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he2, hd2] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he1, hd1] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, ←hf2, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he2, hd1, hd2] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, ←hf2, ←hf3, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he0]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz426)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, hd0, hd2, zero_add] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, ←hf2, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_add, map_zero, ←hf1, ←hf2, ←hf3, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

private theorem h125_page22  :
    Subsingleton ((KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 6 (22,147)) := by
  classical
  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h439 : HasDifferential E 2 (22,147) (24,148)
      (basis .sphere 22 147 2) (basis .sphere 24 148 0) := by
    have hrow := result ⟨.sphere,.equation,2,22,147,[2],24,148,[0],"S0_AdamsE2_ss",3747⟩ (by
      exact List.mem_of_getElem? (i := 439) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (22,147) (24,148) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 22 147 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 24 148 [0] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h438 : HasDifferential E 2 (22,147) (24,148)
      (basis .sphere 22 147 3) (basis .sphere 24 148 1) := by
    have hrow := result ⟨.sphere,.equation,2,22,147,[3],24,148,[1],"S0_AdamsE2_ss",3746⟩ (by
      exact List.mem_of_getElem? (i := 438) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (22,147) (24,148) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 22 147 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 24 148 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h436 : HasDifferential E 4 (18,144) (22,147)
      (basis .sphere 18 144 1) (basis .sphere 22 147 1) := by
    have hrow := result ⟨.sphere,.equation,4,18,144,[1],22,147,[1],"S0_AdamsE2_ss",3744⟩ (by
      exact List.mem_of_getElem? (i := 436) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (18,144) (22,147) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 144 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 22 147 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h437 : HasDifferential E 4 (18,144) (22,147)
      (basis .sphere 18 144 2 + basis .sphere 18 144 3) (basis .sphere 22 147 0 + basis .sphere 22 147 3) := by
    have hrow := result ⟨.sphere,.equation,4,18,144,[2, 3],22,147,[0, 3],"S0_AdamsE2_ss",3745⟩ (by
      exact List.mem_of_getElem? (i := 437) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (18,144) (22,147) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 144 [2, 3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 22 147 [0, 3] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,22,147,["17,1,255,1", "13,3,101,1", "0,1,9,1,292,1", "0,8,449,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 266 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (22,147) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = basis .sphere 22 147 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = basis .sphere 22 147 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = basis .sphere 22 147 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = basis .sphere 22 147 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = basis .sphere 22 147 3 := he 3
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,24,148,["0,2,8,1,316,1", "0,10,440,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 275 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (24,148) ≃ₗ[ℤ] (Fin 2 →₀ F2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = basis .sphere 24 148 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = basis .sphere 24 148 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = basis .sphere 24 148 1 := hf 1
  have hd2 : E.d 2 (22,147) (basis .sphere 22 147 2) =
      basis .sphere 24 148 0 := h439.eq_on_page_two.2
  have hd3 : E.d 2 (22,147) (basis .sphere 22 147 3) =
      basis .sphere 24 148 1 := h438.eq_on_page_two.2
  have hz436 : RepresentsOnPage E 6 (22,147) (basis .sphere 22 147 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h436
  have hc436 : E.d 2 (22,147) (basis .sphere 22 147 1) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz436
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz436⟩
  have hd1 := hc436
  have hz437 : RepresentsOnPage E 6 (22,147) (basis .sphere 22 147 0 + basis .sphere 22 147 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h437
  have hc437 : E.d 2 (22,147) (basis .sphere 22 147 0 + basis .sphere 22 147 3) = 0 := by
    obtain ⟨x,hx⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤6) hz437
    rw [←hx.eq_on_page_two] at hx
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hx ⟨0,hz437⟩
  have hd0 : E.d 2 (22,147) (basis .sphere 22 147 0) =
      basis .sphere 24 148 1 := by
    have hn : -(basis .sphere 24 148 1) = basis .sphere 24 148 1 := by
      apply f.injective
      rw [map_neg,←hf1,LinearEquiv.apply_symm_apply]
      ext i
      simp only [Finsupp.neg_apply]
      exact ZMod.neg_eq_self_mod_two _
    have hh := hc437
    rw [map_add,hd3] at hh
    exact (eq_neg_of_add_eq_zero_left hh).trans hn
  apply sixth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (22,147)
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
    exact RepresentsOnPage.zero (E:=E) (p:=(22,147)) (r:=6) (by decide)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he3, hd3] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he2, hd2] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he2, he3, hd2, hd3] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he1]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz436)
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he3, hd1, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he2, hd1, hd2, zero_add] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_zero, ←hf0, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he0, he3]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (hz437)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, hd0, hd2] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he2, he3, hd0, hd2, hd3] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    rw [he0, he1, he3]
    simpa only [add_assoc,add_left_comm,add_comm,zero_add] using (represents_add_tail (hz436) hz437)
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2)) at hxe
    try simp only [map_add] at hxe
    rw [hxe] at hx ⊢
    simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add, map_zero, ←hf0, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.add_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

private theorem h125_page23  :
    Subsingleton ((KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 6 (23,148)) := by
  classical
  apply page_subsingleton_of_le (KIP126.Main.Internal.Selected.Normalized.sequence .sphere) 4 6 23 148 (by decide) (by decide)
  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h445 : HasDifferential E 3 (23,148) (26,150)
      ((basis .sphere 23 148 0)) ((basis .sphere 26 150 2)) := by
    have hrow := result ⟨.sphere,.equation,3,23,148,[0],26,150,[2],"S0_AdamsE2_ss",3812⟩ (by
      exact List.mem_of_getElem? (i := 445) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (23,148) (26,150) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 23 148 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 26 150 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h446 : HasDifferential E 2 (23,148) (25,149)
      ((basis .sphere 23 148 1)) ((basis .sphere 25 149 2)) := by
    have hrow := result ⟨.sphere,.equation,2,23,148,[1],25,149,[2],"S0_AdamsE2_ss",3813⟩ (by
      exact List.mem_of_getElem? (i := 446) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (23,148) (25,149) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 23 148 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 25 149 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h453 : HasDifferential E 2 (24,149) (26,150)
      ((basis .sphere 24 149 0)) ((basis .sphere 26 150 1)) := by
    have hrow := result ⟨.sphere,.equation,2,24,149,[0],26,150,[1],"S0_AdamsE2_ss",3896⟩ (by
      exact List.mem_of_getElem? (i := 453) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (24,149) (26,150) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 24 149 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 26 150 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,23,148,["0,2,9,1,292,1", "0,9,449,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 271 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (23,148) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = basis .sphere 23 148 i.val at he
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,24,149,["9,1,13,1,194,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 276 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (24,149) ≃ₗ[ℤ] (Fin 1 →₀ F2) at f
  change ∀ i : Fin 1, f.symm (Finsupp.single i 1) = basis .sphere 24 149 i.val at hf
  obtain ⟨g,hg⟩ := basis_correct ⟨.sphere,26,150,["557,1", "8,1,13,4,23,1", "8,3,9,1,101,1", "0,1,17,1,260,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 285 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (26,150) ≃ₗ[ℤ] (Fin 4 →₀ F2) at g
  change ∀ i : Fin 4, g.symm (Finsupp.single i 1) = basis .sphere 26 150 i.val at hg
  obtain ⟨k,hk⟩ := basis_correct ⟨.sphere,25,149,["17,1,260,1", "8,1,9,1,219,1", "0,11,440,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 280 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (25,149) ≃ₗ[ℤ] (Fin 3 →₀ F2) at k
  change ∀ i : Fin 3, k.symm (Finsupp.single i 1) = basis .sphere 25 149 i.val at hk
  have d20 : E.d 2 (23,148) (basis .sphere 23 148 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h445
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have d21 : E.d 2 (23,148) (basis .sphere 23 148 1) =
      basis .sphere 25 149 2 := h446.eq_on_page_two.2
  have df0 : E.d 2 (24,149) (basis .sphere 24 149 0) =
      basis .sphere 26 150 1 := h453.eq_on_page_two.2
  have incoming (x : E.Page 2 (24,149)) : g (E.d 2 (24,149) x) 2 = 0 := by
    have hall (a : Fin 1 →₀ F2) : g (E.d 2 (24,149) (f.symm a)) 2 = 0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (24,149) (f.symm (Finsupp.single i 1))) 2 = 0
          rw [hf i]
          fin_cases i
          rw [df0]
          rw [show basis .sphere 26 150 1 = g.symm (Finsupp.single 1 1) from (hg 1).symm,LinearEquiv.apply_symm_apply]
          norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h445
  have hd' : E.d 3 (23,148) a = b := hd
  have hbne : b ≠ 0 := by
    intro hb0
    obtain ⟨_,z,hx,hz⟩ := hb
    have hh := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (24,149) z).mp (hz.trans hb0)
    change (Subobject.ofLE _ _ ((E.ssData (26,150)).Z_anti bot_le) ≫
      (E.ssData (26,150)).pageπ 0) z ∈ LinearMap.range (E.d 2 (24,149)).hom at hh
    change (Subobject.ofLE _ _ ((E.ssData (26,150)).Z_anti bot_le) ≫
      (E.ssData (26,150)).pageπ 0) z = basis .sphere 26 150 2 at hx
    rw [hx] at hh
    obtain ⟨u,hu⟩ := hh
    have hzero := incoming u
    rw [hu] at hzero
    rw [show basis .sphere 26 150 2 = g.symm (Finsupp.single 2 1) from (hg 2).symm,LinearEquiv.apply_symm_apply] at hzero
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hzero
  have frame (q : E.Page 3 (23, 148)) : q=0 ∨ q=a := by
    let A := E.ssData (23, 148)
    haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance q
    let x : E.Page 2 (23, 148) := (Subobject.ofLE _ _ (A.Z_anti bot_le) ≫ A.pageπ 0) z
    have hx : RepresentsOnPage E 3 (23, 148) x q := ⟨by decide,z,rfl,hz⟩
    have hc : E.d 2 (23, 148) x = 0 := by
      obtain ⟨z,hz⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) hx
      rw [←hz.eq_on_page_two] at hz
      exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hz ⟨q,hx⟩
    have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) := by
      ext i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1)) := by
      rw [←heq,LinearEquiv.symm_apply_apply]
    generalize h0 : e x 0 = c0 at hxe
    generalize h1 : e x 1 = c1 at hxe
    fin_cases c0 <;> fin_cases c1
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero,map_zero] at hxe
      rw [hxe] at hx
      exact Or.inl (represents_unique hx (RepresentsOnPage.zero (by decide)))
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2)) at hxe
      simp only [Finsupp.single_zero,zero_add] at hxe
      rw [show e.symm (Finsupp.single 1 1) = basis .sphere 23 148 1 from he 1] at hxe
      have hh := congrArg (fun y => k y 2) hc
      rw [hxe] at hh
      simp only [d21] at hh
      simp only [show basis .sphere 25 149 2 = k.symm (Finsupp.single 2 1) from (hk 2).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2)) at hxe
      simp only [Finsupp.single_zero,add_zero] at hxe
      rw [show e.symm (Finsupp.single 0 1) = basis .sphere 23 148 0 from he 0] at hxe
      rw [hxe] at hx
      exact Or.inr (represents_unique hx (by simpa only [he] using ha))
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2)) at hxe
      simp only [map_add] at hxe
      rw [show e.symm (Finsupp.single 0 1) = basis .sphere 23 148 0 from he 0] at hxe
      rw [show e.symm (Finsupp.single 1 1) = basis .sphere 23 148 1 from he 1] at hxe
      have hh := congrArg (fun y => k y 2) hc
      rw [hxe] at hh
      simp only [map_add,d20,d21] at hh
      simp only [show basis .sphere 25 149 2 = k.symm (Finsupp.single 2 1) from (hk 2).symm] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  have hker (q : E.Page 3 (23,148)) (hq : E.d 3 (23,148) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  let S := E.pageShortComplex 3 ((23,148)-E.diffDeg 3)
  have hs : S.Exact := S.moduleCat_exact_iff.mpr (by
    intro x hx
    exact ⟨0,by rw [hker x hx,map_zero]⟩)
  exact ModuleCat.subsingleton_of_isZero ((pageHomologyIso E 3 (23,148)
    (by change (2:ℤ)≤3; omega)).isZero_iff.mpr ((S.exact_iff_isZero_homology).mp hs))

private theorem h125_page24  :
    Subsingleton ((KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 6 (24,149)) := by
  classical
  let E := KIP126.Main.Internal.Selected.Normalized.sequence .sphere
  have h453 : HasDifferential E 2 (24,149) (26,150)
      (basis .sphere 24 149 0) (basis .sphere 26 150 1) := by
    have hrow := result ⟨.sphere,.equation,2,24,149,[0],26,150,[1],"S0_AdamsE2_ss",3896⟩ (by
      exact List.mem_of_getElem? (i := 453) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (24,149) (26,150) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 24 149 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 26 150 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,24,149,["9,1,13,1,194,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 276 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (24,149) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = basis .sphere 24 149 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = basis .sphere 24 149 0 := he 0
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,26,150,["557,1", "8,1,13,4,23,1", "8,3,9,1,101,1", "0,1,17,1,260,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 285 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (26,150) ≃ₗ[ℤ] (Fin 4 →₀ F2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1) = basis .sphere 26 150 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 4) 1) = basis .sphere 26 150 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 4) 1) = basis .sphere 26 150 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 4) 1) = basis .sphere 26 150 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 4) 1) = basis .sphere 26 150 3 := hf 3
  have hd0 : E.d 2 (24,149) (basis .sphere 24 149 0) =
      basis .sphere 26 150 1 := h453.eq_on_page_two.2
  apply sixth_zero_of_second_kernel (E:=E) (by change (2:ℤ)≤2; omega) (24,149)
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
    exact RepresentsOnPage.zero (E:=E) (p:=(24,149)) (r:=6) (by decide)
  · change x = e.symm (Finsupp.single 0 (1:F2)) at hxe
    try simp only [Finsupp.single_zero,map_add,map_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx ⊢
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1, LinearEquiv.apply_symm_apply, Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

/-- The precise high-filtration elimination in pi_(125,130).
In AF15..24 the finite records and BHS weight130 formula leave no
associated grade. In particular the d5 source at AF15 is not a permanent
cycle, and the AF18 d5 target has lambda exponent13>=4. Boundary-lift
arguments may choose a lambda^4-torsion lift; arbitrary lifts can differ
by higher filtration, which this range calculation must retain and remove.
This is not a claim that every lift of that target is lambda^4-torsion. -/

private theorem stem125_sixth_pages_20_24
    (s : ℕ) (hs : 20 ≤ s) (hs' : s ≤ 24) :
    Subsingleton ((KIP126.Main.Internal.Selected.Normalized.sequence .sphere).Page 6 (s,(s:ℤ)+125)) := by
  classical

  interval_cases s
  · exact h125_page20
  · exact h125_page21
  · exact h125_page22
  · exact h125_page23
  · exact h125_page24



end
end KIP126.Main.Internal.High125
