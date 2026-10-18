module
public import KIP126.Main.Conditions
import all KIP126.Main.SectionSeven.WeakYFinite
import all KIP126.Main.Internal.High125.Differential
/-! Exact AF15/16 kernel calculations, AnyYHelpers:541–1111,1504–1594
at bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal.AnyYFinite
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Literature KIP126.Kervaire.Route
open KIP126.Main.Internal.Selected KIP126.Main.Internal.Selected.NuError
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
private theorem y_detection_page_af16_source_frame
    (x : (Normalized.sphere).Page 2 (16,141))
    (hc : x ∈ nCycles 7 (16,141)) :
    x=0 ∨ x=Normalized.basis .sphere 16 141 1 ∨ x=Normalized.basis .sphere 16 141 2 ∨ x=Normalized.basis .sphere 16 141 1+Normalized.basis .sphere 16 141 2 := by
  let E := Normalized.sphere
  have h369 : HasDifferential E 2 (14,140) (16,141)
      (Normalized.basis .sphere 14 140 1) (Normalized.basis .sphere 16 141 2) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,14,140,[1],16,141,[2],"S0_AdamsE2_ss",3253⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 369) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (14,140) (16,141) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 14 140 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [2] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h370 : HasDifferential E 4 (12,138) (16,141)
      (Normalized.basis .sphere 12 138 3) (Normalized.basis .sphere 16 141 1) := by
    have hrow := Normalized.result ⟨.sphere,.equation,4,12,138,[3],16,141,[1],"S0_AdamsE2_ss",3254⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 370) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (12,138) (16,141) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 138 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [1] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h371 : HasDifferential E 2 (16,141) (18,142)
      (Normalized.basis .sphere 16 141 0) (Normalized.basis .sphere 18 142 0 + Normalized.basis .sphere 18 142 1) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,16,141,[0],18,142,[0, 1],"S0_AdamsE2_ss",3255⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 371) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (16,141) (18,142) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 142 [0, 1] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h372 : HasDifferential E 2 (16,141) (18,142)
      (Normalized.basis .sphere 16 141 3) (Normalized.basis .sphere 18 142 1) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,16,141,[3],18,142,[1],"S0_AdamsE2_ss",3256⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 372) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (16,141) (18,142) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 18 142 [1] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,16,141,["473,1", "1,1,448,1", "0,1,67,1,107,1", "0,2,449,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 232 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (16,141) ≃ₗ[ℤ] (Fin 4 →₀ ZMod 2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 16 141 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = Normalized.basis .sphere 16 141 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = Normalized.basis .sphere 16 141 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = Normalized.basis .sphere 16 141 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = Normalized.basis .sphere 16 141 3 := he 3
  obtain ⟨f,hf⟩ := Normalized.basis_correct ⟨.sphere,18,142,["0,1,472,1", "0,4,440,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 245 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (18,142) ≃ₗ[ℤ] (Fin 2 →₀ ZMod 2) at f
  change ∀ i : Fin 2, f.symm (Finsupp.single i 1) = Normalized.basis .sphere 18 142 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 2) 1) = Normalized.basis .sphere 18 142 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 2) 1) = Normalized.basis .sphere 18 142 1 := hf 1
  obtain ⟨_,u,v,hu,hv,hd⟩ := h370
  have hd' : E.d 4 (12,138) u=v := hd
  have hdv : E.d 4 (16,141) v=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=4) (p:=(12,138)) ⟨u,hd'⟩
  have hv2 : RepresentsOnPage E 2 (16,141) (Normalized.basis .sphere 16 141 1)
      (Normalized.basis .sphere 16 141 1) := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hv
    rw [←hb.eq_on_page_two] at hb
    exact hb
  have hd1 : E.d 2 (16,141) (Normalized.basis .sphere 16 141 1)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hv2 ⟨v,hv⟩
  have hz2 : RepresentsOnPage E 4 (16,141) (Normalized.basis .sphere 16 141 2) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h369
  have hd2 : E.d 2 (16,141) (Normalized.basis .sphere 16 141 2)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤4) hz2
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz2⟩
  have hd0 : E.d 2 (16,141) (Normalized.basis .sphere 16 141 0) =
      Normalized.basis .sphere 18 142 0 + Normalized.basis .sphere 18 142 1 := h371.eq_on_page_two.2
  have hd3 : E.d 2 (16,141) (Normalized.basis .sphere 16 141 3) =
      Normalized.basis .sphere 18 142 1 := h372.eq_on_page_two.2
  obtain ⟨xc,hxc⟩ := (WeakYFinite.nCycle_iff_reaches 8 (by decide) (16,141) x).mp ⟨by decide,hc⟩
  change RepresentsOnPage E 8 (16,141) x xc at hxc
  have hx : E.d 2 (16,141) x=0 := by
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤8) hxc
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<8) hx2 ⟨xc,hxc⟩
    simpa only [hx2.eq_on_page_two] using h
  have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) := by
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3)) := by rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  generalize hc3 : e x 3=c3 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    exact Or.inl hxe
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [he3, hd3] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    simp only [he2] at hxe
    exact Or.inr (Or.inr (Or.inl hxe))
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he2, he3, hd2, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    simp only [he1] at hxe
    exact Or.inr (Or.inl hxe)
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he1, he3, hd1, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    simp only [he1, he2] at hxe
    exact Or.inr (Or.inr (Or.inr hxe))
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add] at hxe
    rw [hxe] at hx
    simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he3, hd0, hd3] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he2, hd0, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he2, he3, hd0, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he3, hd0, hd1, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (1:ZMod 2)) at hxe
    simp only [map_add] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 0) hx
    simp only [map_add,map_zero,←hf0, ←hf1,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval

private theorem y_detection_page_af15_source_frame
    (x : (Normalized.sphere).Page 2 (15,140))
    (hc : x ∈ nCycles 8 (15,140)) :
    x=0 ∨ x=Normalized.basis .sphere 15 140 1 ∨ x=Normalized.basis .sphere 15 140 4 ∨ x=Normalized.basis .sphere 15 140 1+Normalized.basis .sphere 15 140 4 := by
  let E := Normalized.sphere
  have h354 : HasDifferential E 2 (13,139) (15,140)
      (Normalized.basis .sphere 13 139 1) (Normalized.basis .sphere 15 140 4) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,13,139,[1],15,140,[4],"S0_AdamsE2_ss",3150⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 354) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (13,139) (15,140) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 139 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h355 : HasDifferential E 4 (11,137) (15,140)
      (Normalized.basis .sphere 11 137 2) (Normalized.basis .sphere 15 140 1) := by
    have hrow := Normalized.result ⟨.sphere,.equation,4,11,137,[2],15,140,[1],"S0_AdamsE2_ss",3151⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 355) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (11,137) (15,140) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 137 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [1] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h357 : HasDifferential E 2 (15,140) (17,141)
      (Normalized.basis .sphere 15 140 0) (Normalized.basis .sphere 17 141 3) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,15,140,[0],17,141,[3],"S0_AdamsE2_ss",3153⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 357) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (15,140) (17,141) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 17 141 [3] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h358 : HasDifferential E 2 (15,140) (17,141)
      (Normalized.basis .sphere 15 140 3) (Normalized.basis .sphere 17 141 1) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,15,140,[3],17,141,[1],"S0_AdamsE2_ss",3154⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 358) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (15,140) (17,141) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 17 141 [1] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,15,140,["456,1", "67,1,107,1", "1,1,439,1", "0,1,449,1", "0,3,425,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 224 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (15,140) ≃ₗ[ℤ] (Fin 5 →₀ ZMod 2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 15 140 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 15 140 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 15 140 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 15 140 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 15 140 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 15 140 4 := he 4
  obtain ⟨f,hf⟩ := Normalized.basis_correct ⟨.sphere,17,141,["472,1", "0,2,448,1", "0,3,440,1", "0,3,439,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 239 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (17,141) ≃ₗ[ℤ] (Fin 4 →₀ ZMod 2) at f
  change ∀ i : Fin 4, f.symm (Finsupp.single i 1) = Normalized.basis .sphere 17 141 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 4) 1) = Normalized.basis .sphere 17 141 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 4) 1) = Normalized.basis .sphere 17 141 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 4) 1) = Normalized.basis .sphere 17 141 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 4) 1) = Normalized.basis .sphere 17 141 3 := hf 3
  obtain ⟨xraw,yraw,hx,hy,hd⟩ := KIP126.Main.Internal.High125.stem125_af15_nonzero_d5
  have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [2]=true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 20 144 [0]=true := rfl
  simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  obtain ⟨_,u,v,hu,hv,hd,hn⟩ := hd
  have hd' : E.d 5 (15,140) u=v := hd
  have hz1 : RepresentsOnPage E 5 (15,140) (Normalized.basis .sphere 15 140 1) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide) h355
  have hz4 : RepresentsOnPage E 5 (15,140) (Normalized.basis .sphere 15 140 4) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h354
  have hd1 : E.d 2 (15,140) (Normalized.basis .sphere 15 140 1)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz1
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz1⟩
  have hd2 : E.d 2 (15,140) (Normalized.basis .sphere 15 140 2)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hu
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨u,hu⟩
  have hd4 : E.d 2 (15,140) (Normalized.basis .sphere 15 140 4)=0 := by
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤5) hz4
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨0,hz4⟩
  have hd0 : E.d 2 (15,140) (Normalized.basis .sphere 15 140 0)=Normalized.basis .sphere 17 141 3 := h357.eq_on_page_two.2
  have hd3 : E.d 2 (15,140) (Normalized.basis .sphere 15 140 3)=Normalized.basis .sphere 17 141 1 := h358.eq_on_page_two.2
  obtain ⟨xc,hxc⟩ := (WeakYFinite.nCycle_iff_reaches 9 (by decide) (15,140) x).mp ⟨by decide,hc⟩
  change RepresentsOnPage E 9 (15,140) x xc at hxc
  have hx : E.d 2 (15,140) x=0 := by
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤9) hxc
    have h := represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<9) hx2 ⟨xc,hxc⟩
    simpa only [hx2.eq_on_page_two] using h
  have heq : e x = Finsupp.single 0 (e x 0) + Finsupp.single 1 (e x 1) + Finsupp.single 2 (e x 2) + Finsupp.single 3 (e x 3) + Finsupp.single 4 (e x 4) := by
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
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    exact Or.inl hxe
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    simp only [he4] at hxe
    exact Or.inr (Or.inr (Or.inl hxe))
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [he3, hd3] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he3, he4, hd3, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    exfalso
    apply hn
    have hrep : RepresentsOnPage E 5 (15,140) x u := by
      rw [hxe]
      rw [he2]
      simpa only [zero_add,add_zero] using hu
    exact hd'.symm.trans (represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<9) hrep ⟨xc,hxc⟩)
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    exfalso
    apply hn
    have hrep : RepresentsOnPage E 5 (15,140) x u := by
      rw [hxe]
      rw [he2, he4]
      simpa only [zero_add,add_zero] using represents_add_tail (hu) hz4
    exact hd'.symm.trans (represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<9) hrep ⟨xc,hxc⟩)
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he2, he3, hd2, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he2, he3, he4, hd2, hd3, hd4, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
    simp only [he1] at hxe
    exact Or.inr (Or.inl hxe)
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    simp only [he1, he4] at hxe
    exact Or.inr (Or.inr (Or.inr hxe))
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he1, he3, hd1, hd3, zero_add] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he1, he3, he4, hd1, hd3, hd4, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    exfalso
    apply hn
    have hrep : RepresentsOnPage E 5 (15,140) x u := by
      rw [hxe]
      rw [he1, he2]
      simpa only [zero_add,add_zero] using represents_add_tail (hz1) hu
    exact hd'.symm.trans (represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<9) hrep ⟨xc,hxc⟩)
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    exfalso
    apply hn
    have hrep : RepresentsOnPage E 5 (15,140) x u := by
      rw [hxe]
      rw [he1, he2, he4]
      simpa only [zero_add,add_zero] using represents_add_tail (represents_add_tail (hz1) hu) hz4
    exact hd'.symm.trans (represents_d_zero_of_later (by change (2:ℤ)≤5; omega) (by decide : (5:ℤ)<9) hrep ⟨xc,hxc⟩)
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he1, he2, he3, hd1, hd2, hd3, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (0:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,zero_add] at hxe
    rw [hxe] at hx
    simp only [map_add, he1, he2, he3, he4, hd1, hd2, hd3, hd4, zero_add, add_zero] at hx
    have hval := congrArg (fun y => f y 1) hx
    simp only [map_zero,←hf1,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,add_zero] at hxe
    rw [hxe] at hx
    simp only [he0, hd0] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he4, hd0, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he3, hd0, hd3] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he3, he4, hd0, hd3, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he2, hd0, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he2, he4, hd0, hd2, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he2, he3, hd0, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (0:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he2, he3, he4, hd0, hd2, hd3, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, hd0, hd1, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he4, hd0, hd1, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he3, hd0, hd1, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (0:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he3, he4, hd0, hd1, hd3, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he2, hd0, hd1, hd2, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (0:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he2, he4, hd0, hd1, hd2, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_zero, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (0:ZMod 2)) at hxe
    simp only [Finsupp.single_zero,map_add,add_zero] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he2, he3, hd0, hd1, hd2, hd3, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval
  · change x = e.symm (Finsupp.single 0 (1:ZMod 2) + Finsupp.single 1 (1:ZMod 2) + Finsupp.single 2 (1:ZMod 2) + Finsupp.single 3 (1:ZMod 2) + Finsupp.single 4 (1:ZMod 2)) at hxe
    simp only [map_add] at hxe
    rw [hxe] at hx
    simp only [map_add, he0, he1, he2, he3, he4, hd0, hd1, hd2, hd3, hd4, add_zero] at hx
    have hval := congrArg (fun y => f y 3) hx
    simp only [map_add,map_zero,←hf1, ←hf3,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hval
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hval


private theorem y_detection_page_af15_source_boundary  :
    nCycles 8 (15,140) ≤ nBoundaries 4 (15,140) := by
  intro x hx
  let E := Normalized.sphere
  have h355 : HasDifferential E 4 (11,137) (15,140)
      (Normalized.basis .sphere 11 137 2) (Normalized.basis .sphere 15 140 1) := by
    have hrow := Normalized.result ⟨.sphere,.equation,4,11,137,[2],15,140,[1],"S0_AdamsE2_ss",3151⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 355) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (11,137) (15,140) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 137 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [1] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h354 : HasDifferential E 2 (13,139) (15,140)
      (Normalized.basis .sphere 13 139 1) (Normalized.basis .sphere 15 140 4) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,13,139,[1],15,140,[4],"S0_AdamsE2_ss",3150⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 354) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (13,139) (15,140) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 139 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 140 [4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have hb1 : Normalized.basis .sphere 15 140 1 ∈ nBoundaries 4 (15,140) :=
    boundary_of_zero_representative (r:=5) (p:=(15,140))
      (differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h355)
  have hb4 : Normalized.basis .sphere 15 140 4 ∈ nBoundaries 4 (15,140) :=
    boundary_of_zero_representative (r:=5) (p:=(15,140))
      (differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) h354)
  rcases y_detection_page_af15_source_frame x hx with rfl|rfl|rfl|rfl
  · exact Submodule.zero_mem _
  · exact hb1
  · exact hb4
  · exact Submodule.add_mem _ hb1 hb4
private theorem y_detection_page_af16_source_boundary  :
    nCycles 7 (16,141) ≤ nBoundaries 4 (16,141) := by
  intro x hx
  let E := Normalized.sphere
  have h370 : HasDifferential E 4 (12,138) (16,141)
      (Normalized.basis .sphere 12 138 3) (Normalized.basis .sphere 16 141 1) := by
    have hrow := Normalized.result ⟨.sphere,.equation,4,12,138,[3],16,141,[1],"S0_AdamsE2_ss",3254⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 370) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (12,138) (16,141) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 138 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [1] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h369 : HasDifferential E 2 (14,140) (16,141)
      (Normalized.basis .sphere 14 140 1) (Normalized.basis .sphere 16 141 2) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,14,140,[1],16,141,[2],"S0_AdamsE2_ss",3253⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 369) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (14,140) (16,141) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 14 140 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 141 [2] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have hb1 : Normalized.basis .sphere 16 141 1 ∈ nBoundaries 4 (16,141) :=
    boundary_of_zero_representative (r:=5) (p:=(16,141))
      (differential_target_later_zero (by change (2:ℤ)≤4; omega) (by decide : (4:ℤ)<5) h370)
  have hb2 : Normalized.basis .sphere 16 141 2 ∈ nBoundaries 4 (16,141) :=
    boundary_of_zero_representative (r:=5) (p:=(16,141))
      (differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<5) h369)
  rcases y_detection_page_af16_source_frame x hx with rfl|rfl|rfl|rfl
  · exact Submodule.zero_mem _
  · exact hb1
  · exact hb2
  · exact Submodule.add_mem _ hb1 hb2
end
end KIP126.Main.SectionSeven.Internal.AnyYFinite
