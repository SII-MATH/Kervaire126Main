module
public import KIP126.Main.Conditions
import all KIP126.Main.Internal.Selected.NuErrorData
/-! The original Main AF10 computation used to lift the Q3 relation to Q5,
NuFifth.lean:2361–2920, bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.Internal.NuFifth
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Literature KIP126.Kervaire.Route KIP126.Main.Internal.Selected
open KIP126.ProofTools.Operations
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
private theorem nu_af10_frame  :
    ∃ a : (Normalized.sphere).Page 3 (10,135),
    ∃ b : (Normalized.sphere).Page 3 (13,137),
      RepresentsOnPage (Normalized.sphere) 3 (10,135) (Normalized.basis .sphere 10 135 0) a ∧
      RepresentsOnPage (Normalized.sphere) 3 (13,137) (Normalized.basis .sphere 13 137 0) b ∧
      (Normalized.sphere).d 3 (10,135) a=b ∧
      ∀ z : (Normalized.sphere).Page 3 (10,135), z=0 ∨ z=a := by
  let E := Normalized.sphere
  have h251 : HasDifferential E 2 (8,134) (10,135)
      (Normalized.basis .sphere 8 134 1) (Normalized.basis .sphere 10 135 3) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
      exact List.mem_of_getElem? (i := 251) (by rfl))
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (8,134) (10,135) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 8 134 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [3] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h252 : HasDifferential E 3 (10,135) (13,137)
      (Normalized.basis .sphere 10 135 0) (Normalized.basis .sphere 13 137 0) := by
    have hrow := Normalized.result ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2784⟩ (by
      exact List.mem_of_getElem? (i := 252) (by rfl))
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (10,135) (13,137) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 137 [0] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h253 : HasDifferential E 2 (10,135) (12,136)
      (Normalized.basis .sphere 10 135 1) (Normalized.basis .sphere 12 136 1 + Normalized.basis .sphere 12 136 2) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2785⟩ (by
      exact List.mem_of_getElem? (i := 253) (by rfl))
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [1, 2] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h254 : HasDifferential E 2 (10,135) (12,136)
      (Normalized.basis .sphere 10 135 2) (Normalized.basis .sphere 12 136 3 + Normalized.basis .sphere 12 136 4) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2786⟩ (by
      exact List.mem_of_getElem? (i := 254) (by rfl))
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [3, 4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h255 : HasDifferential E 2 (10,135) (12,136)
      (Normalized.basis .sphere 10 135 4) (Normalized.basis .sphere 12 136 4) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2787⟩ (by
      exact List.mem_of_getElem? (i := 255) (by rfl))
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [4] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 182) (by rfl))
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 10 135 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 10 135 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 10 135 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 10 135 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 10 135 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 10 135 4 := he 4
  obtain ⟨f,hf⟩ := Normalized.basis_correct ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 200) (by rfl))
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = Normalized.basis .sphere 12 136 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 12 136 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 12 136 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 12 136 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 12 136 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 12 136 4 := hf 4
  obtain ⟨_,a0,b0,ha0,hb0,hd⟩ := h252
  have hd' : E.d 3 (10,135) a0=b0 := hd
  have hz3 : RepresentsOnPage E 3 (10,135) (Normalized.basis .sphere 10 135 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide) h251
  have dz {p : ℤ×ℤ} {x : E.Page 2 p} (hx : ReachesPage E 3 p x) : E.d 2 p x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide : (2:ℤ)≤3) ha
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) hb ⟨a,ha⟩
  have hd0 : E.d 2 (10,135) (Normalized.basis .sphere 10 135 0)=0 := dz ⟨a0,ha0⟩
  have hd1 : E.d 2 (10,135) (Normalized.basis .sphere 10 135 1)=
      Normalized.basis .sphere 12 136 1 + Normalized.basis .sphere 12 136 2 := h253.eq_on_page_two.2
  have hd2 : E.d 2 (10,135) (Normalized.basis .sphere 10 135 2)=
      Normalized.basis .sphere 12 136 3 + Normalized.basis .sphere 12 136 4 := h254.eq_on_page_two.2
  have hd3 : E.d 2 (10,135) (Normalized.basis .sphere 10 135 3)=0 := dz ⟨0,hz3⟩
  have hd4 : E.d 2 (10,135) (Normalized.basis .sphere 10 135 4)=
      Normalized.basis .sphere 12 136 4 := h255.eq_on_page_two.2
  have frame (a : E.Page 3 (10,135)) : a=0 ∨ a=a0 := by
    let A := E.ssData (10,135)
    haveI : Epi (A.pageπ 1) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,hza⟩ := (ModuleCat.epi_iff_surjective (A.pageπ 1)).mp inferInstance a
    let x : E.Page 2 (10,135) := (Subobject.ofLE _ _ (A.Z_anti (by decide : (0:WithTop ℕ)≤1)) ≫ A.pageπ 0) z
    have hxa : RepresentsOnPage E 3 (10,135) x a := ⟨by decide,z,rfl,hza⟩
    have hc : E.d 2 (10,135) x=0 := dz ⟨a,hxa⟩
    have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4) := by
      apply Finsupp.ext
      intro i
      fin_cases i <;> simp
    have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4)) := by
      rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc0 : e x 0=c0 at hxe
    generalize hc1 : e x 1=c1 at hxe
    generalize hc2 : e x 2=c2 at hxe
    generalize hc3 : e x 3=c3 at hxe
    generalize hc4 : e x 4=c4 at hxe
    fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;> fin_cases c4
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
      rw [hxe] at hc hxa
      exact Or.inl (represents_unique hxa (RepresentsOnPage.zero (by decide : (2:ℤ)≤3)))
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he4] at hc hxa
      simp only [hd4] at hc
      have hh := congrArg (fun y=>f y 4) hc
      simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he3] at hc hxa
      exact Or.inl (represents_unique hxa hz3)
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he3, he4] at hc hxa
      simp only [map_add,hd3,hd4,zero_add] at hc
      have hh := congrArg (fun y=>f y 4) hc
      simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he2] at hc hxa
      simp only [hd2] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he2, he4] at hc hxa
      simp only [map_add,hd2,hd4] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he2, he3] at hc hxa
      simp only [map_add,hd2,hd3,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he2, he3, he4] at hc hxa
      simp only [map_add,hd2,hd3,hd4,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1] at hc hxa
      simp only [hd1] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he4] at hc hxa
      simp only [map_add,hd1,hd4] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he3] at hc hxa
      simp only [map_add,hd1,hd3,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he3, he4] at hc hxa
      simp only [map_add,hd1,hd3,hd4,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he2] at hc hxa
      simp only [map_add,hd1,hd2] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he2, he4] at hc hxa
      simp only [map_add,hd1,hd2,hd4] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he2, he3] at hc hxa
      simp only [map_add,hd1,hd2,hd3,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (0:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,zero_add] at hxe
      rw [hxe] at hc hxa
      simp only [he1, he2, he3, he4] at hc hxa
      simp only [map_add,hd1,hd2,hd3,hd4,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0] at hc hxa
      exact Or.inr (represents_unique hxa ha0)
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he4] at hc hxa
      simp only [map_add,hd0,hd4,zero_add] at hc
      have hh := congrArg (fun y=>f y 4) hc
      simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he3] at hc hxa
      exact Or.inr (by simpa only [add_zero] using represents_unique hxa (represents_add_tail ha0 hz3))
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he3, he4] at hc hxa
      simp only [map_add,hd0,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 4) hc
      simp only [map_zero,←hf4,LinearEquiv.apply_symm_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he2] at hc hxa
      simp only [map_add,hd0,hd2,zero_add] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he2, he4] at hc hxa
      simp only [map_add,hd0,hd2,hd4,zero_add] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he2, he3] at hc hxa
      simp only [map_add,hd0,hd2,hd3,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (0:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he2, he3, he4] at hc hxa
      simp only [map_add,hd0,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 3) hc
      simp only [map_add,map_zero,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1] at hc hxa
      simp only [map_add,hd0,hd1,zero_add] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd4,zero_add] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he3] at hc hxa
      simp only [map_add,hd0,hd1,hd3,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (0:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he3, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he2] at hc hxa
      simp only [map_add,hd0,hd1,hd2,zero_add] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (0:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he2, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd4,zero_add] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (0:F2)) at hxe
      try simp only [Finsupp.single_zero,map_add,add_zero] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he2, he3] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
    · change x=e.symm (Finsupp.single 0 (1:F2) + Finsupp.single 1 (1:F2) + Finsupp.single 2 (1:F2) + Finsupp.single 3 (1:F2) + Finsupp.single 4 (1:F2)) at hxe
      try simp only [map_add] at hxe
      rw [hxe] at hc hxa
      simp only [he0, he1, he2, he3, he4] at hc hxa
      simp only [map_add,hd0,hd1,hd2,hd3,hd4,zero_add,add_zero] at hc
      have hh := congrArg (fun y=>f y 1) hc
      simp only [map_add,map_zero,←hf1,←hf2,←hf3,←hf4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hh
      norm_num [Finsupp.single_apply,Fin.ext_iff] at hh
  exact ⟨a0,b0,ha0,hb0,hd',frame⟩
private theorem nu_af10_d3_target_nonzero
    {a : (Normalized.sphere).Page 3 (13,137)}
    (ha : RepresentsOnPage (Normalized.sphere) 3 (13,137)
      (Normalized.basis .sphere 13 137 0) a) : a≠0 := by
  let E := Normalized.sphere
  have h279 : HasDifferential E 3 (8,134) (11,136)
      (Normalized.basis .sphere 8 134 3) (Normalized.basis .sphere 11 136 1) := by
    have hrow := Normalized.result ⟨.sphere,.equation,3,8,134,[3],11,136,[1],"S0_AdamsE2_ss",2850⟩ (by
      exact List.mem_of_getElem? (i := 279) (by rfl))
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (8,134) (11,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 8 134 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 136 [1] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h280 : HasDifferential E 3 (8,134) (11,136)
      (Normalized.basis .sphere 8 134 2) (Normalized.basis .sphere 11 136 2) := by
    have hrow := Normalized.result ⟨.sphere,.equation,3,8,134,[2],11,136,[2],"S0_AdamsE2_ss",2851⟩ (by
      exact List.mem_of_getElem? (i := 280) (by rfl))
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (8,134) (11,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 8 134 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 136 [2] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h282 : HasDifferential E 4 (11,136) (15,139)
      (Normalized.basis .sphere 11 136 0) (Normalized.basis .sphere 15 139 0) := by
    have hrow := Normalized.result ⟨.sphere,.equation,4,11,136,[0],15,139,[0],"S0_AdamsE2_ss",2853⟩ (by
      exact List.mem_of_getElem? (i := 282) (by rfl))
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (11,136) (15,139) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 136 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 15 139 [0] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h283 : HasDifferential E 2 (11,136) (13,137)
      (Normalized.basis .sphere 11 136 4) (Normalized.basis .sphere 13 137 3) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2854⟩ (by
      exact List.mem_of_getElem? (i := 283) (by rfl))
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (11,136) (13,137) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 136 [4] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 137 [3] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h281 : ReachesPage E 5 (11,136) (Normalized.basis .sphere 11 136 3) := by
    have hrow := Normalized.result ⟨.sphere,.reaches,5,11,136,[3],11,136,[],"S0_AdamsE2_ss",2852⟩ (by
      exact List.mem_of_getElem? (i := 281) (by rfl))
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,hd⟩ := hrow
    change ReachesPage E 5 (11,136) x at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 136 [3] = true := rfl
    simp only [Normalized.decode,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 208) (by rfl))
  change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀ i : Fin 4, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 13 137 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 4) 1) = Normalized.basis .sphere 13 137 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 4) 1) = Normalized.basis .sphere 13 137 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 4) 1) = Normalized.basis .sphere 13 137 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 4) 1) = Normalized.basis .sphere 13 137 3 := he 3
  obtain ⟨f,hf⟩ := Normalized.basis_correct ⟨.sphere,11,136,["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
    exact List.mem_of_getElem? (i := 192) (by rfl))
  change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = Normalized.basis .sphere 11 136 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 11 136 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 11 136 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 11 136 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 11 136 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 11 136 4 := hf 4
  let ell (x : E.Page 2 (13,137)) : F2 := e x 0
  have hsub {r : ℤ} {p : ℤ×ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    obtain ⟨hr,z,hz,ha⟩ := hx
    obtain ⟨_,w,hw,hb⟩ := hy
    exact ⟨hr,z-w,by rw [map_sub,hz,hw],by rw [map_sub,ha,hb]⟩
  have dz {p : ℤ×ℤ} {x : E.Page 2 p} {r : ℤ} (hr : 3≤r)
      (hx : ReachesPage E r p x) : E.d 2 p x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by omega) hb ⟨a,ha⟩
  have hd0 : E.d 2 (11,136) (Normalized.basis .sphere 11 136 0)=0 := by
    obtain ⟨_,a,b,ha,_,_⟩ := h282
    exact dz (by decide) ⟨a,ha⟩
  have hd1 : E.d 2 (11,136) (Normalized.basis .sphere 11 136 1)=0 := by
    obtain ⟨_,a,b,_,hb,_⟩ := h279
    exact dz (by decide) ⟨b,hb⟩
  have hd2 : E.d 2 (11,136) (Normalized.basis .sphere 11 136 2)=0 := by
    obtain ⟨_,a,b,_,hb,_⟩ := h280
    exact dz (by decide) ⟨b,hb⟩
  have hd3 : E.d 2 (11,136) (Normalized.basis .sphere 11 136 3)=0 := dz (by decide) h281
  have hd4 : E.d 2 (11,136) (Normalized.basis .sphere 11 136 4)=Normalized.basis .sphere 13 137 3 := h283.eq_on_page_two.2
  have incoming_zero (x : E.Page 2 (11,136)) : ell (E.d 2 (11,136) x)=0 := by
    have hall (a : Fin 5 →₀ F2) : ell (E.d 2 (11,136) (f.symm a))=0 := by
      dsimp only [ell]
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change e (E.d 2 (11,136) (f.symm (Finsupp.single i 1))) 0=0
          fin_cases i
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 0 1))) 0=0
            simp only [hf0,hd0,map_zero,Finsupp.zero_apply]
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 1 1))) 0=0
            simp only [hf1,hd1,map_zero,Finsupp.zero_apply]
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 2 1))) 0=0
            simp only [hf2,hd2,map_zero,Finsupp.zero_apply]
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 3 1))) 0=0
            simp only [hf3,hd3,map_zero,Finsupp.zero_apply]
          · change e (E.d 2 (11,136) (f.symm (Finsupp.single 4 1))) 0=0
            rw [hf4,hd4,←he3,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  have nz3 {x : E.Page 2 (13,137)} (hx : ell x=1) {a : E.Page 3 (13,137)}
      (ha : RepresentsOnPage E 3 (13,137) x a) : a≠0 := by
    intro ha0
    obtain ⟨_,z,hz2,hz3⟩ := ha
    obtain ⟨u,hu⟩ := (next_projection_zero_iff_incoming E 2 (by change (2:ℤ)≤2; omega) (11,136) z).mp (hz3.trans ha0)
    change E.d 2 (11,136) u = (Subobject.ofLE _ _ ((E.ssData (13,137)).Z_anti bot_le) ≫ (E.ssData (13,137)).pageπ 0) z at hu
    change (Subobject.ofLE _ _ ((E.ssData (13,137)).Z_anti bot_le) ≫ (E.ssData (13,137)).pageπ 0) z=x at hz2
    have hh := incoming_zero u
    rw [hu,hz2,hx] at hh
    exact one_ne_zero hh
  apply nz3 (x:=Normalized.basis .sphere 13 137 0) ?_ ha
  dsimp only [ell]
  rw [←he0,LinearEquiv.apply_symm_apply]
  simp
theorem nu_af10_cycles_boundary :
    cycles model .sphere 4 (10,135) ≤ boundaries model .sphere 2 (10,135) := by
  intro x hx
  have hx5 := (KIP126.ProofTools.isCycle_iff_reaches model .sphere 5 (by decide) (10,135) x).mp
    ⟨by decide,hx⟩
  obtain ⟨a4,ha4⟩ := NuError.normalized_reaches 5 (10,135) x hx5
  obtain ⟨a3,ha3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) ha4
  have hd : Normalized.sphere.d 3 (10,135) a3=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) ha3 ⟨a4,ha4⟩
  obtain ⟨a,b,ha,hb,hab,frame⟩ := nu_af10_frame
  have haz : a3=0 := by
    rcases frame a3 with h|h
    · exact h
    · exact (nu_af10_d3_target_nonzero hb (hab.symm.trans (by simpa only [h] using hd))).elim
  rw [haz] at ha3
  have hz := NuError.actual_zero_representative 3 (10,135) _ ha3
  rw [NuError.denormalize_label] at hz
  exact represents_zero_mem_boundary model .sphere 3 (10,135) x hz

theorem nu_af10_cycle_quotient_zero : Subsingleton (CycleQuotient model .sphere 4 2 (10,135)) := by
  have hz (x : CycleQuotient model .sphere 4 2 (10,135)) : x=0 := by
    obtain ⟨x⟩ := x
    exact (KIP126.Main.Internal.subquotientClass_eq_zero_iff _ _ _).mpr (nu_af10_cycles_boundary x.property)
  exact ⟨fun x y=>(hz x).trans (hz y).symm⟩
end
end KIP126.Main.Internal.NuFifth
