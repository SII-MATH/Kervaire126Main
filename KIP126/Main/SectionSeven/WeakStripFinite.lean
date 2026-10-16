module
public import KIP126.Main.Conditions
public import KIP126.ProofTools.Operations
public import KIP126.ProofTools.Representatives
import all KIP126.Main.SectionSeven.WeakYFinite
/-! WeakRepresentative finite calculations, bbac1fc05843 (MIT):
329–371,399–1123,1676–1874. The repeated E3 kernel calculation is shared. -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal.WeakStripFinite
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Literature KIP126.Kervaire.Route
open KIP126.ProofTools.Operations
open KIP126.Main.Internal.Selected KIP126.Main.Internal.Selected.NuError
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem main_h6b_third_kernel_frame   :
    ∃ b2 b3:(Normalized.sphere).Page 3 (9,134),
      RepresentsOnPage (Normalized.sphere) 3 (9,134) (Normalized.basis .sphere 9 134 2) b2 ∧
      RepresentsOnPage (Normalized.sphere) 3 (9,134) (Normalized.basis .sphere 9 134 3) b3 ∧
      ∀y:(Normalized.sphere).Page 3 (9,134), (Normalized.sphere).d 3 (9,134) y=0 →
        y=0 ∨ y=b2 ∨ y=b3 ∨ y=b3+b2 := by
  let E := Normalized.sphere
  have h226 : HasDifferential E 3 (9,134) (12,136)
      ((Normalized.basis .sphere 9 134 1)) ((Normalized.basis .sphere 12 136 0)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 226) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (9,134) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [0] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h227 : HasDifferential E 2 (9,134) (11,135)
      ((Normalized.basis .sphere 9 134 0)) ((Normalized.basis .sphere 11 135 3) + (Normalized.basis .sphere 11 135 4)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,9,134,[0],11,135,[3, 4],"S0_AdamsE2_ss",2698⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 227) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (9,134) (11,135) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 135 [3, 4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h228 : HasDifferential E 2 (9,134) (11,135)
      ((Normalized.basis .sphere 9 134 4)) ((Normalized.basis .sphere 11 135 4)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,9,134,[4],11,135,[4],"S0_AdamsE2_ss",2699⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 228) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (9,134) (11,135) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [4] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 135 [4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h251 : HasDifferential E 2 (8,134) (10,135)
      ((Normalized.basis .sphere 8 134 1)) ((Normalized.basis .sphere 10 135 3)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,8,134,[1],10,135,[3],"S0_AdamsE2_ss",2783⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 251) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (8,134) (10,135) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 8 134 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [3] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h252 : HasDifferential E 3 (10,135) (13,137)
      ((Normalized.basis .sphere 10 135 0)) ((Normalized.basis .sphere 13 137 0)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2784⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 252) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (10,135) (13,137) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 137 [0] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h253 : HasDifferential E 2 (10,135) (12,136)
      ((Normalized.basis .sphere 10 135 1)) ((Normalized.basis .sphere 12 136 1) + (Normalized.basis .sphere 12 136 2)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,10,135,[1],12,136,[1, 2],"S0_AdamsE2_ss",2785⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 253) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [1, 2] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h254 : HasDifferential E 2 (10,135) (12,136)
      ((Normalized.basis .sphere 10 135 2)) ((Normalized.basis .sphere 12 136 3) + (Normalized.basis .sphere 12 136 4)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,10,135,[2],12,136,[3, 4],"S0_AdamsE2_ss",2786⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 254) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [3, 4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h255 : HasDifferential E 2 (10,135) (12,136)
      ((Normalized.basis .sphere 10 135 4)) ((Normalized.basis .sphere 12 136 4)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,10,135,[4],12,136,[4],"S0_AdamsE2_ss",2787⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 255) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (10,135) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 135 [4] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h174 : ReachesPage E 3 (6,132) (Normalized.basis .sphere 6 132 0) := by
    have hh := Normalized.result ⟨.sphere,.reaches,3,6,132,[0],6,132,[],"S0_AdamsE2_ss",2574⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 174) rfl)
    dsimp only [Normalized.Statement] at hh
    obtain ⟨x,hx,hh⟩ := hh
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 6 132 [0]=true := rfl
    simp only [Normalized.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hh
    exact hh
  have h224 : ReachesPage E 1000 (9,134) (Normalized.basis .sphere 9 134 2) := by
    have hh := Normalized.result ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 224) rfl)
    dsimp only [Normalized.Statement] at hh
    obtain ⟨x,hx,hh⟩ := hh
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [2]=true := rfl
    simp only [Normalized.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hh
    exact hh
  have h225 : ReachesPage E 7 (9,134) (Normalized.basis .sphere 9 134 3) := by
    have hh := Normalized.result ⟨.sphere,.reaches,7,9,134,[3],9,134,[],"S0_AdamsE2_ss",2696⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 225) rfl)
    dsimp only [Normalized.Statement] at hh
    obtain ⟨x,hx,hh⟩ := hh
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [3]=true := rfl
    simp only [Normalized.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hh
    exact hh
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
    exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 173) rfl)
  change E.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 9 134 i.val at he
  obtain ⟨f,hf⟩ := Normalized.basis_correct ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
    exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 191) rfl)
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = Normalized.basis .sphere 11 135 i.val at hf
  obtain ⟨g,hg⟩ := Normalized.basis_correct ⟨.sphere,10,135,["413,1", "412,1", "0,1,391,1", "0,1,390,1", "0,2,375,1"]⟩ (by
    exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 182) rfl)
  change E.Page 2 (10,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = Normalized.basis .sphere 10 135 i.val at hg
  obtain ⟨k,hk⟩ := Normalized.basis_correct ⟨.sphere,12,136,["1,1,387,1", "0,1,410,1", "0,1,409,1", "0,2,389,1", "0,4,367,1"]⟩ (by
    exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 200) rfl)
  change E.Page 2 (12,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
  change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = Normalized.basis .sphere 12 136 i.val at hk
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 9 134 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 9 134 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 9 134 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 9 134 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 9 134 4 := he 4
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 11 135 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 11 135 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 11 135 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 11 135 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 11 135 4 := hf 4
  have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 10 135 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 10 135 1 := hg 1
  have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 10 135 2 := hg 2
  have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 10 135 3 := hg 3
  have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 10 135 4 := hg 4
  have hk0 : k.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 12 136 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 12 136 1 := hk 1
  have hk2 : k.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 12 136 2 := hk 2
  have hk3 : k.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 12 136 3 := hk 3
  have hk4 : k.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 12 136 4 := hk 4
  have dg0 : E.d 2 (10,135) (Normalized.basis .sphere 10 135 0) = 0 := by
    obtain ⟨_,x,y,hx,hy,hd⟩ := h252
    obtain ⟨x2,hx2⟩ := represents_before (by decide : (2:ℤ)≤2) (by decide) hx
    rw [←hx2.eq_on_page_two] at hx2
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega)
      (by decide) hx2 ⟨_,hx⟩
  have dg3 : E.d 2 (10,135) (Normalized.basis .sphere 10 135 3)=0 := by
    have hd : E.d 2 (8,134) (Normalized.basis .sphere 8 134 1)=Normalized.basis .sphere 10 135 3 := h251.eq_on_page_two.2
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(8,134)) ⟨_,hd⟩
  have dg1 : E.d 2 (10,135) (Normalized.basis .sphere 10 135 1)=Normalized.basis .sphere 12 136 1 + Normalized.basis .sphere 12 136 2 := h253.eq_on_page_two.2
  have dg2 : E.d 2 (10,135) (Normalized.basis .sphere 10 135 2)=Normalized.basis .sphere 12 136 3 + Normalized.basis .sphere 12 136 4 := h254.eq_on_page_two.2
  have dg4 : E.d 2 (10,135) (Normalized.basis .sphere 10 135 4)=Normalized.basis .sphere 12 136 4 := h255.eq_on_page_two.2
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
    apply represents_next_nonzero_of_not_incoming (E:=E) (r:=2) (q:=(10,135))
      (by decide) (by decide) ht (NuError.middle_rep2 (by decide) ht)
    intro u hu
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
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) hr ha
    rw [←hb.eq_on_page_two] at hb
    exact hb
  have d1 : E.d 2 (9,134) (Normalized.basis .sphere 9 134 1)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb1) ⟨b1,hb1⟩
  have d2 : E.d 2 (9,134) (Normalized.basis .sphere 9 134 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb2) ⟨b2,hb2⟩
  have d3 : E.d 2 (9,134) (Normalized.basis .sphere 9 134 3)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) (hrep2 (by decide) hb3) ⟨b3,hb3⟩
  have d0 : E.d 2 (9,134) (Normalized.basis .sphere 9 134 0)=Normalized.basis .sphere 11 135 3+Normalized.basis .sphere 11 135 4 := h227.eq_on_page_two.2
  have d4 : E.d 2 (9,134) (Normalized.basis .sphere 9 134 4)=Normalized.basis .sphere 11 135 4 := h228.eq_on_page_two.2
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    obtain ⟨hr,z,hz,ha⟩ := hx
    obtain ⟨_,w,hw,hb⟩ := hy
    exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,ha,hb]⟩
  have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (c : F2) (h : RepresentsOnPage E r p x a) :
      RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
    split
    · exact RepresentsOnPage.zero h.1
    · exact h
  have f2_expand {N : ℕ} (f : Fin N →₀ F2) :
      f = ∑ i : Fin N, if f i=0 then 0 else Finsupp.single i 1 := by
    ext i
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i]
    · generalize f i=b
      fin_cases b <;> simp
    · intro j hj hji
      by_cases hf : f j=0
      · simp [hf]
      · simp [hf,hji]
    · simp
  have frame (y : E.Page 3 (9,134)) (hy : E.d 3 (9,134) y=0) : y=0 ∨ y=b2 ∨ y=b3 ∨ y=b3+b2 := by
    obtain ⟨x,hx⟩ := PageThree.exists_representative (9,134) y
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
  exact ⟨b2,b3,hb2,hb3,frame⟩
private theorem candidates_raw   :
    HasNonzeroDifferential (Normalized.sphere) 3 (6,132) (9,134)
      (Normalized.basis .sphere 6 132 0) (Normalized.basis .sphere 9 134 3) ∨
    HasNonzeroDifferential (Normalized.sphere) 3 (6,132) (9,134)
      (Normalized.basis .sphere 6 132 0) (Normalized.basis .sphere 9 134 3 + Normalized.basis .sphere 9 134 2) := by
  let E := Normalized.sphere
  obtain ⟨b2,b3,hb2,hb3,frame⟩ := main_h6b_third_kernel_frame
  have h174 : ReachesPage E 3 (6,132) (Normalized.basis .sphere 6 132 0) := by
    have hh := Normalized.result ⟨.sphere,.reaches,3,6,132,[0],6,132,[],"S0_AdamsE2_ss",2574⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 174) rfl)
    dsimp only [Normalized.Statement] at hh
    obtain ⟨x,hx,hh⟩ := hh
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 6 132 [0]=true := rfl
    simp only [Normalized.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hh
    exact hh
  have n659 : ¬ HasDifferential E 3 (6,132) (9,134) (Normalized.basis .sphere 6 132 0) (0) := by
    have hh := Normalized.result ⟨.sphere,.refutation,3,6,132,[0],9,134,[],"proofs.db/log",2047477⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 659) rfl)
    dsimp only [Normalized.Statement] at hh
    obtain ⟨x,hx,y,hy,hh⟩ := hh
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 6 132 [0]=true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 []=true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hh
    exact hh
  have n660 : ¬ HasDifferential E 3 (6,132) (9,134) (Normalized.basis .sphere 6 132 0) (Normalized.basis .sphere 9 134 2) := by
    have hh := Normalized.result ⟨.sphere,.refutation,3,6,132,[0],9,134,[2],"proofs.db/log",2047478⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 660) rfl)
    dsimp only [Normalized.Statement] at hh
    obtain ⟨x,hx,y,hy,hh⟩ := hh
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 6 132 [0]=true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [2]=true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
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
    rw [h]; exact NuError.middle_add hb3 hb2
private theorem main_h6b_finite_cosets
    (x:Normalized.Page .sphere 9 134) (hx:x∈nCycles 7 (9,134)) :
    x∈nBoundaries 3 (9,134) ∨
    x-Normalized.basis .sphere 9 134 2∈nBoundaries 3 (9,134) := by
  let E:=Normalized.sphere
  let B:=nBoundaries 3 (9,134)
  let u:Normalized.Page .sphere 9 134:=Normalized.basis .sphere 9 134 2
  let v:Normalized.Page .sphere 9 134:=Normalized.basis .sphere 9 134 3
  have hu:u+u=0 := by
    obtain ⟨e,he⟩:=Normalized.basis_correct ⟨.sphere,9,134,["391,1","390,1","69,1,82,1","18,1,190,1","0,1,375,1"]⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 173) rfl)
    change E.Page 2 (9,134)≃ₗ[ℤ](Fin 5→₀F2) at e
    apply e.injective
    ext i
    simp only [map_add,map_zero,Finsupp.add_apply,Finsupp.zero_apply]
    generalize e u i=a
    fin_cases a <;> decide
  have hnu:-u=u := by
    exact neg_eq_iff_add_eq_zero.mpr (by simpa only [add_comm] using hu)
  have hv:v∈B ∨ v-u∈B := by
    rcases candidates_raw with h|h
    · left
      exact NuError.boundary_of_zero_representative (r:=4) (p:=(9,134))
        (differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h.toHasDifferential)
    · right
      have hb:v+u∈B := NuError.boundary_of_zero_representative (r:=4) (p:=(9,134))
        (differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h.toHasDifferential)
      simpa only [sub_eq_add_neg,hnu] using hb
  obtain ⟨b2,b3,hb2,hb3,frame⟩:=main_h6b_third_kernel_frame
  obtain ⟨a8,ha8⟩:ReachesPage E 8 (9,134) x:=
    (WeakYFinite.nCycle_iff_reaches 8 (by decide) (9,134) x).mp ⟨by decide,hx⟩
  obtain ⟨a3,ha3⟩:=represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤8) ha8
  have hd:E.d 3 (9,134) a3=0:=represents_d_zero_of_later
    (by change (2:ℤ)≤3; omega) (by decide) ha3 ⟨a8,ha8⟩
  have hdiff {y:E.Page 2 (9,134)} {a:E.Page 3 (9,134)}
      (hxa:RepresentsOnPage E 3 (9,134) x a)
      (hya:RepresentsOnPage E 3 (9,134) y a) : x-y∈B := by
    have hh:RepresentsOnPage E 3 (9,134) (x-y) 0 := by
      obtain ⟨hr,z,hz,hza⟩:=hxa
      obtain ⟨_,w,hw,hwa⟩:=hya
      refine ⟨hr,z-w,by rw [map_sub,hz,hw],?_⟩
      rw [map_sub,hza,hwa,sub_self]
    exact WeakYFinite.nBoundaries_monotone (9,134) (by decide : (2:ℤ)≤3)
      (NuError.boundary_of_zero_representative (r:=3) (p:=(9,134)) hh)
  rcases frame a3 hd with h|h|h|h
  · left
    rw [h] at ha3
    exact WeakYFinite.nBoundaries_monotone (9,134) (by decide : (2:ℤ)≤3)
      (NuError.boundary_of_zero_representative (r:=3) (p:=(9,134)) ha3)
  · right
    rw [h] at ha3
    exact hdiff ha3 hb2
  · rw [h] at ha3
    have hh:=hdiff ha3 hb3
    change x-v∈B at hh
    rcases hv with hv|hv
    · left
      have he:(x-v)+v=x:=sub_add_cancel x v
      simpa only [he] using B.add_mem hh hv
    · right
      have he:(x-v)+(v-u)=x-u:=by abel
      simpa only [he] using B.add_mem hh hv
  · rw [h] at ha3
    have hb:RepresentsOnPage E 3 (9,134) (v+u) (b3+b2) := by
      obtain ⟨hr,z,hz,hza⟩:=hb3
      obtain ⟨_,w,hw,hwa⟩:=hb2
      exact ⟨hr,z+w,by rw [map_add,hz,hw],by rw [map_add,hza,hwa]⟩
    have hh:=hdiff ha3 hb
    rcases hv with hv|hv
    · right
      have he:(x-(v+u))+v=x-u:=by abel
      simpa only [he] using B.add_mem hh hv
    · left
      have he:(x-(v+u))+(v-u)=x := by
        calc
          _=x-(u+u) := by abel
          _=x := by rw [hu,sub_zero]
      simpa only [he] using B.add_mem hh hv
private theorem main_af8_cycles_boundary   :
    nCycles 8 (8,133) ≤ nBoundaries 2 (8,133) := by
  let E := Normalized.sphere
  have h200 : HasDifferential E 3 (8,133) (11,135)
      (Normalized.basis .sphere 8 133 0) (Normalized.basis .sphere 11 135 0) := by
    have hrow := Normalized.result ⟨.sphere,.equation,3,8,133,[0],11,135,[0],"S0_AdamsE2_ss",2629⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 200) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (8,133) (11,135) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 8 133 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 135 [0] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h201 : HasDifferential E 2 (8,133) (10,134)
      (Normalized.basis .sphere 8 133 1) (Normalized.basis .sphere 10 134 2 + Normalized.basis .sphere 10 134 4) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,8,133,[1],10,134,[2, 4],"S0_AdamsE2_ss",2630⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 201) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (8,133) (10,134) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 8 133 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 10 134 [2, 4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h226 : HasDifferential E 3 (9,134) (12,136)
      (Normalized.basis .sphere 9 134 1) (Normalized.basis .sphere 12 136 0) := by
    have hrow := Normalized.result ⟨.sphere,.equation,3,9,134,[1],12,136,[0],"S0_AdamsE2_ss",2697⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 226) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (9,134) (12,136) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 136 [0] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h227 : HasDifferential E 2 (9,134) (11,135)
      (Normalized.basis .sphere 9 134 0) (Normalized.basis .sphere 11 135 3 + Normalized.basis .sphere 11 135 4) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,9,134,[0],11,135,[3, 4],"S0_AdamsE2_ss",2698⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 227) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (9,134) (11,135) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 135 [3, 4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h228 : HasDifferential E 2 (9,134) (11,135)
      (Normalized.basis .sphere 9 134 4) (Normalized.basis .sphere 11 135 4) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,9,134,[4],11,135,[4],"S0_AdamsE2_ss",2699⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 228) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (9,134) (11,135) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [4] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 135 [4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    simpa only [add_assoc] using hd
  have h224 : ReachesPage E 1000 (9,134) (Normalized.basis .sphere 9 134 2) := by
    have hrow := Normalized.result ⟨.sphere,.reaches,1000,9,134,[2],9,134,[],"S0_AdamsE2_ss",2695⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 224) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,hd⟩ := hrow
    change ReachesPage E 1000 (9,134) x at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [2] = true := rfl
    simp only [Normalized.decode,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hd
    simpa only [add_assoc] using hd
  have h225 : ReachesPage E 7 (9,134) (Normalized.basis .sphere 9 134 3) := by
    have hrow := Normalized.result ⟨.sphere,.reaches,7,9,134,[3],9,134,[],"S0_AdamsE2_ss",2696⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 225) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,hd⟩ := hrow
    change ReachesPage E 7 (9,134) x at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 134 [3] = true := rfl
    simp only [Normalized.decode,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,8,133,["376,1", "375,1"]⟩ (by
    exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 161) rfl)
  change E.Page 2 (8,133) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 8 133 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 2) 1) = Normalized.basis .sphere 8 133 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 2) 1) = Normalized.basis .sphere 8 133 1 := he 1
  obtain ⟨f,hf⟩ := Normalized.basis_correct ⟨.sphere,9,134,["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ (by
    exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 173) rfl)
  change E.Page 2 (9,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = Normalized.basis .sphere 9 134 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 9 134 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 9 134 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 9 134 2 := hf 2
  have hf3 : f.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 9 134 3 := hf 3
  have hf4 : f.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 9 134 4 := hf 4
  obtain ⟨g,hg⟩ := Normalized.basis_correct ⟨.sphere,11,135,["411,1", "410,1", "409,1", "0,1,389,1", "0,3,367,1"]⟩ (by
    exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 191) rfl)
  change E.Page 2 (11,135) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = Normalized.basis .sphere 11 135 i.val at hg
  have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 11 135 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 11 135 1 := hg 1
  have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 11 135 2 := hg 2
  have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 11 135 3 := hg 3
  have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 11 135 4 := hg 4
  obtain ⟨k,hk⟩ := Normalized.basis_correct ⟨.sphere,10,134,["389,1", "388,1", "1,1,366,1", "0,1,373,1", "0,2,367,1"]⟩ (by
    exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 181) rfl)
  change E.Page 2 (10,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at k
  change ∀ i : Fin 5, k.symm (Finsupp.single i 1) = Normalized.basis .sphere 10 134 i.val at hk
  have hk0 : k.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 10 134 0 := hk 0
  have hk1 : k.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 10 134 1 := hk 1
  have hk2 : k.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 10 134 2 := hk 2
  have hk3 : k.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 10 134 3 := hk 3
  have hk4 : k.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 10 134 4 := hk 4
  have dz {p : ℤ×ℤ} {x : E.Page 2 p} {r : ℤ} (hr : 3≤r)
      (hx : ReachesPage E r p x) : E.d 2 p x=0 := by
    obtain ⟨a,ha⟩ := hx
    obtain ⟨b,hb⟩ := represents_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) ha
    rw [←hb.eq_on_page_two] at hb
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by omega) hb ⟨a,ha⟩
  have hd0 : E.d 2 (9,134) (Normalized.basis .sphere 9 134 0) =
      Normalized.basis .sphere 11 135 3 + Normalized.basis .sphere 11 135 4 := h227.eq_on_page_two.2
  have hd1 : E.d 2 (9,134) (Normalized.basis .sphere 9 134 1) = 0 := by
    obtain ⟨_,x,y,hx,_,_⟩ := h226
    exact dz (by decide) ⟨x,hx⟩
  have hd2 : E.d 2 (9,134) (Normalized.basis .sphere 9 134 2) = 0 := dz (by decide) h224
  have hd3 : E.d 2 (9,134) (Normalized.basis .sphere 9 134 3) = 0 := dz (by decide) h225
  have hd4 : E.d 2 (9,134) (Normalized.basis .sphere 9 134 4) =
      Normalized.basis .sphere 11 135 4 := h228.eq_on_page_two.2
  have incoming_zero (x : E.Page 2 (9,134)) : g (E.d 2 (9,134) x) 0=0 := by
    have hall (a : Fin 5 →₀ F2) : g (E.d 2 (9,134) (f.symm a)) 0=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hci ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (9,134) (f.symm (Finsupp.single i 1))) 0=0
          fin_cases i
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 0 1))) 0=0
            simp only [hf0,hd0,map_add,←hg3,←hg4,LinearEquiv.apply_symm_apply,Finsupp.add_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 1 1))) 0=0
            simp only [hf1,hd1,map_zero,Finsupp.zero_apply]
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 2 1))) 0=0
            simp only [hf2,hd2,map_zero,Finsupp.zero_apply]
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 3 1))) 0=0
            simp only [hf3,hd3,map_zero,Finsupp.zero_apply]
          · change g (E.d 2 (9,134) (f.symm (Finsupp.single 4 1))) 0=0
            simp only [hf4,hd4,←hg4,LinearEquiv.apply_symm_apply]
            norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using hall (f x)
  obtain ⟨_,a,b,ha,hb,hd⟩ := h200
  have hd' : E.d 3 (8,133) a=b := hd
  have hbne : b≠0 := by
    apply represents_next_nonzero_of_not_incoming (E:=E) (r:=2) (q:=(9,134))
      (by decide) (by decide) hb (NuError.middle_rep2 (by decide) hb)
    intro u hu
    have hh := incoming_zero u
    rw [hu,←hg0,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  have hn : E.d 2 (8,133) (e.symm (Finsupp.single 1 1)) ≠ 0 := by
    rw [he1]
    have hh : E.d 2 (8,133) (Normalized.basis .sphere 8 133 1) =
      Normalized.basis .sphere 10 134 2 + Normalized.basis .sphere 10 134 4 := h201.eq_on_page_two.2
    rw [hh]
    intro hz
    have hz' := congrArg (fun x=>k x 2) hz
    simp only [map_add,map_zero,←hk2,←hk4,LinearEquiv.apply_symm_apply,Finsupp.add_apply,Finsupp.zero_apply] at hz'
    norm_num [Finsupp.single_apply,Fin.ext_iff] at hz'
  have frame : ∀ q : E.Page 3 (8,133), q=0 ∨ q=a :=
    frame_after_second (by change (2:ℤ)≤2; omega) (by decide) e (he0.symm ▸ ha) hn
  have ker (q : E.Page 3 (8,133)) (hq : E.d 3 (8,133) q=0) : q=0 := by
    rcases frame q with hh|hh
    · exact hh
    · exact (hbne (by simpa only [hh,hd'] using hq)).elim
  intro x hx
  obtain ⟨a9,ha9⟩ := (WeakYFinite.nCycle_iff_reaches 9 (by decide) (8,133) x).mp
    ⟨by decide, by simpa using hx⟩
  obtain ⟨a3,ha3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤9) ha9
  have hd3 : E.d 3 (8,133) a3=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) ha3 ⟨a9,ha9⟩
  rw [ker a3 hd3] at ha3
  exact NuError.boundary_of_zero_representative (r:=3) (p:=(8,133)) ha3
private theorem main_af7_all_labels   (x : Normalized.Page .sphere 7 132) :
    x=0 ∨ x=Normalized.basis .sphere 7 132 0 := by
  classical
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,7,132,["0,2,340,1"]⟩ (by
    exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.degrees) (i := 149) rfl)
  change (Normalized.sphere).Page 2 (7,132) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
  change ∀i:Fin 1,e.symm (Finsupp.single i 1)=Normalized.basis .sphere 7 132 i.val at he
  have hf : e x=Finsupp.single (0:Fin 1) ((e x) 0) := by
    apply Finsupp.ext
    intro i
    have hi:i=0 := Subsingleton.elim _ _
    subst i
    simp only [Finsupp.single_eq_same]
  have h01 : (e x) 0=0 ∨ (e x) 0=1 := by
    generalize (e x) 0=a
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases h01 with hx|hx
  · left
    apply e.injective
    rw [hf,hx,Finsupp.single_zero,map_zero]
  · right
    rw [hx] at hf
    exact (e.symm_apply_apply x).symm.trans ((congrArg e.symm hf).trans (he 0))
private theorem main_af7_label_boundary   :
    Normalized.basis .sphere 7 132 0 ∈ nBoundaries 3 (7,132) := by
  let E := Normalized.sphere
  have hd : HasDifferential E 3 (4,130) (7,132)
      (Normalized.basis .sphere 4 130 0) (Normalized.basis .sphere 7 132 0) := by
    have hrow := Normalized.result ⟨.sphere,.equation,3,4,130,[0],7,132,[0],"S0_AdamsE2_ss",2437⟩ (by
      exact List.mem_of_getElem? (l := KIP126.Computation.Table.Raw.claims) (i := 157) rfl)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (4,130) (7,132) a b at h
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 4 130 [0]=true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 7 132 [0]=true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  exact NuError.boundary_of_zero_representative (r:=4) (p:=(7,132))
    (differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide) hd)

end
end KIP126.Main.SectionSeven.Internal.WeakStripFinite
