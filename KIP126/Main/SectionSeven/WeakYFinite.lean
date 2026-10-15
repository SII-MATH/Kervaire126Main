module
public import KIP126.Main.Conditions
public import KIP126.Def.ProofTools.Operations
public import KIP126.Def.ProofTools.Representatives
import all KIP126.Main.Internal.Selected.NuErrorData
/-! Original WeakYDetection finite calculations, bbac1fc05843 (MIT),
lines 786–986 and 2019–2249. Shared AF12/AF13 calculations reuse NuErrorData. -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal.WeakYFinite
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Literature KIP126.Kervaire.Route
open KIP126.ProofTools.Operations
open KIP126.Main.Internal.Selected KIP126.Main.Internal.Selected.NuError
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem nBoundaries_le_cycles (p : ℤ×ℤ) (b c : ℤ) : nBoundaries b p ≤ nCycles c p := by
  intro x hx
  exact boundaries_le_cycles model .sphere p b c hx
private theorem nBoundaries_monotone (p : ℤ×ℤ) {a b : ℤ} (h : a≤b) : nBoundaries a p ≤ nBoundaries b p := by
  intro x hx
  exact boundaries_monotone model .sphere p h hx
private theorem nCycle_iff_reaches (r : ℤ) (hr : 2≤r) (p : ℤ×ℤ) (x : Normalized.sphere.Page 2 p) :
    (2≤r ∧ x∈nCycles (r-1) p) ↔ ReachesPage Normalized.sphere r p x := by
  constructor
  · rintro ⟨_,hx⟩
    have h := normalized_reaches r p (denormalize p x)
      ((KIP126.ProofTools.isCycle_iff_reaches model .sphere r hr p _).mp ⟨by omega,hx⟩)
    have heq : Normalized.label p (denormalize p x)=x := by
      dsimp only [Normalized.label,denormalize]
      rw [←ModuleCat.comp_apply,eqToHom_trans,eqToHom_refl]
      rfl
    rwa [heq] at h
  · intro hx
    exact ⟨hr,nCycle_of_reaches r hr p x hx⟩

private theorem af13_basis_not_cycle  :
    Normalized.basis .sphere 13 138 1 ∉ nCycles 3 (13,138) := by
  let E := Normalized.sphere
  have h231 : HasDifferential E 4 (9,135) (13,138)
      ((Normalized.basis .sphere 9 135 2)) ((Normalized.basis .sphere 13 138 0)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,4,9,135,[2],13,138,[0],"S0_AdamsE2_ss",2790⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 231 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 135 [2] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 138 [0] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h232 : HasDifferential E 4 (9,135) (13,138)
      ((Normalized.basis .sphere 9 135 1)) ((Normalized.basis .sphere 13 138 2)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,4,9,135,[1],13,138,[2],"S0_AdamsE2_ss",2791⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 232 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 4 (9,135) (13,138) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 9 135 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 138 [2] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h288 : HasDifferential E 2 (11,137) (13,138)
      ((Normalized.basis .sphere 11 137 0)) ((Normalized.basis .sphere 13 138 3)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,11,137,[0],13,138,[3],"S0_AdamsE2_ss",2927⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 288 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (11,137) (13,138) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 137 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 138 [3] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h289 : HasDifferential E 2 (11,137) (13,138)
      ((Normalized.basis .sphere 11 137 3)) ((Normalized.basis .sphere 13 138 4)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,11,137,[3],13,138,[4],"S0_AdamsE2_ss",2928⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 289 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (11,137) (13,138) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 137 [3] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 138 [4] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h329 : HasDifferential E 3 (13,138) (16,140)
      ((Normalized.basis .sphere 13 138 1)) ((Normalized.basis .sphere 16 140 1)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,3,13,138,[1],16,140,[1],"S0_AdamsE2_ss",3012⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 329 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 3 (13,138) (16,140) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 13 138 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 140 [1] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h314 : HasDifferential E 2 (12,138) (14,139)
      ((Normalized.basis .sphere 12 138 1)) ((Normalized.basis .sphere 14 139 2)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,12,138,[1],14,139,[2],"S0_AdamsE2_ss",3017⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 314 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (12,138) (14,139) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 12 138 [1] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 14 139 [2] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h343 : HasDifferential E 2 (14,139) (16,140)
      ((Normalized.basis .sphere 14 139 0)) ((Normalized.basis .sphere 16 140 2)) := by
    have hrow := Normalized.result ⟨.sphere,.equation,2,14,139,[0],16,140,[2],"S0_AdamsE2_ss",3081⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 343 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (14,139) (16,140) x y at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 14 139 [0] = true := rfl
    have vy : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 16 140 [2] = true := rfl
    simp only [Normalized.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h342 : ReachesPage E 1000 (14,139) (Normalized.basis .sphere 14 139 1) := by
    have hh := Normalized.result ⟨.sphere,.reaches,1000,14,139,[1],14,139,[],"S0_AdamsE2_ss",3080⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 342 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hh
    obtain ⟨x,hx,hh⟩ := hh
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 14 139 [1]=true := rfl
    simp only [Normalized.decode,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hh
    exact hh
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,13,138,["24,1,190,1", "3,1,335,1", "0,1,425,1", "0,4,391,1", "0,5,375,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 209 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 13 138 i.val at he
  obtain ⟨f,hf⟩ := Normalized.basis_correct ⟨.sphere,14,139,["449,1", "1,1,7,1,275,1", "0,2,425,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 217 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = Normalized.basis .sphere 14 139 i.val at hf
  obtain ⟨g,hg⟩ := Normalized.basis_correct ⟨.sphere,16,140,["9,1,261,1", "1,1,438,1", "0,1,448,1", "0,2,440,1", "0,2,439,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 231 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (16,140) ≃ₗ[ℤ] (Fin 5 →₀ F2) at g
  change ∀ i : Fin 5, g.symm (Finsupp.single i 1) = Normalized.basis .sphere 16 140 i.val at hg
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 13 138 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 13 138 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 13 138 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 13 138 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 13 138 4 := he 4
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = Normalized.basis .sphere 14 139 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = Normalized.basis .sphere 14 139 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = Normalized.basis .sphere 14 139 2 := hf 2
  have hg0 : g.symm (Finsupp.single (0:Fin 5) 1) = Normalized.basis .sphere 16 140 0 := hg 0
  have hg1 : g.symm (Finsupp.single (1:Fin 5) 1) = Normalized.basis .sphere 16 140 1 := hg 1
  have hg2 : g.symm (Finsupp.single (2:Fin 5) 1) = Normalized.basis .sphere 16 140 2 := hg 2
  have hg3 : g.symm (Finsupp.single (3:Fin 5) 1) = Normalized.basis .sphere 16 140 3 := hg 3
  have hg4 : g.symm (Finsupp.single (4:Fin 5) 1) = Normalized.basis .sphere 16 140 4 := hg 4
  have df0 : E.d 2 (14,139) (Normalized.basis .sphere 14 139 0)=Normalized.basis .sphere 16 140 2 := h343.eq_on_page_two.2
  have df1 : E.d 2 (14,139) (Normalized.basis .sphere 14 139 1)=0 := by
    obtain ⟨x,hx⟩ := h342
    exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<1000)
      (NuError.middle_rep2 (by decide) hx) ⟨x,hx⟩
  have df2 : E.d 2 (14,139) (Normalized.basis .sphere 14 139 2)=0 :=
    IsPageBoundary.d_eq_zero (E:=E) (r:=2) (p:=(12,138)) ⟨_,h314.eq_on_page_two.2⟩
  have incoming (x : E.Page 2 (14,139)) : g (E.d 2 (14,139) x) 1=0 := by
    have all (a : Fin 3 →₀ F2) : g (E.d 2 (14,139) (f.symm a)) 1=0 := by
      induction a using Finsupp.induction with
      | zero => simp
      | @single_add i c a hi hc ih =>
        rw [map_add,map_add,map_add,Finsupp.add_apply,ih,add_zero]
        fin_cases c
        · simp
        · change g (E.d 2 (14,139) (f.symm (Finsupp.single i 1))) 1=0
          rw [hf]
          fin_cases i
          all_goals dsimp only
          all_goals simp only [df0,df1,df2,map_zero,Finsupp.zero_apply,←hg2,LinearEquiv.apply_symm_apply]
          all_goals norm_num [Finsupp.single_apply,Fin.ext_iff]
    simpa only [LinearEquiv.symm_apply_apply] using all (f x)
  obtain ⟨_,b1,t,hb1,ht,db1⟩ := h329
  have db1' : E.d 3 (13,138) b1=t := db1
  have tn : t≠0 := by
    apply represents_next_nonzero_of_not_incoming (E:=E) (r:=2) (q:=(14,139))
      (by decide) (by decide) ht (NuError.middle_rep2 (by decide) ht)
    intro u hu
    have hh := incoming u
    rw [hu,←hg1,LinearEquiv.apply_symm_apply] at hh
    norm_num [Finsupp.single_apply] at hh
  intro hc
  obtain ⟨b4,hb4⟩ := (nCycle_iff_reaches 4 (by decide) (13,138)
    (Normalized.basis .sphere 13 138 1)).mp ⟨by decide,hc⟩
  exact tn (db1'.symm.trans (represents_d_zero_of_later
    (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) hb1 ⟨b4,hb4⟩))

private theorem af13_cycles_boundary  :
    nCycles 3 (13,138) ≤ nBoundaries 4 (13,138) := by
  intro x hx
  rcases (nu9_af13_cosets).2 x with h|h
  · exact h
  · exfalso
    apply af13_basis_not_cycle
    have hh := (nBoundaries_le_cycles (13,138) 4 3) h
    simpa only [sub_sub_cancel] using (nCycles 3 (13,138)).sub_mem hx hh

private theorem af15_incoming2_zero  :
    (Normalized.sphere).d 2 (13,138)=0 := by
  let E:=Normalized.sphere
  ext x
  have hc:x∈nCycles 2 (13,138) := by
    obtain ⟨hb,hx⟩:=nu9_af13_cosets
    rcases hx x with hx|hx
    · exact nBoundaries_le_cycles (13,138) 4 2 hx
    · have hsum := (nCycles 2 (13,138)).add_mem
        (nBoundaries_le_cycles (13,138) 4 2 hx) hb
      simpa only [sub_add_cancel] using hsum
  obtain ⟨a,ha⟩:ReachesPage E 3 (13,138) x :=
    (nCycle_iff_reaches 3 (by decide) (13,138) x).mp ⟨by decide,hc⟩
  exact represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide)
    (NuError.middle_rep2 (by decide) ha) ⟨a,ha⟩

private theorem af15_incoming3_zero  :
    (Normalized.sphere).d 3 (12,137)=0 := by
  let E:=Normalized.sphere
  ext a
  obtain ⟨x,hx⟩ := PageThree.exists_representative (12,137) a
  have hd:E.d 2 (12,137) x=0:=represents_d_zero_of_later
    (by change (2:ℤ)≤2; omega) (by decide) (NuError.middle_rep2 (by decide) hx) ⟨a,hx⟩
  exact represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide) hx
    ⟨0,nu9_af12_kernel x hd⟩

private theorem af11_d4_target_nonzero
    (a:(Normalized.sphere).Page 4 (15,139))
    (ha:RepresentsOnPage (Normalized.sphere) 4 (15,139)
      (Normalized.basis .sphere 15 139 0) a):a≠0 := by
  let E:=Normalized.sphere
  obtain ⟨e,he⟩:=Normalized.basis_correct ⟨.sphere,15,139,["448,1","3,2,287,1","0,1,440,1","0,1,439,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 223 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (15,139)≃ₗ[ℤ](Fin 4→₀F2) at e
  change ∀i:Fin 4,e.symm (Finsupp.single i 1)=Normalized.basis .sphere 15 139 i.val at he
  have hn:Normalized.basis .sphere 15 139 0≠0 := by
    erw [←he 0]
    intro hz
    have hh:=congrArg (fun x=>e x 0) hz
    norm_num [Finsupp.single_apply] at hh
  obtain ⟨a3,ha3⟩:=represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ha
  have hn3:a3≠0:=represents_next_nonzero_of_incoming_zero
    (E:=E) (r:=2) (p:=(15,139)) (by change (2:ℤ)≤2; omega) (by decide)
    (af15_incoming2_zero) ha3 (NuError.middle_rep2 (by decide) ha3) hn
  exact represents_next_nonzero_of_incoming_zero
    (E:=E) (r:=3) (p:=(15,139)) (by change (2:ℤ)≤3; omega) (by decide)
    (af15_incoming3_zero) ha ha3 hn3

private theorem y_finite_cosets
    (x:Normalized.Page .sphere 11 136) (hx:x∈nCycles 5 (11,136)) :
    x∈nBoundaries 5 (11,136) ∨
    x-Normalized.basis .sphere 11 136 3∈nBoundaries 5 (11,136) := by
  let E:=Normalized.sphere
  have h279 : HasDifferential E 3 (8,134) (11,136)
      (Normalized.basis .sphere 8 134 3) (Normalized.basis .sphere 11 136 1) := by
    have hrow := Normalized.result ⟨.sphere,.equation,3,8,134,[3],11,136,[1],"S0_AdamsE2_ss",2850⟩ (by
      unfold KIP126.Computation.Table.Raw.claims
      iterate 279 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
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
      unfold KIP126.Computation.Table.Raw.claims
      iterate 280 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
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
      unfold KIP126.Computation.Table.Raw.claims
      iterate 282 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
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
      unfold KIP126.Computation.Table.Raw.claims
      iterate 283 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
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
      unfold KIP126.Computation.Table.Raw.claims
      iterate 281 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [Normalized.Statement] at hrow
    obtain ⟨x,hx,hd⟩ := hrow
    change ReachesPage E 5 (11,136) x at hd
    have vx : KIP126.Computation.Table.Raw.coordinatesValid KIP126.Computation.Table.Raw.degrees .sphere 11 136 [3] = true := rfl
    simp only [Normalized.decode,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hd
    simpa only [add_assoc] using hd
  obtain ⟨e,he⟩ := Normalized.basis_correct ⟨.sphere,11,136,["69,1,89,1", "1,1,389,1", "1,1,388,1", "0,2,391,1", "0,3,375,1"]⟩ (by
    unfold KIP126.Computation.Table.Raw.degrees
    iterate 192 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E.Page 2 (11,136) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = Normalized.basis .sphere 11 136 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1)=Normalized.basis .sphere 11 136 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1)=Normalized.basis .sphere 11 136 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1)=Normalized.basis .sphere 11 136 2 := he 2
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1)=Normalized.basis .sphere 11 136 4 := he 4
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1)=Normalized.basis .sphere 11 136 3 := he 3

  obtain ⟨_,a0,b0,ha0,hb0,hd0⟩:=h282
  obtain ⟨y5,hy5⟩:=h281
  obtain ⟨y4,hy4⟩:=represents_before (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤5) hy5
  have hbne:b0≠0:=af11_d4_target_nonzero b0 hb0
  have hy_d4:E.d 4 (11,136) y4=0:=represents_d_zero_of_later
    (by change (2:ℤ)≤4; omega) (by decide) hy4 ⟨y5,hy5⟩
  have h1:RepresentsOnPage E 4 (11,136) (Normalized.basis .sphere 11 136 1) 0:=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h279
  have h2:RepresentsOnPage E 4 (11,136) (Normalized.basis .sphere 11 136 2) 0:=
    differential_target_later_zero (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) h280
  have d0:E.d 2 (11,136) (Normalized.basis .sphere 11 136 0)=0:=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) (NuError.middle_rep2 (by decide) ha0) ⟨a0,ha0⟩
  have d1:E.d 2 (11,136) (Normalized.basis .sphere 11 136 1)=0:=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) (NuError.middle_rep2 (by decide) h1) ⟨0,h1⟩
  have d2:E.d 2 (11,136) (Normalized.basis .sphere 11 136 2)=0:=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) (NuError.middle_rep2 (by decide) h2) ⟨0,h2⟩
  have d3:E.d 2 (11,136) (Normalized.basis .sphere 11 136 3)=0:=
    represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide) (NuError.middle_rep2 (by decide) hy4) ⟨y4,hy4⟩
  have d4:E.d 2 (11,136) (Normalized.basis .sphere 11 136 4)=Normalized.basis .sphere 13 137 3:=h283.eq_on_page_two.2
  have hd4ne:Normalized.basis .sphere 13 137 3≠0 := by
    obtain ⟨f,hf⟩:=Normalized.basis_correct ⟨.sphere,13,137,["76,1,82,1","9,1,251,1","7,1,275,1","0,5,367,1"]⟩ (by
      unfold KIP126.Computation.Table.Raw.degrees
      iterate 208 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (13,137)≃ₗ[ℤ](Fin 4→₀F2) at f
    change ∀i:Fin 4,f.symm (Finsupp.single i 1)=Normalized.basis .sphere 13 137 i.val at hf
    erw [←hf 3]
    intro hz
    have hh:=congrArg (fun x=>f x 3) hz
    norm_num [Finsupp.single_apply] at hh
  obtain ⟨a6,ha6⟩:ReachesPage E 6 (11,136) x:=
    (nCycle_iff_reaches 6 (by decide) (11,136) x).mp ⟨by decide,hx⟩
  have dx:E.d 2 (11,136) x=0:=represents_d_zero_of_later
    (by change (2:ℤ)≤2; omega) (by decide) (NuError.middle_rep2 (by decide) ha6) ⟨a6,ha6⟩
  let c:Fin 5→F2:=e x
  have hcoef:=congrArg e.symm (NuError.middle_expand (e x))
  simp only [LinearEquiv.symm_apply_apply,map_sum,map_add,Fin.sum_univ_succ,apply_ite,map_zero] at hcoef
  change x=(if c 0=0 then 0 else e.symm (Finsupp.single 0 1)) + ((if c 1=0 then 0 else e.symm (Finsupp.single 1 1)) + ((if c 2=0 then 0 else e.symm (Finsupp.single 2 1)) + ((if c 3=0 then 0 else e.symm (Finsupp.single 3 1)) + ((if c 4=0 then 0 else e.symm (Finsupp.single 4 1)) + 0)))) at hcoef
  simp only [he0,he1,he2,he3,he4,add_zero] at hcoef
  have c4:c 4=0 := by
    have hd:=congrArg (E.d 2 (11,136)) hcoef
    rw [dx] at hd
    by_contra h4
    simp only [h4,ite_false,map_add,apply_ite,map_zero,d0,d1,d2,d3,d4,ite_self,zero_add] at hd
    exact hd4ne hd.symm
  simp only [c4,ite_true,add_zero] at hcoef
  have hrep:RepresentsOnPage E 4 (11,136) x
      ((if c 0=0 then 0 else a0)+(if c 3=0 then 0 else y4)) := by
    rw [hcoef]
    simpa only [ite_self,zero_add] using
      NuError.middle_add (NuError.middle_if (c 0) ha0)
        (NuError.middle_add (NuError.middle_if (c 1) h1) (NuError.middle_add (NuError.middle_if (c 2) h2) (NuError.middle_if (c 3) hy4)))
  have hd:E.d 4 (11,136) ((if c 0=0 then 0 else a0)+(if c 3=0 then 0 else y4))=0:=
    represents_d_zero_of_later (by change (2:ℤ)≤4; omega) (by decide) hrep ⟨a6,ha6⟩
  have c0:c 0=0 := by
    by_contra h0
    simp only [h0,ite_false,map_add,apply_ite,hy_d4,ite_self,add_zero] at hd
    exact hbne (hd0.symm.trans hd)
  simp only [c0,ite_true,zero_add] at hrep
  by_cases h3:c 3=0
  · left
    simp only [h3,ite_true] at hrep
    exact nBoundaries_monotone (11,136) (by decide : (3:ℤ)≤5)
      (boundary_of_zero_representative (r:=4) (p:=(11,136)) hrep)
  · right
    simp only [h3,ite_false] at hrep
    have hsub:RepresentsOnPage E 4 (11,136) (x-Normalized.basis .sphere 11 136 3) 0 := by
      obtain ⟨hr,z,hz,hza⟩:=hrep
      obtain ⟨_,w,hw,hwa⟩:=hy4
      refine ⟨hr,z-w,by rw [map_sub,hz,hw],?_⟩
      rw [map_sub,hza,hwa,sub_self]
    exact nBoundaries_monotone (11,136) (by decide : (3:ℤ)≤5)
      (boundary_of_zero_representative (r:=4) (p:=(11,136)) hsub)



end
end KIP126.Main.SectionSeven.Internal.WeakYFinite
