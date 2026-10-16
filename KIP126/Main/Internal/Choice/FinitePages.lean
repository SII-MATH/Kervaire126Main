module
public import KIP126.Main.Conditions
public import KIP126.Computation.Table
import all KIP126.Main.Internal.PageCalculus
import all KIP126.Main.Internal.Choice.PageFrames

/-! Original finite computations in Selected/ChoiceInvariance:28–109,509–628,
bbac1fc05843 (MIT), now consuming the fixed upstream table directly. -/
@[expose] section
namespace KIP126.Main.Internal.Choice
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Computation.Table KIP126.Main.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
private theorem raw_h365_0 : HasDifferential model.classical.sphere 2 (1,64) (3,65) (KIP126.Computation.Table.basis .sphere 1 64 0) (KIP126.Computation.Table.basis .sphere 3 65 0) := by
  classical
  have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 1, 64, [0], 3, 65, [0], "S0_AdamsE2_ss", 401⟩ (by
    exact List.mem_of_getElem? (i := 142) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential model.classical.sphere 2 (1,64) (3,65) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 1 64 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 3 65 [0] = true := rfl
  simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem raw_h466_1 : HasDifferential model.classical.sphere 2 (2,65) (4,66) (KIP126.Computation.Table.basis .sphere 2 65 0) (KIP126.Computation.Table.basis .sphere 4 66 0) := by
  classical
  have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 2, 65, [0], 4, 66, [0], "S0_AdamsE2_ss", 417⟩ (by
    exact List.mem_of_getElem? (i := 145) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential model.classical.sphere 2 (2,65) (4,66) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 2 65 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 4 66 [0] = true := rfl
  simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem raw_h567_2 : HasDifferential model.classical.sphere 2 (3,66) (5,67) (KIP126.Computation.Table.basis .sphere 3 66 1) (KIP126.Computation.Table.basis .sphere 5 67 2) := by
  classical
  have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 3, 66, [1], 5, 67, [2], "S0_AdamsE2_ss", 437⟩ (by
    exact List.mem_of_getElem? (i := 150) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential model.classical.sphere 2 (3,66) (5,67) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 3 66 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 5 67 [2] = true := rfl
  simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem raw_h3_3 : HasDifferential model.classical.sphere 3 (5,67) (8,69) (KIP126.Computation.Table.basis .sphere 5 67 1) (KIP126.Computation.Table.basis .sphere 8 69 0) := by
  classical
  have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 3, 5, 67, [1], 8, 69, [0], "S0_AdamsE2_ss", 453⟩ (by
    exact List.mem_of_getElem? (i := 160) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential model.classical.sphere 3 (5,67) (8,69) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 5 67 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 8 69 [0] = true := rfl
  simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem raw_h668_4 : HasDifferential model.classical.sphere 2 (4,67) (6,68) (KIP126.Computation.Table.basis .sphere 4 67 0) (KIP126.Computation.Table.basis .sphere 6 68 1) := by
  classical
  have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 4, 67, [0], 6, 68, [1], "S0_AdamsE2_ss", 455⟩ (by
    exact List.mem_of_getElem? (i := 155) (by rfl))
  dsimp only [Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential model.classical.sphere 2 (4,67) (6,68) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 4 67 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 6 68 [1] = true := rfl
  simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  exact hd

private theorem raw_relations :
    HasDifferential model.classical.sphere 2 (1,64) (3,65) (KIP126.Computation.Table.basis .sphere 1 64 0) (KIP126.Computation.Table.basis .sphere 3 65 0) ∧
    HasDifferential model.classical.sphere 2 (2,65) (4,66) (KIP126.Computation.Table.basis .sphere 2 65 0) (KIP126.Computation.Table.basis .sphere 4 66 0) ∧
    HasDifferential model.classical.sphere 2 (3,66) (5,67) (KIP126.Computation.Table.basis .sphere 3 66 1) (KIP126.Computation.Table.basis .sphere 5 67 2) ∧
    HasDifferential model.classical.sphere 3 (5,67) (8,69) (KIP126.Computation.Table.basis .sphere 5 67 1) (KIP126.Computation.Table.basis .sphere 8 69 0) ∧
    HasDifferential model.classical.sphere 2 (5,67) (7,68) (KIP126.Computation.Table.basis .sphere 5 67 0) (KIP126.Computation.Table.basis .sphere 7 68 0+KIP126.Computation.Table.basis .sphere 7 68 1) ∧
    HasDifferential model.classical.sphere 2 (4,67) (6,68) (KIP126.Computation.Table.basis .sphere 4 67 0) (KIP126.Computation.Table.basis .sphere 6 68 1) ∧
    ReachesPage model.classical.sphere 1000 (6,68) (KIP126.Computation.Table.basis .sphere 6 68 0) := by
  classical
  classical
  let E := model.classical.sphere
  have h365 : HasDifferential E 2 (1,64) (3,65) (KIP126.Computation.Table.basis .sphere 1 64 0) (KIP126.Computation.Table.basis .sphere 3 65 0) := raw_h365_0
  have h466 : HasDifferential E 2 (2,65) (4,66) (KIP126.Computation.Table.basis .sphere 2 65 0) (KIP126.Computation.Table.basis .sphere 4 66 0) := raw_h466_1
  have h567 : HasDifferential E 2 (3,66) (5,67) (KIP126.Computation.Table.basis .sphere 3 66 1) (KIP126.Computation.Table.basis .sphere 5 67 2) := raw_h567_2
  have h3 : HasDifferential E 3 (5,67) (8,69) (KIP126.Computation.Table.basis .sphere 5 67 1) (KIP126.Computation.Table.basis .sphere 8 69 0) := raw_h3_3
  have h2out : HasDifferential E 2 (5,67) (7,68) (KIP126.Computation.Table.basis .sphere 5 67 0) (KIP126.Computation.Table.basis .sphere 7 68 0+KIP126.Computation.Table.basis .sphere 7 68 1) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .equation, 2, 5, 67, [0], 7, 68, [0, 1], "S0_AdamsE2_ss", 454⟩ (by
      exact List.mem_of_getElem? (i := 161) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,y,hy,hd⟩ := hrow
    change HasDifferential E 2 (5,67) (7,68) x y at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 5 67 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 7 68 [0, 1] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have h668 : HasDifferential E 2 (4,67) (6,68) (KIP126.Computation.Table.basis .sphere 4 67 0) (KIP126.Computation.Table.basis .sphere 6 68 1) := raw_h668_4
  have hcycle : ReachesPage E 1000 (6,68) (KIP126.Computation.Table.basis .sphere 6 68 0) := by
    have hrow := KIP126.Computation.Table.result ⟨.sphere, .reaches, 1000, 6, 68, [0], 6, 68, [], "S0_AdamsE2_ss", 470⟩ (by
      exact List.mem_of_getElem? (i := 167) (by rfl))
    dsimp only [Statement] at hrow
    obtain ⟨x,hx,hd⟩ := hrow
    change ReachesPage E 1000 (6,68) x at hd
    have vx : Raw.coordinatesValid Raw.degrees .sphere 6 68 [0] = true := rfl
    simp only [KIP126.Computation.Table.decode,vx,if_true,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at hd
    exact hd
  exact ⟨h365,h466,h567,h3,h2out,h668,hcycle⟩


private theorem theta_choice_finite_pages :
    Subsingleton (model.classical.sphere.Page 3 (3,65)) ∧
    Subsingleton (model.classical.sphere.Page 3 (4,66)) ∧
    Subsingleton (model.classical.sphere.Page 4 (5,67)) := by
  classical
  classical
  let E := model.classical.sphere
  obtain ⟨h365,h466,h567,h3,h2out,h668,hcycle⟩ := raw_relations
  obtain ⟨e3,he3⟩ := KIP126.Computation.Table.basis_correct ⟨.sphere, 3, 65, ["0,1,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 102) (by rfl))
  change E.Page 2 (3,65) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e3
  change ∀i:Fin 1, e3.symm (Finsupp.single i 1)=KIP126.Computation.Table.basis .sphere 3 65 i.val at he3
  obtain ⟨e4,he4⟩ := KIP126.Computation.Table.basis_correct ⟨.sphere, 4, 66, ["0,2,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 113) (by rfl))
  change E.Page 2 (4,66) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e4
  change ∀i:Fin 1, e4.symm (Finsupp.single i 1)=KIP126.Computation.Table.basis .sphere 4 66 i.val at he4
  obtain ⟨e5,he5⟩ := KIP126.Computation.Table.basis_correct ⟨.sphere, 5, 67, ["76,1", "1,1,70,1", "0,3,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 121) (by rfl))
  change E.Page 2 (5,67) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e5
  change ∀i:Fin 3, e5.symm (Finsupp.single i 1)=KIP126.Computation.Table.basis .sphere 5 67 i.val at he5
  obtain ⟨e6,he6⟩ := KIP126.Computation.Table.basis_correct ⟨.sphere, 6, 68, ["18,1,24,1", "0,4,18,2"]⟩ (by
    exact List.mem_of_getElem? (i := 131) (by rfl))
  change E.Page 2 (6,68) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e6
  change ∀i:Fin 2, e6.symm (Finsupp.single i 1)=KIP126.Computation.Table.basis .sphere 6 68 i.val at he6
  obtain ⟨e7,he7⟩ := KIP126.Computation.Table.basis_correct ⟨.sphere, 7, 68, ["0,1,75,1", "0,1,74,1"]⟩ (by
    exact List.mem_of_getElem? (i := 141) (by rfl))
  change E.Page 2 (7,68) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e7
  change ∀i:Fin 2, e7.symm (Finsupp.single i 1)=KIP126.Computation.Table.basis .sphere 7 68 i.val at he7
  obtain ⟨e8,he8⟩ := KIP126.Computation.Table.basis_correct ⟨.sphere, 8, 69, ["0,2,74,1"]⟩ (by
    exact List.mem_of_getElem? (i := 154) (by rfl))
  change E.Page 2 (8,69) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e8
  change ∀i:Fin 1, e8.symm (Finsupp.single i 1)=KIP126.Computation.Table.basis .sphere 8 69 i.val at he8
  have he60 : e6.symm (Finsupp.single 0 1)=KIP126.Computation.Table.basis .sphere 6 68 0 := he6 0
  have he61 : e6.symm (Finsupp.single 1 1)=KIP126.Computation.Table.basis .sphere 6 68 1 := he6 1
  have he70 : e7.symm (Finsupp.single 0 1)=KIP126.Computation.Table.basis .sphere 7 68 0 := he7 0
  have he71 : e7.symm (Finsupp.single 1 1)=KIP126.Computation.Table.basis .sphere 7 68 1 := he7 1
  have he80 : e8.symm (Finsupp.single 0 1)=KIP126.Computation.Table.basis .sphere 8 69 0 := he8 0
  have dz (r:ℤ) (hr:2<r) (p:ℤ×ℤ) (x:E.Page 2 p)
      (hx:ReachesPage E r p x) : E.d 2 p x=0 := by
    obtain ⟨x2,hx2⟩ := reaches_before (by decide : (2:ℤ)≤2) (by omega : (2:ℤ)≤r) hx
    have hh := represents_d_zero_of_later (by change (model.classical.obj _).r₀ ≤ 2; rw [model.classical.firstPage]) hr hx2 hx
    simpa only [hx2.eq_on_page_two] using hh
  have hz365 := differential_target_later_zero (by change (model.classical.obj _).r₀ ≤ 2; rw [model.classical.firstPage])
    (by decide : (2:ℤ)<3) h365
  have hz466 := differential_target_later_zero (by change (model.classical.obj _).r₀ ≤ 2; rw [model.classical.firstPage])
    (by decide : (2:ℤ)<3) h466
  have hz567 := differential_target_later_zero (by change (model.classical.obj _).r₀ ≤ 2; rw [model.classical.firstPage])
    (by decide : (2:ℤ)<3) h567
  have hz668 := differential_target_later_zero (by change (model.classical.obj _).r₀ ≤ 2; rw [model.classical.firstPage])
    (by decide : (2:ℤ)<3) h668
  refine ⟨choice_single_basis_zero_page (by decide : (2:ℤ)≤3) e3 _ (he3 0) hz365,
    choice_single_basis_zero_page (by decide : (2:ℤ)≤3) e4 _ (he4 0) hz466,?_⟩
  have hd60 := dz 1000 (by decide) (6,68) _ hcycle
  have hd61 := dz 3 (by decide) (6,68) _ ⟨0,hz668⟩
  exact late_page_generic E (by dsimp only [E]; rw [model.classical.firstPage])
    (model.classical.differentialDegree _ 2)
    (fun i=>KIP126.Computation.Table.basis .sphere 5 67 i.val)
    (fun i=>KIP126.Computation.Table.basis .sphere 6 68 i.val)
    (fun i=>KIP126.Computation.Table.basis .sphere 7 68 i.val)
    (fun i=>KIP126.Computation.Table.basis .sphere 8 69 i.val)
    e5 he5 e6 he6 e7 he7 e8 he8 h3 h2out hz567 hd60 hd61



end
end KIP126.Main.Internal.Choice
end
