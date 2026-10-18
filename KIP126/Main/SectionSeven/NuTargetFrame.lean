module
public import KIP126.E2Computation.Table.Values
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.Selected.InfinityFrames
/-! The target E₆ component computation from NuTargetHelpers.lean:1327–1643,
bbac1fc05843 (MIT). The generic three-coordinate kernel proof is reused
from SpectralSequence.FinitePageCalculus. -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FinitePageCalculus KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.ProofTools.Operations
open KIP126.Computation.Table KIP126.Main.Internal
noncomputable section

theorem target_page_six_frame :
    ∃ a : model.classical.sphere.Page 6 (14,139),
      RepresentsOnPage model.classical.sphere 6 (14,139) KIP126.Computation.Standard.T a ∧
      ∀ y : model.classical.sphere.Page 6 (14,139), y=0 ∨ y=a := by
  have hd2 : HasDifferential model.classical.sphere 2 (12,138) (14,139)
      (basis .sphere 12 138 1) (basis .sphere 14 139 2) := by
    have h := result ⟨.sphere,.equation,2,12,138,[1],14,139,[2],"S0_AdamsE2_ss",3079⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 341) rfl)
    dsimp only [Statement] at h
    obtain ⟨x,hx,y,hy,hd⟩ := h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 12 138 [1] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 14 139 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have hd3 : HasDifferential model.classical.sphere 2 (14,139) (16,140)
      (basis .sphere 14 139 0) (basis .sphere 16 140 2) := by
    have h := result ⟨.sphere,.equation,2,14,139,[0],16,140,[2],"S0_AdamsE2_ss",3081⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 343) rfl)
    dsimp only [Statement] at h
    obtain ⟨x,hx,y,hy,hd⟩ := h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 14 139 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 16 140 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,14,139,["449,1","1,1,7,1,275,1","0,2,425,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 217) rfl)
  change model.classical.sphere.Page 2 (14,139) ≃ₗ[ℤ] (Fin 3 →₀ ZMod 2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = basis .sphere 14 139 i.val at he
  obtain ⟨f,hf⟩ := basis_correct ⟨.sphere,16,140,["9,1,261,1","1,1,438,1","0,1,448,1","0,2,440,1","0,2,439,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 231) rfl)
  change model.classical.sphere.Page 2 (16,140) ≃ₗ[ℤ] (Fin 5 →₀ ZMod 2) at f
  change ∀ i : Fin 5, f.symm (Finsupp.single i 1) = basis .sphere 16 140 i.val at hf
  obtain ⟨a,ha⟩ := KIP126.Main.Internal.Selected.permanent_reaches .sphere 6 (by decide) (14,139)
    KIP126.Computation.Standard.T ((permanent_cycle_iff_mem .sphere (14,139) _).mp KIP126.Computation.Standard.t_permanent_cycle)
  have hz : RepresentsOnPage model.classical.sphere 6 (14,139) (basis .sphere 14 139 2) 0 :=
    differential_target_later_zero (by rw [model.classical.firstPage] <;> omega) (by decide) hd2
  have hn : model.classical.sphere.d 2 (14,139) (basis .sphere 14 139 0) ≠ 0 := by
    intro hn
    have h := hd3.eq_on_page_two.2
    simp only [ModuleCat.comp_apply,hn,map_zero] at h
    have hh := congrArg (fun y => f y 2) h.symm
    have hf2 : f.symm (Finsupp.single (2:Fin 5) 1) = basis .sphere 16 140 2 := hf 2
    rw [←hf2,LinearEquiv.apply_symm_apply,f.map_zero] at hh
    norm_num [Finsupp.single_apply] at hh
  refine ⟨a,ha,?_⟩
  apply choice_frame_of_three_basis (by decide : (2:ℤ)<6)
    (by rw [model.classical.firstPage]) e _ _ _ (he 0) (he 1) (he 2) a
  · have hT : e.symm (Finsupp.single (1:Fin 3) 1) = KIP126.Computation.Standard.T :=
      (he 1).trans basis_T
    exact (congrArg (fun x => RepresentsOnPage model.classical.sphere 6 (14,139) x a)
      ((he 1).symm.trans hT)).mpr ha
  · exact hz
  · exact hn

end
end KIP126.Main.SectionSeven.Internal
