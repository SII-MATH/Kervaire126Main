module

public import KIP126.AdamsComputation.Table.Values
public import KIP126.ProofTools.Operations
import all KIP126.Main.SectionSeven.NuTargetLinear

/-! The two P/Q coset computations from NuTargetHelpers.lean:151–275,
bbac1fc05843 (MIT), using the retained finite archive rows and coordinates. -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FinitePageCalculus KIP126.Literature
open KIP126.AdamsSynthetic.Standard KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.Computation.Table
noncomputable section

private theorem p_cosets (x : model.classical.sphere.Page 2 (11,133)) :
    x ∈ boundaries model .sphere 3 (11,133) ∨
    x-KIP126.Computation.Standard.P ∈ boundaries model .sphere 3 (11,133) := by
  have hd : HasDifferential model.classical.sphere 3 (8,131) (11,133)
      (basis .sphere 8 131 0) (basis .sphere 11 133 0 + basis .sphere 11 133 1) := by
    have h := result ⟨.sphere,.equation,3,8,131,[0],11,133,[0,1],"S0_AdamsE2_ss",2621⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 267) rfl)
    dsimp only [Statement] at h
    obtain ⟨x,hx,y,hy,hd⟩ := h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 131 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 11 133 [0,1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,11,133,["371,1","69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 189) rfl)
  change model.classical.sphere.Page 2 (11,133) ≃ₗ[ℤ] (Fin 2 →₀ ZMod 2) at e
  change ∀ i : Fin 2, e.symm (Finsupp.single i 1) = basis .sphere 11 133 i.val at he
  have hb : basis .sphere 11 133 0 + basis .sphere 11 133 1 ∈ boundaries model .sphere 3 (11,133) :=
    represents_zero_mem_boundary model .sphere 4 (11,133) _
      (differential_target_later_zero (by rw [model.classical.firstPage] <;> omega) (by decide) hd)
  have hb' : e.symm (Finsupp.single 0 1) + e.symm (Finsupp.single 1 1) ∈ boundaries model .sphere 3 (11,133) := by
    rw [he 0,he 1]
    exact hb
  have heP : e.symm (Finsupp.single (1:Fin 2) 1) = KIP126.Computation.Standard.P :=
    (he 1).trans basis_P
  simpa only [heP] using two_coordinate_cosets e _ hb' x

private theorem q_cosets (x : model.classical.sphere.Page 2 (12,134)) :
    x ∈ boundaries model .sphere 3 (12,134) ∨
    x-KIP126.Computation.Standard.Q ∈ boundaries model .sphere 3 (12,134) := by
  have hd2 : HasDifferential model.classical.sphere 2 (10,133) (12,134)
      (basis .sphere 10 133 0) (basis .sphere 12 134 2) := by
    have h := result ⟨.sphere,.equation,2,10,133,[0],12,134,[2],"S0_AdamsE2_ss",2682⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 294) rfl)
    dsimp only [Statement] at h
    obtain ⟨x,hx,y,hy,hd⟩ := h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  have hd3 : HasDifferential model.classical.sphere 3 (9,132) (12,134)
      (basis .sphere 9 132 0) (basis .sphere 12 134 1) := by
    have h := result ⟨.sphere,.equation,3,9,132,[0],12,134,[1],"S0_AdamsE2_ss",2683⟩ (by
      exact List.mem_of_getElem? (l := Raw.claims) (i := 295) rfl)
    dsimp only [Statement] at h
    obtain ⟨x,hx,y,hy,hd⟩ := h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 132 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [1] = true := rfl
    simp only [decode,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Option.some.injEq] at hx hy
    rw [←hx,←hy] at hd
    exact hd
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,12,134,["18,1,188,1","0,1,371,1","0,1,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 198) rfl)
  change model.classical.sphere.Page 2 (12,134) ≃ₗ[ℤ] (Fin 3 →₀ ZMod 2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = basis .sphere 12 134 i.val at he
  have hb1 : e.symm (Finsupp.single 1 1) ∈ boundaries model .sphere 3 (12,134) := by
    rw [he 1]
    exact represents_zero_mem_boundary model .sphere 4 (12,134) _
      (differential_target_later_zero (by rw [model.classical.firstPage] <;> omega) (by decide) hd3)
  have hb2 : e.symm (Finsupp.single 2 1) ∈ boundaries model .sphere 3 (12,134) := by
    rw [he 2]
    exact represents_zero_mem_boundary model .sphere 4 (12,134) _
      (differential_target_later_zero (by rw [model.classical.firstPage] <;> omega) (by decide) hd2)
  have heQ : e.symm (Finsupp.single (0:Fin 3) 1) = KIP126.Computation.Standard.Q :=
    (he 0).trans basis_Q
  simpa only [heQ] using three_coordinate_cosets e _ hb1 hb2 x

end
end KIP126.Main.SectionSeven.Internal
