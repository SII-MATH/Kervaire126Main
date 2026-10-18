module
public import KIP126.E2Computation.Table.Relations
import all KIP126.Main.SectionSeven.NuTargetE2Calculus
import all KIP126.Main.SectionSeven.NuTargetLinear
public import KIP126.ProofTools.Operations
/-! The finite linear calculation in NuTargetHelpers.lean:1766–1955,
bbac1fc05843 (MIT). Only the original primitive polynomial relations are
consumed; the universal AF13 conclusion is proved here. -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory KIP126.AdamsSynthetic.Standard
open KIP126.Computation.Standard KIP126.Computation.Table
noncomputable section

theorem nu_target_h0_af13_image_boundary_two :
    ∀ a : model.classical.sphere.Page 2 (13,138),
      model.sphereAlgebra.product (1,1) (13,138) h0 a ∈
        KIP126.Literature.boundaries model .sphere 2 (14,139) := by
  classical
  have b0 := basis_value ⟨.mul (.generator 24 5 36) (.named .x_94_8),0⟩ (by decide)
  have b1 := basis_value ⟨.mul (.generator 3 1 8) (.generator 335 12 130),1⟩ (by decide)
  have b2 := basis_value ⟨.mul (.named .h0) (.generator 425 12 137),2⟩ (by decide)
  have b3 := basis_value ⟨.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_125_9_2),3⟩ (by decide)
  have b4 := basis_value ⟨.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_125_8),4⟩ (by decide)
  have bt := basis_value ⟨.mul (.mul (.named .h0) (.named .h0)) (.generator 425 12 137),2⟩ (by decide)
  have rel0 := h0_obstruction_rel0
  have rel1 := h0_obstruction_rel1
  have rel2 := h0_obstruction_rel2
  have rel3 := h0_obstruction_rel3
  simp only [Expression.value,Expression.degree,atom_h0] at b0 b1 b2 b3 b4 bt rel0 rel1 rel2 rel3
  have hd : KIP126.Core.SpectralSequence.HasDifferential model.classical.sphere 2 (12,138) (14,139)
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
  let B := KIP126.Literature.boundaries model .sphere 2 (14,139)
  have hbt : basis .sphere 14 139 2 ∈ B :=
    KIP126.ProofTools.Internal.Mahowald.represents_zero_mem_boundary model .sphere 3 (14,139) _
      (KIP126.Core.SpectralSequence.FinitePageCalculus.differential_target_later_zero
        (by rw [model.classical.firstPage]) (by decide) hd)
  have hb (i : Fin 5) : product (r := (14,139)) h0 (basis .sphere 13 138 i.val) ∈ B := by
    fin_cases i
    · change product h0 (basis .sphere 13 138 0) ∈ B
      rw [b0]
      have ha := product_assoc_at h0 (generatorImage 24 5 36) (atom .x_94_8)
        (pq := (6,37)) (qr := (13,138)) (o := (14,139))
        (by decide) (by decide) (by decide) (by decide)
      rw [←ha,rel0]
      simpa only [product,map_zero,LinearMap.zero_apply] using B.zero_mem
    · change product h0 (basis .sphere 13 138 1) ∈ B
      rw [b1]
      have ha := product_assoc_at h0 (generatorImage 3 1 8) (generatorImage 335 12 130)
        (pq := (2,9)) (qr := (13,138)) (o := (14,139))
        (by decide) (by decide) (by decide) (by decide)
      rw [←ha,rel1,←bt]
      exact hbt
    · change product h0 (basis .sphere 13 138 2) ∈ B
      rw [b2]
      have ha := product_assoc_at h0 h0 (generatorImage 425 12 137)
        (pq := (2,2)) (qr := (13,138)) (o := (14,139))
        (by decide) (by decide) (by decide) (by decide)
      rw [←ha,←bt]
      exact hbt
    · change product h0 (basis .sphere 13 138 3) ∈ B
      rw [b3]
      let a4 := product (r := (4,4)) (product (r := (3,3)) (product (r := (2,2)) h0 h0) h0) h0
      change product h0 (product (r := (13,138)) a4 (atom .x_125_9_2)) ∈ B
      have ha := product_assoc_at h0 a4 (atom .x_125_9_2)
        (pq := (5,5)) (qr := (13,138)) (o := (14,139))
        (by decide) (by decide) (by decide) (by decide)
      have hc := KIP126.Computation.Table.product_comm 1 1 4 4 (by decide) h0 a4
      rw [←ha,hc]
      change product (r := (14,139)) (product (r := (5,5)) a4 h0) (atom .x_125_9_2) ∈ B
      rw [rel2]
      exact B.zero_mem
    · change product h0 (basis .sphere 13 138 4) ∈ B
      rw [b4]
      let a5 := product (r := (5,5)) (product (r := (4,4)) (product (r := (3,3)) (product (r := (2,2)) h0 h0) h0) h0) h0
      change product h0 (product (r := (13,138)) a5 (atom .x_125_8)) ∈ B
      have ha := product_assoc_at h0 a5 (atom .x_125_8)
        (pq := (6,6)) (qr := (13,138)) (o := (14,139))
        (by decide) (by decide) (by decide) (by decide)
      have hc := KIP126.Computation.Table.product_comm 1 1 5 5 (by decide) h0 a5
      rw [←ha,hc]
      change product (r := (14,139)) (product (r := (6,6)) a5 h0) (atom .x_125_8) ∈ B
      rw [rel3]
      exact B.zero_mem
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,13,138,["24,1,190,1","3,1,335,1","0,1,425,1","0,4,391,1","0,5,375,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 209) rfl)
  change model.classical.sphere.Page 2 (13,138) ≃ₗ[ℤ] (Fin 5 →₀ ZMod 2) at e
  change ∀i : Fin 5, e.symm (Finsupp.single i 1) = basis .sphere 13 138 i.val at he
  intro x
  have hx := congrArg e.symm (binary_expansion (e x))
  simp only [LinearEquiv.symm_apply_apply,map_sum,apply_ite,map_zero] at hx
  rw [hx,map_sum]
  apply Submodule.sum_mem
  intro i _
  by_cases h : (e x) i=0
  · simp only [h,if_true,map_zero]
    exact B.zero_mem
  · simp only [h,if_false]
    rw [he]
    exact hb i

end
end KIP126.Main.SectionSeven.Internal
