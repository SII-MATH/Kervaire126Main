module
public import KIP126.Computation.Table.Relations
import all KIP126.Main.SectionSeven.NuTargetE2Calculus
import all KIP126.Main.SectionSeven.NuTargetLinear
/-! The finite linear calculation in NuTargetHelpers.lean:1956–2085,
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

theorem nu_target_h2_af13_product_zero :
    ∀ a : model.classical.sphere.Page 2 (13,135),
      model.sphereAlgebra.product (1,4) (13,135) h2 a = 0 := by
  classical
  have b0 := basis_value ⟨.generator 407 13 135,0⟩ (by decide)
  have b1 := basis_value ⟨.mul (.mul (.named .h1) (.named .h1)) (.generator 351 11 131),1⟩ (by decide)
  have b2 := basis_value ⟨.mul (.mul (.named .h0) (.named .h0)) (.mul (.named .h6) (.named .M_mul_d_0)),2⟩ (by decide)
  have rel0 := h2_obstruction_rel0
  have rel1 := h2_obstruction_rel1
  have rel2 := h2_obstruction_rel2
  have rel12 := h1_h2_zero
  simp only [Expression.value,Expression.degree,atom_h0,atom_h1,atom_h2,atom_h6] at b0 b1 b2 rel0 rel1 rel2 rel12
  have hc12 : product (r := (2,6)) h2 h1 = 0 := by
    rw [KIP126.Computation.Table.product_comm 1 4 1 2 (by decide)]
    exact rel12
  have hb0 : product (r := (14,139)) h2 (basis .sphere 13 135 0) = 0 := by
    rw [b0]
    exact rel0
  have hb1 : product (r := (14,139)) h2 (basis .sphere 13 135 1) = 0 := by
    rw [b1]
    have ha := product_assoc_at h2 (product (r := (2,4)) h1 h1)
      (generatorImage 351 11 131) (pq := (3,8)) (qr := (13,135)) (o := (14,139))
      (by decide) (by decide) (by decide) (by decide)
    rw [←ha]
    have ha' := product_assoc_at h2 h1 h1 (pq := (2,6)) (qr := (2,4)) (o := (3,8))
      (by decide) (by decide) (by decide) (by decide)
    rw [←ha',hc12]
    simp only [product,map_zero,LinearMap.zero_apply]
  have hb2 : product (r := (14,139)) h2 (basis .sphere 13 135 2) = 0 := by
    rw [b2]
    let a := product (r := (2,2)) h0 h0
    let b := atom .M_mul_d_0
    let c := generatorImage 89 10 72
    change product h2 (product (r := (13,135)) a (product (r := (11,133)) h6 b)) = 0
    have h0a := KIP126.Computation.Table.product_comm 1 4 2 2 (by decide) h2 a
    have ha := product_assoc_at h2 a (product (r := (11,133)) h6 b)
      (pq := (3,6)) (qr := (13,135)) (o := (14,139))
      (by decide) (by decide) (by decide) (by decide)
    rw [←ha,h0a]
    have ha' := product_assoc_at a h2 (product (r := (11,133)) h6 b)
      (pq := (3,6)) (qr := (12,137)) (o := (14,139))
      (by decide) (by decide) (by decide) (by decide)
    rw [ha']
    have hc := KIP126.Computation.Table.product_comm 1 4 1 64 (by decide) h2 h6
    have hm1 := product_assoc_at h2 h6 b (pq := (2,68)) (qr := (11,133)) (o := (12,137))
      (by decide) (by decide) (by decide) (by decide)
    have hm2 := product_assoc_at h6 h2 b (pq := (2,68)) (qr := (11,73)) (o := (12,137))
      (by decide) (by decide) (by decide) (by decide)
    rw [←hm1,hc,hm2,rel1]
    have hz := product_assoc_at h6 h0 c (pq := (2,65)) (qr := (11,73)) (o := (12,137))
      (by decide) (by decide) (by decide) (by decide)
    have hc0 := KIP126.Computation.Table.product_comm 1 64 1 1 (by decide) h6 h0
    have hz' := product_assoc_at h0 h6 c (pq := (2,65)) (qr := (11,136)) (o := (12,137))
      (by decide) (by decide) (by decide) (by decide)
    rw [←hz,hc0,hz']
    have hA := product_assoc_at a h0 (product (r := (11,136)) h6 c)
      (pq := (3,3)) (qr := (12,137)) (o := (14,139))
      (by decide) (by decide) (by decide) (by decide)
    rw [←hA]
    let a3 := product (r := (3,3)) a h0
    have hB := product_assoc_at a3 h6 c
      (pq := (4,67)) (qr := (11,136)) (o := (14,139))
      (by decide) (by decide) (by decide) (by decide)
    have hC := KIP126.Computation.Table.product_comm 3 3 1 64 (by decide) a3 h6
    have hD := product_assoc_at h6 a3 c
      (pq := (4,67)) (qr := (13,75)) (o := (14,139))
      (by decide) (by decide) (by decide) (by decide)
    rw [←hB,hC,hD]
    change product (r := (14,139)) h6 (product (r := (13,75)) a3 c) = 0
    have hz3 : product (r := (13,75)) a3 c = 0 := rel2
    rw [hz3]
    simp only [product,map_zero]
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,13,135,["407,1","1,2,351,1","0,2,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 206) rfl)
  change model.classical.sphere.Page 2 (13,135) ≃ₗ[ℤ] (Fin 3 →₀ ZMod 2) at e
  change ∀i : Fin 3, e.symm (Finsupp.single i 1) = basis .sphere 13 135 i.val at he
  intro x
  have hx := congrArg e.symm (binary_expansion (e x))
  simp only [LinearEquiv.symm_apply_apply,map_sum,apply_ite,map_zero] at hx
  rw [hx,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : (e x) i=0
  · simp only [h,if_true,map_zero]
  · simp only [h,if_false]
    rw [he]
    fin_cases i
    · exact hb0
    · exact hb1
    · exact hb2

end
end KIP126.Main.SectionSeven.Internal
