module
public import KIP126.AdamsComputation.Table.ThetaRelations
import all KIP126.Main.SectionSeven.NuTargetE2Calculus
import all KIP126.Main.SectionSeven.NuTargetLinear

/-! Complete finite-span product calculation, Section7/ThetaMassey:44–161,
bbac1fc05843 (MIT). Primitive archive equations are upstream; the assertion
for every element of the three-dimensional actual group is proved here. -/
@[expose] section
namespace KIP126.Main.Internal.Theta
open CategoryTheory KIP126.AdamsSynthetic.Standard
open KIP126.Computation.Standard KIP126.Computation.Table
open KIP126.Main.SectionSeven.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem h5_square_times_entire_770_zero :
    ∀ b : model.classical.sphere.Page 2 (7,70),
      product (r := (9,134)) h5Square b = 0 := by
  classical
  let six : Expression := .mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0))
    (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)
  have b0 := basis_value ⟨.generator 85 7 70,0⟩ (by decide)
  have b1 := basis_value ⟨.generator 84 7 70,1⟩ (by decide)
  have b2 := basis_value ⟨.mul six (.named .h6),2⟩ (by decide)
  have r0 := theta_h5_generator85_zero
  have r1 := theta_h5_generator84_zero
  have r2 := theta_h5_h6_zero
  simp only [Expression.value,Expression.degree,atom_h5,atom_h6] at b0 b1 r0 r1 r2
  change basis .sphere 7 70 2 = product (r := (7,70)) six.value (atom .h6) at b2
  rw [atom_h6] at b2
  have hb0 : product (r := (8,102)) h5 (basis .sphere 7 70 0)=0 := by rw [b0]; exact r0
  have hb1 : product (r := (8,102)) h5 (basis .sphere 7 70 1)=0 := by rw [b1]; exact r1
  have hb2 : product (r := (8,102)) h5 (basis .sphere 7 70 2)=0 := by
    rw [b2]
    have ha := product_assoc_at h5 six.value h6 (pq := (7,38)) (qr := (7,70)) (o := (8,102))
      (by decide) (by decide) (by decide) (by decide)
    have hc := product_comm 1 32 6 6 (by decide) h5 six.value
    have ha' := product_assoc_at six.value h5 h6 (pq := (7,38)) (qr := (2,96)) (o := (8,102))
      (by decide) (by decide) (by decide) (by decide)
    rw [←ha,hc,ha',r2]
    simp only [product,map_zero]
  obtain ⟨e,he⟩ := basis_correct ⟨.sphere,7,70,["85,1","84,1","0,6,69,1"]⟩ (by
    exact List.mem_of_getElem? (l := Raw.degrees) (i := 143) rfl)
  change model.classical.sphere.Page 2 (7,70) ≃ₗ[ℤ] (Fin 3 →₀ ZMod 2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1)=basis .sphere 7 70 i.val at he
  have h5zero (x : model.classical.sphere.Page 2 (7,70)) : product (r := (8,102)) h5 x=0 := by
    have hx := congrArg e.symm (binary_expansion (e x))
    simp only [LinearEquiv.symm_apply_apply,map_sum,apply_ite,map_zero] at hx
    change model.sphereAlgebra.product (1,32) (7,70) h5 x=0
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
  intro b
  have ha := product_assoc_at h5 h5 b (pq := (2,64)) (qr := (8,102)) (o := (9,134))
    (by decide) (by decide) (by decide) (by decide)
  change product (product (r := (2,64)) h5 h5) b = 0
  rw [ha,h5zero]
  simp only [product,map_zero]
end
end KIP126.Main.Internal.Theta
