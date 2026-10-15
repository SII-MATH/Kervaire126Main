module
public import KIP126.Main.Conditions
public import KIP126.Def.Computation.Table.Values

/-! The h₁U vanishing used in Selected/DetectionData, derived from the
original bounded multiplication relation h₀h₁=0 and actual associativity. -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory KIP126.AdamsSynthetic.Standard KIP126.Computation.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
private theorem h1_u_zero : product (r := (11,136)) h1 U=0 := by
  have h10 : product (r := (2,3)) h1 h0=0 :=
    (KIP126.Computation.Table.product_comm 1 2 1 1 (by decide) h1 h0).trans
      KIP126.Computation.Table.h0_h1_zero
  have h1sq : product (r := (3,4)) h1 h0Square=0 := by
    have ha := model.sphereAlgebra.assoc (1,2) (1,1) (1,1) h1 h0 h0
    have he : product (r := (3,4)) (product (r := (2,3)) h1 h0) h0 =
        product (r := (3,4)) h1 h0Square := eq_of_heq ha
    rw [←he,h10]
    simp only [product,map_zero,LinearMap.zero_apply]
  have ha := model.sphereAlgebra.assoc (1,2) (2,2) (8,132) h1 h0Square (atom .x_124_8)
  have he : product (r := (11,136)) (product (r := (3,4)) h1 h0Square) (atom .x_124_8)=
      product (r := (11,136)) h1 U := eq_of_heq ha
  rw [←he,h1sq]
  simp only [product,map_zero,LinearMap.zero_apply]
end
end KIP126.Main.Internal.Selected
