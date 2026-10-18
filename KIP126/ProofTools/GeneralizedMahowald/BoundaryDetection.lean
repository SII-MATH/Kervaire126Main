module
import all KIP126.ProofTools.GeneralizedMahowald.BoundaryLambda
import all KIP126.ProofTools.GeneralizedMahowald.PageCalculus
/-! The zero-target branch of the retained Mahowald proof, original 3060–3078 (MIT). -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
private theorem finite_top_boundary_detects_zero (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t : ℤ) (z : Ambient model X (s,t))
    (hz : z ∈ boundaries model X q (s,t)) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t-(q-1:ℕ))
      (finiteTargetLabel model X q s t (q-1) z) 0 := by
  let y : cycles model X ((q:ℤ)-t+(t-(q-1:ℕ))) (s,t) :=
    ⟨z, boundaries_le_cycles model X (s,t) q _ hz⟩
  have he : HasInfinityRepresentative _ 2 _ (finiteTargetLabel model X q s t (q-1) z) 0 := by
    apply (finite_target_label_iff X q hq s t (q-1) (by omega) y 0).mpr
    rw [map_zero]
    symm
    exact quotient_map_class_eq_zero (le_refl _) (le_refl _) y (by
      change z ∈ boundaries model X (1+t-(t-(q-1:ℕ))) (s,t)
      convert hz using 1
      congr 1
      omega)
  refine ⟨0,he,0,?_,?_⟩
  · exact map_zero _
  · simp only [map_zero]
end
end KIP126.ProofTools.Internal.Mahowald
