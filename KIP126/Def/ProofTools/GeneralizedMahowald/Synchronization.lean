module
import all KIP126.Def.ProofTools.GeneralizedLeibniz.CrossingDelta

/-! The differential no-crossing branch removes the actual finite boundary
ambiguity. A higher-source correction has absolute boundary above the
selected target filtration; projection then lies beyond the finite quotient
window and is zero. This statement keeps the source filtration hypothesis
explicit and does not identify independently chosen shifted E₂ labels. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem relative_boundary_equal_of_no_crossing (X : ClassicalObject)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q) (s t : ℤ)
    (hnc : NoCrossingOn model X (i+q) (i+1) (s,t))
    (a a₀ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : FiltrationAtLeast model.syntheticTower (s+1) (a-a₀)) :
    a ≫ ((model.quotients.tower _).triangle hi (show i < i+q by omega)).delta =
      a₀ ≫ ((model.quotients.tower _).triangle hi (show i < i+q by omega)).delta := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let M := model.convergentMap (.quotient i (.nu X)) (.shift (1,-(i:ℤ)) (.nu X))
    (absoluteBoundary A i)
  have hnc' : TowerNoCrossing M (t-s,t) s (i+q) := by
    have H := classical_noCrossing_absolute_boundary X (i+1) (i+q) s t hnc
    exact H
  have h := tower_image_same_target_of_no_crossing M (t-s,t) s (i+q)
    (by omega) hnc' a a₀ ha
  change FiltrationAtLeast model.syntheticTower (s+(i+q)+1)
    (a ≫ absoluteBoundary A i - a₀ ≫ absoluteBoundary A i) at h
  rw [←Preadditive.sub_comp] at h
  have hα := (absolute_boundary_filtration_iff X i (t-s) t (s+(i+q)+1) (a-a₀)).mp h
  let α := biSuspensionHomEquiv (t-s) t i A ((a-a₀) ≫ XModLambdaN.proj A i)
  have hproj : FiltrationAtLeast model.syntheticTower (s+(i+q)+1)
      (α ≫ XModLambdaN.incl A ((i+q)-i)) :=
    map_preserves_filtration (model.convergentMap (.nu X) (.quotient ((i+q)-i) (.nu X))
      (XModLambdaN.incl A ((i+q)-i))) (t-s-1,t+i) (s+(i+q)+1) α hα
  have hz := finite_high_filtration_zero X ((i+q)-i) (by omega) (t-s-1) (t+i)
    (s+(i+q)+1) (by omega) _ hproj
  apply (biSuspensionHomEquiv (t-s) t i (XModLambdaN A ((i+q)-i))).injective
  rw [cofiber_boundary_projection X i (i+q) hi (by omega),
    cofiber_boundary_projection X i (i+q) hi (by omega)]
  apply sub_eq_zero.mp
  simpa only [α,Preadditive.sub_comp,map_sub] using hz

end
end KIP126.ProofTools.Internal.Mahowald
