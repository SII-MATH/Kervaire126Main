module

import all KIP126.ProofTools.GeneralizedLeibniz.WeightedReverse
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionDetection

@[expose] section
namespace KIP126.ProofTools.Internal.FiniteLifting

open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- A common source can be compared with a separately chosen bottom
representative using a genuine high-filtration image condition. -/
private theorem filtered_image_difference
    {C D : Type*} [AddCommGroup C] [AddCommGroup D]
    (f : C →+ D) (F : ℤ → AddSubgroup C) (G : ℤ → AddSubgroup D)
    (hG : Antitone G) (su sv cutoff : ℤ) (hcut : cutoff ≤ sv)
    (c c0 : C) (hsource : c-c0 ∈ F (su+1))
    (hcutoff : f c ∈ G cutoff) (hknown : f c0 ∈ G sv)
    (hprecision : ∀ e, e ∈ F (su+1) → f e ∈ G cutoff →
      f e ∈ G (sv+1)) :
    f c-f c0 ∈ G (sv+1) := by
  have he : f (c-c0) ∈ G cutoff := by
    rw [map_sub]
    exact (G cutoff).sub_mem hcutoff (hG hcut hknown)
  simpa only [map_sub] using hprecision (c-c0) hsource he

/-- A finite representative criterion for an actual Adams differential.
The equality involving the boundary is the commutative-square equation,
not a detection assumption on the boundary or the desired differential. -/
private theorem finite_differential_from_common_representatives
    (X : ClassicalObject) (i k d : ℕ) (hdi : d < i) (hik : i-d ≤ k)
    (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (b : BiHom (t-s) (t-d)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (hb : Detects (model.convergence (.quotient i (.nu X))) (s,t,t-d)
      ((model.family.quotientProjection
        (model.nu.functor.obj (X.obj model.auxiliary)) i).pageMap 2 (s,t,t-d)
        (nuWeightLabel model X s t (t-d) (by omega) x)) b)
    {C : Type*} [AddCommGroup C]
    (F : ℤ → AddSubgroup C)
    (f : C →+ BiHom ((t+k)-(s+k+1)) (t-d+i)
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (su cutoff : ℤ) (hcut : cutoff ≤ s+k+1)
    (c c0 : C) (hsource : c-c0 ∈ F (su+1))
    (hcomm : homotopyRegrade (by omega) rfl
      (biSuspensionHomEquiv (t-s) (t-d) i
        (model.nu.functor.obj (X.obj model.auxiliary))
        (b ≫ XModLambdaN.proj _ i)) = f c)
    (hcutoff : FiltrationAtLeast model.syntheticTower cutoff (f c))
    (hknown : Detects (model.convergence (.nu X)) (s+k+1,t+k,t-d+i)
      (nuWeightLabel model X (s+k+1) (t+k) (t-d+i) (by omega) y) (f c0))
    (hprecision : ∀ e, e ∈ F (su+1) →
      FiltrationAtLeast model.syntheticTower cutoff (f e) →
      FiltrationAtLeast model.syntheticTower (s+k+1+1) (f e)) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let p : ℤ × ℤ := ((t+k)-(s+k+1),t-d+i)
  let G : ℤ → AddSubgroup (BiHom p.1 p.2 A) := fun v =>
    (model.syntheticTower.filtrationSubmodule A v p).toAddSubgroup
  have hG : Antitone G := by
    intro u v huv z hz
    exact model.syntheticTower.filtrationSubmodule_antitone A p huv hz
  have hknownFiltration : f c0 ∈ G (s+k+1) :=
    detects_filtration (.nu X) (s+k+1,t+k,t-d+i) _ _ hknown
  have hd : FiltrationAtLeast model.syntheticTower (s+k+1+1) (f c-f c0) :=
    filtered_image_difference f F G hG su (s+k+1) cutoff hcut c c0
      hsource hcutoff hknownFiltration hprecision
  have hboundary := detects_of_high_difference (.nu X)
    (s+k+1,t+k,t-d+i) _ (f c0) (f c) hknown hd
  rw [←hcomm] at hboundary
  exact finite_detected_boundary_differential_weighted X i k d hdi hik s t
    x y b hb hboundary

end
end KIP126.ProofTools.Internal.FiniteLifting
