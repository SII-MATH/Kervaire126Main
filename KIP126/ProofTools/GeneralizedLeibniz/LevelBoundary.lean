module
import all KIP126.ProofTools.GeneralizedLeibniz.LeftEdge
import all KIP126.ProofTools.GeneralizedLeibniz.BoundaryDivision
import all KIP126.ProofTools.GeneralizedMahowald.FinalDivision

/-! The forward absolute-boundary comparison at arbitrary lambda level.
For quotient exponent q and source level d, the effective classical window is
q-d. A classical differential d_(K+1) therefore gives a boundary detected by
lambda^(K-q+d) of its target. The proof uses finite lambda multiplication,
the actual quotient boundary and its natural sphere-coordinate comparison.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
set_option Elab.async false

private theorem level_nu_weight_detects_transport (X : ClassicalObject)
    (s t w w' : ℤ) (hw : w=w') (hwt : w≤t) (hw't : w'≤t)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) w (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : Detects (model.convergence (.nu X)) (s,t,w)
      (nuWeightLabel model X s t w hwt x) a) :
    Detects (model.convergence (.nu X)) (s,t,w')
      (nuWeightLabel model X s t w' hw't x) (homotopyRegrade rfl hw a) := by
  subst w'
  exact ha

private theorem level_regraded_automorphism_detects (X : ClassicalObject)
    (s t w : ℤ) (hw : w≤t) (m : ℤ) (hm : m=t-s)
    (x : Ambient model X (s,t))
    (u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w)
    (a : BiHom m w (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : Detects (model.convergence (.nu X)) (s,t,w)
      (nuWeightLabel model X s t w hw x) (homotopyRegrade hm rfl a)) :
    Detects (model.convergence (.nu X)) (s,t,w)
      (nuWeightLabel model X s t w hw x) (homotopyRegrade hm rfl (u.hom≫a)) := by
  subst m
  exact sphere_automorphism_nu_detects X s t w hw x u a ha

/-- Actual forward boundary at every retained source level `d < q`.
Taking `q = n+d-1` and `K = r-1` gives the GL left edge
`delta_q(lambda^d x) = lambda^(r-n) y`. -/
private theorem differential_absolute_boundary_level (X : ClassicalObject)
    (q K d : ℕ) (hdq : d<q) (hqK : q-d≤K) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+K+1,t+K))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (K+1) (s,t) (s+K+1,t+K) x y)
    (hy : y ∈ permanentCycles model X (s+K+1,t+K)) :
    ∃ a : BiHom (t-s) (t-d)
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
      Detects (model.convergence (.quotient q (.nu X))) (s,t,t-d)
        ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap
          2 (s,t,t-d) (nuWeightLabel model X s t (t-d) (by omega) x)) a ∧
      Detects (model.convergence (.nu X)) (s+K+1,t+K,t-d+q)
        (nuWeightLabel model X (s+K+1) (t+K) (t-d+q) (by omega) y)
        (homotopyRegrade (by dsimp; omega) rfl
          (biSuspensionHomEquiv (t-s) (t-d) q
            (model.nu.functor.obj (X.obj model.auxiliary))
            (a ≫ XModLambdaN.proj _ q))) := by
  by_cases hd0 : d=0
  · subst d
    simp only [Nat.sub_zero] at hqK
    obtain ⟨a,ha,hb⟩ := differential_absolute_boundary X q K (by omega) hqK s t x y hd hy
    have has := first_label_detects_unshifted X q (by omega) s t x a ha
    rw [←zero_weight_label X q s t x] at has
    have H (w : ℤ) (hw : w=t) :
        ∃ a : BiHom (t-s) w
            (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
          Detects (model.convergence (.quotient q (.nu X))) (s,t,w)
            ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap
              2 (s,t,w) (nuWeightLabel model X s t w (by omega) x)) a ∧
          Detects (model.convergence (.nu X)) (s+K+1,t+K,w+q)
            (nuWeightLabel model X (s+K+1) (t+K) (w+q) (by omega) y)
            (homotopyRegrade (by dsimp; omega) rfl
              (biSuspensionHomEquiv (t-s) w q
                (model.nu.functor.obj (X.obj model.auxiliary))
                (a ≫ XModLambdaN.proj _ q))) := by
      subst w
      exact ⟨a,has,hb⟩
    exact H (t-(0:ℕ)) (by omega)
  · have hdpos : 0<d := by omega
    let A := model.nu.functor.obj (X.obj model.auxiliary)
    obtain ⟨b,hb,hδ⟩ := differential_absolute_boundary X (q-d) K (by omega) hqK
      s t x y hd hy
    have hbdet := first_label_detects_unshifted X (q-d) (by omega) s t x b hb
    rw [←zero_weight_label X (q-d) s t x] at hbdet
    let a := finiteWeightedLambdaClass X q d hdpos hdq s t t b
    have hadet := finite_weighted_lambda_detects X q d hdpos hdq s t t
      (by constructor <;> omega) x b hbdet
    refine ⟨a,hadet,?_⟩
    let β := biSuspensionHomEquiv (t-s) t (q-d:ℕ) A (b≫XModLambdaN.proj A (q-d))
    let u := boundaryDivisionSourceIso d q hdq.le (t-s) t
    have hauto := level_regraded_automorphism_detects X (s+K+1) (t+K)
      (t+(q-d:ℕ)) (by omega) ((t-s)-1) (by omega) y u β hδ
    have hcomparison :
        homotopyRegrade rfl (by omega)
          (biSuspensionHomEquiv (t-s) (t-d) q A (a≫XModLambdaN.proj A q)) =
        u.hom≫β := by
      have ha : a=finiteLambdaClass X q d hdpos hdq s t b := rfl
      rw [ha,finiteLambdaClass_vertical]
      exact (divided_boundary_eq_reindex X d q hdpos hdq (t-s) t b).trans
        (boundaryDivisionReindex_eq_precomp d q hdq.le (t-s) t A β)
    rw [←hcomparison] at hauto
    have hfinal := level_nu_weight_detects_transport X (s+K+1) (t+K)
      (t+(q-d:ℕ)) (t-d+q) (by omega) (by omega) (by omega) y _ hauto
    simpa only [normalized_homotopy_regrade_trans] using hfinal

end
end KIP126.ProofTools.Internal.Leibniz
