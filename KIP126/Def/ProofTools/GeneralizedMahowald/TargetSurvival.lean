module
import all KIP126.Def.ProofTools.GeneralizedMahowald.SuspensionDetection
import all KIP126.Def.ProofTools.GeneralizedLeibniz.RightEdge

/-! The actual rho lift preserves every retained finite lambda label.
The resulting finite E-infinity class gives the prescribed first-label lift
in the shorter quotient, which is the source survival step of MH2. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000

private theorem finite_target_rho_detects (X : ClassicalObject)
    (i j k : ℕ) (hki : k < i) (hij : i ≤ j) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : Detects (model.convergence (.quotient i (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X i s t k x) a)
    (b : BiHom (t-s) (t-k) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) j))
    (hb : b≫(model.quotients.tower _).rho i j hij=a) :
    Detects (model.convergence (.quotient j (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X j s t k x) b := by
  have hlabel : nuWeightLabel model X s t (t-k) (by omega) x =
      targetNuLabel model X s t k x := by
    have hk' : (t-(t-k)).toNat=k := by omega
    have transport (a b : ℕ) (hab : a=b)
        (h : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 h (targetNuLabel model X s t a x) = targetNuLabel model X s t b x := by
      subst b
      rfl
    exact transport _ k hk' _
  have ha' : Detects (model.convergence (.quotient i (.nu X))) (s,t,t-k)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) i).pageMap
        2 (s,t,t-k) (nuWeightLabel model X s t (t-k) (by omega) x)) a := by
    rw [hlabel]
    exact ha
  have hh := rho_lift_detects X i j (by omega) hij s t (t-k) (by omega) x a ha' b hb
  rw [hlabel] at hh
  exact hh

private theorem finite_target_rho_bottom_lift (X : ClassicalObject)
    (i j k : ℕ) (hki : k < i) (hij : i ≤ j) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : Detects (model.convergence (.quotient i (.nu X))) (s,t,t-k)
      (finiteTargetLabel model X i s t k x) a)
    (b : BiHom (t-s) (t-k) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) j))
    (hb : b≫(model.quotients.tower _).rho i j hij=a) :
    ∃ c : BiHom (t-s) t (XModLambdaN (nuZero model X) (j-k)),
      c≫(model.quotients.tower _).rho 1 (j-k) (by omega) = firstLabel model X s t x := by
  obtain ⟨c,hc⟩ := finite_detected_target_bottom_lift X j k (by omega) s t x b
    (finite_target_rho_detects X i j k hki hij s t x a ha b hb)
  let f : model.nu.functor.obj (X.obj model.auxiliary) ⟶ nuZero model X :=
    SyntheticCategory.biShift_zero.inv.app _
  refine ⟨c≫XModLambdaN.map f (j-k),?_⟩
  rw [Category.assoc,←(model.quotients.natural f).rho_naturality (by omega),←Category.assoc,hc]
  simp only [f,Category.assoc,←model.quotients.functoriality.map_comp,
    Iso.hom_inv_id_app,model.quotients.functoriality.map_id,Category.comp_id]

end
end KIP126.ProofTools.Internal.Mahowald
