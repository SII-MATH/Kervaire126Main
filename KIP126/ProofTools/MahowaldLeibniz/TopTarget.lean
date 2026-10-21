module

import all KIP126.ProofTools.MahowaldLeibniz.MayTarget
import all KIP126.ProofTools.MahowaldLeibniz.LastLayer

/-! Exact identification of the signed May output with one selected highest-layer inclusion. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem top_target_regrade_self {A : SyntheticSpectrum} {m w : ℤ}
    (a : BiHom m w A) : homotopyRegrade rfl rfl a=a := rfl

/-- One selected Q₁-to-top-layer inclusion, with only quotient-length and
weight equalities transported. -/
private def finiteTopLabelAtWeight (X : ClassicalObject) (d : ℕ) (hd : 0<d)
    (N : ℕ) (hN : d+1=N) (s t w : ℤ) (hw : t-d=w)
    (x : Ambient model X (s,t)) :
    BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N) :=
  hN ▸ homotopyRegrade rfl hw (finiteTopLabel X d hd s t x)

private theorem finite_top_label_at_weight_detects
    (X : ClassicalObject) (d : ℕ) (hd : 0<d)
    (N : ℕ) (hN : d+1=N) (s t w : ℤ) (hw : t-d=w)
    (x : Ambient model X (s,t)) :
    Detects (model.convergence (.quotient N (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
        2 (s,t,w) (nuWeightLabel model X s t w (by omega) x))
      (finiteTopLabelAtWeight X d hd N hN s t w hw x) := by
  subst N
  subst w
  rw [finite_coefficient_weight_label]
  simpa only [finiteTopLabelAtWeight,top_target_regrade_self] using
    finiteTopLabel_detects X d hd s t x

/-- The highest-layer target attached to the specified May label v.
Its definition uses a single selected top inclusion, not an iterated
coefficient insertion or a choice of leading representative. -/
private def finiteMayTopLabel (X : ClassicalObject) (c q : ℕ) (hq : 0<q)
    (s t : ℤ) (v : Ambient model X (s+q+1,t+q)) :
    BiHom ((t-s)-1) (t-c)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1))) :=
  homotopyRegrade (by omega) rfl
    (finiteTopLabelAtWeight X (c+q) (by omega) (c+(q+1)) (by omega)
      (s+q+1) (t+q) (t-c) (by omega) v)

private theorem finite_may_top_label_detects
    (X : ClassicalObject) (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (v : Ambient model X (s+q+1,t+q)) :
    Detects (model.convergence (.quotient (c+(q+1)) (.nu X))) (s+q+1,t+q,t-c)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1))).pageMap
        2 (s+q+1,t+q,t-c) (nuWeightLabel model X (s+q+1) (t+q) (t-c) (by omega) v))
      (homotopyRegrade (by dsimp; omega) rfl (finiteMayTopLabel X c q hq s t v)) := by
  simpa only [finiteMayTopLabel,homotopy_regrade_inverse] using
    finite_top_label_at_weight_detects X (c+q) (by omega) (c+(q+1)) (by omega)
      (s+q+1) (t+q) (t-c) (by omega) v

/-- Highest-layer uniqueness identifies the actual homotopy class, not
merely its associated graded label.  No cycle condition on v is needed. -/
private theorem finite_may_target_eq_top_of_detects
    (X : ClassicalObject) (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (v : Ambient model X (s+q+1,t+q))
    (bN : BiHom ((t-s)-1) (t-c)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1))))
    (hb : Detects (model.convergence (.quotient (c+(q+1)) (.nu X))) (s+q+1,t+q,t-c)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1))).pageMap
        2 (s+q+1,t+q,t-c) (nuWeightLabel model X (s+q+1) (t+q) (t-c) (by omega) v))
      (homotopyRegrade (by dsimp; omega) rfl bN)) :
    bN = finiteMayTopLabel X c q hq s t v := by
  have h := finite_top_detection_unique X (c+(q+1)) (by omega)
    (s+q+1) (t+q) (t-c) (by omega) _ _ _ hb
    (finite_may_top_label_detects X c q hq s t v)
  have h' := congrArg (homotopyRegrade
    (show (t+q)-(s+q+1)=(t-s)-1 by omega) (rfl : t-c=t-c)) h
  simpa only [homotopy_regrade_inverse] using h'

/-- The raw signed and coefficient-extended May output is precisely the
ordinary suspension of the single selected Q₁-to-Qₚ highest-layer inclusion
of the specified v. -/
private theorem finite_may_signed_target_eq_top_at_level
    (X : ClassicalObject) (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (v : Ambient model X (s+q+1,t+q))
    (en : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q+1))⟦(1:ℤ)⟧)
    (eN : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (c+(q+1)) ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1)))⟦(1:ℤ)⟧)
    (hen : XModLambdaN.incl _ (q+1)≫en.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
    (heN : XModLambdaN.incl _ (c+(q+1))≫eN.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (c+(q+1)))) :
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel X (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) ⟶
        XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((model.quotients.tower _).triangle hq (Nat.lt_succ_self q)).lambdaMap
    finiteCoefficientInsert _ c (q+1) (by omega) (t-s) t
        ((-(b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map ly))≫en.inv)≫eN.hom =
      ordinarySuspendedRepresentative _ (t-s) (t-c) (finiteMayTopLabel X c q hq s t v) := by
  dsimp only
  obtain ⟨bN,hb,hraw⟩ := finite_may_signed_target_at_level X c q hq s t v en eN hen heN
  rw [finite_may_target_eq_top_of_detects X c q hq s t v bN hb] at hraw
  exact hraw

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
