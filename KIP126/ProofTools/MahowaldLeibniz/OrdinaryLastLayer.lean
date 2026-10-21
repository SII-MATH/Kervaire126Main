module

import all KIP126.ProofTools.MahowaldLeibniz.LastLayer
import all KIP126.ProofTools.MahowaldLeibniz.FixedModel

/-! The last-layer condition when the first normalization exponent is zero.
The page operation is the actual ordinary map, and the boundary denominator
is the full finite-quotient length. -/

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

private theorem finite_top_label_ordinary_natural
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (d : ℕ) (hd : 0 < d) (s t : ℤ) (x : Ambient model X (s,t)) :
    finiteTopLabel X d hd s t x ≫ XModLambdaN.map (model.nu.functor.map f) (d+1) =
      finiteTopLabel Y d hd s t ((model.classical.map f).pageMap 2 (s,t) x) := by
  unfold finiteTopLabel
  rw [finiteTopOfFirst_natural,native_first_label_natural]

/-- The actual ordinary finite map kills every class in the last filtration
when its entire classical E₂ image belongs to the final boundary subgroup. -/
private theorem ordinary_map_last_layer_zero
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (hNC2 : ∀ x : Ambient model X (s,t),
      (model.classical.map f).pageMap 2 (s,t) x ∈ boundaries model Y (d+1) (s,t))
    (a : BiHom (t-s) (t-d)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (d+1)))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    a ≫ XModLambdaN.map (model.nu.functor.map f) (d+1) = 0 := by
  obtain ⟨x,rfl⟩ := finiteTopLabel_exists X d hd s t a ha
  rw [finite_top_label_ordinary_natural]
  exact (finiteTopLabel_zero_iff_boundary Y d hd s t _).mpr (hNC2 x)

private theorem ordinary_map_top_filtration_zero
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (N : ℕ) (hN : 2 ≤ N) (s t w : ℤ) (hw : t-w=N-1)
    (hNC2 : ∀ x : Ambient model X (s,t),
      (model.classical.map f).pageMap 2 (s,t) x ∈ boundaries model Y N (s,t))
    (a : BiHom (t-s) w
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    a ≫ XModLambdaN.map (model.nu.functor.map f) N = 0 := by
  cases N with
  | zero => omega
  | succ d =>
    have hw' : w=t-d := by push_cast at hw; omega
    subst w
    exact ordinary_map_last_layer_zero X Y f d (by omega) s t hNC2 a ha

/-- NC1 and NC2 annihilate the entire ambiguity for an ordinary first arrow.
This is the finite criterion used in the two PDF branches with e_f=0. -/
private theorem ordinary_map_pdf_annihilation
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (c K : ℕ) (hK : 2 ≤ K) (S T : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < K-1 →
      cycles model X ((K:ℤ)-j) (S+j,T+j) ≤
        boundaries model X ((c:ℤ)+j+1) (S+j,T+j))
    (hNC2 : ∀ x : Ambient model X (S+K-1,T+K-1),
      (model.classical.map f).pageMap 2 (S+K-1,T+K-1) x ∈
        boundaries model Y (c+K) (S+K-1,T+K-1))
    (a : BiHom (T-S) (T-c)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+K)))
    (ha : FiltrationAtLeast model.syntheticTower (S+1) a) :
    a ≫ XModLambdaN.map (model.nu.functor.map f) (c+K) = 0 := by
  have hlast := (finite_filtration_collapse_of_middle_conditions X c K hK S T hmid a).mp ha
  let b : BiHom ((T+K-1)-(S+K-1)) (T-c)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+K)) :=
    homotopyRegrade (by omega) rfl a
  have hb : FiltrationAtLeast model.syntheticTower (S+K-1) b :=
    homotopy_regrade_filtration (by omega) rfl _ a hlast
  have hz := ordinary_map_top_filtration_zero X Y f (c+K) (by omega)
    (S+K-1) (T+K-1) (T-c) (by omega) hNC2 b hb
  have hh := congrArg (homotopyRegrade
    (show (T+K-1)-(S+K-1)=T-S by omega) (rfl : T-c=T-c)) hz
  have regrade_zero {m m' w w' : ℤ} {A : SyntheticSpectrum}
      (hm : m=m') (hw : w=w') : homotopyRegrade hm hw (0 : BiHom m w A)=0 := by
    subst m'; subst w'; rfl
  simpa only [b,regrade_comp,homotopy_regrade_inverse,regrade_zero] using hh

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
