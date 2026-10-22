module

public import KIP126.ProofTools.MahowaldLeibniz
import all KIP126.ProofTools.MahowaldLeibniz.LastLayer
import all KIP126.ProofTools.MahowaldLeibniz.TerminalSquare
import KIP126.AdamsSynthetic.Standard.FirstQuotientCompatibility

/-! Boundary preservation for the actual positive normalized first-quotient
operation.  Unlike an ordinary page-map argument, this uses the finite
quotient/shift comparison and the selected positive first-quotient label. -/

@[expose] section
namespace KIP126.ProofTools.Internal.LastLayerComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

private theorem regrade_zero {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') :
    homotopyRegrade hm hw (0 : BiHom m w A) = 0 := by
  subst m'; subst w'; rfl

private theorem shifted_first_label_uncast
    (X : ClassicalObject) (n : ℕ) (hn : n = 1) (s t : ℤ)
    (x : Ambient model X (s,t))
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) n ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n))
    (hε : XModLambdaN.incl _ n ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ n)) :
    homotopyRegrade (show t-s+0 = t-s by omega) (rfl : t+1 = t+1)
      (oneQuotientUncast _ n hn (t-s+0) (t+1)
        (shiftHomotopyClass (0,1) (t-s,t)
          (oneQuotientCast _ n hn (t-s) t (nativeFirstLabel X s t x)) ≫ ε.inv)) =
      (model.firstQuotient X 1 s t).symm x := by
  subst n
  have H := firstQuotient_positive_shift X s t x ε hε
  simpa only [oneQuotientUncast, oneQuotientCast, nativeFirstLabel_eq_regrade, regrade_comp] using H

private theorem positive_first_top_zero_of_boundary
    (X : ClassicalObject) (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (x : Ambient model X (s,t))
    (hx : x ∈ boundaries model X (d+1) (s,t)) :
    finiteTopOfFirst ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) d hd (t-s) (t+1)
      ((model.firstQuotient X 1 s t).symm x) = 0 := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  letI := model.exactness.shiftCommShift (0,1)
  letI := model.exactness.shiftExact (0,1)
  obtain ⟨εn,hεn,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) ((d+1)-d) A
  obtain ⟨εq,hεq,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) (d+1) A
  let b := oneQuotientCast A ((d+1)-d) (by omega) (t-s) t (nativeFirstLabel X s t x)
  have htop : finiteTopLabel X d hd s t x =
      finiteLambdaClass X (d+1) d hd (Nat.lt_succ_self d) s t b :=
    finiteTopOfFirst_eq_raw A d hd (t-s) t _
  have hshift := shifted_finite_lambda_class_general X (0,1) (d+1) d hd
    (Nat.lt_succ_self d) s t εn εq hεn hεq b
  rw [←htop] at hshift
  have hraw := raw_eq_finiteTopOfFirst ((SyntheticCategory.biShift (0,1)).obj A) d hd
    (t-s+0) (t+1) (shiftHomotopyClass (0,1) (t-s,t) b ≫ εn.inv)
  have hz : finiteTopLabel X d hd s t x = 0 :=
    (finiteTopLabel_zero_iff_boundary X d hd s t x).mpr hx
  rw [hz] at hshift
  have hzero : finiteTopOfFirst ((SyntheticCategory.biShift (0,1)).obj A) d hd
      (t-s+0) (t+1)
      (oneQuotientUncast _ ((d+1)-d) (by omega) (t-s+0) (t+1)
        (shiftHomotopyClass (0,1) (t-s,t) b ≫ εn.inv)) = 0 := by
    rw [←hraw, ←hshift]
    simp only [shiftHomotopyClass, Functor.map_zero, comp_zero,
      regrade_precomp, zero_comp]
  have hr := congrArg (homotopyRegrade (show t-s+0=t-s by omega)
    (rfl : t+1-d=t+1-d)) hzero
  rw [finiteTopOfFirst_regrade _ d hd (t-s+0) (t-s) (t+1) (t+1)
    (by omega) rfl, shifted_first_label_uncast X ((d+1)-d) (by omega) s t x εn hεn] at hr
  simpa only [regrade_zero] using hr

/-- The selected positive normalized Q₁ operation preserves every relevant
finite boundary cutoff. No boundary-preservation hypothesis is supplied by
the caller. The proof uses actual finite top layers and coherent shifts. -/
private theorem cofiber_first_quotient_boundary_mem
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (d : ℕ) (hd : 0 < d) (s t : ℤ)
    (x : Ambient model T.X (s,t))
    (hx : x ∈ boundaries model T.X (d+1) (s,t)) :
    KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
      boundaries model T.Y (d+1) (s+1,t+1) := by
  have hsource := positive_first_top_zero_of_boundary T.X d hd s t x hx
  have hn := finiteTopOfFirst_natural (lastLayerNormalizedMap T hf) d hd (t-s) (t+1)
    ((model.firstQuotient T.X 1 s t).symm x)
  rw [hsource, zero_comp] at hn
  have hfirst := normalizedFirstMap_boundary T hf s t x
  have ht := congrArg (finiteTopOfFirst _ d hd ((t+1)-(s+1)) (t+1)) hfirst
  rw [←finiteTopOfFirst_regrade] at ht
  change _ = finiteTopLabel T.Y d hd (s+1) (t+1) _ at ht
  rw [←hn] at ht
  have htarget : finiteTopLabel T.Y d hd (s+1) (t+1)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) = 0 := by
    simpa only [regrade_zero] using ht.symm
  exact (finiteTopLabel_zero_iff_boundary T.Y d hd (s+1) (t+1) _).mp htarget

end
end KIP126.ProofTools.Internal.LastLayerComparison

namespace KIP126.ProofTools.Standard
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Kervaire.Route KIP126.Literature

/-- The actual normalized first-quotient operation sends each finite source
boundary subgroup to the same target boundary cutoff. This is derived from
the coherent finite-quotient map, rather than added as a naturality premise. -/
private theorem cofiberFirstQuotientBoundary_preservesBoundaries
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (p : ℕ) (hp : 2 ≤ p) (s t : ℤ)
    (x : Ambient model T.X (s,t))
    (hx : x ∈ boundaries model T.X p (s,t)) :
    cofiberFirstQuotientBoundary T hf s t x ∈
      boundaries model T.Y p (s+1,t+1) := by
  cases p with
  | zero => omega
  | succ d =>
    simpa only [Nat.cast_succ] using
      KIP126.ProofTools.Internal.LastLayerComparison.cofiber_first_quotient_boundary_mem
        T hf d (by omega) s t x (by simpa only [Nat.cast_succ] using hx)

end KIP126.ProofTools.Standard
