module

public import KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.Internal.DetectionLabels
import all KIP126.Main.Internal.QuotientCalculus

/-! Successive P/Q filtration removal from NuTargetHelpers.lean:551–585,
696–738, at bbac1fc05843 (MIT). The hypotheses are the actual classical
coset calculations; no downstream result package is introduced. -/
@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature KIP126.Main.Internal
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section

theorem finite_peel_permanent (q k : ℕ) (hq : 0 < q) (hk : k < q) (s t : ℤ)
    (x : model.classical.sphere.Page 2 (s,t))
    (hx : IsPermanentCycle model.classical.sphere (s,t) x)
    (hcoset : ∀ y : model.classical.sphere.Page 2 (s,t),
      y ∈ boundaries model .sphere (1+k) (s,t) ∨
      y-x ∈ boundaries model .sphere (1+k) (s,t))
    (c0 : BiHom (t-s) t (S_0_0 : SyntheticSpectrum))
    (hc0 : (KIP126.Literature.sphereFirstQuotient model) s t (quotientClass 1 c0) = x)
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) q))
    (ha : FiltrationAtLeast model.syntheticTower s a) :
    ∃ b : Bool, FiltrationAtLeast model.syntheticTower (s+1)
      (a-(if b then quotientClass q (lambdaMultiply k c0) else 0)) := by
  let c : cycles model .sphere ((q:ℤ)-t+(t-k)) (s,t) :=
    ⟨x,permanentCycles_le_cycles model .sphere (s,t) _ ((permanent_cycle_iff_mem .sphere (s,t) x).mp hx)⟩
  have hframe : ∀ z : CycleQuotient model .sphere ((q:ℤ)-t+(t-k)) (1+t-(t-k)) (s,t),
      z = 0 ∨ z = subquotientClass _ _ c := by
    intro z
    obtain ⟨z,rfl⟩ := Quotient.exists_rep z
    change subquotientClass _ _ z = 0 ∨ subquotientClass _ _ z = subquotientClass _ _ c
    rcases hcoset z.val with hz | hz
    · left
      apply (subquotientClass_eq_zero_iff _ _ _).mpr
      exact (congrArg (fun j : ℤ => z.val ∈ boundaries model .sphere j (s,t))
        (show (1:ℤ)+k=1+t-(t-k) by omega)).mp hz
    · right
      apply sub_eq_zero.mp
      rw [←map_sub]
      apply (subquotientClass_eq_zero_iff _ _ _).mpr
      exact (congrArg (fun j : ℤ => (z-c).val ∈ boundaries model .sphere j (s,t))
        (show (1:ℤ)+k=1+t-(t-k) by omega)).mp hz
  have frame := finite_sphere_frame q k hq hk s t c hframe
  have hc := model.sphereDetectionCompatible.homotopy_lambda s t k c0
  change Detects (model.convergence .sphere) (s,t,t-k)
    (sphereLabel s t k ((KIP126.Literature.sphereFirstQuotient model) s t (quotientClass 1 c0))) (lambdaMultiply k c0) at hc
  rw [hc0] at hc
  have hcq := detects_map .sphere (.quotient q .sphere) (XModLambdaN.incl _ q)
    (s,t,t-k) (sphereLabel s t k x) (lambdaMultiply k c0) hc
  exact finite_detection_peel q (s,t,t-k) (quotientLabel q s t k x) frame
    (quotientClass q (lambdaMultiply k c0)) hcq a ha

theorem pq_lift_peel
    (hpCoset : ∀ x : model.classical.sphere.Page 2 (11,133),
      x ∈ boundaries model .sphere 3 (11,133) ∨
      x-KIP126.Computation.Standard.P ∈ boundaries model .sphere 3 (11,133))
    (hqCoset : ∀ x : model.classical.sphere.Page 2 (12,134),
      x ∈ boundaries model .sphere 3 (12,134) ∨
      x-KIP126.Computation.Standard.Q ∈ boundaries model .sphere 3 (12,134))
    (a : BiHom 122 127 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (ha : FiltrationAtLeast model.syntheticTower 11 a) :
    ∃ (p : BiHom 122 133 (S_0_0 : SyntheticSpectrum))
      (q : BiHom 122 134 (S_0_0 : SyntheticSpectrum)) (bp bq : Bool),
      (KIP126.Literature.sphereFirstQuotient model) 11 133 (quotientClass 1 p) = KIP126.Computation.Standard.P ∧
      (KIP126.Literature.sphereFirstQuotient model) 12 134 (quotientClass 1 q) = KIP126.Computation.Standard.Q ∧
      FiltrationAtLeast model.syntheticTower 13
        (a-((if bp then (show BiHom 122 127 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)
          from quotientClass 9 (lambdaMultiply 6 p)) else 0) +
        (if bq then (show BiHom 122 127 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)
          from quotientClass 9 (lambdaMultiply 7 q)) else 0))) := by
  have hp := KIP126.Computation.Standard.p_permanent_cycle
  have hq := KIP126.Computation.Standard.q_permanent_cycle
  obtain ⟨p,hp0⟩ := sphere_permanent_first_quotient_lift 11 133 _ hp
  obtain ⟨q,hq0⟩ := sphere_permanent_first_quotient_lift 12 134 _ hq
  have cp : ∀ y : model.classical.sphere.Page 2 (11,133),
      y ∈ boundaries model .sphere 7 (11,133) ∨
      y-KIP126.Computation.Standard.P ∈ boundaries model .sphere 7 (11,133) := by
    intro y
    rcases hpCoset y with h | h
    · exact Or.inl (boundaries_monotone model .sphere (11,133) (by decide : (3:ℤ) ≤ 7) h)
    · exact Or.inr (boundaries_monotone model .sphere (11,133) (by decide : (3:ℤ) ≤ 7) h)
  have cq : ∀ y : model.classical.sphere.Page 2 (12,134),
      y ∈ boundaries model .sphere 8 (12,134) ∨
      y-KIP126.Computation.Standard.Q ∈ boundaries model .sphere 8 (12,134) := by
    intro y
    rcases hqCoset y with h | h
    · exact Or.inl (boundaries_monotone model .sphere (12,134) (by decide : (3:ℤ) ≤ 8) h)
    · exact Or.inr (boundaries_monotone model .sphere (12,134) (by decide : (3:ℤ) ≤ 8) h)
  obtain ⟨bp,hbp⟩ := finite_peel_permanent 9 6 (by decide) (by decide)
    11 133 _ hp cp p hp0 a ha
  let v : BiHom 122 127 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) := quotientClass 9 (lambdaMultiply 6 p)
  change FiltrationAtLeast model.syntheticTower 12 (a-(if bp then v else 0)) at hbp
  obtain ⟨bq,hbq⟩ := finite_peel_permanent 9 7 (by decide) (by decide)
    12 134 _ hq cq q hq0 (a-(if bp then v else 0)) hbp
  refine ⟨p,q,bp,bq,hp0,hq0,?_⟩
  simpa only [v,sub_sub,Nat.cast_ofNat,Int.reduceAdd,Int.reduceSub] using hbq

end
end KIP126.Main.SectionSeven.Internal
