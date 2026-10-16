module
import all KIP126.Def.ProofTools.GeneralizedLeibniz.BoundaryDivision
import all KIP126.Def.ProofTools.GeneralizedLeibniz.RightEdge
import all KIP126.Def.ProofTools.GeneralizedLeibniz.DivisionLabels

/-! The weighted reverse absolute-boundary comparison in AimPaper Remark
`rmk:qvoewfj`, including zero lambda exponent. A higher rho lift preserves
the detected source. Actual lambda division, equal Q1 boundary labels and
the exact boundary indeterminacy then give the original classical
differential. This proof does not use either unfinished GL/MH theorem. -/

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
set_option maxHeartbeats 6000000

private theorem nu_weight_detects_transport (X : ClassicalObject) (s t w w' : ℤ)
    (hw : w=w') (hwt : w≤t) (hw't : w'≤t) (x : Ambient model X (s,t))
    (a : BiHom (t-s) w (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : Detects (model.convergence (.nu X)) (s,t,w)
      (nuWeightLabel model X s t w hwt x) a) :
    Detects (model.convergence (.nu X)) (s,t,w')
      (nuWeightLabel model X s t w' hw't x) (homotopyRegrade rfl hw a) := by
  subst w'; exact ha

private theorem finite_detected_boundary_differential_weighted_pos (X : ClassicalObject)
    (i q d : ℕ) (hd : 0 < d) (hdi : d < i) (hiq : i ≤ q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (y : Ambient model X (s+(q-d:ℕ)+1,t+(q-d:ℕ)))
    (a : BiHom (t-s) (t-d) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : Detects (model.convergence (.quotient i (.nu X))) (s,t,t-d)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) i).pageMap 2 (s,t,t-d)
        (nuWeightLabel model X s t (t-d) (by omega) x)) a)
    (hy : Detects (model.convergence (.nu X)) (s+(q-d:ℕ)+1,t+(q-d:ℕ),t-d+i)
      (nuWeightLabel model X (s+(q-d:ℕ)+1) (t+(q-d:ℕ)) (t-d+i) (by omega) y)
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv (t-s) (t-d) i (model.nu.functor.obj (X.obj model.auxiliary))
          (a ≫ XModLambdaN.proj _ i)))) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
      ((q-d:ℕ)+1) (s,t) (s+(q-d:ℕ)+1,t+(q-d:ℕ)) x y := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  have hdq : d < q := by omega
  have hk : 0 < q-d := by omega
  have hfil : FiltrationAtLeast model.syntheticTower ((t-d)-(t-s)+q+1)
      (biSuspensionHomEquiv (t-s) (t-d) i A (a ≫ XModLambdaN.proj A i)) := by
    have hf := detects_filtration (.nu X) (s+(q-d:ℕ)+1,t+(q-d:ℕ),t-d+i) _ _ hy
    have hf := (regrade_filtration_iff _ _ _ _).mp hf
    have he : (t-d)-(t-s)+(q:ℤ)+1 = s+(q-d:ℕ)+1 := by omega
    rw [he]
    exact hf
  obtain ⟨b,hb⟩ : ∃ b : BiHom (t-s) (t-d) (XModLambdaN A q),
      b ≫ (model.quotients.tower A).rho i q hiq = a := by
    rcases hiq.eq_or_lt with rfl | hlt
    · exact ⟨a,by rw [(model.quotients.tower A).rho_id,Category.comp_id]⟩
    · exact absolute_boundary_filtration_lift_weighted X i q (by omega) hlt (t-s) (t-d) a hfil
  have hbd := rho_lift_detects X i q (by omega) hiq s t (t-d) (by constructor <;> omega) x a ha b hb
  obtain ⟨c,hc⟩ := finite_detected_source_division X q d hd hdq s t x b hbd
  obtain ⟨x0,hx0⟩ := quotient_first_label_exists X (q-d) hk s t c
  have hxcong := finite_lambda_division_first_label_congruent X q d hd hdq s t x x0 c hx0 b hbd hc
  let β := boundaryRepresentative X (q-d) s t c
  obtain ⟨z,hz⟩ := nu_first_label_exists X (s+(q-d:ℕ)+1) (t+(q-d:ℕ)) β
  have hdz := adjacent_boundary_differential X (q-d) hk s t x0 z c hx0 hz
  let α : BiHom ((t+(q-d:ℕ))-(s+(q-d:ℕ)+1)) (t+(q-d:ℕ)) A :=
    homotopyRegrade (by omega) (by omega)
      (biSuspensionHomEquiv (t-s) (t-d) q A (b ≫ XModLambdaN.proj A q))
  have hα : α ≫ XModLambdaN.incl A 1 = firstLabel model X (s+(q-d:ℕ)+1) (t+(q-d:ℕ)) z ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 := by
    have hdiv := divided_boundary_first_quotient X d q hd hdq (t-s) t c
    dsimp only at hdiv
    rw [hc] at hdiv
    have hdiv := congrArg (homotopyRegrade (by omega : (t-s)-1=(t+(q-d:ℕ))-(s+(q-d:ℕ)+1)) rfl) hdiv
    have hαβ : α ≫ XModLambdaN.incl A 1 = β ≫ XModLambdaN.incl A 1 := by
      simpa only [α,β,boundaryRepresentative,regrade_precomp,←Category.assoc,eqToHom_trans] using hdiv
    exact hαβ.trans hz
  have hp := first_label_lift_permanent X (s+(q-d:ℕ)+1) (t+(q-d:ℕ)) z α hα
  have hzdet : Detects (model.convergence (.nu X)) (s+(q-d:ℕ)+1,t+(q-d:ℕ),t-d+i)
      (nuWeightLabel model X (s+(q-d:ℕ)+1) (t+(q-d:ℕ)) (t-d+i) (by omega) z)
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv (t-s) (t-d) i A (a ≫ XModLambdaN.proj A i))) := by
    by_cases hiq' : i=q
    · subst i
      have hdet := nu_first_label_detects X (s+(q-d:ℕ)+1) (t+(q-d:ℕ)) z hp α hα
      have hdet := nu_weight_detects_transport X (s+(q-d:ℕ)+1) (t+(q-d:ℕ))
        (t+(q-d:ℕ)) (t-d+q) (by omega) (by omega) (by omega) z α hdet
      have hb' : b=a := by simpa only [(model.quotients.tower A).rho_id,Category.comp_id] using hb
      simpa only [α,hb',regrade_precomp,←Category.assoc,eqToHom_trans] using hdet
    · have hdet := nu_lambda_detects X (q-i) (by omega) (s+(q-d:ℕ)+1) (t+(q-d:ℕ)) z hp α hα
      have hdet := nu_weight_detects_transport X (s+(q-d:ℕ)+1) (t+(q-d:ℕ))
        ((t+(q-d:ℕ))-(q-i:ℕ)) (t-d+i) (by omega) (by omega) (by omega) z _ hdet
      convert hdet using 1
      rw [←hb,absolute_boundary_restriction]
      dsimp only [α]
      rw [lambda_regrade]
      simp only [A,regrade_precomp,←Category.assoc,eqToHom_trans]
  have hcong := nu_detected_labels_congruent X (s+(q-d:ℕ)+1) (t+(q-d:ℕ)) (t-d+i)
    (by omega) y z _ hy hzdet
  have hboundary : y-z ∈ boundaries model X (q-d:ℕ) (s+(q-d:ℕ)+1,t+(q-d:ℕ)) :=
    boundaries_monotone model X _ (by omega) hcong
  have hdxy0 := (differentialAt_of_congruent model X
    (⟨by omega,hdz⟩ : DifferentialAt model X ((q-d:ℕ)+1) (s,t) (s+(q-d:ℕ)+1,t+(q-d:ℕ)) x0 z)
    ⟨by omega,by simpa only [add_sub_cancel_right] using hboundary⟩).2
  exact differential_of_source_boundary_congruent X ((q-d:ℕ)+1) (d+1) (s,t)
    (s+(q-d:ℕ)+1,t+(q-d:ℕ)) x x0 y hdxy0 hxcong

private theorem finite_detected_boundary_differential_weighted (X : ClassicalObject)
    (i k d : ℕ) (hdi : d < i) (hik : i-d ≤ k) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (a : BiHom (t-s) (t-d) (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : Detects (model.convergence (.quotient i (.nu X))) (s,t,t-d)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) i).pageMap 2 (s,t,t-d)
        (nuWeightLabel model X s t (t-d) (by omega) x)) a)
    (hy : Detects (model.convergence (.nu X)) (s+k+1,t+k,t-d+i)
      (nuWeightLabel model X (s+k+1) (t+k) (t-d+i) (by omega) y)
      (homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv (t-s) (t-d) i (model.nu.functor.obj (X.obj model.auxiliary))
          (a ≫ XModLambdaN.proj _ i)))) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  by_cases hd : d=0
  · subst d
    simp only [Nat.sub_zero] at hik
    have H (w : ℤ) (hw : w=t)
        (a0 : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
        (ha0 : Detects (model.convergence (.quotient i (.nu X))) (s,t,w)
          ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) i).pageMap 2 (s,t,w)
            (nuWeightLabel model X s t w (by omega) x)) a0)
        (hy0 : Detects (model.convergence (.nu X)) (s+k+1,t+k,w+i)
          (nuWeightLabel model X (s+k+1) (t+k) (w+i) (by omega) y)
          (homotopyRegrade (by dsimp; omega) rfl
            (biSuspensionHomEquiv (t-s) w i (model.nu.functor.obj (X.obj model.auxiliary))
              (a0 ≫ XModLambdaN.proj _ i)))) :
        HasDifferential (model.classical.obj (X.obj model.auxiliary))
          (k+1) (s,t) (s+k+1,t+k) x y := by
      subst w
      exact finite_detected_boundary_differential X i k (by omega) hik s t x y a0 ha0 hy0
    exact H (t-(0:ℕ)) (by omega) a ha hy
  · generalize hq : k+d=q at *
    have he : q-d=k := by omega
    subst k
    exact finite_detected_boundary_differential_weighted_pos X i q d
      (by omega) hdi (by omega) s t x y a ha hy

end
end KIP126.ProofTools.Internal.Leibniz
