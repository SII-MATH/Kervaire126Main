module

public import KIP126.Def.AdamsSynthetic.ExtensionLaws.GeneralizedLeibniz.Predicates
public import KIP126.Literature.AdamsSynthetic.ComparisonTheorems

@[expose] public section

/-! The generalized Leibniz rule from LWX Theorem 6.1, under the stated
classical/synthetic comparison hypotheses. The two marked geometric proof
obligations remain unproved; the other steps establish the required cycle
and representative comparisons. No computed differential is a premise. -/
namespace KIP126.Main.ExtensionLaws

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Classical.Adams
open KIP126.Literature.AdamsSynthetic

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn)

open CategoryTheory.Limits KIP126.Classical.Adams.PageRepresentatives
open KIP126.SpectralSequence

private theorem representsOnPage_of_congruent {Z : C} {R : ℤ}
    (hR : 2 ≤ R) {p : ℤ × ℤ} {x y : Ambient H Z p}
    {xr : (adamsTowerInternalSpectralSequence H.unit Z).Page R p}
    (hx : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit Z) R p x xr)
    (hy : Congruent H Z (R - 1) p y x) :
    RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit Z) R p y xr := by
  let E := adamsTowerInternalSpectralSequence H.unit Z
  let P := E.ssData p
  let k : WithTop ℕ := ↑(R - 2).toNat
  change ∃ _ : 2 ≤ R, ∃ z : (Subobject.underlying.obj (P.Z k) : ModuleCat ℤ),
    cycleMap H Z k p z = x ∧ P.pageπ k z = xr at hx
  obtain ⟨_, z, hzx, hzr⟩ := hx
  have hb : y - x ∈ boundaries H Z (R - 1) p := hy.2
  change ∃ b, boundaryMap H Z (↑(R - 1 - 1).toNat) p b = y - x at hb
  rw [show R - 1 - 1 = R - 2 by omega] at hb
  obtain ⟨b, hb⟩ := hb
  let j := Subobject.ofLE (P.B k) (P.Z k) (P.B_le_Z k)
  have hlabel : j ≫ cycleMap H Z k p = boundaryMap H Z k p := by
    dsimp only [j, cycleMap, boundaryMap, P, E]
    rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
  have hboundary : (P.pageπ k) (j b) = 0 := by
    have hj : j ≫ P.pageπ k = 0 := cokernel.condition _
    exact congrArg (fun f => f b) hj
  refine ⟨hR, z + j b, ?_, ?_⟩
  · change cycleMap H Z k p (z + j b) = y
    rw [map_add]
    have hzb : cycleMap H Z k p (j b) = y - x := by
      change (j ≫ cycleMap H Z k p) b = _
      rw [hlabel]
      exact hb
    rw [hzb]
    change cycleMap H Z k p z = x at hzx
    rw [hzx]
    abel
  · change P.pageπ k (z + j b) = xr
    rw [map_add, hboundary, add_zero]
    exact hzr

private theorem differentialAt_of_congruent {Z : C} {R : ℤ}
    {p q : ℤ × ℤ} {x : Ambient H Z p} {y z : Ambient H Z q}
    (hd : DifferentialAt H Z R p q x y)
    (hz : Congruent H Z (R - 1) q z y) :
    DifferentialAt H Z R p q x z := by
  obtain ⟨hR, hdeg, xr, yr, hx, hy, hdiff⟩ := hd
  exact ⟨hR, hdeg, xr, yr, hx, representsOnPage_of_congruent hR hy hz, hdiff⟩

open KIP126.Synthetic.SpectralSequence

private theorem lambda_target_class
    (synthetic : SyntheticComparisonTheorems D) (Y : ClassicalObject) (s t : ℤ) (k j : ℕ)
    (x : E2 H (Y.obj D.hopfAndDetector) s t)
    (hx : IsPermanent H (Y.obj D.hopfAndDetector) (s, t) x)
    (e : ((D.family.nu D.nu (Y.obj D.hopfAndDetector)).sequence.ssData (s, t, t - k)).eInfty)
    (he : HasInfinityRepresentative _ 2 (s, t, t - k) (targetNuLabel D Y s t k x) e) :
    synthetic.eInfty.presentation.nuWindow (Y.obj D.hopfAndDetector) (s, t) (t - k - j) (by omega)
      (synthetic.eInfty.weightShift.lambdaMap (D.nu.functor.obj (Y.obj D.hopfAndDetector)) j (s, t) (t - k) e) =
      KIP126.Algebra.NestedQuotient.projection _ _ ⟨x, hx⟩ := by
  have heq := (synthetic.eInfty.labels.2 Y (s, t) k ⟨x, hx⟩ e).mp he
  have hm := synthetic.eInfty.maps.lambda_nu (Y.obj D.hopfAndDetector) j (s, t) (t - k) (by omega) e
  rw [heq] at hm
  exact hm

/-- MainPaper Theorem 6.1. The applied comparison input supplies the synthetic
δ/λ/ρ comparisons; all differential, extension, and no-crossing premises
remain explicit in the conclusion's predicate. -/
theorem generalizedLeibniz (synthetic : SyntheticComparisonTheorems D)
    (X Y : ClassicalObject) (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector) :
    KIP126.AdamsSynthetic.ExtensionLaws.GeneralizedLeibnizLaw D X Y f := by
  intro page r m l s t x y xInfinity yInfinity hpage hpr hm hmUpper hl
    hx hy hxInfinity hyInfinity hdx hf hfInfinity hsourceCrossing htargetCrossing
  have hR : 2 ≤ r + l - m := by omega
  have hy_later : IsCycle H (Y.obj D.hopfAndDetector) (r + l - m - 1)
      (s + m, t + m) y := by
    by_cases hlmin : l = (normalizedExponent H f : ℤ)
    · convert hy using 1
      omega
    have hlstrict : (normalizedExponent H f : ℤ) < l := lt_of_le_of_ne hl (Ne.symm hlmin)
    -- Remaining geometric obligation (GL1), MainPaper 6.1, lines 1625–1650:
    -- synchronize the two source relations in the δ/f square using
    -- hsourceCrossing, then use htargetCrossing on its lower edge. The
    -- resulting δ-extension forces y to survive through d_(r+l-m-1).
    sorry
  let q : ℕ := (r + l - m - 1).toNat
  have hq : 0 < q := by dsimp only [q]; omega
  have hqZ : (q : ℤ) = r + l - m - 1 := Int.toNat_of_nonneg (by omega)
  have hyq : y ∈ cycles H (Y.obj D.hopfAndDetector) q (s + m, t + m) := by
    simpa only [hqZ] using hy_later.2
  obtain ⟨a, ha, hda⟩ := synthetic.bockstein Y q hq (s + m) (t + m) y hyq
  have htarget : (s + r + l, t + r - 1 + l) =
      (s + m + (q : ℤ) + 1, t + m + (q : ℤ)) := by
    ext <;> omega
  let yExpected : Ambient H (Y.obj D.hopfAndDetector)
      (s + m + (q : ℤ) + 1, t + m + (q : ℤ)) :=
    (eqToHom (congrArg (fun p => Ambient H (Y.obj D.hopfAndDetector) p) htarget)) yInfinity
  have htarget_congruent : Congruent H (Y.obj D.hopfAndDetector) q
      (s + m + (q : ℤ) + 1, t + m + (q : ℤ))
      yExpected (bocksteinLabel D Y q hq (s + m) (t + m) a) := by
    refine ⟨by omega, ?_⟩
    let W := Classical.choice hfInfinity
    have undo_label {p₁ p₂ : ℤ × ℤ × ℤ} (hp : p₁ = p₂)
        (z : (D.family.nu D.nu (Y.obj D.hopfAndDetector)).E₂ p₁)
        (e : ((D.family.nu D.nu (Y.obj D.hopfAndDetector)).sequence.ssData p₂).eInfty)
        (he : HasInfinityRepresentative _ 2 p₂ (regradeE2 hp z) e) :
        HasInfinityRepresentative (D.family.nu D.nu (Y.obj D.hopfAndDetector)) 2 p₁ z
          ((eqToHom (congrArg (fun p => ((D.family.nu D.nu
            (Y.obj D.hopfAndDetector)).sequence.ssData p).eInfty) hp.symm)) e) := by
      subst p₂
      exact he
    have ht := W.target_rep
    dsimp only [infiniteTargetForExtension] at ht
    have h_ungraded := undo_label _ _ _ ht
    have h_propagated_target := lambda_target_class D synthetic Y
      (s + r + l) (t + r - 1 + l) (l - normalizedExponent H f).toNat (r - page).toNat
      yInfinity hyInfinity _ h_ungraded
    have h_boundary_le :
        1 + (t + r - 1 + l) - ((t + r - 1 + l) -
          (l - normalizedExponent H f).toNat - (r - page).toNat) ≤ (q : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
      omega
    have h_propagated_target_q := congrArg
      (permanentQuotientMap H (Y.obj D.hopfAndDetector) h_boundary_le
        (s + r + l, t + r - 1 + l)) h_propagated_target
    -- Remaining geometric obligation (GL2), MainPaper 6.1, lines 1644–1652:
    -- h_propagated_target_q gives the λ^(r-page) target label in Z∞/B_q.
    -- Identify the propagated δ-extension target with this Bockstein lift's
    -- label modulo the actual B_q. This is the δ/classical differential
    -- comparison, with the λ exponents r-page and m-e(f) retained.
    -- GL1 supplies the Bockstein lift; GL2 and the proved representative
    -- congruence lemma then give the original differential equation.
    sorry
  have hchosen : DifferentialAt H (Y.obj D.hopfAndDetector) ((q : ℤ) + 1)
      (s + m, t + m) (s + m + (q : ℤ) + 1, t + m + (q : ℤ))
      y (bocksteinLabel D Y q hq (s + m) (t + m) a) := ⟨by omega, hda⟩
  have hfinal := differentialAt_of_congruent hchosen
    (by simpa only [add_sub_cancel_right] using htarget_congruent)
  have hRq : (q : ℤ) + 1 = r + l - m := by omega
  rw [hRq] at hfinal
  have undo_transport {p₁ p₂ : ℤ × ℤ} (hp : p₁ = p₂)
      (z : Ambient H (Y.obj D.hopfAndDetector) p₁)
      (h : DifferentialAt H (Y.obj D.hopfAndDetector) (r + l - m) (s + m, t + m) p₂ y
        ((eqToHom (congrArg (fun p => Ambient H (Y.obj D.hopfAndDetector) p) hp)) z)) :
      DifferentialAt H (Y.obj D.hopfAndDetector) (r + l - m) (s + m, t + m) p₁ y z := by
    subst p₂
    exact h
  exact undo_transport htarget yInfinity hfinal

end KIP126.Main.ExtensionLaws
