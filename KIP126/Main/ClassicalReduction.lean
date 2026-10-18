module

public import KIP126.Main.Conditions
import all KIP126.Main.Internal.PageCalculus

/-! Classical part of Proposition 7.8, adapted from Selected/ClassicalData
at bbac1fc05843 (MIT; see the retained source LICENSE). The fixed computation facts are called directly;
no dataset, literature witness or result package is a theorem parameter. -/
@[expose] section
namespace KIP126.Main
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Classical.Adams
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Standard (model)
open KIP126.Computation.Standard (W T)
open Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem earlier_zero_at
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ)}
    {r t : ℤ} {p q : ℤ × ℤ} {x : E.Page 2 p} {y : E.Page 2 q}
    (hdeg : p + E.diffDeg r = q) (hr0 : E.r₀ ≤ r) (hrt : r < t)
    (hx : SurvivesTo E r p x)
    (htargets : DifferentialTargets E r p x
      (Eq.mp (congrArg (fun d => ↥(E.Page 2 d)) hdeg.symm) y))
    (hy : SurvivesTo E t q y) : HasDifferential E r p q x 0 := by
  subst q
  exact earlier_zero_of_target_survives hr0 hrt hx htargets hy

private theorem sphere_start : model.classical.sphere.r₀ = 2 :=
  model.classical.firstPage SphereSpectrum

private theorem sixth_degree : (8,134) + model.classical.sphere.diffDeg 6 = (14,139) := by
  simp only [ClassicalAdamsFamily.sphere, ClassicalAdamsFamily.obj,
    model.classical.differentialDegree, Prod.mk_add_mk, Int.reduceSub, Int.reduceAdd]

/-- The target's nonvanishing follows from the recorded nonmultiplicity fact. -/
private theorem target_nonzero : T ≠ 0 := by
  intro hz
  apply KIP126.Computation.Standard.t_not_h0_multiple
  refine ⟨0, ?_⟩
  simp only [KIP126.Computation.Standard.product, map_zero, hz]

/-- Paper condition (3) is exactly survival of T to E12. -/
private theorem d6_vanishes_iff_target_survives_twelve :
    Stem126D6Vanishes ↔ SurvivesTo model.classical.sphere 12 (14,139) T := by
  constructor
  · intro hc3
    apply permanent_survives_of_no_early_hit (by rw [sphere_start])
      12 (by decide) KIP126.Computation.Standard.t_permanent_cycle target_nonzero
    intro r hr hr12 hit
    rcases KIP126.Computation.Standard.t_only_incoming r hit with ⟨he,hd⟩ | ⟨he,_⟩
    · subst r
      exact nonzero_differential_not_zero hd hc3
    · omega
  · intro hs
    exact earlier_zero_at sixth_degree (by rw [sphere_start]; decide) (by decide)
      KIP126.Computation.Standard.w_to_e6 KIP126.Computation.Standard.w_d6_targets hs

/-- A nonzero d12 excludes permanent survival and forces condition (3). -/
private theorem d12_necessary (hd : H6SquareSupportsD12) : ¬ H6SquarePermanent ∧ Stem126D6Vanishes := by
  refine ⟨nonzero_differential_not_permanent (E := model.classical.sphere)
    (by rw [sphere_start]; decide) hd, ?_⟩
  exact d6_vanishes_iff_target_survives_twelve.mpr hd.target_survives

end
end KIP126.Main
