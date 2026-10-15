module

public import KIP126.Main.Literature.Near126.Sphere.Data
public import KIP126.Def.SpectralSequence.Computation.Proofs

@[expose] public section

namespace KIP126.Computation.Near126
open KIP126.Classical.Adams
open KIP126.SpectralSequence

/-- Either possible target gives a nonzero d₃ in the fixed Adams sequence. -/
theorem SphereDifferentialFacts.d3_x_126_6_ne_zero (F : SphereDifferentialFacts) :
    sphereAdamsData.d 3 (6, 132) ≠ 0 := by
  rcases F.d3_x_126_6_candidates with h | h
  · obtain ⟨_, _, h⟩ := h
    exact h.d_ne_zero
  · obtain ⟨_, _, h⟩ := h
    exact h.d_ne_zero

/-- An example of a usable non-hitting input, at every admissible page. -/
theorem SphereSurvivalFacts.y_not_hit_on_page (F : SphereSurvivalFacts)
    (r : ℤ) (hr : 2 ≤ r) :
    ¬ HitOnPage sphereAdamsData r (11, 136)
      (linToSphereE2 11 136 (by decide) Y) := by
  obtain ⟨_, h⟩ := F.y_not_hit
  exact h.not_hit hr

end KIP126.Computation.Near126
