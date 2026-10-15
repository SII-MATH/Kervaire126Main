module

public import KIP126.Main.Literature.Near126.Sphere.Conditions.Predicates
public import KIP126.Main.Literature.Near126.Sphere.Data
public import KIP126.Def.SpectralSequence.Computation.Proofs

@[expose] public section

namespace KIP126.Computation.Near126
open CategoryTheory KIP126.Classical.Adams KIP126.SpectralSequence

/-- The table-facing notation and the fixed final class denote exactly the
same d₁₂ condition; this does not use any differential evidence. -/
theorem Sphere.d12_iff_differential :
    Sphere.H6SquareSupportsD12 ↔ Sphere.Differential 12 KIP126.LinE2.dataH6Sq T := by
  constructor
  · intro h
    exact ⟨by decide, by decide, h⟩
  · rintro ⟨_, _, h⟩
    exact h

/-- Under the explicit survival and exhaustive target inputs, failure of Stem126D6Vanishes
means the actual d₆ hits T. No new source fact or reduction axiom is used. -/
theorem SphereSurvivalFacts.d6_vanishes_iff_not_nonzero_d6 (F : SphereSurvivalFacts) :
    Sphere.Stem126D6Vanishes ↔ ¬ Sphere.Differential 6 W T := by
  have hvanish := differentialVanishesOn_iff_not_hasNonzeroDifferential
    (E := sphereAdamsData) (r := 6) (p := (8, 134))
    (x := linToSphereE2 8 134 (by decide) W)
    (linToSphereE2 14 139 (by decide) T) F.w_d6_targets
  constructor
  · rintro ⟨_, hz⟩ ⟨_, _, h⟩
    exact hvanish.mp hz h
  · intro hn
    refine ⟨F.w_to_e6, hvanish.mpr ?_⟩
    exact fun h => hn ⟨by decide, by decide, h⟩

/-- With Stem126D6Vanishes, the complete incoming-exhaustion input for T reduces to the
fixed nonzero d₁₂ alternative. This is not a proof that H6SquareSupportsD12 is false. -/
theorem SphereSurvivalFacts.hit_t_iff_d12 (F : SphereSurvivalFacts)
    (hc3 : Sphere.Stem126D6Vanishes) (r : ℤ) :
    HitOnPage sphereAdamsData r (14, 139)
        (linToSphereE2 14 139 (by decide) T) ↔
      r = 12 ∧ Sphere.H6SquareSupportsD12 := by
  constructor
  · intro h
    rcases F.t_only_incoming r h with ⟨_, h6⟩ | ⟨hr, h12⟩
    · exact False.elim ((F.d6_vanishes_iff_not_nonzero_d6.mp hc3) h6)
    · exact ⟨hr, Sphere.d12_iff_differential.mpr h12⟩
  · rintro ⟨rfl, h12⟩
    exact h12.hit_target

end KIP126.Computation.Near126
