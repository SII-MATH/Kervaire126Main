module

public import KIP126.Main.Computation.Nonvanishing
public import KIP126.Main.Computation.Vanishing

@[expose] public section

namespace KIP126.Classical.Adams

open KIP126.StableHomotopy KIP126.SpectralSequence

/-- Initial nonvanishing and absence of incoming differentials are proved.
The remaining computational target is precisely all-stage liftability in
the chosen actual tower. This equivalence does not assume that liftability. -/
theorem computedH6Square_nonzeroSurvival_iff :
    NonzeroSurvival sphereAdamsData (2, 128) computedH6Square ↔
      ∃ z : adamsCycleAmbient standardFoundation.hf2.unit SphereSpectrum 2 128,
        (∀ n : ℕ, z.val ∈ adamsCycles standardFoundation.hf2.unit SphereSpectrum
          (n + 2) (by omega) 2 128) ∧
        (adamsCycleBoundaries standardFoundation.hf2.unit SphereSpectrum
          2 (by decide) 2 128).mkQ z =
          (adamsTowerSSDataPageIso standardFoundation.hf2.unit SphereSpectrum 2 128 0).hom
            computedH6Square := by
  exact (sphereAdamsData_h6_nonzeroSurvival_iff computedH6Square).trans
    (and_iff_right computedH6Square_ne_zero)

end KIP126.Classical.Adams
