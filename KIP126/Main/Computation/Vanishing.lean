module

public import KIP126.Literature.Standard.Sphere.Sequence
public import KIP126.Def.ClassicalAdams.SphereVanishing.Proofs

@[expose] public section

namespace KIP126.Classical.Adams

open KIP126.StableHomotopy KIP126.SpectralSequence

/-- All incoming-differential sources for the fixed `(2,128)` component vanish.
The proof uses the tower and the Eilenberg--Mac Lane property, not Milnor
coordinates or the Lin table. -/
theorem sphereAdamsData_h6_incoming_source_subsingleton (r : ℤ) (hr : 2 ≤ r) :
    Subsingleton (sphereAdamsData.Page r ((2, 128) - sphereAdamsData.diffDeg r)) :=
  sphereAdamsInternal_h6_incoming_source_subsingleton standardFoundation.hf2 r hr

/-- A proved no-incoming-differential fact for downstream internal SSData reasoning. -/
theorem sphereAdamsData_h6_incoming_d_eq_zero (r : ℤ) (hr : 2 ≤ r) :
    sphereAdamsData.d r ((2, 128) - sphereAdamsData.diffDeg r) = 0 :=
  sphereAdamsInternal_h6_incoming_d_eq_zero standardFoundation.hf2 r hr

/-- The fixed computational target reduces to initial nonvanishing and a
representative lifting through every stage of its actual Adams tower. -/
theorem sphereAdamsData_h6_nonzeroSurvival_iff (x : sphereAdamsData.Page 2 (2, 128)) :
    NonzeroSurvival sphereAdamsData (2, 128) x ↔
      x ≠ 0 ∧ ∃ z : adamsCycleAmbient standardFoundation.hf2.unit SphereSpectrum 2 128,
        (∀ n : ℕ, z.val ∈ adamsCycles standardFoundation.hf2.unit SphereSpectrum
          (n + 2) (by omega) 2 128) ∧
        (adamsCycleBoundaries standardFoundation.hf2.unit SphereSpectrum
          2 (by decide) 2 128).mkQ z =
          (adamsTowerSSDataPageIso standardFoundation.hf2.unit SphereSpectrum 2 128 0).hom x :=
  sphereAdams_h6_nonzeroSurvival_iff standardFoundation.hf2 x

end KIP126.Classical.Adams
