module

public import KIP126.Def.ClassicalAdams.SphereClasses.Product.Proofs
public import KIP126.Computation.LinCoordinates.Certificates.Model.RelationCertificates
public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Computation.LinCoordinates.Interpretation.SphereAndCofiber.Consequences

/-! Stable sphere filtration bounds and passage to permanent survival. -/

@[expose] public section

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory.Limits KIP126.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
open KIP126.SpectralSequence.FinitePageCalculus
open KIP126.LinE2.RelationCertificates
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.LinE2 KIP126.Computation.Near126
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

variable {D : AdamsComparison H M Syn} {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}

/-- At n=125 the exact arithmetic is 125 < 2*65-3=127.  No claim is
inferred merely from the absence of rows past the file's t=261 cutoff. -/
theorem sphere_page_zero_stem125_tail (V : SphereVanishingLine H)
    (r s : ℤ) (hr : 2 ≤ r) (hs : 65 ≤ s) :
    Subsingleton ((sequence D .sphere).Page r (s,s+125)) := by
  exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum
    2 r s (s+125) (by omega) hr (V s (s+125) (by omega) (by omega))

/-- Late outgoing differentials from all relevant positive-stem classes
have zero actual target page.  This supplies the missing infinite tail of
an honest finite `ReachesPage 1000` record. -/
theorem late_outgoing_target_zero (V : SphereVanishingLine H)
    (s t : ℕ) (hn : 1 < (t : ℤ) - s) (hn' : (t : ℤ) - s ≤ 127)
    (r : ℤ) (hr : 1000 ≤ r) :
    Subsingleton ((sequence D .sphere).Page r ((s : ℤ)+r,(t : ℤ)+r-1)) := by
  exact adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum
    2 r ((s : ℤ)+r) ((t : ℤ)+r-1) (by omega) (by omega)
    (V _ _ (by omega) (by omega))

/-- A single finite-page common representative, together with eventual
zero outgoing targets, gives a single representative in the actual Z-infinity
intersection.  This conclusion intentionally allows an incoming boundary. -/
theorem permanent_cycle_of_reaches1000 (V : SphereVanishingLine H)
    (s t : ℕ) (hn : 1 < (t : ℤ) - s) (hn' : (t : ℤ) - s ≤ 127)
    (x : E2 H SphereSpectrum s t)
    (hx : ReachesPage (sequence D .sphere) 1000 (s,t) x) :
    IsPermanentCycle (sequence D .sphere) (s,t) x := by
  apply isPermanentCycle_of_reachesPage (sequence D .sphere) 1000
    (by change (2 : ℤ) ≤ 1000; omega) (s, t) x hx
  intro r hr
  haveI : Subsingleton ((sequence D .sphere).Page r
      (((s : ℤ), (t : ℤ)) + (sequence D .sphere).diffDeg r)) := by
    change Subsingleton ((sequence D .sphere).Page r ((s : ℤ) + r, (t : ℤ) + (r - 1)))
    simpa only [add_sub_assoc] using late_outgoing_target_zero (D := D) V s t hn hn' r hr
  ext y
  exact Subsingleton.elim _ _

/-- Nonzero permanence needs nonzero survival to E1000.  For s<1000 every
later incoming source has negative filtration; the actual tower vanishing
lemma excludes it.  E2 nonzero or `ReachesPage` alone is not this hypothesis. -/
theorem nonzero_permanent_of_survives1000 (V : SphereVanishingLine H)
    (s t : ℕ) (hs : s < 1000)
    (hn : 1 < (t : ℤ) - s) (hn' : (t : ℤ) - s ≤ 127)
    (x : E2 H SphereSpectrum s t)
    (hx : SurvivesTo (sequence D .sphere) 1000 (s,t) x) :
    NonzeroSurvival (sequence D .sphere) (s,t) x := by
  apply nonzeroSurvival_of_survivesTo (sequence D .sphere) 1000
    (by change (2 : ℤ) ≤ 1000; omega) (s, t) x hx
  · intro r hr
    haveI : Subsingleton ((sequence D .sphere).Page r
        (((s : ℤ), (t : ℤ)) + (sequence D .sphere).diffDeg r)) := by
      change Subsingleton ((sequence D .sphere).Page r ((s : ℤ) + r, (t : ℤ) + (r - 1)))
      simpa only [add_sub_assoc] using late_outgoing_target_zero (D := D) V s t hn hn' r hr
    ext y
    exact Subsingleton.elim _ _
  · intro r hr
    haveI : Subsingleton ((sequence D .sphere).Page r
        (((s : ℤ), (t : ℤ)) - (sequence D .sphere).diffDeg r)) :=
      adamsTowerInternal_page_subsingleton_of_negative H.unit SphereSpectrum
        r ((s : ℤ) - r) ((t : ℤ) - (r - 1)) (by omega)
    ext y
    change (sequence D .sphere).d r _ y = 0
    rw [Subsingleton.elim y 0, map_zero]

end
end KIP126.Computation.SphereAndCofiber
end
