module

public import KIP126.Computation.Hypotheses
public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Hi.Proofs
public import KIP126.Main.Computation.LinCoordinates.Certificates.AdamsOneLine.H6Coordinates

@[expose] public section


/-! The Adams one-line differential d₂(h₆) = h₀h₅² on the standard sphere,
with the coordinates of computation-log record 5541.

Both coordinate identifications follow from degree exhaustion and
nonvanishing of the specified classes. The argument requires no general
identification between multiplication in the presentation and the canonical
cobar cup product. The Adams one-line theorem is an explicit literature
hypothesis; the lemmas here prove its coordinate interpretation.
-/

namespace KIP126.Main.Computation.LinCoordinates

open CategoryTheory KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.LinE2

/-- The data source spans the full degree-(1,64) component of actual E₂. -/
theorem sphereH6_exhaustive (P : LinE2Presentation)
    (x : sphereAdamsData.Page 2 (1, 64)) :
    x = 0 ∨ x = P.comparison 1 64 (by decide) dataH6 := KIP126.Algebra.LinearEquiv.zero_or_of_exhaustion
    (P.comparison 1 64 (by decide)) dataH6 OneLineH6.source_eq_zero_or x

/-- CSV h₆ denotes the existing standard Milnor class. -/
theorem sphereH6_standard_class (P : LinE2Presentation) :
    P.comparison 1 64 (by decide) dataH6 =
      Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 6 := KIP126.Algebra.LinearEquiv.image_eq_of_exhaustion
    (P.comparison 1 64 (by decide)) dataH6 OneLineH6.source_eq_zero_or _
    (MilnorCohomology.internal_hi_ne_zero standardFoundation.hf2 standardMilnorCooperations 6)

/-- Degree-(3,65) exhaustion is a mathematical consequence of the fixed
quotient's generating degrees, without assuming a CSV basis certificate. -/
theorem sphereH0H5Sq_exhaustive (P : LinE2Presentation)
    (x : sphereAdamsData.Page 2 (3, 65)) :
    x = 0 ∨ x = P.comparison 3 65 (by decide) OneLineH6.target := KIP126.Algebra.LinearEquiv.zero_or_of_exhaustion
    (P.comparison 3 65 (by decide)) OneLineH6.target OneLineH6.target_eq_zero_or x

/-- The explicit literature result certifies nonvanishing of the canonical
target. At page two its page representative is the same element. -/
theorem sphereH0H5Sq_ne_zero
    (literature : KIP126.ExternalHypotheses.LiteratureHypotheses) :
    Sphere.Internal.h0HiSquare standardFoundation.hf2 standardMilnorCooperations 5 ≠ 0 := by
  have h := literature.theorems.adamsOneLine_d2 6 (by decide)
  obtain ⟨_, _, yr, _, hy, _, hne⟩ := h
  exact fun hz => hne (hy.eq_on_page_two.symm.trans hz)

/-- CSV h₀h₅² denotes the canonical cobar target using its unique nonzero
class. No general comparison of the two multiplications is assumed. -/
theorem sphereH0H5Sq_standard_class
    (literature : KIP126.ExternalHypotheses.LiteratureHypotheses) (P : LinE2Presentation) :
    P.comparison 3 65 (by decide) OneLineH6.target =
      Sphere.Internal.h0HiSquare standardFoundation.hf2 standardMilnorCooperations 5 := KIP126.Algebra.LinearEquiv.image_eq_of_exhaustion
    (P.comparison 3 65 (by decide)) OneLineH6.target OneLineH6.target_eq_zero_or _
    (sphereH0H5Sq_ne_zero literature)

/-- Exact original source CSV coordinates. -/
theorem h6_hasCoordinates : KIP126.ExternalHypotheses.HasCoordinates dataH6 [0] := by
  refine ⟨[OneLineH6.sourceRow], rfl, ?_, ?_⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact ⟨OneLineH6.sourceRow_mem, rfl, rfl⟩
  · simpa only [List.map_singleton, List.sum_singleton] using OneLineH6.source_value

/-- Exact original target CSV coordinates. -/
theorem h0h5Sq_hasCoordinates :
    KIP126.ExternalHypotheses.HasCoordinates OneLineH6.target [0] := by
  refine ⟨[OneLineH6.targetRow], rfl, ?_, ?_⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact ⟨OneLineH6.targetRow_mem, rfl, rfl⟩
  · simpa only [List.map_singleton, List.sum_singleton] using OneLineH6.target_value

/-- The table's specified source and nonzero target satisfy the differential
in the fixed sphere Adams sequence, using the literature theorem and the
same coordinate presentation. -/
theorem row5541_hasNonzeroDifferential
    (literature : KIP126.ExternalHypotheses.LiteratureHypotheses) (P : LinE2Presentation) :
    HasNonzeroDifferential sphereAdamsData 2 (1, 64) (3, 65)
      (P.comparison 1 64 (by decide) dataH6)
      (P.comparison 3 65 (by decide) OneLineH6.target) := by
  rw [sphereH6_standard_class, sphereH0H5Sq_standard_class literature]
  exact literature.theorems.adamsOneLine_d2 6 (by decide)

/-- The same source cannot have a zero d₂ target. This rejects changing the
record's nonzero target into the empty coordinate vector. -/
theorem row5541_rejects_zero
    (literature : KIP126.ExternalHypotheses.LiteratureHypotheses) (P : LinE2Presentation) :
    ¬ HasDifferential sphereAdamsData 2 (1, 64) (3, 65)
      (P.comparison 1 64 (by decide) dataH6) 0 := by
  intro hz
  obtain ⟨_, hd⟩ :=
    (row5541_hasNonzeroDifferential literature P).toHasDifferential.eq_on_page_two
  obtain ⟨_, hzero⟩ := hz.eq_on_page_two
  have htargetzero := hd.symm.trans hzero
  rw [sphereH0H5Sq_standard_class literature] at htargetzero
  exact sphereH0H5Sq_ne_zero literature htargetzero

set_option maxHeartbeats 2000000 in
/-- Full mathematical interpretation of proofs.db row 5541, retaining both
literal coordinate checks and page-representative obligations. -/
theorem row5541 (literature : KIP126.ExternalHypotheses.LiteratureHypotheses)
    (P : LinE2Presentation) :
    KIP126.ExternalHypotheses.DifferentialStatement P ⟨5541, "d2", 1, 64, 2, [0], [0]⟩ := by
  obtain ⟨h, xr, yr, hx, hy, hd⟩ :=
    (row5541_hasNonzeroDifferential literature P).toHasDifferential
  dsimp only [KIP126.ExternalHypotheses.DifferentialStatement]
  refine ⟨by decide, by decide, dataH6, OneLineH6.target,
    h6_hasCoordinates, h0h5Sq_hasCoordinates, h, xr, yr, ?_, ?_, ?_⟩
  · exact hx
  · exact hy
  · exact hd

end KIP126.Main.Computation.LinCoordinates
