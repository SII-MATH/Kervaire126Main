module

public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Main.Computation.LinCoordinates.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Main.Computation.SphereAndCofiber.Staircase


import all Init.Data.String.Search
import all Init.Data.String.Slice

import all Init.Data.String.Legacy

@[expose] public section


/-! Filtration and representative calculations for Proposition 7.8 and
Lemma 7.14 (`lem:x_123_9`). The complete bases, products and differential
calculations refer to the same standard sphere as the literature hypotheses.
These lemmas derive the required homotopy relations from those inputs. -/
namespace KIP126.Main.SectionSeven
open KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic
noncomputable section

-- Preserve the outer local attribute preceding this section in AlphaOne.
attribute [local irreducible] KIP126.LinE2.homogeneousPart
section AlphaOneStaircaseProof
open CategoryTheory
open KIP126.LinE2 KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.ExternalHypotheses KIP126.Computation.LinCalculations KIP126.Computation.SphereAndCofiber
set_option maxRecDepth 10000
private theorem stem124_filtration_fourteen_fifteen_permanent_cycles {literature : LiteratureHypotheses}
    (c : ComputationHypotheses literature)
    (V : SphereVanishingLine standardFoundation.hf2) :
    IsPermanentCycle (sequence standardAdamsComparison .sphere) (14,138)
      (c.sphereAndCofiber.interpretation.basis .sphere 14 138 2) ∧
    IsPermanentCycle (sequence standardAdamsComparison .sphere) (15,139)
      (c.sphereAndCofiber.interpretation.basis .sphere 15 139 1 + c.sphereAndCofiber.interpretation.basis .sphere 15 139 3) := by
  constructor
  · exact permanent_cycle_of_reaches1000 V 14 138 (by norm_num) (by norm_num) _
      (staircase_af14_reaches1000 c)
  · exact permanent_cycle_of_reaches1000 V 15 139 (by norm_num) (by norm_num) _
      (staircase_af15_reaches1000 c)

end AlphaOneStaircaseProof

end
end KIP126.Main.SectionSeven
