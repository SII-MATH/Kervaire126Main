module

public import KIP126.Computation.LinCoordinates.Interpretation.SphereAndCofiber.Certification

@[expose] public section

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.SpectralSequence KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.LinE2
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}

/-- Recover the same seven conditions without reinterpreting the data. -/
theorem AdamsComputationTheorems.interpretationCorrect {D : AdamsComparison H M Syn} {L : SphereAdamsClasses H}
    {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I : AdamsComputationTheorems D L G) :
    E2InterpretationCorrect I.interpretation L G where
  basis := I.basis
  monomials := I.monomials
  products := I.products
  distinguishedClasses := I.distinguishedClasses
  adamsStatements := I.adamsStatements
  cofiberInclusion := I.cofiberInclusion
  cofiberBoundary := I.cofiberBoundary

end
end KIP126.Computation.SphereAndCofiber
