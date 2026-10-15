module

public import KIP126.Def.ClassicalAdams.SSDataModel.Data
public import KIP126.Literature.Standard.Foundation
public import KIP126.Def.ClassicalAdams.TowerSSData.Sequence.Data

@[expose] public section

namespace KIP126.Classical.Adams

open KIP126.StableHomotopy

/-- The internal sphere Adams sequence constructed from the foundation in M.
This specializes the actual sphere tower; it does not select a second sequence
or require a Lin presentation, CSV basis certificate, or computed differential.
The classical H𝔽₂ context is fixed using the explicit background existence
assumption. -/
noncomputable def sphereAdamsSequence : AdamsSSData where
  sequence := adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum
  firstPage := rfl
  differentialDegree _ := rfl

/-- The same internal sequence used by both the standard h₆² statement and the external computation hypotheses. -/
noncomputable abbrev sphereAdamsData := sphereAdamsSequence.sequence

end KIP126.Classical.Adams
