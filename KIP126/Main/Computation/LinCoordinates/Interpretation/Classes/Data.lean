module

public import KIP126.Main.Computation.LinCoordinates.Presentation

@[expose] public section

namespace KIP126.Classical.Adams

/-- Range-limited data coordinates on the fixed internal E₂. -/
noncomputable abbrev linToSphereE2 := linE2Presentation.comparison

/-- The fixed degree-(1,64) data class on the internal sphere page. -/
noncomputable def computedH6 : sphereAdamsData.Page 2 (1, 64) :=
  linToSphereE2 1 64 (by decide) KIP126.LinE2.dataH6

/-- A concrete data square mapped into the fixed SSData E₂, not an arbitrary
element postulated by name. Its data model contains no permanence assumption. -/
noncomputable def computedH6Square : sphereAdamsData.Page 2 (2, 128) :=
  linToSphereE2 2 128 (by decide) KIP126.LinE2.dataH6Sq

end KIP126.Classical.Adams
