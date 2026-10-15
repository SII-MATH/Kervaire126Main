module

public import KIP126.Computation.LinCoordinates.Interpretation.Near126.Classes.Data
public import KIP126.Main.Computation.LinCoordinates.Interpretation.Classes.Data
public import KIP126.Main.Literature.HopfCofiber.Predicates
public import KIP126.Main.Literature.HopfCofiber.Pages.Data

@[expose] public section

namespace KIP126.Computation.Near126
open KIP126.Classical.Adams

/-- Explicit missing geometric input on the already fixed sphere. Its h₂
condition is a statement about an actual filtration-one tower lift, not a
name, an arbitrary page map, or a freely chosen hopfAndDetector spectral sequence.
There is no global inhabitant or claim that h₂ detection chooses a unique ν. -/
structure H2DetectedSphereMap where
  map : SphereThreeMap
  represents_h2 :
    (SphereFiltrationOneRepresents map (linToSphereE2 1 4 (by decide) (atom .h2)))

noncomputable def H2DetectedSphereMap.ybar (N : H2DetectedSphereMap) :=
  sphereMapCofiberBottomE2 N.map (11, 136) (linToSphereE2 11 136 (by decide) Y)

noncomputable def H2DetectedSphereMap.tbar (N : H2DetectedSphereMap) :=
  sphereMapCofiberBottomE2 N.map (14, 139) (linToSphereE2 14 139 (by decide) T)

/-- The bottom-cell correction is fixed by the CSV and induced inclusion.
The remaining topLift must still be identified with X[4] using the top-cell
map and a suspension comparison; no such identification is asserted here. -/
noncomputable def H2DetectedSphereMap.xbar (N : H2DetectedSphereMap)
    (topLift : (sphereMapCofiberAdams N.map).Page 2 (8, 134)) :=
  topLift + sphereMapCofiberBottomE2 N.map (8, 134)
    (linToSphereE2 8 134 (by decide) (atom .x_126_8)) +
    sphereMapCofiberBottomE2 N.map (8, 134)
      (linToSphereE2 8 134 (by decide) (atom .x_126_8_2))

/-- The cofiber sequence and bottom-cell classes are now determined by the
fixed sphere and N.map. The topLift comparison and all external evidence
values are still explicit outstanding inputs. -/
abbrev H2DetectedSphereMap.ComputationFacts (N : H2DetectedSphereMap)
    (topLift : (sphereMapCofiberAdams N.map).Page 2 (8, 134)) :=
  HopfCofiberFacts (sphereMapCofiberAdams N.map) (N.xbar topLift) N.ybar N.tbar

end KIP126.Computation.Near126
