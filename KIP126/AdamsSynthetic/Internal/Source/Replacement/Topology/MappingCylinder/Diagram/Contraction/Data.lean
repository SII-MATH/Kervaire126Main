module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.MappingCylinder.Diagram.Data

@[expose] section

namespace KIP126.Topology.MappingCylinder
open CategoryTheory CategoryTheory.Limits
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Move a cylinder parameter linearly toward its final endpoint. -/
def contractionTime : C(I × I,I) := ⟨fun z => ⟨(z.2 : ℝ)+(1-z.2)*z.1,by
  constructor
  · nlinarith [z.1.property.1,z.1.property.2,z.2.property.1,z.2.property.2]
  · nlinarith [z.1.property.1,z.1.property.2,z.2.property.1,z.2.property.2]⟩,by fun_prop⟩

end KIP126.Topology.MappingCylinder
