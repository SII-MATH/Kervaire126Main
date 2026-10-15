module

public import KIP126.Computation.LinCoordinates.Model.E2.Data

@[expose] public section

namespace KIP126.LinE2

theorem generatorDegree_eq_row (i : Generator) :
    generatorDegree i = (RawData.generatorRow i.val).2 := by
  simp [generatorDegree, RawData.generators, i.isLt]

end KIP126.LinE2
