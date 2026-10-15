module

public import KIP126.Literature.Standard.Sphere.Sequence
public import KIP126.Computation.Tmf.Model.Predicates
public import KIP126.Computation.Tmf.Presentation.Algebra.Data

@[expose] public section

namespace KIP126.Classical.Adams
open Classical.Adams

/-- am14 的单位与乘法比较义务，约束已选的同一个 target/coordinates。
乘法使用实际 Adams 层配对及 target.mul；不再容许独立选择一个页面乘法。
所有张量、HF₂ 环结构及相容性都属于同一个固定 Adams 背景。 -/
def StandardTmfMultiplicationComparison
    (T : TmfAdamsPresentation standardFoundation.hf2) : Prop :=
  let c := KIP126.AdamsSynthetic.Standard.classicalContext
  letI : Foundation.TensorTriangulatedStructure c.stableContext := c.tensorStructure
  T.coordinates.RespectsUnit ∧
    Tmf.E2Presentation.RespectsMultiplication c.cooperationStructure.ring T.coordinates

end KIP126.Classical.Adams
