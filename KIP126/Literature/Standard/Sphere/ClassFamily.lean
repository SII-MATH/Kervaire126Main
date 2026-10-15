module

public import KIP126.Literature.Standard.Sphere.Classes
public import KIP126.Def.ClassicalAdams.SphereClasses.Hi.Internal.Data

@[expose] public section

/-! Standard Milnor hᵢ and its square in the fixed actual sphere Adams E₂. -/
namespace KIP126.Classical.Adams
open KIP126.Classical.Adams

/-- am9：由同一固定塔及 Milnor cocycle 构造的标准族；没有新的类选择。 -/
noncomputable def standardHi (i : ℕ) :
    sphereAdamsData.Page 2 (1, ((2 ^ i : ℕ) : ℤ)) :=
  Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations i

/-- 标准平方是同一 Milnor cocycle 的 concatenation square 的内部 E₂ 类。
与固定 Lin 计算类的识别仍是另一个比较义务。 -/
noncomputable def standardHiSquare (i : ℕ) :
    sphereAdamsData.Page 2 (2, ((2 ^ (i + 1) : ℕ) : ℤ)) :=
  Sphere.Internal.hiSquare standardFoundation.hf2 standardMilnorCooperations i

end KIP126.Classical.Adams
