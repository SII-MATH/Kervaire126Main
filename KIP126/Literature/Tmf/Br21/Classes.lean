module

public import KIP126.Def.StableHomotopy.Cohomology.Data

public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Data

@[expose] public section

/-! Source endpoint classes for BR21, before any program-coordinate comparison. -/
namespace KIP126.Classical.Adams.Tmf
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- The source's w₂² and βg⁴ in its actual HF₂-Adams E₂.
Their identification with the fixed program expressions requires an external
computation comparison. -/
structure Br21Classes (H : Mod2EilenbergMacLane (C := C)) (X : C) where
  v2Sixteen : (adamsTowerInternalSpectralSequence H.unit X).Page 2 (16, 112)
  betaGFour : (adamsTowerInternalSpectralSequence H.unit X).Page 2 (19, 114)

end KIP126.Classical.Adams.Tmf
