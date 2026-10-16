module

public import KIP126.Def.ProofTools.Stretching
public import KIP126.Def.ProofTools.GeneralizedLeibniz
public import KIP126.Def.ProofTools.GeneralizedMahowald
import all KIP126.Def.ProofTools.GeneralizedMahowald.ZeroLayerSpecial

/-! Fixed callable paper tools. The remaining general GL1/GL2 and MH2
obligations stay registered in their original theorem bodies. Main uses the
proved zero-layer nu-cofiber instance below. Upstream construction and
external-result duties stay in the modules that supply those interfaces. -/

namespace KIP126.ProofTools.Standard
/-- The proved zero-layer nu-cofiber instance used by Main. -/
public alias nuCofiberMahowaldZeroLayer :=
  KIP126.ProofTools.Internal.Mahowald.main_nu_mahowald_zero_layer
end KIP126.ProofTools.Standard
