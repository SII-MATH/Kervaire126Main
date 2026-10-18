module

public import KIP126.ProofTools.Stretching
public import KIP126.ProofTools.GeneralizedLeibniz
public import KIP126.ProofTools.GeneralizedMahowald
public import KIP126.ProofTools.GeneralizedMahowald.ZeroLayerSpecial

/-! Fixed callable paper tools. The remaining general GL1/GL2 and MH2
obligations stay registered in their original theorem bodies. Main uses the
proved zero-layer nu-cofiber instance defined in ZeroLayerSpecial. Upstream construction and
external-result duties stay in the modules that supply those interfaces. -/
