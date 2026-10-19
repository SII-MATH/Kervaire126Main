module

public import KIP126.ProofTools.Stretching
public import KIP126.ProofTools.GeneralizedLeibniz
public import KIP126.ProofTools.GeneralizedMahowald
public import KIP126.ProofTools.GeneralizedMahowald.ZeroLayerSpecial

/-! Fixed callable paper tools. The refuted zero-layer GL/MH theorems were
retired; their law definitions and counterexample evidence remain. The proved
level-aware versions are exported by KIP126.ProofTools. Main uses the proved
zero-layer nu-cofiber instance defined in ZeroLayerSpecial. Upstream construction
and external-result duties stay in the modules that supply those interfaces. -/
