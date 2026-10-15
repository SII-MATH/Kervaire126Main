module

public import KIP126.Def.ClassicalAdams.Context.Data
public import KIP126.Literature.Background.HF2Completion

@[expose] public section

/-! Existence assumption for the standard classical mod-two Adams context.
The context includes an HF₂-local stable category, its mod-two coefficient
object and Milnor coordinates, and the compatible tensor and cooperation
structures. Its equivalence with HF₂-local prespectra preserves the specified
suspensions, cofibers, homotopy groups and smash product.
This module assumes existence of all these data together. -/
namespace KIP126.AdamsSynthetic

/-- Existence of an HF₂ Adams context with compatible Milnor coordinates
and the specified HF₂-local stable homotopy interpretation. -/
axiom hf2AdamsContext_exists : Nonempty (KIP126.HF2AdamsContext KIP126.StableHomotopy.Spectra.completionModel)

end KIP126.AdamsSynthetic
