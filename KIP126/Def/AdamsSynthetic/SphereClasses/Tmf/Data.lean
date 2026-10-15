module

public import KIP126.Def.AdamsSynthetic.SphereClasses.Data

@[expose] public section

namespace KIP126.Literature.AdamsSynthetic
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
open KIP126.AdamsSynthetic
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)}

/-- The two classical sphere E₂ classes used in the tmf detection argument.
Their identification with the fixed CSV expressions is a computation
hypothesis. The expression g⁴Δh₁g uses these classes and the same product.
Source convention: BMQ §7, g detects κ̄ and Δh₁g detects w. -/
structure TmfDetectionClasses (H : Mod2EilenbergMacLane (C := C)) where
  g : E2 H SphereSpectrum 4 24
  delta_h_1_mul_g : E2 H SphereSpectrum 9 54

def TmfDetectionClasses.high125 (L : TmfDetectionClasses H) (M : MilnorCooperations H) :
    E2 H SphereSpectrum 25 150 :=
  let g_sq : E2 H SphereSpectrum 8 48 :=
    Sphere.Internal.product H M (s := 4) (t := 24) (s' := 4) (t' := 24) L.g L.g
  let g_pow_four : E2 H SphereSpectrum 16 96 :=
    Sphere.Internal.product H M (s := 8) (t := 48) (s' := 8) (t' := 48) g_sq g_sq
  Sphere.Internal.product H M (s := 16) (t := 96) (s' := 9) (t' := 54) g_pow_four L.delta_h_1_mul_g

end
end KIP126.Literature.AdamsSynthetic
