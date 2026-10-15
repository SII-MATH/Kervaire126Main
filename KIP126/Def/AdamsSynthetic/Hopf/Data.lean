module

public import KIP126.Def.AdamsSynthetic.Comparison.Coherent.Data

@[expose] public section

namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn] [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)

/-- Canonical source regrading of the normalized classical η map. The
positive-filtration assertion is a premise, not part of this construction. -/
noncomputable def etaSourceIso
    (he : normalizedExponent H D.hopfAndDetector.etaMap = 1) :
    Smn (Syn := Syn) 1 2 ≅
      (SyntheticCategory.biShift (0, (normalizedExponent H D.hopfAndDetector.etaMap : ℤ))).obj
        (D.nu.functor.obj (Sphere (C := C) 1)) := by
  rw [he]
  exact ((SyntheticCategory.biShift (0,1)).mapIso
      (D.nu.suspensionIso SphereSpectrum) ≪≫
    (SyntheticCategory.biShift_comp (1,1) (0,1)).app (D.nu.functor.obj SphereSpectrum) ≪≫
    (SyntheticCategory.biShift (1,2)).mapIso D.nu.unitIso).symm
end KIP126.AdamsSynthetic
