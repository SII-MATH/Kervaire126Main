module

public import KIP126.Def.Synthetic.NormalizedMap.Data
public import KIP126.Def.ClassicalAdams.TowerResolution.Proofs

@[expose] public section

namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams

/-- Every degree-one sphere map has positive mod-two Adams filtration;
its normalized lift therefore uses exponent one. -/
theorem normalizedExponent_sphere_degree_one {C : Type 1}
    [StableHomotopyCategory.{1, 0} C] [HasFunctorialCofiber (C := C)]
    (H : Mod2EilenbergMacLane (C := C))
    (f : HomotopyGroup 1 (SphereSpectrum (C := C))) : normalizedExponent H f = 1 := by
  classical
  have hz : CategoryStruct.comp f (adamsUnit H.unit SphereSpectrum) = 0 := by
    apply (cancel_mono (rightUnitor H.HF2).hom).mp
    letI := H.homotopy_vanishes 1 (by decide)
    exact Subsingleton.elim _ _
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂
    (adamsResolutionTriangle H.unit SphereSpectrum 0)
    (adamsResolutionTriangle_distinguished H.unit SphereSpectrum 0) f hz
  have hf : AdamsFiltrationAtLeast H f 1 := by
    refine ⟨g, ?_⟩
    simpa [adamsTowerMap, adamsTowerComposite, adamsResolutionTriangle, Triangle.mk, adamsTower]
      using hg.symm
  simp only [normalizedExponent, if_pos hf]

end KIP126.Synthetic.Context
