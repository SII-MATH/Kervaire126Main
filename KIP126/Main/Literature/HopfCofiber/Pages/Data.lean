module

public import KIP126.Main.Literature.HopfCofiber.Predicates
public import KIP126.Def.ClassicalAdams.TowerNaturality.Page.Proofs
public import KIP126.Literature.Standard.Sphere.Sequence

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory KIP126.StableHomotopy
noncomputable section

/-- Actual bottom-cell E₂ map from the fixed sphere, not a supplied map. -/
def sphereMapCofiberBottomE2 (f : SphereThreeMap) (p : ℤ × ℤ) :
    sphereAdamsData.Page 2 p →ₗ[ℤ] (sphereMapCofiberAdams f).Page 2 p :=
  adamsInternalE2Induced standardFoundation.hf2.unit (sphereMapCofiberInclusion f) p

/-- Actual top-cell E₂ map. Identifying the target with the degree-shifted
sphere E₂ still requires a suspension comparison and is not silently assumed. -/
def sphereMapCofiberTopE2 (f : SphereThreeMap) (p : ℤ × ℤ) :
    (sphereMapCofiberAdams f).Page 2 p →ₗ[ℤ]
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit
        ((Sphere (C := standardFoundation.Spectrum) 3)⟦(1 : ℤ)⟧)).Page 2 p :=
  adamsInternalE2Induced standardFoundation.hf2.unit (sphereMapCofiberProjection f) p

end
end KIP126.Classical.Adams
