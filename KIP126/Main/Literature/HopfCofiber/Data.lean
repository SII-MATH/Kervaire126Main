module

public import KIP126.Literature.Standard.Sphere.Sequence
public import KIP126.Def.ClassicalAdams.TowerNaturality.Proofs

@[expose] public section

/-! Cofibers of maps S³ → S⁰ in the *same* foundation as sphereAdamsData.
The map is explicit until a detected Hopf-map input is supplied. -/
namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
noncomputable section

abbrev SphereThreeMap := Sphere (C := standardFoundation.Spectrum) 3 ⟶ SphereSpectrum

def sphereMapCofiber (f : SphereThreeMap) : standardFoundation.Spectrum :=
  HasFunctorialCofiber.cofib f

def sphereMapCofiberInclusion (f : SphereThreeMap) :
    (SphereSpectrum : standardFoundation.Spectrum) ⟶ sphereMapCofiber f :=
  HasFunctorialCofiber.cofibι f

/-- The top-cell target is ΣS³; reindexing it as S⁴ is kept explicit. -/
def sphereMapCofiberProjection (f : SphereThreeMap) :
    sphereMapCofiber f ⟶ (Sphere (C := standardFoundation.Spectrum) 3)⟦(1 : ℤ)⟧ :=
  HasFunctorialCofiber.cofibδ f

def sphereMapCofiberTriangle (f : SphereThreeMap) :
    HoCofiberSequence (C := standardFoundation.Spectrum) :=
  HoCofiberSequence.ofMorphism f

/-- Not an arbitrary spectral sequence: reuse the fixed unit and actual cofiber. -/
def sphereMapCofiberAdams (f : SphereThreeMap) :
    KIP126.SpectralSequence (ModuleCat ℤ) (ℤ × ℤ) :=
  adamsTowerInternalSpectralSequence standardFoundation.hf2.unit (sphereMapCofiber f)

/-- The bottom-cell map induces genuine maps of tower stages. -/
def sphereMapCofiberInclusionTower (f : SphereThreeMap) (s : ℕ) :=
  adamsTowerInduced standardFoundation.hf2.unit (sphereMapCofiberInclusion f) s

/-- The top-cell map induces genuine maps to the tower of ΣS³. -/
def sphereMapCofiberProjectionTower (f : SphereThreeMap) (s : ℕ) :=
  adamsTowerInduced standardFoundation.hf2.unit (sphereMapCofiberProjection f) s

/-- The E₂ class of a filtration-one lift, using the actual exact-couple map. -/
def sphereFiltrationOneClass
    (a : HomotopyGroup 3 (adamsTower standardFoundation.hf2.unit SphereSpectrum 1)) :
    sphereAdamsSequence.sequence.Page 2 (1, 4) :=
  (adamsTowerSSDataPageIso standardFoundation.hf2.unit SphereSpectrum 1 4 0).inv
    ((adamsCycleBoundaries standardFoundation.hf2.unit SphereSpectrum 2 (by decide) 1 4).mkQ
      ⟨adamsJ standardFoundation.hf2.unit SphereSpectrum 1 4 a,
        adamsJ_mem_cycles standardFoundation.hf2.unit SphereSpectrum 2 (by decide) 1 4 a⟩)

end
end KIP126.Classical.Adams
