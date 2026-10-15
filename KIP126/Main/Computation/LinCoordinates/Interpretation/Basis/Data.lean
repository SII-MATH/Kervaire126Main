module

public import KIP126.Main.Computation.LinCoordinates.Interpretation.Classes.Data

@[expose] public section

namespace KIP126.Classical.Adams
open KIP126.LinE2 KIP126.Algebra

/-- The actual E₂ coordinates associated with `linE2Presentation`, using
the scalar action already specified on the spectral sequence. -/
noncomputable def sphereE2Coordinates (s t : ℕ) (ht : t ≤ 261) :
    sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ)) ≃ₗ[ℤ] (BasisIndex s t →₀ F2) :=
  KIP126.Main.AdamsSynthetic.computation.theorems.sphereBasis.coordinates s t ht

/-- The actual sphere basis vector with the specified CSV index. -/
noncomputable def sphereE2Basis (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ)) :=
  (sphereE2Coordinates s t ht).symm (Finsupp.single i 1)

/-- Lookup by the original additive-basis CSV index, not an algebra generator ID. -/
noncomputable def sphereE2BasisByCSV? (s t : ℕ) (ht : t ≤ 261) (index : ℕ) :
    Option (sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ))) :=
  (findBasisIndex? s t index).map (sphereE2Basis s t ht)

end KIP126.Classical.Adams
