module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

@[expose] public section

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory Opposite Simplicial

universe u

/-- The actual realization with the specified simplicial vertex as basepoint. -/
noncomputable def basedRealization (K : SSet.{u}) (v : K.obj (op ⦋0⦌)) :
    BasedSpace.{u} where
  space := SSet.toTop.obj K
  point := TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app K).app (op ⦋0⦌) v)

end KIP126.StableHomotopy.Spectra
