module

public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.Colimit.Instances
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Tail.Data

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- The actual based colimit at each level of any small strict diagram. -/
noncomputable def pointwiseColimitLevel {J : Type u} [Category.{u} J]
    (F : J ⥤ Prespectrum.{u}) (n : ℕ) : BasedSpace.{u} :=
  colimit (F ⋙ evaluationFunctor n)

noncomputable def pointwiseColimitLevelInclusion {J : Type u} [Category.{u} J]
    (F : J ⥤ Prespectrum.{u}) (n : ℕ) (j : J) :
    (F.obj j).level n ⟶ pointwiseColimitLevel F n :=
  colimit.ι (F ⋙ evaluationFunctor n) j

end KIP126.StableHomotopy.Spectra.Prespectrum
