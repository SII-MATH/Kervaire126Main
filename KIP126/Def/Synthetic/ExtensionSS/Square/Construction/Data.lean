module

public import KIP126.Def.Synthetic.ExtensionSS.Square.Proofs

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence.SyntheticExtensionData

open CategoryTheory KIP126.Synthetic.Context KIP126.SpectralSequence
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  {F : SyntheticAdamsFamily Syn} {X Y X' Y' : Syn}
  {g : X ⟶ Y} {g' : X' ⟶ Y'}

/-- The actual square of homotopy maps induces the ESS representative map. -/
noncomputable def FilteredSquare.complexMap {D : SyntheticExtensionData F g}
    {E : SyntheticExtensionData F g'} {a : X ⟶ X'} {b : Y ⟶ Y'}
    (S : FilteredSquare D E a b) (p : ℤ × ℤ) :
    FilteredComplex.Morphism (D.complex p) (E.complex p) :=
  underlyingComplexMap D.filteredMap E.filteredMap S.source S.target S.homotopy_comm p

end KIP126.Synthetic.SpectralSequence.SyntheticExtensionData
