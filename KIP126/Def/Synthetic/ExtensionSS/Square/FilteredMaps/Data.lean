module

public import KIP126.Def.Synthetic.ExtensionSS.Square.Predicates
public import KIP126.Def.SpectralSequence.BoundedExtension.Square.Construction.Data

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory KIP126.Synthetic.Context KIP126.SpectralSequence
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  {F : SyntheticAdamsFamily Syn} {X Y X' Y' : Syn}
  {g : X ⟶ Y} {g' : X' ⟶ Y'}

namespace SyntheticExtensionData

def filteredMap (D : SyntheticExtensionData F g) :
    KIP126.SpectralSequence.FilteredMorphism D.source.filtration D.target.filtration where
  map := D.map.aMap
  compat := D.map.filtration_compat

noncomputable def FilteredSquare.source {D : SyntheticExtensionData F g}
    {E : SyntheticExtensionData F g'} {a : X ⟶ X'} {b : Y ⟶ Y'}
    (S : FilteredSquare D E a b) :
    KIP126.SpectralSequence.FilteredMorphism D.source.filtration E.source.filtration where
  map := syntheticHomotopyMap a
  compat := S.source_preserves

noncomputable def FilteredSquare.target {D : SyntheticExtensionData F g}
    {E : SyntheticExtensionData F g'} {a : X ⟶ X'} {b : Y ⟶ Y'}
    (S : FilteredSquare D E a b) :
    KIP126.SpectralSequence.FilteredMorphism D.target.filtration E.target.filtration where
  map := syntheticHomotopyMap b
  compat := S.target_preserves

end SyntheticExtensionData
end KIP126.Synthetic.SpectralSequence
