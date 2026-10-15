module

public import KIP126.Def.Synthetic.ExtensionSS.Square.FilteredMaps.Data

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence.SyntheticExtensionData

open CategoryTheory KIP126.Synthetic.Context KIP126.SpectralSequence
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  {F : SyntheticAdamsFamily Syn} {X Y X' Y' : Syn}
  {g : X ⟶ Y} {g' : X' ⟶ Y'}

theorem FilteredSquare.homotopy_comm {D : SyntheticExtensionData F g}
    {E : SyntheticExtensionData F g'} {a : X ⟶ X'} {b : Y ⟶ Y'}
    (S : FilteredSquare D E a b) (p : ℤ × ℤ) :
    S.source.map p ≫ E.filteredMap.map p = D.filteredMap.map p ≫ S.target.map p := by
  change syntheticHomotopyMap a p ≫ E.map.aMap p =
    D.map.aMap p ≫ syntheticHomotopyMap b p
  rw [D.aMap_eq, E.aMap_eq]
  ext h
  change (h ≫ a) ≫ g' = (h ≫ g) ≫ b
  rw [Category.assoc, S.comm, Category.assoc]

end KIP126.Synthetic.SpectralSequence.SyntheticExtensionData
