module

public import KIP126.Def.Synthetic.ExtensionSS.Data

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory KIP126.Synthetic.Context KIP126.SpectralSequence
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  {F : SyntheticAdamsFamily Syn} {X Y X' Y' : Syn}
  {g : X ⟶ Y} {g' : X' ⟶ Y'}

namespace SyntheticExtensionData

/-- A square of the specified synthetic maps preserving the specified
abutment filtrations. Every vertical homotopy map is postcomposition by the
displayed synthetic map, not an independent operation on an ESS. -/
structure FilteredSquare (D : SyntheticExtensionData F g)
    (E : SyntheticExtensionData F g') (a : X ⟶ X') (b : Y ⟶ Y') : Prop where
  comm : a ≫ g' = g ≫ b
  source_preserves : ∀ s p,
    ∃ φ : Subobject.underlying.obj (D.source.filtration.F s p) ⟶
        Subobject.underlying.obj (E.source.filtration.F s p),
      φ ≫ (E.source.filtration.F s p).arrow =
        (D.source.filtration.F s p).arrow ≫ syntheticHomotopyMap a p
  target_preserves : ∀ s p,
    ∃ φ : Subobject.underlying.obj (D.target.filtration.F s p) ⟶
        Subobject.underlying.obj (E.target.filtration.F s p),
      φ ≫ (E.target.filtration.F s p).arrow =
        (D.target.filtration.F s p).arrow ≫ syntheticHomotopyMap b p


end SyntheticExtensionData
end KIP126.Synthetic.SpectralSequence
