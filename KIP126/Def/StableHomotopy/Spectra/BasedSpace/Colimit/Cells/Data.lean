module

public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.Under.Data
public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
public import Mathlib.Topology.Category.TopCat.Limits.Products

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u w
variable {α : Type w} {A B : α → BasedSpace.{u}} {g : ∀ i, A i ⟶ B i}
  {X Y : BasedSpace.{u}} {f : X ⟶ Y} (c : AttachCells.{u} g f)

/-- The unbased disjoint union of the actual cell-boundary maps. -/
def attachmentTop : TopCat.of (Σ i : c.ι, A (c.π i)) ⟶ X.space :=
  TopCat.ofHom ⟨fun z => (c.cofan₁.inj z.1 ≫ c.g₁).map z.2,
    continuous_sigma (fun i => (c.cofan₁.inj i ≫ c.g₁).map.continuous)⟩

/-- The genuine disjoint union of the underlying generating maps. -/
def attachmentLeft : TopCat.of (Σ i : c.ι, A (c.π i)) ⟶
    TopCat.of (Σ i : c.ι, B (c.π i)) :=
  TopCat.ofHom ⟨fun z => ⟨z.1,(g (c.π z.1)).map z.2⟩,
    continuous_sigma (fun i => continuous_sigmaMk.comp (g (c.π i)).map.continuous)⟩

/-- The actual cell maps assemble as an unbased disjoint-union map. -/
def attachmentBottom : TopCat.of (Σ i : c.ι, B (c.π i)) ⟶ Y.space :=
  TopCat.ofHom ⟨fun z => (c.cell z.1).map z.2,
    continuous_sigma (fun i => (c.cell i).map.continuous)⟩

end KIP126.StableHomotopy.Spectra.BasedSpace
