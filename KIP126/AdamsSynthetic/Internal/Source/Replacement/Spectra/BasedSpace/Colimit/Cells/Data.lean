module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/BasedSpace/Colimit/Cells/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.Under.Data
import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
import Mathlib.Topology.Category.TopCat.Limits.Products

@[expose] section

namespace KIP126.AdamsSynthetic.Source.BasedSpace

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

end KIP126.AdamsSynthetic.Source.BasedSpace
