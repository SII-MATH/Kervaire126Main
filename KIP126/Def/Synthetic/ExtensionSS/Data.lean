module

public import KIP126.Def.Synthetic.AdamsSequence.Data
public import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Data
public import KIP126.Def.SpectralSequence.Convergence.Data
public import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs
public import KIP126.Def.SpectralSequence.FilteredComplex.SSData.Proofs
public import KIP126.Def.SpectralSequence.FilteredComplex.Data
import all KIP126.Def.SpectralSequence.FilteredComplex.Data
public import KIP126.Def.SpectralSequence.Convergence.Proofs
public import Mathlib.CategoryTheory.Abelian.Exact
public import KIP126.Def.SpectralSequence.Basic.Data
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

@[expose] public section

/-! The extension sequence of an actual synthetic map. Both abutments are
actual bigraded homotopy groups; both maps are induced by that same map.
Bounded convergence is explicit input, not asserted for arbitrary objects. -/

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory CategoryTheory.Limits KIP126.SpectralSequence
open KIP126.Synthetic.Context

universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- Postcomposition by the specified synthetic map on actual homotopy. -/
def syntheticHomotopyMap {X Y : Syn} (g : X ⟶ Y) (p : ℤ × ℤ) :
    syntheticHomotopy X p ⟶ syntheticHomotopy Y p :=
  ModuleCat.ofHom (Preadditive.rightComp (Smn p.1 p.2) g).toIntLinearMap


end
end KIP126.Synthetic.SpectralSequence
