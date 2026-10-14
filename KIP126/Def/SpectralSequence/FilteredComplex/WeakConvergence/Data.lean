module

import all KIP126.Def.SpectralSequence.FilteredComplex.WeakConvergence.Comparison.Proofs
import all KIP126.Def.SpectralSequence.FilteredComplex.SpectralSequenceConstruction.Data

@[expose] section

/-!
# Weak convergence of a bounded filtered complex

The infinity-page comparison is proved in `Comparison/Proofs.lean`.
This module assembles the convergence record with the identity reindexing.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Weak convergence of the filtered-complex spectral sequence to filtered homology. -/
noncomputable def FilteredComplex.weakConvergence (FC : FilteredComplex C)
    (bnd : FC.IsBounded) :
    Convergence (FC.toSpectralSequence bnd) FC.homologySSObj FC.homologySSFiltration where
  reindex := id
  reindex_bijective := Function.bijective_id
  iso := fun ⟨s, k⟩ => Classical.choice (FC.weakConvergenceIso_nonempty bnd s k)

end KIP126.Core.SpectralSequence
