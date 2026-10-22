module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Free/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.Prespectrum.Tail.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

noncomputable def freeStabilization : ∀ (n : ℕ) (A : BasedSpace.{u}),
    free (n+1) A.suspension ⟶ free n A
  | 0, A => eqToHom (congrArg desuspension (suspensionSpectrum_tail A)) ≫
      paddedTailInclusion (suspensionSpectrum A)
  | n+1, A => eqToHom (free_succ (n+1) A.suspension) ≫
      desuspensionMap (freeStabilization n A) ≫ eqToHom (free_succ n A).symm

end KIP126.AdamsSynthetic.Source.Prespectrum
