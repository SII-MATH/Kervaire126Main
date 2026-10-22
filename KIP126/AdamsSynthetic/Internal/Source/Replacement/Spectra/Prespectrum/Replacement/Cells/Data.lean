module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Privately adapted from SII-MATH/Kervaire126Main, commit
c60fbbbb93ee1f225e69bb8b93d06b4f842d031d,
KIP126/Def/StableHomotopy/Spectra/Prespectrum/Replacement/Cells/Data.lean.
-/

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.FiniteSupport.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Spectra.BasedSpace.AdjoinPoint.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory
open KIP126.Topology.HomotopyLifting

universe u

/-- The free prespectrum on an actual cubical boundary with a disjoint
basepoint, indexed by the free level and cube dimension. -/
def cubicalCellSource (i : ℕ × ℕ) : Prespectrum.{u} :=
  free i.1 (BasedSpace.adjoinPoint (cubeBoundaryObject i.2))

/-- The corresponding free prespectrum on the whole actual cube. -/
def cubicalCellTarget (i : ℕ × ℕ) : Prespectrum.{u} :=
  free i.1 (BasedSpace.adjoinPoint (cubeObject i.2))

/-- The genuine free cell-boundary morphisms used for strict spectrum
replacement. The independent basepoint allows arbitrary boundary data. -/
noncomputable def cubicalCellBoundary (i : ℕ × ℕ) :
    cubicalCellSource.{u} i ⟶ cubicalCellTarget.{u} i :=
  freeMap i.1 (BasedSpace.adjoinPointMap (cubeBoundaryInclusion i.2))

end KIP126.AdamsSynthetic.Source.Prespectrum
