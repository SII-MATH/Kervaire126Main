module

import all KIP126.Literature.Geometry.Manifolds
import Lean

/-! Representation audit. The ordinary public types are sealed to avoid
exporting analysis-library instances into the older spectral calculations.
The full definitions must nevertheless be genuine geometric data. -/
open KIP126.Literature.Geometry
open scoped Manifold ContDiff

example (n : ℕ) (M : ClosedStablyFramedManifold n) :
    CompactSpace M.manifold.Carrier := inferInstance
example (n : ℕ) (M : ClosedStablyFramedManifold n) :
    T2Space M.manifold.Carrier := inferInstance
example (n : ℕ) (M : ClosedStablyFramedManifold n) :
    SecondCountableTopology M.manifold.Carrier := inferInstance
example (n : ℕ) (M : ClosedStablyFramedManifold n) :
    IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ M.manifold.Carrier := inferInstance

-- The actual stabilized tangent frame, not just a Boolean framing flag.
example (n : ℕ) (M : ClosedStablyFramedManifold n) :
    IsLocalFrameOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin M.framing.rank)) ∞
      M.framing.sections Set.univ := M.framing.isFrame

#check_failure KIP126.AdamsSynthetic.Standard.model

-- Inspect private bodies too: no project spectral object or result can be
-- hidden inside a supposedly geometric carrier type.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := #[``ClosedSmoothManifold, ``StableFraming, ``ClosedStablyFramedManifold]
  let mut seen : NameSet := {}
  while let some name := pending.back? do
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throwError "Missing geometric representation: {name}"
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`KIP126).isPrefixOf mod do continue
    unless mod == `KIP126.Literature.Geometry.Manifolds do
      throwError "Geometric representation imports project spectral data: {name}: {mod}"
    let body := info.value? (allowOpaque := true)
    if info.isAxiom || info.type.hasSorry || body.any (·.hasSorry) then
      throwError "Geometric representation is not constructed: {name}"
    pending := pending ++ info.type.getUsedConstants
    if let some value := body then pending := pending ++ value.getUsedConstants
