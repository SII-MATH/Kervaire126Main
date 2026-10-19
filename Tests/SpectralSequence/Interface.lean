module

public import KIP126.SpectralSequence
import Lean

open Lean Elab Command

set_option maxHeartbeats 0

-- A normal consumer imports only the public entry point. The contract locks
-- complete types, universe parameters, exports and transitive axiom dependencies.
run_cmd do
  let contract ← ofExcept <| Json.parse (include_str "../../interface/baselines/spectral-sequence-api.json")
  let named ← ofExcept <| contract.getObjValAs? (Array Json) "declarations"
  let generated ← ofExcept <| contract.getObjValAs? (Array Json) "generated_declarations"
  let declarations := named ++ generated
  let expectedExports ← ofExcept <| contract.getObjValAs? (Array String) "exports"
  let env ← getEnv
  let exported := env.setExporting true
  for mod in env.header.moduleNames do
    if (`KIP126).isPrefixOf mod &&
        !(`KIP126.SpectralSequence).isPrefixOf mod then
      throwError "SpectralSequence crossed its dependency boundary: {mod}"
  for decl in declarations do
    let name ← ofExcept <| decl.getObjValAs? String "name"
    let expectedType ← ofExcept <| decl.getObjValAs? String "type_fingerprint"
    let universes ← ofExcept <| decl.getObjValAs? (List String) "universes"
    let some info := exported.find? name.toName
      | throwError "Missing public interface: {name}"
    unless toString (hash (toString info.type)) == expectedType &&
        info.levelParams.map Name.toString == universes do
      throwError "Public type or universe parameters changed: {name}"
  let mut actualExports : Array String := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`KIP126).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    unless (exported.find? name).isSome do continue
    if isPrivateName name then continue
    actualExports := actualExports.push name.toString
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun n =>
      n != `propext && n != `Classical.choice && n != `Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected axiom dependency in {name}: {unexpected}"
  unless actualExports.qsort (· < ·) == expectedExports.qsort (· < ·) do
    let added := actualExports.filter (!expectedExports.contains ·)
    let missing := expectedExports.filter (!actualExports.contains ·)
    throwError "Public exports changed; added: {added}; missing: {missing}"

#check_failure KIP126.Core.SpectralSequence.Subobject.thirdIso
#check_failure KIP126.Core.SpectralSequence.PageHomology.factor_cokernelMap
#check_failure KIP126.Core.SpectralSequence.submoduleCokernelIso
-- Main page calculus consumes these existing proved representative operations.
#check KIP126.Core.SpectralSequence.subobjectModule_kernel
#check KIP126.Core.SpectralSequence.subobjectModule_image
#check KIP126.Core.SpectralSequence.cokernel_π_eq_zero_iff_mem_range
#check KIP126.Core.SpectralSequence.subobject_cokernel_π_eq_zero_iff
#check_failure KIP126.Core.SpectralSequence.FilteredComplex
#check_failure KIP126.Core.SpectralSequence.Filtration.completion
#check_failure KIP126.Core.SpectralSequence.FilteredComplex.DifferentialHelpers.kernelSubobject_epiDesc'

open CategoryTheory KIP126.Core KIP126.Core.SpectralSequence

universe u v
variable {R : Type u} [Ring R]
variable (E : SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))

example (r : ℤ) (p : ℤ × ℤ) (x : E.Page 2 p) (y z : E.Page r p)
    (hy : RepresentsOnPage E r p x y) (hz : RepresentsOnPage E r p x z) : y = z :=
  hy.unique hz

example (r : ℤ) (p : ℤ × ℤ) (y : E.Page r (p + E.diffDeg r))
    (hy : IsPageBoundary E r p y) : IsPageCycle E r (p + E.diffDeg r) y :=
  hy.isCycle

example (N : ℤ) (hN : E.r₀ ≤ N) (p : ℤ × ℤ) (x : E.Page 2 p)
    (hx : SurvivesTo E N p x)
    (hout : ∀ r : ℤ, N ≤ r → E.d r p = 0)
    (hin : ∀ r : ℤ, N ≤ r → E.d r (p - E.diffDeg r) = 0) :
    NonzeroSurvival E p x :=
  nonzeroSurvival_of_survivesTo E N hN p x hx hout hin
