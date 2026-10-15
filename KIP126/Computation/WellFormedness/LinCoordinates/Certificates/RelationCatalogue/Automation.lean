module

public import KIP126.Computation.WellFormedness.LinCoordinates.Certificates.RelationCatalogue.Support
public import Lean
public meta import KIP126.Computation.LinCoordinates.Generated.E2
import all Init.Data.List.SplitOn.Basic

@[expose] public section


/-! Compose small kernel certificates against the original archive.
The generated character lists are noncomputable proposal data: this prevents
native code generation from duplicating every suffix of a long literal list.
Every Boolean leaf is proved by `decide +kernel`; every final archive binding
is checked by kernel definitional equality. -/
namespace KIP126.LinE2.RelationCatalogue.Automation
open Lean Meta Elab Tactic

/-- Bind a noncomputable character proposal and its Boolean proof to the
original singleton chunk goal, without elaborator evaluation of that goal. -/
syntax (name := linHomogeneousChunk) "lin_homogeneous_chunk " ident ident : tactic
elab_rules : tactic
  | `(tactic| lin_homogeneous_chunk $chars:ident $checked:ident) => withMainContext do
    let csName ← realizeGlobalConstNoOverloadWithInfo chars
    let proofName ← realizeGlobalConstNoOverloadWithInfo checked
    let cs := mkConst csName
    let s := mkApp (mkConst ``String.ofList) cs
    let hs := mkApp2 (mkConst ``charsChunkCheck_ofList) cs (mkConst proofName)
    let tail := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``String)
    let proof := mkAppN (mkConst ``chunksCheck_cons)
      #[s, tail, hs, mkConst ``chunksCheck_nil]
    (← getMainGoal).assign proof
    replaceMainGoal []

/-- Join already checked complete chunks without rerunning their checkers. -/
syntax (name := linHomogeneousCompose) "lin_homogeneous_compose " ident+ : tactic
elab_rules : tactic
  | `(tactic| lin_homogeneous_compose $names:ident*) => withMainContext do
    let mut xs := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``String)
    let mut proof := mkConst ``chunksCheck_nil
    for id in names.reverse do
      let name ← realizeGlobalConstNoOverloadWithInfo id
      let type := (← getConstInfo name).type
      let some (_, lhs, _) := type.eq? | throwError "expected a chunk certificate"
      unless lhs.isAppOf ``chunksCheck do
        throwError "expected a chunksCheck equality"
      let ys := lhs.appArg!
      proof := mkAppN (mkConst ``chunksCheck_append) #[ys, xs, mkConst name, proof]
      xs := mkApp3 (mkConst ``List.append [Level.zero]) (mkConst ``String) ys xs
    (← getMainGoal).assign proof
    replaceMainGoal []
end KIP126.LinE2.RelationCatalogue.Automation
