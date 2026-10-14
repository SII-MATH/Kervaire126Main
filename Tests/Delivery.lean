module

public import KIP126.Interface.Challenge2
import Lean

open KIP126 KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] {D : Model C Syn}

example (L : Literature.LiteratureInterface D) (I : Computation.ComputationInterface L) :
    Challenge2 D := ⟨L,I⟩

example (I : Challenge2 D) : I.computation.bindings.toBindings.atom .g = I.literature.bindings.tmf.g :=
  I.computation.bindings.g_agrees

set_option linter.unusedVariables false in
example (L L' : Literature.LiteratureInterface D) (I : Computation.ComputationInterface L) : True := by
  fail_if_success have : Computation.ComputationInterface L' := I
  trivial

-- No third root field and no globally supplied witness.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some info := getStructureInfo? env `KIP126.Challenge2
    | throwError "Missing Challenge2 structure"
  unless info.fieldNames == #[`literature, `computation] do
    throwError "Challenge2 must retain exactly its two correlated deliveries; got {info.fieldNames}"

#check_failure KIP126.Main.Axiom.challenge2
#check_failure KIP126.Main.StageInput.witness
