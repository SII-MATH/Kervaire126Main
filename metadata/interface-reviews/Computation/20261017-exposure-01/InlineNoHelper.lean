module
public meta import Lean
private def secret : Nat := 37
@[expose] public def visible : Nat := by
  run_tac
    let target ← Lean.Elab.Tactic.getMainTarget
    let e ← Lean.withoutExporting do
      Lean.Elab.Term.elabTermAndSynthesize (Lean.mkIdent `secret) (some target)
    let e ← Lean.withoutExporting <| Lean.Meta.deltaExpand e Lean.isPrivateName
    Lean.Elab.Tactic.closeMainGoal `inlinePrivate e
@[expose] public def dependent : Fin visible := ⟨0, by decide⟩
