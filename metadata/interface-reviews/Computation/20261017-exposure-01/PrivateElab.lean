module
import Lean
open Lean Elab Term Meta
local syntax (name := inlinePrivate) "inline_private% " term : term
@[local term_elab inlinePrivate] private meta def elabInlinePrivate : TermElab := fun stx expectedType => withoutExporting do
  let e ← elabTermAndSynthesize stx[1] expectedType
  deltaExpand e isPrivateName
private def secret : Nat := 37
@[expose] public def visible : Nat := inline_private% secret
@[expose] public def dependent : Fin visible := ⟨0, by decide⟩
