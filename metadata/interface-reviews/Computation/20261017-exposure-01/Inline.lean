module
public import Lean
open Lean Elab Term Meta
elab "inline_private% " t:term : term <= expectedType => withoutExporting do
  let e ← elabTermAndSynthesize t expectedType
  deltaExpand e isPrivateName
private def secret : Nat := 37
@[expose] public def visible : Nat := inline_private% secret
@[expose] public def dependent : Fin visible := ⟨0, by decide⟩
@[no_expose] public def hidden : Nat := secret
