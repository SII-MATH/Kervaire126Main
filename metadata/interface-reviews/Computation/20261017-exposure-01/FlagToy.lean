module

import Lean
/-! Keep the typed implementation behind a genuinely private kernel name.
The declaration is elaborated without exporting implementation dependencies;
its existing expected type is retained by the caller's typed let. -/
local syntax (name := truePrivateImplementation) "true_private% " term : term

@[local term_elab truePrivateImplementation]
private meta def elabTruePrivateImplementation : Lean.Elab.Term.TermElab :=
  fun stx expectedType? => do
    let name := Lean.mkPrivateName (← Lean.getEnv)
      (← Lean.mkAuxDeclName `_implementation)
    Lean.withoutExporting do
      let value ← Lean.Elab.Term.elabTermAndSynthesize stx[1] expectedType?
      Lean.withOptions (Lean.ResolveName.backward.privateInPublic.set · true) do
        Lean.Meta.mkAuxDefinitionFor (compile := false) name value

@[expose] section
namespace TruePrivateToy
private def catalogue : Array Nat := #[3, 5]
public noncomputable def count : Nat := true_private% (
  let result : Nat := catalogue.size
  result)
public noncomputable def entry (i : Fin count) : Nat := true_private% (
  let result : Nat := catalogue[i]
  result)
private theorem count_eq : count = 2 := rfl
end TruePrivateToy
