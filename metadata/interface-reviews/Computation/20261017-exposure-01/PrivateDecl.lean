module
private def secret : Nat := 37
@[expose] section
public def visible : Nat := private_decl% secret
private abbrev Alias := Fin visible
private def privateValue : Alias := ⟨0, by decide⟩
public def dependent : Fin visible := private_decl% (let result : Fin visible := privateValue; result)
public def after : dependent.val = 0 := by rfl
end
