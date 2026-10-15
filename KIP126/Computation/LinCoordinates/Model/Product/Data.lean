module

public import KIP126.Computation.WellFormedness.LinCoordinates.E2

@[expose] public section

namespace KIP126.LinE2

/-- Bigraded multiplication in the actual truncated quotient. The strict
calculator separately rejects products outside t ≤ 261. -/
noncomputable def mulAt {s t s' t' : ℕ} (a : E2At s t) (b : E2At s' t') :
    E2At (s + s') (t + t') :=
  ⟨a.val * b.val, multiply_mem a.property b.property⟩

end KIP126.LinE2
