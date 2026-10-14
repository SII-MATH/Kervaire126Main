module

public import KIP126.Main.Conditions
public import KIP126.Main.SectionSeven.AlphaOne
public import KIP126.Main.SectionSeven.NormalizedNu
public import KIP126.Main.SectionSeven.Indeterminacy
public import KIP126.Main.SectionSeven.TodaNonempty

/-! Proposition 7.9's paper-specific divisibility step.
Source: Kervaire126 bbac1fc05843,
Main/Solution/Route/Section7/NuTarget.lean:65-104 (MIT; see the retained source LICENSE).
The old proof is retained in the migration source archive. It is not an
external result: this declaration is a proof-port-pending Main obligation
while the AlphaOne, Toda, ninth-quotient ν and P/Q helper chain is adapted
from concrete table coordinates to the fixed public upstream operations. -/

@[expose] section
namespace KIP126.Main.SectionSeven
open KIP126.Computation.Standard (T)

/-- The P and Q branches must produce actual representatives and the exact
λν divisibility equation. No such conclusion is added to an upstream API. -/
public theorem target_nu_divisible (hc3 : C3) (hc5 : C5) :
    TargetNuDivisible T hopfNu := by
  sorry

end KIP126.Main.SectionSeven
