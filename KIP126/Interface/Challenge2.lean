module

public import KIP126.Def.Literature
public import KIP126.Def.Computation

/-! The original two correlated deliveries, now on an explicit common model.
Adapted from Interface/Challenge/Challenge2 at bbac1fc05843 (Apache-2.0).
No global witness or existence axiom is introduced. -/

@[expose] section
namespace KIP126
open StableHomotopy Synthetic.Context Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

public structure Challenge2 (D : Model C Syn) where
  literature : Literature.LiteratureInterface D
  computation : Computation.ComputationInterface literature

end KIP126
