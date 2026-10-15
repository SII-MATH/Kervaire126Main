module

public import KIP126.Literature.Standard.Sphere.Sequence
public import KIP126.Literature.Standard.Milnor
public import KIP126.Def.ClassicalAdams.SphereClasses.Hi.Internal.Data

@[expose] public section

/-! Standard classes on the fixed sphere Adams sequence, defined before the external computation hypotheses.
The generic constructions live in Def and take the foundation and its Milnor
coordinates explicitly. Here they are specialized to Def's standardHF2AdamsContext.
No new object or correctness axiom is introduced by these definitions.
-/
namespace KIP126.Classical.Adams

/-- The standard class of [ξ₁^64] in the same internal sphere E₂ as the data labels. -/
noncomputable def standardH6 : sphereAdamsData.Page 2 (1, 64) :=
  Sphere.Internal.hi standardFoundation.hf2 standardMilnorCooperations 6

/-- The standard class of the cobar concatenation [ξ₁^64 | ξ₁^64].
This is the standard h₆² class in the final permanence theorem, in (s,t) = (2,128), stem 126.
It is defined before, and independently of, any CSV encoding or comparison.
Its identification with a supplied page product is a separate compatibility
question; neither a product comparison nor permanence is assumed here. -/
noncomputable def standardH6Square : sphereAdamsData.Page 2 (2, 128) :=
  Sphere.Internal.hiSquare standardFoundation.hf2 standardMilnorCooperations 6

end KIP126.Classical.Adams
