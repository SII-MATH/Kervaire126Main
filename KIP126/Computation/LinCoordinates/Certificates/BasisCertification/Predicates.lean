module

public import KIP126.Computation.LinCoordinates.Model.BasisCatalogue.Data

@[expose] public section


/-!
# LinProgram/Certificates/BasisCertification/Predicates

Fixed-data basis certification predicate or construction from explicit certification; it does not prove the certification input.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

namespace KIP126.LinE2
open KIP126.Algebra

/-- The specific CSV monomials, not arbitrary chosen vectors, form a basis.
This asserts correct degrees, linear independence and spanning simultaneously. -/
def BasisTableCorrect (s t : ℕ) : Prop :=
  ∃ b : Module.Basis (BasisIndex s t) F2 (E2At s t),
    ∀ i, (b i).val = basisValue (basisRowAt s t i)

end KIP126.LinE2
