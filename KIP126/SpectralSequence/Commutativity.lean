module

import all KIP126.SpectralSequence.Commutativity.Basic.Proofs
import all KIP126.SpectralSequence.Commutativity.Predicates
import all KIP126.SpectralSequence.Commutativity.Square.Proofs
import all KIP126.SpectralSequence.Commutativity.Detection.Proofs

@[expose] section

/-!
# Commutativity for extension spectral-sequence data

This entry point contains the axiom-free part of
`KIPBase/SpectralSequence/Commutativity.lean`: both square presentations,
their conversion, the induced associated-graded commutative square, and the
detection-index transport.

The source's `ESSRelation` and `ESSVanishes` referred to `essDiff`, whose
object-valued definition was itself unfinished.  The claimed differential,
boundary-transfer, page-functoriality, and detection theorems were likewise
unfinished.  They are intentionally not restated as facts here.  They can be
added after a concrete ESS differential object is defined and the proofs are
completed.
-/
