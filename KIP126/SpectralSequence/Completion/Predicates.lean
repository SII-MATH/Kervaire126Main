module

import all KIP126.SpectralSequence.Completion.Data
import all KIP126.SpectralSequence.Internal.Algebra.Filtration.Predicates

/-!
# Completion predicates

Completion uses the same private `Filtration.IsMittagLeffler` predicate as
the underlying filtration algebra: images of deeper filtration levels in a
fixed level eventually stabilize.
-/
