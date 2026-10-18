module

/-
Copyright (c) 2026 Jiashuo Zhang and KIP126 contributors.
Released under the MIT license; see LICENSE.
Adapted from SII-MATH/Kervaire126, commit
8cb35dad5f75ecc095e474df6c765baec9b175bf.
-/

import all KIP126.AdamsSynthetic.Internal.Milnor.Cobar

@[expose] section

/-! The square-zero obligation for the specified polynomial cobar differential.

The source repository proves this identity conditionally on Milnor coordinates
for an Adams tower (KIP126/Def/ClassicalAdams/MilnorCooperations/Proofs.lean,
commit 8cb35dad5f75ecc095e474df6c765baec9b175bf).  Here it must instead be proved
from the actual coproduct formula.  The canonical cobar source must not depend
on the Adams-page comparison whose target it is meant to identify. -/

namespace KIP126.AdamsSynthetic.Milnor

/-- The fixed Milnor cobar differential squares to zero.  This is the remaining
pure algebra obligation; no Adams tower or freely chosen cooperation is input. -/
theorem differential_squared (s t : ℕ) (x : cochains s t) :
    differential (s + 1) t (differential s t x) = 0 := by
  sorry

end KIP126.AdamsSynthetic.Milnor
