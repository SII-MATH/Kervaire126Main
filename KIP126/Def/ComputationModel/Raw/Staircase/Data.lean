module

public import KIP126.Def.ComputationModel.Raw.Data

@[expose] public section

/-!
# Lossless rows of the fixed sphere staircase

This is the schema of `S0_AdamsE2_ss` in the already pinned
`S0_AdamsSS_t261.db` (SHA-256
518a2ed86af6d4f7bcdc5db135ab6252bd50df34492ae208663aa1c140a820ed).
Source: v126.3.cw49 `ss/main.h:1095–1098`. It is a snapshot, not a
`proofs.db` log: SQL NULL in `diff` is read as `NULL_DIFF` by `load_ss`.
We retain that NULL, empty strings, signed integers, and the row ID.
-/

namespace KIP126.Computation.LinCalculations.Raw

structure StaircaseRow where
  id : Int
  s : Option Int
  t : Option Int
  base : Option String
  diff : Option String
  level : Option Int
  deriving Repr, DecidableEq, BEq

end KIP126.Computation.LinCalculations.Raw
