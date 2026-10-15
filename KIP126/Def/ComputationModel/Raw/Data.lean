module

@[expose] public section

/-!
# Lossless rows and syntactic codes of the pinned Lin log

Source version: Zenodo 14875701, `v126.3.cw49`, `SSeqCpp-master/ss`.
The schema is `mylog.h:53–55`; the insertion variants are
`mylog.cpp:25–58`. Every nullable column is retained as `Option`.
The signed SQL integers, raw strings, generated `stem`, and `info` are
preserved; this is not the normalized finite-differential export type.

The decoders below only describe program syntax. Neither a reason code,
a root-depth row, nor a sentinel establishes a mathematical conclusion.
No importer, table, CSV, or raw database is modified by these definitions.
-/

namespace KIP126.Computation.LinCalculations.Raw

/-- The complete `log` row. SQLite's integer primary key is non-null;
every other column lacks a `NOT NULL` constraint. -/
structure LogRow where
  id : Int
  depth : Option Int
  reason : Option String
  name : Option String
  stem : Option Int
  s : Option Int
  t : Option Int
  r : Option Int
  x : Option String
  dx : Option String
  info : Option String
  deriving Repr, DecidableEq, BEq

/-- The exact upstream enum alternatives, in source order
(`mylog.h:13–37`). They are provenance tags, not proof certificates. -/
inductive LogReason where
  | manual | degree | degree2 | deduce | deduce2 | ddCof | ddCof2
  | cofseqIn | cofseqOut | naturality | synthetic | syntheticExtension
  | syntheticPermanent | deduceSquare | deduceProduct | deduceFx
  | commutativity | definition | tryForward | tryInverse | migrate | d2
  deriving Repr, DecidableEq, BEq

/-- `REASONS_DB` from `mylog.h:40`. In particular this map is not
injective: both ordinary and cofiber-sequence deduction use D/DI. -/
def LogReason.databaseCode : LogReason → String
  | .manual => "M"
  | .degree => "G"
  | .degree2 => "GI"
  | .deduce | .ddCof => "D"
  | .deduce2 | .ddCof2 => "DI"
  | .cofseqIn => "ToCs"
  | .cofseqOut => "OutCsI"
  | .naturality => "N"
  | .synthetic => "Syn"
  | .syntheticExtension => "SynCs"
  | .syntheticPermanent => "SynCsIn"
  | .deduceSquare => "XX"
  | .deduceProduct => "XY"
  | .deduceFx => "FX"
  | .commutativity => "CsCm"
  | .definition => "Def"
  | .tryForward => "T"
  | .tryInverse => "TI"
  | .migrate => "Mg"
  | .d2 => "d2"

/-- Possible enum origins of a database code, retaining the D/DI
ambiguity. An unrecognized code has no candidate; the original string
remains in `LogRow.reason`. -/
def reasonCandidates : String → List LogReason
  | "M" => [.manual]
  | "G" => [.degree]
  | "GI" => [.degree2]
  | "D" => [.deduce, .ddCof]
  | "DI" => [.deduce2, .ddCof2]
  | "ToCs" => [.cofseqIn]
  | "OutCsI" => [.cofseqOut]
  | "N" => [.naturality]
  | "Syn" => [.synthetic]
  | "SynCs" => [.syntheticExtension]
  | "SynCsIn" => [.syntheticPermanent]
  | "XX" => [.deduceSquare]
  | "XY" => [.deduceProduct]
  | "FX" => [.deduceFx]
  | "CsCm" => [.commutativity]
  | "Def" => [.definition]
  | "T" => [.tryForward]
  | "TI" => [.tryInverse]
  | "Mg" => [.migrate]
  | "d2" => [.d2]
  | _ => []

/-- A syntactic depth classification. Metadata includes start/end rows
at -1 and -2. Root depth by itself does not certify an unconditional fact;
the reason and the meaning of the row still require interpretation. -/
inductive DepthCode where
  | missing
  | metadata (depth : Int)
  | root
  | branch (depth : Nat)
  deriving Repr, DecidableEq, BEq

def depthCode : Option Int → DepthCode
  | none => .missing
  | some d => if d < 0 then .metadata d else if d = 0 then .root else .branch d.toNat

/-- Numeric page codes are separated before any page interpretation.
An ordinary candidate still requires spectrum, reason, depth, degree,
coordinate, and source-window checks. -/
inductive PageCode where
  | missing
  | ordinaryCandidate (r : Nat)
  | sentinel999
  | permanentThreshold1000
  | boundarySentinel1001
  | other (r : Int)
  deriving Repr, DecidableEq, BEq

/-- The conservative finite range agrees with the existing translator.
The three distinguished values come from `main.h:20–25`. In particular,
999 is not interpreted as nonzero permanent survival, and 1001 is not a
finite-page differential (`ss.cpp:583–587`, OutCsI boundary branch). -/
def pageCode : Option Int → PageCode
  | none => .missing
  | some r =>
      if r = 999 then .sentinel999
      else if r = 1000 then .permanentThreshold1000
      else if r = 1001 then .boundarySentinel1001
      else if 2 ≤ r ∧ r < 999 then .ordinaryCandidate r.toNat
      else .other r

/-- Purely lexical coordinate classes. SQL NULL, an unknown sentinel,
and the empty encoding of the zero vector remain distinct. This does
not parse arbitrary text into a finite-page class. -/
inductive CoordinateCode where
  | sqlNull
  | zero
  | unknownSentinel (encoding : String)
  | encoded (encoding : String)
  deriving Repr, DecidableEq, BEq

/-- `NULL_DIFF` is the vector `{-1}` (`main.h:25`); `[NULL]` is also
recognized by the current text translator. All other nonempty strings
are retained for a separate validated coordinate parser. -/
def coordinateCode : Option String → CoordinateCode
  | none => .sqlNull
  | some "" => .zero
  | some text =>
      if text = "-1" ∨ text = "[NULL]" then .unknownSentinel text else .encoded text

/-- Exact scalar/vector normalization in `cofseq.cpp:899–914` after
`GetDiffAndLevel` returns. It intentionally retains the collision:
every level below 5000, including a boundary or the zero-vector level
-1, returns `(999, [])`; level 9000 with `NULL_DIFF = [-1]` does too.
Consequently this output cannot imply nonzero E∞ survival. -/
def getRAndDiffEncoding (level : Int) (diff : List Int) : Int × List Int :=
  if level < 5000 then (999, [])
  else if diff = [-1] then (10000 - level - 1, [])
  else (10000 - level, diff)

end KIP126.Computation.LinCalculations.Raw
