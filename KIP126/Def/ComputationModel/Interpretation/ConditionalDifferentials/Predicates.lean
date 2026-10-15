module

public import KIP126.Def.ComputationModel.Interpretation.ConditionalDifferentials.Data

@[expose] public section

/-!
# Conditional meaning and candidate coverage

These predicates state mathematical obligations, not a soundness theorem
for the pinned program. Retaining a trial, decoding its depth, or finding
nonempty `info` does not discharge any of them. A refutation may instead use
mathematical consequences of nested trials; no text-based contradiction
criterion is imposed.
-/

namespace KIP126.Computation.LinCalculations.ConditionalDifferentials

open CategoryTheory KIP126 KIP126.SpectralSequence

universe u v w
variable {R : Type u} [Ring R] {ι : Type w}
  {E : ι → SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)}

/-- Zero endpoints are allowed. In particular an inverse row with zero
source requires the target label to represent zero on Eᵣ; it does not
assert a nonzero differential hitting that label on page r. -/
def FiniteDifferentialEquation.Statement (e : FiniteDifferentialEquation E) : Prop :=
  HasDifferential (E e.object) e.r e.sourceDegree e.targetDegree e.source e.target

def ContextHolds (context : List (FiniteDifferentialEquation E)) : Prop :=
  ∀ e ∈ context, e.Statement

def ConditionalFact (context : List (FiniteDifferentialEquation E)) (e : FiniteDifferentialEquation E) : Prop :=
  ContextHolds context → e.Statement

/-- Actual inconsistency of the listed differential assumptions. The text
of an error message is neither a hypothesis nor a witness of this predicate. -/
def Contradiction (context : List (FiniteDifferentialEquation E)) : Prop :=
  ContextHolds context → False

/-- Refute only the newly tried equation, relative to its enclosing context.
An empty outer context gives an unconditional refutation, not the tried
equation as an unconditional fact. -/
def TrialRefuted (context : List (FiniteDifferentialEquation E)) (trial : FiniteDifferentialEquation E) : Prop :=
  ContextHolds context → ¬ trial.Statement

/-- Two incompatible consequences of the same actual-equation context.
This is one precise mathematical contradiction pattern, not a parser for
the program's free-form diagnostic text. -/
def EquationConflict (context : List (FiniteDifferentialEquation E)) (e : FiniteDifferentialEquation E) : Prop :=
  ConditionalFact context e ∧ TrialRefuted context e

/-- Coverage must be proved for this exact window and this exact context.
The retained log does not provide it: noncontradictory trials were rolled
back, and previously excluded candidates need not have retained local rows. -/
def CandidateCoverage (context : List (FiniteDifferentialEquation E)) (window : DifferentialCandidates E) : Prop :=
  ContextHolds context → ∃ e ∈ window.equations, e.Statement

/-- Explicit coverage plus refutations of every alternative. This is the
mathematical premise needed to deduce the selected equation; simply counting
retained trials or seeing one D row supplies neither part. -/
def CandidateElimination (context : List (FiniteDifferentialEquation E))
    (window : DifferentialCandidates E) (selected : FiniteDifferentialEquation E) : Prop :=
  selected ∈ window.equations ∧ CandidateCoverage context window ∧
    ∀ e ∈ window.equations, e ≠ selected → TrialRefuted context e

/-- Exhaustion can refute an outer assumption even when its log row has
empty `info`: all candidates in a separately justified covering window
are refuted under that same outer context. Retained child rows alone do
not establish the coverage conjunct. -/
def CandidateExhaustion (context : List (FiniteDifferentialEquation E))
    (window : DifferentialCandidates E) : Prop :=
  CandidateCoverage context window ∧
    ∀ e ∈ window.equations, TrialRefuted context e

variable (lookup : String → Option ι) (coordinate : CoordinateDictionary E)

/-- A raw trial is tied to its actual finite equation through the explicit
object lookup and partial coordinate dictionary. Unknown/sentinel trials
remain outside this finite interpretation. -/
def TrialRealizes (row : Raw.LogRow) (equation : FiniteDifferentialEquation E) : Prop :=
  ∃ raw, decodeTrialEquation row = .ok raw ∧
    realizeFiniteEquation E lookup coordinate raw = some equation

def DeductionRealizes (row : Raw.LogRow) (equation : FiniteDifferentialEquation E) : Prop :=
  ∃ raw, decodeDeductionEquation row = .ok raw ∧
    realizeFiniteEquation E lookup coordinate raw = some equation

/-- Every enclosing trial must be interpreted, in order. A context with an
unresolved trial cannot be silently shortened to its finite subset. -/
def ContextRealizes (frames : List TrialFrame) (context : List (FiniteDifferentialEquation E)) : Prop :=
  List.Forall₂ (fun frame e => TrialRealizes lookup coordinate frame.row e) frames context

/-- Soundness obligation for each successfully scoped AND interpreted
retained finite trial. This does not assert that every retained row admits
such an interpretation; `FiniteTrialCoverage` is a separate obligation. -/
def RetainedTrialRefutations (rows : List Raw.LogRow) : Prop :=
  ∀ entry ∈ scopeRows rows, ∀ frames direction,
    entry.scope = .scoped frames (some direction) →
    ∀ context equation, ContextRealizes lookup coordinate frames context →
      TrialRealizes lookup coordinate entry.row equation → TrialRefuted context equation

/-- Retained D/DI rows are conclusions conditional on the complete enclosing
trial stack. Root rows have the empty context. NULL-reason hints are excluded. -/
def RetainedConditionalFacts (rows : List Raw.LogRow) : Prop :=
  ∀ entry ∈ scopeRows rows, ∀ frames,
    entry.scope = .scoped frames none →
    ∀ context equation, ContextRealizes lookup coordinate frames context →
      DeductionRealizes lookup coordinate entry.row equation → ConditionalFact context equation

/-- Explicit coverage for a selected finite trial row, including its entire
enclosing context. This predicate cannot be concluded merely from presence
in `scopeRows`, and is intentionally not required for sentinel/unknown rows. -/
def FiniteTrialCoverage (rows : List Raw.LogRow) (row : Raw.LogRow) : Prop :=
  ∃ entry ∈ scopeRows rows, entry.row = row ∧ ∃ frames direction context equation,
    entry.scope = .scoped frames (some direction) ∧
    ContextRealizes lookup coordinate frames context ∧
    TrialRealizes lookup coordinate row equation

end KIP126.Computation.LinCalculations.ConditionalDifferentials

namespace KIP126.Computation.LinCalculations.ConditionalDifferentials
open CategoryTheory
universe u v w

/-- cm3：指定谱序列与坐标下，条件微分推理的可靠性。
每条已解释的 trial 在其完整前提下得到反驳；D/DI 记录给出相同前提下
成立的微分结论。全日志是否都可解释由单独的覆盖条件描述。
这是参数化条件，不是固定外部假设的组成部分。 -/
structure ConditionalDifferentialSoundness {R : Type u} [Ring R] {ι : Type w}
    (E : ι → SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))
    (lookup : String → Option ι)
    (coordinates : Computation.LinCalculations.ConditionalDifferentials.CoordinateDictionary E)
    (rows : List Computation.LinCalculations.Raw.LogRow) : Prop where
  trial_refutations :
    Computation.LinCalculations.ConditionalDifferentials.RetainedTrialRefutations lookup coordinates rows
  conditional_facts :
    Computation.LinCalculations.ConditionalDifferentials.RetainedConditionalFacts lookup coordinates rows


end KIP126.Computation.LinCalculations.ConditionalDifferentials
