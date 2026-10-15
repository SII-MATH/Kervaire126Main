module

public import KIP126.Def.ComputationModel.Interpretation.ConditionalDifferentials.Decode.Data
public import KIP126.Def.SpectralSequence.Computation.Predicates

@[expose] public section

/-!
# Mathematical data for conditional finite-page branches

The object family and partial coordinate dictionary are explicit parameters.
A project application must bind them to the fixed spectrum catalogue and
its actual E₂ comparison. No log text supplies an arbitrary proposition or
an independently chosen spectral-sequence differential.
-/

namespace KIP126.Computation.LinCalculations.ConditionalDifferentials

open CategoryTheory KIP126
noncomputable section

universe u v w
variable {R : Type u} [Ring R] {ι : Type w}
  (E : ι → SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ))

/-- An equation on the EXISTING internal differential, with actual E₂ labels.
The bounds deliberately exclude the program's 999/1000/1001 sentinels. -/
structure FiniteDifferentialEquation where
  object : ι
  r : ℤ
  finitePage : 2 ≤ r ∧ r < 999
  sourceDegree : ℤ × ℤ
  targetDegree : ℤ × ℤ
  source : (E object).Page 2 sourceDegree
  target : (E object).Page 2 targetDegree

/-- The same partial coordinate-dictionary shape used by staircase
interpretation. Out-of-range or unknown coordinates return `none`.
This type alone does not certify that a dictionary is the pinned one. -/
abbrev CoordinateDictionary :=
  (i : ι) → (p : ℤ × ℤ) → List Nat → Option ((E i).Page 2 p)

/-- Bind a syntactic payload to actual objects and actual E₂ classes.
The existing `HasDifferential` predicate, defined in the predicates module,
will determine its mathematical truth; this function asserts none. -/
def realizeFiniteEquation (lookup : String → Option ι)
    (coordinate : CoordinateDictionary E) (raw : RawEquation) :
    Option (FiniteDifferentialEquation E) :=
  match lookup raw.name with
  | none => none
  | some i =>
      match coordinate i raw.sourceDegree raw.sourceIndices,
          coordinate i raw.targetDegree raw.targetIndices with
      | some x, some y =>
          if h : 2 ≤ raw.r ∧ raw.r < 999 then
            some ⟨i, raw.r, h, raw.sourceDegree, raw.targetDegree, x, y⟩
          else none
      | _, _ => none

/-- All binary sums, including zero. Duplicates are retained if the supplied
vectors are dependent. The count-zero window contains exactly the zero sum,
as in `deduce.cpp:412–415,461–464`; no basis independence is assumed here. -/
def binarySums {A : Type*} [AddMonoid A] : List A → List A
  | [] => [0]
  | x :: xs =>
      let rest := binarySums xs
      rest ++ rest.map (fun y => x + y)

/-- An explicit finite candidate window. `first` records the index of its
first vector in the program's staircase basis; the list contains exactly
the selected vectors, so its length is `nd.count`. Supplying this data does
NOT prove that the window is exhaustive or that it came from the artifact.
The missing staircase snapshot/basis binding must be supplied separately. -/
inductive DifferentialCandidates where
  | forward (i : ι) (r : ℤ) (finitePage : 2 ≤ r ∧ r < 999)
      (p q : ℤ × ℤ) (source : (E i).Page 2 p)
      (first : Nat) (vectors : List ((E i).Page 2 q))
  | inverse (i : ι) (r : ℤ) (finitePage : 2 ≤ r ∧ r < 999)
      (p q : ℤ × ℤ) (target : (E i).Page 2 q)
      (first : Nat) (vectors : List ((E i).Page 2 p))

/-- Candidate equations keep one endpoint fixed and range over every
binary sum in the specified window. Inverse candidates vary the SOURCE. -/
def DifferentialCandidates.equations : DifferentialCandidates E → List (FiniteDifferentialEquation E)
  | .forward i r h p q x _ vectors =>
      (binarySums vectors).map (fun y => ⟨i, r, h, p, q, x, y⟩)
  | .inverse i r h p q y _ vectors =>
      (binarySums vectors).map (fun x => ⟨i, r, h, p, q, x, y⟩)

end
end KIP126.Computation.LinCalculations.ConditionalDifferentials
