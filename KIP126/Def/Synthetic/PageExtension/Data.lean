module

public import KIP126.Def.Synthetic.PageExtension.Family.Data
public import KIP126.Def.Synthetic.PageExtension.Relation.Data

@[expose] public section

namespace KIP126.Synthetic.PageExtension
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.SpectralSequence

universe u v u' v'
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

/-- An actual finite extension between specified classical E₂ classes.
The target cycle level is q-k, where q=r-1 and k=n-e(f); hence it is exactly
the paper's Z_(r-1-n+e). Source and target transports are fixed by P. -/
structure FiniteExtensionWitness (P : NormalizedPageFamily H N F f)
    (r : ℕ) (n s t : ℤ)
    (x : PageRepresentatives.Ambient H X (s, t))
    (y : PageRepresentatives.Ambient H Y (s + n, t + n)) where
  page_ge_two : 2 ≤ r
  exponent_le_length : (normalizedExponent H f : ℤ) ≤ n
  exponent_lt_quotient : P.lambdaExponent n < r - 1
  sourceCycle : PageRepresentatives.cycles H X (r - 1 : ℕ) (s, t)
  targetCycle : PageRepresentatives.cycles H Y (r - 1 - P.lambdaExponent n : ℕ)
    (s + n, t + n)
  source_eq : sourceCycle.val = x
  target_eq : targetCycle.val = y
  relation : DifferentialRelation
    ((P.finite (r - 1) (by omega)).ess (P.degree s t)) n (s, 1)
    (elementMap (P.finiteSourceMap (r - 1) (by omega) s t sourceCycle))
    (elementMap (P.finiteTargetMap (r - 1) (by omega) n s t
      exponent_le_length exponent_lt_quotient targetCycle))

/-- The infinite clause uses actual permanent E₂ representatives and the
untruncated normalized map, with no arithmetic involving infinity. -/
structure InfiniteExtensionWitness (P : NormalizedPageFamily H N F f)
    (n s t : ℤ)
    (x : PageRepresentatives.Ambient H X (s, t))
    (y : PageRepresentatives.Ambient H Y (s + n, t + n)) where
  exponent_le_length : (normalizedExponent H f : ℤ) ≤ n
  sourceCycle : PageRepresentatives.permanentCycles H X (s, t)
  targetCycle : PageRepresentatives.permanentCycles H Y (s + n, t + n)
  source_eq : sourceCycle.val = x
  target_eq : targetCycle.val = y
  relation : DifferentialRelation (P.infinite.ess (P.degree s t)) n (s, 1)
    (elementMap (P.infiniteSourceMap s t sourceCycle))
    (elementMap (P.infiniteTargetMap n s t exponent_le_length targetCycle))

/-- The target coset is the inverse image of the actual ESS
boundary coset in the paper's target cycle module. The ESS boundary includes all shorter ESS images. Identifying this inverse
image with the paper's ordinary Adams boundary plus shorter-image formula
requires comparison coherence and a kernel theorem; that identification is
not asserted for arbitrary top-weight comparison isomorphisms. -/
def FiniteExtensionWitness.targetCoset {P : NormalizedPageFamily H N F f}
    {r : ℕ} {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
    {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
    (W : FiniteExtensionWitness P r n s t x y) :
    Set (PageRepresentatives.cycles H Y (r - 1 - P.lambdaExponent n : ℕ) (s + n, t + n)) :=
  { z | elementMap (P.finiteTargetMap (r - 1) (Nat.sub_pos_of_lt W.page_ge_two)
      n s t W.exponent_le_length W.exponent_lt_quotient z) ∈
    KIP126.Synthetic.PageExtension.targetCoset ((P.finite (r - 1) (Nat.sub_pos_of_lt W.page_ge_two)).ess (P.degree s t))
      n (s, 1) (elementMap (P.finiteTargetMap (r - 1) (Nat.sub_pos_of_lt W.page_ge_two)
        n s t W.exponent_le_length W.exponent_lt_quotient W.targetCycle)) }

def InfiniteExtensionWitness.targetCoset {P : NormalizedPageFamily H N F f}
    {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
    {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
    (W : InfiniteExtensionWitness P n s t x y) :
    Set (PageRepresentatives.permanentCycles H Y (s + n, t + n)) :=
  { z | elementMap (P.infiniteTargetMap n s t W.exponent_le_length z) ∈
    KIP126.Synthetic.PageExtension.targetCoset (P.infinite.ess (P.degree s t)) n (s, 1)
      (elementMap (P.infiniteTargetMap n s t W.exponent_le_length W.targetCycle)) }

end
end KIP126.Synthetic.PageExtension
