module

public import KIP126.Def.Synthetic.PageExtension.Solutions.Data
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Order.Proofs

@[expose] public section

/-! Finite representative fibers for fixed permanent classical labels.
Every finite label is the inclusion of the same original representative;
this definition neither chooses a solution nor asserts nonemptiness. -/

namespace KIP126.Synthetic.PageExtension

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams.PageRepresentatives

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

namespace NormalizedPageFamily

/-- The actual finite solution fiber at a quotient longer than the λ
exponent, using the inclusions of the fixed permanent source and target.
The strict inequality also supplies positivity of the quotient length. -/
def PermanentFiniteSolutions (P : NormalizedPageFamily H N F f)
    (q : ℕ) (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (hkq : P.lambdaExponent n < q)
    (x : permanentCycles H X (s, t))
    (y : permanentCycles H Y (s + n, t + n)) : Type v :=
  P.FiniteSolutions q (by omega) n s t hn hkq
    (Submodule.inclusion (permanentCycles_le_cycles H X (s, t) q) x)
    (Submodule.inclusion (permanentCycles_le_cycles H Y (s + n, t + n)
      (q - P.lambdaExponent n : ℕ)) y)

end NormalizedPageFamily
end KIP126.Synthetic.PageExtension
