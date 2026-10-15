module

public import KIP126.Def.Synthetic.PageExtension.Family.Data
public import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Restriction.Data
public import KIP126.Def.Synthetic.PageExtension.Relation.Data
public import KIP126.Def.Synthetic.ExtensionSS.Solutions.Data

@[expose] public section

/-! Representative fibers for the same actual normalized ESS and its fixed
classical labels. These are concrete subtypes of pairs of homotopy lifts. -/

namespace KIP126.Synthetic.PageExtension

set_option backward.isDefEq.respectTransparency false
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.SpectralSequence
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

namespace NormalizedPageFamily

/-- The actual target label, transported solely along the ESS index equation. -/
noncomputable def finiteTargetClass (P : NormalizedPageFamily H N F f)
    (q : ℕ) (hq : 0 < q) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n) (hkq : P.lambdaExponent n < q)
    (y : PageRepresentatives.cycles H Y (q - P.lambdaExponent n : ℕ) (s + n, t + n)) :
    ModuleCat.of ℤ (ULift.{v} ℤ) ⟶
      ((P.finite q hq).complex (P.degree s t)).assocGraded (s + n) 0 :=
  (P.finite q hq).targetClass (P.degree s t) n s
    (elementMap (P.finiteTargetMap q hq n s t hn hkq y))

/-- Actual finite representative solutions with both classical labels fixed. -/
def FiniteSolutions (P : NormalizedPageFamily H N F f)
    (q : ℕ) (hq : 0 < q) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n) (hkq : P.lambdaExponent n < q)
    (x : PageRepresentatives.cycles H X q (s, t))
    (y : PageRepresentatives.cycles H Y (q - P.lambdaExponent n : ℕ) (s + n, t + n)) :=
  FilteredComplex.Solutions.Fiber ((P.finite q hq).complex (P.degree s t)) n s 1
    (elementMap (P.finiteSourceMap q hq s t x))
    (P.finiteTargetClass q hq n s t hn hkq y)

noncomputable def infiniteTargetClass (P : NormalizedPageFamily H N F f)
    (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (y : PageRepresentatives.permanentCycles H Y (s + n, t + n)) :
    ModuleCat.of ℤ (ULift.{v} ℤ) ⟶
      (P.infinite.complex (P.degree s t)).assocGraded (s + n) 0 :=
  P.infinite.targetClass (P.degree s t) n s
    (elementMap (P.infiniteTargetMap n s t hn y))

/-- Actual solutions in the untruncated normalized-map ESS. Existence is
not inferred merely from nonemptiness of all the finite fibers. -/
def InfiniteSolutions (P : NormalizedPageFamily H N F f)
    (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (x : PageRepresentatives.permanentCycles H X (s, t))
    (y : PageRepresentatives.permanentCycles H Y (s + n, t + n)) :=
  FilteredComplex.Solutions.Fiber (P.infinite.complex (P.degree s t)) n s 1
    (elementMap (P.infiniteSourceMap s t x)) (P.infiniteTargetClass n s t hn y)

end NormalizedPageFamily
end KIP126.Synthetic.PageExtension
