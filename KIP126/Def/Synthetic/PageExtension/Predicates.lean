module

public import KIP126.Def.Synthetic.PageExtension.Data

@[expose] public section

namespace KIP126.Synthetic.PageExtension
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.SpectralSequence

universe u v u' v'
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

def FinitePageExtension (P : NormalizedPageFamily H N F f)
    (r : ℕ) (n s t : ℤ) (x : PageRepresentatives.Ambient H X (s, t))
    (y : PageRepresentatives.Ambient H Y (s + n, t + n)) : Prop :=
  Nonempty (FiniteExtensionWitness P r n s t x y)

def InfinitePageExtension (P : NormalizedPageFamily H N F f)
    (n s t : ℤ) (x : PageRepresentatives.Ambient H X (s, t))
    (y : PageRepresentatives.Ambient H Y (s + n, t + n)) : Prop :=
  Nonempty (InfiniteExtensionWitness P n s t x y)

def FiniteExtensionWitness.Essential {P : NormalizedPageFamily H N F f}
    {r : ℕ} {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
    {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
    (W : FiniteExtensionWitness P r n s t x y) : Prop :=
  EssentialDifferentialRelation
    ((P.finite (r - 1) (Nat.sub_pos_of_lt W.page_ge_two)).ess (P.degree s t)) n (s, 1)
    (elementMap (P.finiteSourceMap (r - 1) (Nat.sub_pos_of_lt W.page_ge_two) s t W.sourceCycle))
    (elementMap (P.finiteTargetMap (r - 1) (Nat.sub_pos_of_lt W.page_ge_two) n s t
      W.exponent_le_length W.exponent_lt_quotient W.targetCycle))

def InfiniteExtensionWitness.Essential {P : NormalizedPageFamily H N F f}
    {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
    {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
    (W : InfiniteExtensionWitness P n s t x y) : Prop :=
  EssentialDifferentialRelation (P.infinite.ess (P.degree s t)) n (s, 1)
    (elementMap (P.infiniteSourceMap s t W.sourceCycle))
    (elementMap (P.infiniteTargetMap n s t W.exponent_le_length W.targetCycle))

end KIP126.Synthetic.PageExtension
