module

public import KIP126.Def.Synthetic.ExtensionRelation.Data

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory KIP126.SpectralSequence
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.PageExtension
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} {unit : S_0_0 ⟶ H}
  {F : SyntheticAdamsFamily Syn} {X Y : Syn} (g : X ⟶ Y)
  (cx : TowerConvergence unit F X) (cy : TowerConvergence unit F Y)

/-- An extension equation is an actual solution fiber of g on filtered
homotopy groups. Changes of representative supply its full indeterminacy. -/
def ExtensionEquation (p : ℤ × ℤ) (s n : ℤ)
    (x : ((F.obj X).sequence.ssData (s, p.1 + s, p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (s + n, p.1 + (s + n), p.2)).eInfty) : Prop :=
  0 ≤ n ∧ Nonempty (FilteredComplex.Solutions.Fiber (extensionComplex unit g p) n s 1
    (elementMap ((extensionSourceIso unit g cx p s).hom x))
    (elementMap ((extensionTargetIso unit g cy p (s + n)).hom y)))

/-- Essential means nonzero modulo the *actual* shorter extension images,
which are the boundary subobject of the same filtered complex at page n. -/
def EssentialExtension (p : ℤ × ℤ) (s n : ℤ)
    (x : ((F.obj X).sequence.ssData (s, p.1 + s, p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (s + n, p.1 + (s + n), p.2)).eInfty) : Prop :=
  ExtensionEquation g cx cy p s n x y ∧
    ¬ Subobject.Factors ((extensionComplex unit g p).boundarySubobject (s + n) 0 n.toNat)
      (elementMap ((extensionTargetIso unit g cy p (s + n)).hom y))

end KIP126.Synthetic.SpectralSequence
