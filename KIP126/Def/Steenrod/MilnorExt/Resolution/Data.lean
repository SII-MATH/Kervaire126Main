module

public import KIP126.Def.Steenrod.MilnorExt.Data
public import KIP126.Def.Steenrod.MilnorExt.Cofree.Data
public import Mathlib.CategoryTheory.Abelian.Injective.Ext

@[expose] public section

/-!
An injective resolution identified with the prescribed normalized Milnor
cofree terms. The differential and augmentation are fixed by their actual
polynomial formulas; they are not unconstrained operations. The resolution also includes the comparison of cocycles with their
polynomial representatives; its existence is a separate mathematical claim.
-/

namespace KIP126.Steenrod.Milnor.Ext

open CategoryTheory KIP126.Algebra
open KIP126.Algebra.GradedComodule

noncomputable section

/-- A normalized cofree resolution of the trivial Milnor comodule, retaining
comodule isomorphisms to the fixed terms and all polynomial compatibility. -/
structure CobarResolution where
  resolution : InjectiveResolution (trivialAt 0)
  termIso : ∀ s : ℕ, resolution.cocomplex.X s ≅ Cofree.term s
  differential : ∀ (s : ℕ) (n : ℤ) (z : (resolution.cocomplex.X s).A n),
    Cofree.termPolynomial (s + 1) n
        (((resolution.cocomplex.d s (s + 1) ≫ (termIso (s + 1)).hom).f n).hom z) =
      Cofree.rawDifferential s
        (Cofree.termPolynomial s n (((termIso s).hom.f n).hom z))
  augmentation :
    Cofree.termPolynomial 0 0
      (((resolution.ι.f 0 ≫ (termIso 0).hom).f 0).hom
        (degreeLineGenerator F2 0)) = 1

/-- Evaluate a representative on the canonical generator in its actual
internal degree, then use the specified cofree coordinates. -/
def CobarResolution.representativePolynomial (R : CobarResolution)
    {s : ℕ} {t : ℤ} (f : trivialAt t ⟶ R.resolution.cocomplex.X s) :
    TensorPower (s + 1) :=
  Cofree.termPolynomial s t
    (((f ≫ (R.termIso s).hom).f t).hom (degreeLineGenerator F2 t))

end

end KIP126.Steenrod.Milnor.Ext
