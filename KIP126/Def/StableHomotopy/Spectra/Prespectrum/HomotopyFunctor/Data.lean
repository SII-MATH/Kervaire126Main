module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum
public import Mathlib.CategoryTheory.Types.Basic

@[expose] public section

/-! The actual cubical stable quotient, as a functor on prespectra and
on their specified ordinary stable localization. -/

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory TypeCat

universe u

/-- Integer stable homotopy before localization, using exactly the
point-set cubical representatives and their displayed relations. -/
def Prespectrum.stableHomotopyFunctor (d : ℤ) : Prespectrum.{u} ⥤ Type u where
  obj X := X.StableHomotopy d
  map f := ofHom (Prespectrum.stableHomotopyMap f d)
  map_id X := by
    ext x
    induction x using Quot.inductionOn with
    | h a => rfl
  map_comp f g := by
    ext x
    induction x using Quot.inductionOn with
    | h a => rfl

/-- Stable homotopy of the ordinary source localization. This descends the
actual quotient functor, rather than supplying a separate homotopy model. -/
noncomputable def sourceStableHomotopyFunctor (d : ℤ) : SourceCategory.{u} ⥤ Type u :=
  Localization.Construction.lift (Prespectrum.stableHomotopyFunctor d)
    (fun _ _ _ hf => (bijective_iff_isIso_ofHom _).mp (hf d))

/-- An ordinary source isomorphism gives an equivalence of the actual
stable cubical quotients in each integer degree. -/
noncomputable def Prespectrum.stableHomotopyEquivOfSourceIso
    {X Y : Prespectrum.{u}} (e : sourceLocalization.obj X ≅ sourceLocalization.obj Y)
    (d : ℤ) : X.StableHomotopy d ≃ Y.StableHomotopy d :=
  ((sourceStableHomotopyFunctor d).mapIso e).toEquiv

end KIP126.StableHomotopy.Spectra
