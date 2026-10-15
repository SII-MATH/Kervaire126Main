module

public import KIP126.Def.Synthetic.AdamsSequence.Data

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory
open KIP126.Synthetic.Context
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- A normalized page map of the existing family functor. -/
def familyPageMap (F : SyntheticAdamsFamily Syn) {X Y : Syn} (f : X ⟶ Y)
    (r : ℤ) (i : Tridegree) : (F.obj X).Page r i ⟶ (F.obj Y).Page r i :=
  eqToHom (by simp only [SyntheticAdamsSS.Page, SyntheticAdamsFamily.obj,
    KIP126.SpectralSequence.Page, F.firstPage]) ≫
    (F.functor.map f).pageMap r i ≫
      eqToHom (by simp only [SyntheticAdamsSS.Page, SyntheticAdamsFamily.obj,
        KIP126.SpectralSequence.Page, F.firstPage])
end
end KIP126.Synthetic.SpectralSequence
