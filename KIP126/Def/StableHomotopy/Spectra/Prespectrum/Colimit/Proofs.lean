module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Colimit.Data

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u
variable {J : Type u} [Category.{u} J]

set_option backward.isDefEq.respectTransparency false

/-- The displayed strict cocone satisfies the actual colimit universal property. -/
noncomputable def pointwiseColimitCocone_isColimit (F : J ⥤ Prespectrum.{u}) :
    IsColimit (pointwiseColimitCocone F) where
  desc := pointwiseColimitDesc
  fac c j := by
    apply Hom.ext
    funext n
    exact congrArg BasedSpace.Hom.map (colimit.ι_desc (pointwiseCoconeLevel c n) j)
  uniq c m hm := by
    apply Hom.ext
    funext n
    change (⟨m.level n, m.point n⟩ : pointwiseColimitLevel F n ⟶ c.pt.level n).map =
      (colimit.desc (F ⋙ evaluationFunctor n) (pointwiseCoconeLevel c n)).map
    apply congrArg (fun (f : pointwiseColimitLevel F n ⟶ c.pt.level n) => f.map)
    apply colimit.hom_ext (F := F ⋙ evaluationFunctor n)
    intro j
    rw [colimit.ι_desc]
    apply BasedSpace.Hom.ext
    exact congrArg (fun f => f.level n) (hm j)

/-- Arbitrary small colimits exist in the original strict prespectrum category. -/
instance prespectrumHasColimits : HasColimitsOfSize.{u,u} Prespectrum.{u} where
  has_colimits_of_shape _ :=
    ⟨fun F => ⟨⟨pointwiseColimitCocone F, pointwiseColimitCocone_isColimit F⟩⟩⟩

end KIP126.StableHomotopy.Spectra.Prespectrum
