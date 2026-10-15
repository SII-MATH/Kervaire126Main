module

public import KIP126.Def.Synthetic.Localization.Recovery.Data
public import KIP126.Def.Synthetic.Localization.Proofs

@[expose] public section

namespace KIP126.Synthetic.Context

open CategoryTheory KIP126.StableHomotopy

set_option backward.isDefEq.respectTransparency false

universe u v u' v'

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
  {N : NuFunctorData C Syn}

/-- Spectral Yoneda lands in the actual λ-invertible subcategory. -/
theorem LambdaRecovery.spectralYoneda_isLambdaInvertible (R : LambdaRecovery N) (X : C) :
    IsLambdaInvertible (R.spectralYoneda.obj X) :=
  (R.equivalence.inverse.obj X).property

/-- Recovery implies faithfulness of the given ν; fullness needs additional
input and is not asserted merely from a left inverse. -/
theorem LambdaRecovery.nu_faithful (R : LambdaRecovery N) : N.functor.Faithful :=
  Functor.Faithful.of_comp_iso R.nuRealizationIso

/-- The recovery identifications are natural for every actual classical map. -/
theorem LambdaRecovery.recovery_naturality (R : LambdaRecovery N) {X Y : C}
    (f : X ⟶ Y) :
    R.realization.map (N.functor.map f) ≫ R.nuRealizationIso.hom.app Y =
      R.nuRealizationIso.hom.app X ≫ f :=
  R.nuRealizationIso.hom.naturality f

/-- The specified ν-to-Yoneda map is a localization unit in the hom-set sense. -/
theorem LambdaRecovery.nuToSpectralYoneda_isLocalizationMap
    (R : LambdaRecovery N) (X : C) :
    IsLambdaLocalizationMap (R.nuToSpectralYoneda.app X) := by
  refine ⟨R.spectralYoneda_isLambdaInvertible X, ?_⟩
  intro Z hZ f
  let e := (lambdaInclusion Syn).mapIso (R.nuLocalization.app X)
  refine ⟨e.inv ≫ R.localization.lift hZ f, ?_, ?_⟩
  · change (R.localization.unit.app (N.functor.obj X) ≫ e.hom) ≫
        (e.inv ≫ R.localization.lift hZ f) = f
    simp only [Category.assoc, Iso.hom_inv_id_assoc, LambdaLocalization.unit_lift]
  · intro g hg
    have h : e.hom ≫ g = R.localization.lift hZ f := by
      apply R.localization.lift_unique hZ f
      change (R.localization.unit.app (N.functor.obj X) ≫ e.hom) ≫ g = f at hg
      simpa only [Category.assoc] using hg
    rw [← h]
    simp

end KIP126.Synthetic.Context
