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

end KIP126.Synthetic.Context
