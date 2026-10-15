module

public import KIP126.Def.Synthetic.Localization.Data
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

/-!
# Explicit recovery of spectra after λ inversion

The comparison supplied here is between the specified ν followed by the
specified reflection and the inverse of an equivalence with classical spectra.
It does not identify ν with the right adjoint of realization: that right
adjoint is the spectral Yoneda embedding.

Source: Pstrągowski, `prop:spectral_yoneda_embedding_the_tau_inversion_of_the_synthetic_analogue`,
`thm:tau_invertible_synthetic_spectra_are_just_spectra`, and
`prop:tau_inversion_cocontinuous_symmetric_monoidal_left_inverse_to_synthetic_analogue`.
These are explicit input records in the project's abstract homotopy background;
no infinity-category model, E∞ algebra, or source theorem is constructed here.
-/

namespace KIP126.Synthetic.Context

open CategoryTheory KIP126.StableHomotopy

universe u v u' v'

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]

/-- The specified localization recovers the same classical category and ν. -/
structure LambdaRecovery (N : NuFunctorData C Syn) where
  localization : LambdaLocalization Syn
  equivalence : LambdaInvertibleObjects Syn ≌ C
  nuLocalization : N.functor ⋙ localization.reflector ≅ equivalence.inverse

variable {N : NuFunctorData C Syn}

/-- Underlying-spectrum realization, with the source and target fixed. -/
def LambdaRecovery.realization (R : LambdaRecovery N) : Syn ⥤ C :=
  R.localization.reflector ⋙ R.equivalence.functor

/-- The spectral Yoneda embedding determined by the same equivalence. -/
def LambdaRecovery.spectralYoneda (R : LambdaRecovery N) : C ⥤ Syn :=
  R.equivalence.inverse ⋙ lambdaInclusion Syn

/-- Realization is left adjoint to spectral Yoneda, not to ν. -/
def LambdaRecovery.adjunction (R : LambdaRecovery N) :
    R.realization ⊣ R.spectralYoneda :=
  R.localization.adjunction.comp R.equivalence.toAdjunction

/-- Applying realization after the specified ν recovers the identity functor. -/
def LambdaRecovery.nuRealizationIso (R : LambdaRecovery N) :
    N.functor ⋙ R.realization ≅ 𝟭 C :=
  (Functor.associator N.functor R.localization.reflector R.equivalence.functor).symm ≪≫
    Functor.isoWhiskerRight R.nuLocalization R.equivalence.functor ≪≫ R.equivalence.counitIso

/-- The additional symmetric monoidal input on the actual realization.
No monoidal structure on the full subcategory is presupposed. In the source,
its local unit is the reflection of the synthetic sphere; it need not be the
ambient unit. No strong monoidal structure on the inclusion is assumed here. -/
structure LambdaRecovery.SymmetricMonoidal (R : LambdaRecovery N)
    [SymmetricCategory C] [SymmetricCategory Syn] where
  realization : R.realization.Braided

end KIP126.Synthetic.Context
