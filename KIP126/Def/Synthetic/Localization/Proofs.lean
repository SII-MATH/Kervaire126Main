module

public import KIP126.Def.Synthetic.Localization.Predicates

@[expose] public section

/-! Consequences of the explicit adjunction and of the existing natural λ.
These do not construct the localization or assume a spectral Yoneda model. -/

namespace KIP126.Synthetic.Context

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

theorem isLambdaInvertible_iff_of_iso {X Y : Syn} (e : X ≅ Y) :
    IsLambdaInvertible X ↔ IsLambdaInvertible Y :=
  NatTrans.isIso_app_iff_of_iso SyntheticCategory.lam e

theorem LambdaLocalization.localized_isLambdaInvertible
    (L : LambdaLocalization Syn) (X : Syn) :
    IsLambdaInvertible (L.endofunctor.obj X) :=
  (L.reflector.obj X).property

@[simp] theorem LambdaLocalization.unit_lift (L : LambdaLocalization Syn)
    {X Y : Syn} (hY : IsLambdaInvertible Y) (f : X ⟶ Y) :
    L.unit.app X ≫ L.lift hY f = f := by
  simpa only [LambdaLocalization.unit, LambdaLocalization.lift,
    Adjunction.homEquiv_unit, ObjectProperty.ι_map] using
    (L.adjunction.homEquiv X ⟨Y, hY⟩).apply_symm_apply f

theorem LambdaLocalization.lift_unique (L : LambdaLocalization Syn)
    {X Y : Syn} (hY : IsLambdaInvertible Y) (f : X ⟶ Y)
    (g : L.endofunctor.obj X ⟶ Y) (hg : L.unit.app X ≫ g = f) :
    g = L.lift hY f := by
  have h : ObjectProperty.homMk (P := IsLambdaInvertible)
      (X := L.reflector.obj X) (Y := ⟨Y, hY⟩) g =
      (L.adjunction.homEquiv X ⟨Y, hY⟩).symm f := by
    apply (L.adjunction.homEquiv X ⟨Y, hY⟩).injective
    rw [Equiv.apply_symm_apply]
    change L.unit.app X ≫ g = f
    exact hg
  exact congrArg (fun k => k.hom) h

/-- The chosen unit satisfies the full hom-set universal property. -/
theorem LambdaLocalization.unit_isLocalizationMap (L : LambdaLocalization Syn)
    (X : Syn) : IsLambdaLocalizationMap (L.unit.app X) := by
  refine ⟨L.localized_isLambdaInvertible X, ?_⟩
  intro Z hZ f
  exact ⟨L.lift hZ f, L.unit_lift hZ f, fun g hg => L.lift_unique hZ f g hg⟩

/-- A synthetic object is already local exactly when its unit is invertible. -/
theorem LambdaLocalization.unit_isIso_iff (L : LambdaLocalization Syn) (X : Syn) :
    IsIso (L.unit.app X) ↔ IsLambdaInvertible X := by
  rw [show L.unit = L.adjunction.unit from rfl,
    L.adjunction.isIso_unit_app_iff_mem_essImage]
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    exact (isLambdaInvertible_iff_of_iso e).mp Y.property
  · intro hX
    exact ⟨⟨X, hX⟩, ⟨Iso.refl X⟩⟩

/-- Naturality of λ and full faithfulness of its suspension imply that
precomposition with λ is bijective on maps into an actual local object. -/
theorem lambda_isLocalEquivalence (X : Syn) :
    IsLambdaLocalEquivalence (SyntheticCategory.lam.app X) := by
  intro Z hZ
  letI : IsIso (SyntheticCategory.lam.app Z) := hZ
  let hS := SyntheticCategory.biShift_fullyFaithful (Syn := Syn) (0, -1)
  have hnat (f : X ⟶ Z) :
      (SyntheticCategory.biShift (0, -1)).map f ≫ SyntheticCategory.lam.app Z =
        SyntheticCategory.lam.app X ≫ f := by
    have h := SyntheticCategory.lam.naturality f
    dsimp only [Functor.id_map, Functor.id_obj] at h
    exact h
  constructor
  · intro f g h
    apply hS.map_injective
    apply (cancel_mono (SyntheticCategory.lam.app Z)).mp
    rw [hnat, hnat]
    exact h
  · intro g
    obtain ⟨f, hf⟩ := hS.map_surjective (g ≫ inv (SyntheticCategory.lam.app Z))
    refine ⟨f, ?_⟩
    change SyntheticCategory.lam.app X ≫ f = g
    rw [← hnat, hf]
    simp

/-- A map indistinguishable by all local targets becomes invertible under the
specified reflector. This follows from its adjunction, rather than being a
separate localization assumption. -/
theorem LambdaLocalization.map_isIso_of_isLocalEquivalence
    (L : LambdaLocalization Syn) {X Y : Syn} (f : X ⟶ Y)
    (hf : IsLambdaLocalEquivalence f) : IsIso (L.reflector.map f) := by
  apply isIso_of_coyoneda_map_bijective
  intro Z
  have h : (fun g : L.reflector.obj Y ⟶ Z => L.reflector.map f ≫ g) =
      (fun g => (L.adjunction.homEquiv X Z).symm
        (f ≫ (L.adjunction.homEquiv Y Z) g)) := by
    funext g
    apply (L.adjunction.homEquiv X Z).injective
    rw [Equiv.apply_symm_apply, L.adjunction.homEquiv_naturality_left]
  rw [h]
  exact (L.adjunction.homEquiv X Z).symm.bijective.comp
    ((hf Z.obj Z.property).comp (L.adjunction.homEquiv Y Z).bijective)

/-- The reflector really inverts the existing λ maps. -/
theorem LambdaLocalization.map_lambda_isIso (L : LambdaLocalization Syn) (X : Syn) :
    IsIso (L.reflector.map (SyntheticCategory.lam.app X)) :=
  L.map_isIso_of_isLocalEquivalence _ (lambda_isLocalEquivalence X)

end KIP126.Synthetic.Context
