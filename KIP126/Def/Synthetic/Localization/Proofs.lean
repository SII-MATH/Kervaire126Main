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
