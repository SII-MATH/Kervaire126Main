module

public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.CompactOpen
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] public section

section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

/-- The actual compact-open continuous-map functor with fixed source. -/
noncomputable def continuousMapFunctor (K : TopCat.{u}) : TopCat.{u} ⥤ TopCat.{u} where
  obj X := TopCat.of C(K,X)
  map f := TopCat.ofHom ⟨fun g => f.hom.comp g,ContinuousMap.continuous_postcomp f.hom⟩
  map_id X := by ext f x; rfl
  map_comp f g := by ext h x; rfl

/-- Product with a locally compact space is genuinely left adjoint to
its compact-open mapping-space functor, by the continuous exponential law. -/
noncomputable def tensorLeftContinuousMapAdjunction (K : TopCat.{u}) [LocallyCompactSpace K] :
    tensorLeft K ⊣ continuousMapFunctor K :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => {
      toFun := fun f => TopCat.ofHom (ContinuousMap.curry (f.hom.comp ⟨Prod.swap,continuous_swap⟩))
      invFun := fun g => TopCat.ofHom ((ContinuousMap.uncurry g.hom).comp ⟨Prod.swap,continuous_swap⟩)
      left_inv := fun f => by ext ⟨k,x⟩; rfl
      right_inv := fun g => by ext x k; rfl }
    homEquiv_naturality_left_symm := fun f g => by ext ⟨k,x⟩; rfl
    homEquiv_naturality_right := fun f g => by ext x; rfl }

end KIP126.Topology

end

section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w

/-- Product with an actual locally compact space commutes with arbitrary
existing colimits; this is proved from the compact-open adjunction. -/
theorem tensorLeft_preservesColimits_of_locallyCompact (K : TopCat.{u}) [LocallyCompactSpace K] :
    PreservesColimitsOfSize.{v,w} (tensorLeft K) := by
  letI : (tensorLeft K).IsLeftAdjoint := (tensorLeftContinuousMapAdjunction K).isLeftAdjoint
  infer_instance

end KIP126.Topology

end
