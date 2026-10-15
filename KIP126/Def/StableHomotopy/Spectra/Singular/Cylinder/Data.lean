module

public import KIP126.Def.StableHomotopy.Spectra.Singular
public import KIP126.Def.Topology.SimplicialRealization.Pullback.StandardSimplex.Data

@[expose] public section

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory Opposite Simplicial MonoidalCategory
open scoped unitInterval

universe u

/-- An endpoint inclusion of the actual simplicial cylinder. -/
noncomputable def realizationCylinderEnd (K : SSet.{u}) (i : Fin 2) : K ⟶ K ⊗ Δ[1] :=
  CartesianMonoidalCategory.lift (𝟙 K) (SSet.const (SSet.stdSimplex.obj₀Equiv.symm i))

/-- The actual realized simplicial cylinder, with the ordinary interval coordinate. -/
noncomputable def realizationCylinderHomeomorph (K : SSet.{u}) :
    |K ⊗ Δ[1]| ≃ₜ (|K| × I) :=
  (KIP126.Topology.SimplicialRealization.realizationStandardSimplexProductHomeomorph K 1).trans
    ((Homeomorph.refl _).prodCongr
      ((SimplexCategory.toTopHomeo ⦋1⦌).trans stdSimplexHomeomorphUnitInterval))

/-- Adjunction applied to a continuous cylinder map, using the actual product homeomorphism. -/
noncomputable def singularCylinderAdjoint (K : SSet.{u}) (B : TopCat.{u})
    (f : C(|K| × I, B)) : K ⊗ Δ[1] ⟶ TopCat.toSSet.obj B :=
  sSetTopAdj.homEquiv _ _ (TopCat.ofHom (Y := B)
    (f.comp ⟨realizationCylinderHomeomorph K,(realizationCylinderHomeomorph K).continuous⟩))

/-- The induced actual map to singular realization, with the same cylinder domain. -/
noncomputable def singularCylinder (K : SSet.{u}) (B : TopCat.{u})
    (f : C(|K| × I, B)) : C(|K| × I, |TopCat.toSSet.obj B|) :=
  (SSet.toTop.map (singularCylinderAdjoint K B f)).hom.comp
    ⟨(realizationCylinderHomeomorph K).symm,(realizationCylinderHomeomorph K).symm.continuous⟩

end KIP126.StableHomotopy.Spectra
