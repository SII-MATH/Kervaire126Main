module

public import KIP126.Def.Topology.Cylinder.Endpoints.Data
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

@[expose] public section

namespace KIP126.Topology.MappingCylinder
open CategoryTheory CategoryTheory.Limits
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Pointwise disjoint union of actual topological sequences. -/
def sumDiagram (F G : ℕ ⥤ TopCat.{u}) : ℕ ⥤ TopCat.{u} where
  obj n := TopCat.of (F.obj n ⊕ G.obj n)
  map k := TopCat.ofHom ⟨Sum.map (F.map k) (G.map k),
    (F.map k).hom.continuous.sumMap (G.map k).hom.continuous⟩
  map_id n := by ext x; cases x <;> simp
  map_comp k l := by ext x; cases x <;> simp

/-- The first pointwise summand inclusion. -/
def sumInlDiagram (F G : ℕ ⥤ TopCat.{u}) : F ⟶ sumDiagram F G where
  app _ := TopCat.ofHom ⟨Sum.inl,continuous_inl⟩
  naturality _ _ _ := rfl

/-- The second pointwise summand inclusion. -/
def sumInrDiagram (F G : ℕ ⥤ TopCat.{u}) : G ⟶ sumDiagram F G where
  app _ := TopCat.ofHom ⟨Sum.inr,continuous_inr⟩
  naturality _ _ _ := rfl

/-- The ordinary cylinder on each original stage. -/
def cylinderDiagram (F : ℕ ⥤ TopCat.{u}) : ℕ ⥤ TopCat.{u} where
  obj n := TopCat.of (F.obj n × I)
  map k := TopCat.ofHom ((F.map k).hom.prodMap (ContinuousMap.id I))
  map_id n := by ext x <;> simp
  map_comp k l := by ext x <;> simp

/-- Both ordinary cylinder ends, natural in the original sequence. -/
def endpointDiagram (F : ℕ ⥤ TopCat.{u}) : sumDiagram F F ⟶ cylinderDiagram F where
  app n := cylinderEndpointInclusion (F.obj n)
  naturality n m k := by ext x; cases x <;> rfl

/-- Attach the initial cylinder end to its source and the final end by
its specified stage map. -/
def attachingDiagram {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) :
    sumDiagram F F ⟶ sumDiagram F G where
  app n := TopCat.ofHom ⟨Sum.elim Sum.inl (fun x => Sum.inr (η.app n x)),
    continuous_inl.sumElim (continuous_inr.comp (η.app n).hom.continuous)⟩
  naturality n m k := by
    ext x
    cases x with
    | inl x => rfl
    | inr x => exact congrArg Sum.inr (ConcreteCategory.congr_hom (η.naturality k) x)

/-- The actual pointwise mapping-cylinder diagram, formed as a pushout in
actual topological sequences. -/
noncomputable def diagram {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) : ℕ ⥤ TopCat.{u} :=
  pushout (attachingDiagram η) (endpointDiagram F)

/-- Inclusion of both original summands into the actual mapping cylinder. -/
noncomputable def vertexInclusion {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) :
    sumDiagram F G ⟶ diagram η := pushout.inl (attachingDiagram η) (endpointDiagram F)

/-- Inclusion of the complete original stage cylinders. -/
noncomputable def cylinderInclusion {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) :
    cylinderDiagram F ⟶ diagram η := pushout.inr (attachingDiagram η) (endpointDiagram F)

/-- The original source inclusion into its actual mapping-cylinder diagram. -/
noncomputable def sourceInclusion {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) : F ⟶ diagram η :=
  sumInlDiagram F G ≫ vertexInclusion η

/-- The original target section of its actual mapping-cylinder diagram. -/
noncomputable def targetInclusion {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) : G ⟶ diagram η :=
  sumInrDiagram F G ≫ vertexInclusion η

/-- The natural collapse of the actual mapping cylinder to its target. -/
noncomputable def projection {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) : diagram η ⟶ G := by
  let a : sumDiagram F G ⟶ G := {
    app := fun n => TopCat.ofHom ⟨Sum.elim (η.app n) id,
      (η.app n).hom.continuous.sumElim continuous_id⟩
    naturality := fun n m k => by
      ext x
      cases x with
      | inl x => exact ConcreteCategory.congr_hom (η.naturality k) x
      | inr x => rfl }
  let b : cylinderDiagram F ⟶ G := {
    app := fun n => TopCat.ofHom ((η.app n).hom.comp ContinuousMap.fst)
    naturality := fun n m k => by
      ext x
      exact ConcreteCategory.congr_hom (η.naturality k) x.1 }
  exact pushout.desc a b (by ext n x; cases x <;> rfl)

end KIP126.Topology.MappingCylinder
