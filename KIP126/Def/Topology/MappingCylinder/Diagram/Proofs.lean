module

public import KIP126.Def.Topology.MappingCylinder.Diagram.Data
public import KIP126.Def.Topology.Cylinder.Endpoints.Proofs
public import KIP126.Def.Topology.HomotopyExtension.Closure.Proofs

@[expose] public section

namespace KIP126.Topology.MappingCylinder
open CategoryTheory CategoryTheory.Limits _root_.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Each stage of the actual diagram is the displayed ordinary pushout. -/
theorem diagram_isPushout {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) (n : ℕ) :
    IsPushout ((attachingDiagram η).app n) ((endpointDiagram F).app n)
      ((vertexInclusion η).app n) ((cylinderInclusion η).app n) :=
  (IsPushout.of_hasPushout (attachingDiagram η) (endpointDiagram F)).map
    ((evaluation ℕ TopCat).obj n)

/-- The initial cylinder endpoint is the literal source inclusion. -/
theorem cylinder_zero {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) (n : ℕ) (x : F.obj n) :
    (cylinderInclusion η).app n (x,0) = (sourceInclusion η).app n x :=
  (ConcreteCategory.congr_hom (diagram_isPushout η n).w (Sum.inl x)).symm

/-- The final cylinder endpoint is the specified map followed by the target section. -/
theorem cylinder_one {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) (n : ℕ) (x : F.obj n) :
    (cylinderInclusion η).app n (x,1) = (targetInclusion η).app n (η.app n x) :=
  (ConcreteCategory.congr_hom (diagram_isPushout η n).w (Sum.inr x)).symm

/-- The natural collapse retains both original vertex formulas. -/
theorem projection_vertex {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) (n : ℕ) (x : F.obj n ⊕ G.obj n) :
    (projection η).app n ((vertexInclusion η).app n x) = Sum.elim (η.app n) id x := by
  unfold projection vertexInclusion
  change ((pushout.inl (attachingDiagram η) (endpointDiagram F) ≫ pushout.desc _ _ _ : sumDiagram F G ⟶ G).app n) x = _
  rw [pushout.inl_desc]
  rfl

/-- The collapse is constant along every entire original cylinder. -/
theorem projection_cylinder {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) (n : ℕ) (x : F.obj n) (t : I) :
    (projection η).app n ((cylinderInclusion η).app n (x,t)) = η.app n x := by
  unfold projection cylinderInclusion
  change ((pushout.inr (attachingDiagram η) (endpointDiagram F) ≫ pushout.desc _ _ _ : cylinderDiagram F ⟶ G).app n) (x,t) = _
  rw [pushout.inr_desc]
  rfl

/-- The actual mapping-cylinder projection factors the original transformation. -/
theorem source_projection {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) :
    sourceInclusion η ≫ projection η = η := by
  ext n x
  exact projection_vertex η n (Sum.inl x)

/-- The original target is a strict natural retract of its mapping cylinder. -/
theorem target_projection {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) :
    targetInclusion η ≫ projection η = 𝟙 G := by
  ext n x
  exact projection_vertex η n (Sum.inr x)

/-- Every original source inclusion is a closed embedding. -/
theorem sourceInclusion_isClosedEmbedding {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) (n : ℕ) :
    IsClosedEmbedding ((sourceInclusion η).app n) :=
  (isClosedEmbedding_of_topological_pushout (diagram_isPushout η n).flip
    (cylinderEndpointInclusion_isClosedEmbedding (F.obj n))).comp IsClosedEmbedding.inl

/-- Every original source inclusion has actual homotopy extension. -/
theorem sourceInclusion_hasHomotopyExtension {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) (n : ℕ) :
    HomotopyExtension.HasHomotopyExtension ((sourceInclusion η).app n) :=
  (HomotopyExtension.inl_hasHomotopyExtension (F.obj n) (G.obj n)).comp
    ((cylinderEndpointInclusion_hasHomotopyExtension (F.obj n)).of_isPushout (diagram_isPushout η n).flip)

end KIP126.Topology.MappingCylinder
