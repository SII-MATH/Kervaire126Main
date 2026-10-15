module

public import KIP126.Def.Topology.SequentialColimit.Telescope.Data

@[expose] public section

namespace KIP126.Topology.SequentialColimit

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The defining square of the actual mapping telescope is a topological pushout. -/
theorem telescope_isPushout (F : ℕ ⥤ TopCat.{u}) :
    IsPushout (telescopeAttachingMap F) (telescopeEndpointMap F)
      (telescopeVertexInclusion F) (telescopeCylinderInclusion F) :=
  IsPushout.of_hasPushout _ _

/-- The lower end of an actual telescope cylinder is its stage inclusion. -/
theorem telescopeStageCylinder_zero (F : ℕ ⥤ TopCat.{u}) (n : ℕ) (x : F.obj n) :
    telescopeStageCylinder F n (0,x) = telescopeStageInclusion F n x :=
  (ConcreteCategory.congr_hom (telescope_isPushout F).w (Sum.inl ⟨n,x⟩)).symm

/-- The upper end of a telescope cylinder is the next stage inclusion
composed with the original transition map. -/
theorem telescopeStageCylinder_one (F : ℕ ⥤ TopCat.{u}) (n : ℕ) (x : F.obj n) :
    telescopeStageCylinder F n (1,x) =
      telescopeStageInclusion F (n+1) (F.map (homOfLE (Nat.le_succ n)) x) :=
  (ConcreteCategory.congr_hom (telescope_isPushout F).w (Sum.inr ⟨n,x⟩)).symm

/-- Genuine homotopy-coherent cocone data give an actual continuous map
out of the telescope, retaining every stage map and every cylinder homotopy. -/
theorem exists_telescope_desc (F : ℕ ⥤ TopCat.{u}) {Y : TopCat.{u}}
    (f : ∀ n, C(F.obj n,Y))
    (H : ∀ n, (f n).Homotopy ((f (n+1)).comp (F.map (homOfLE (Nat.le_succ n))).hom)) :
    ∃ d : telescope F ⟶ Y,
      (∀ n (x : F.obj n), d (telescopeStageInclusion F n x) = f n x) ∧
      ∀ n (t : I) (x : F.obj n), d (telescopeStageCylinder F n (t,x)) = H n (t,x) := by
  let v : telescopeVertices F ⟶ Y := TopCat.ofHom
    ⟨fun x => f x.1 x.2,continuous_sigma (fun n => (f n).continuous)⟩
  let p : C(telescopeVertices F,C(I,Y)) :=
    ⟨fun x => ((H x.1).toContinuousMap.comp ContinuousMap.prodSwap).curry x.2,
      continuous_sigma (fun n => ((H n).toContinuousMap.comp ContinuousMap.prodSwap).curry.continuous)⟩
  let c : telescopeCylinders F ⟶ Y := TopCat.ofHom (p.uncurry.comp ContinuousMap.prodSwap)
  have hw : telescopeAttachingMap F ≫ v = telescopeEndpointMap F ≫ c := by
    ext x
    rcases x with x | x
    · exact ((H x.1).apply_zero x.2).symm
    · exact ((H x.1).apply_one x.2).symm
  let d := (telescope_isPushout F).desc v c hw
  refine ⟨d,?_,?_⟩
  · intro n x
    exact ConcreteCategory.congr_hom ((telescope_isPushout F).inl_desc v c hw) ⟨n,x⟩
  · intro n t x
    exact ConcreteCategory.congr_hom ((telescope_isPushout F).inr_desc v c hw) (t,⟨n,x⟩)

/-- Continuous maps from the telescope are determined by their complete
stage-cylinder values. Endpoint values alone are not sufficient. -/
theorem telescope_hom_ext (F : ℕ ⥤ TopCat.{u}) {Y : TopCat.{u}}
    {f g : telescope F ⟶ Y}
    (h : ∀ n (t : I) (x : F.obj n),
      f (telescopeStageCylinder F n (t,x)) = g (telescopeStageCylinder F n (t,x))) : f = g := by
  apply (telescope_isPushout F).hom_ext
  · ext ⟨n,x⟩
    exact (congrArg f (telescopeStageCylinder_zero F n x)).symm.trans
      ((h n 0 x).trans (congrArg g (telescopeStageCylinder_zero F n x)))
  · ext ⟨t,n,x⟩
    exact h n t x

end KIP126.Topology.SequentialColimit
