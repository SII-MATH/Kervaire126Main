module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Proofs
import Mathlib.CategoryTheory.LiftingProperties.Basic

@[expose] section

namespace KIP126.Topology.HomotopyLifting

open CategoryTheory Set _root_.Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The full boundary of a finite cube is closed, including the empty
boundary of the zero-dimensional cube. -/
theorem cubeBoundary_isClosed (n : ℕ) :
    IsClosed (_root_.Cube.boundary (Fin n)) := by
  simpa only [_root_.Cube.boundary,Set.setOf_exists,Set.setOf_or] using
    isClosed_iUnion_of_finite (fun i : Fin n =>
      (isClosed_eq (continuous_apply i) continuous_const).union
        (isClosed_eq (continuous_apply i) continuous_const))

instance cubeObject_normalSpace (n : ℕ) : NormalSpace (cubeObject.{u} n) :=
  inferInstanceAs (NormalSpace (ULift.{u} (Fin n → I)))

instance cubeObject_t1Space (n : ℕ) : T1Space (cubeObject.{u} n) :=
  inferInstanceAs (T1Space (ULift.{u} (Fin n → I)))

instance cubeBoundaryObject_compactSpace (n : ℕ) : CompactSpace (cubeBoundaryObject.{u} n) := by
  letI : CompactSpace (↥(_root_.Cube.boundary (Fin n))) :=
    isCompact_iff_compactSpace.mp (cubeBoundary_isClosed n).isCompact
  exact inferInstanceAs (CompactSpace (ULift.{u} (↥(_root_.Cube.boundary (Fin n)))))

/-- The specified full boundary map is an actual closed embedding. -/
theorem cubeBoundaryInclusion_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding (cubeBoundaryInclusion.{u} n) := by
  change IsClosedEmbedding (fun x : ULift.{u} (↥(_root_.Cube.boundary (Fin n))) =>
    ULift.up x.down.val)
  exact Homeomorph.ulift.symm.isClosedEmbedding.comp
    ((cubeBoundary_isClosed n).isClosedEmbedding_subtypeVal.comp
      Homeomorph.ulift.isClosedEmbedding)

/-- The displayed pointwise lifting condition is exactly the categorical
right lifting property of the actual cube-boundary inclusions. -/
theorem hasCubeBoundaryLifting_iff_lifting {E B : TopCat.{u}} (f : E ⟶ B) :
    HasCubeBoundaryLifting f.hom ↔
      ∀ n, HasLiftingProperty (cubeBoundaryInclusion.{u} n) f := by
  constructor
  · intro hf n
    constructor
    intro g H sq
    let g' : C(↥(_root_.Cube.boundary (Fin n)),E) :=
      g.hom.comp ⟨ULift.up,continuous_uliftUp⟩
    let H' : C(Fin n → I,B) := H.hom.comp ⟨ULift.up,continuous_uliftUp⟩
    obtain ⟨L,hL,hb⟩ := hf n g' H' (fun z =>
      ConcreteCategory.congr_hom sq.w (ULift.up z))
    exact CommSq.HasLift.mk' {
      l := TopCat.ofHom (L.comp ⟨ULift.down,continuous_uliftDown⟩)
      fac_left := by ext z; exact hb z.down
      fac_right := by ext z; exact hL z.down }
  · intro hf n g H hcomm
    letI := hf n
    let g' : cubeBoundaryObject.{u} n ⟶ E :=
      TopCat.ofHom (g.comp ⟨ULift.down,continuous_uliftDown⟩)
    let H' : cubeObject.{u} n ⟶ B :=
      TopCat.ofHom (H.comp ⟨ULift.down,continuous_uliftDown⟩)
    let sq : CommSq g' (cubeBoundaryInclusion n) f H' :=
      ⟨by ext z; exact hcomm z.down⟩
    refine ⟨sq.lift.hom.comp ⟨ULift.up,continuous_uliftUp⟩,?_,?_⟩
    · intro z
      exact ConcreteCategory.congr_hom sq.fac_right (ULift.up z)
    · intro z
      exact ConcreteCategory.congr_hom sq.fac_left (ULift.up z)

end KIP126.Topology.HomotopyLifting
