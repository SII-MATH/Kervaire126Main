module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CWComplex.ClosedEmbedding.Proofs

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Actual homotopy extension extends every real-valued continuous function:
contract its boundary values linearly to zero and evaluate the extended
homotopy at time one. -/
theorem exists_real_extension_of_homotopyExtension
    {A B : TopCat.{u}} {i : A ⟶ B}
    (hi : HomotopyExtension.HasHomotopyExtension i) (f : C(A, ℝ)) :
    ∃ g : C(B, ℝ), ∀ a, g (i a) = f a := by
  let p : C(A × I, ULift.{u} ℝ) :=
    ⟨fun x => ULift.up ((x.2 : ℝ) * f x.1),
      continuous_uliftUp.comp
        ((continuous_subtype_val.comp continuous_snd).mul (f.continuous.comp continuous_fst))⟩
  obtain ⟨H,hH0,hHi⟩ := hi (TopCat.of (ULift.{u} ℝ))
    (ContinuousMap.const B (ULift.up 0)) p (by intro a; simp [p])
  refine ⟨⟨fun b => (H (b,1)).down,
    continuous_uliftDown.comp (H.continuous.comp (continuous_id.prodMk continuous_const))⟩,?_⟩
  intro a
  have hh := congrArg ULift.down (hHi a 1)
  simpa [p] using hh

/-- Every real-valued function on the base of an actual relative CW
complex extends continuously across its genuine cell attachments. -/
theorem relativeCWComplex_exists_real_extension
    {A B : TopCat.{u}} {i : A ⟶ B}
    (c : TopCat.RelativeCWComplex i) (f : C(A, ℝ)) :
    ∃ g : C(B, ℝ), ∀ a, g (i a) = f a :=
  exists_real_extension_of_homotopyExtension
    (HomotopyExtension.relativeCWComplex_hasHomotopyExtension c) f

end KIP126.Topology
