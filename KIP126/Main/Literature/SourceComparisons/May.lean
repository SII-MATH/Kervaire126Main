module

public import KIP126.Computation.Hypotheses.Joint
public import KIP126.Main.Literature.AdamsSynthetic.Theorems
import all KIP126.Def.StableHomotopy.Context.Proofs

@[expose] public section

namespace KIP126.Main.Literature.SourceComparisons
open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Literature.AdamsSynthetic
universe u v w
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

set_option backward.isDefEq.respectTransparency false in
/-- The elementwise May boundary calculation keeps the source sign.
The pushpull lift supplies one common representative for all three arrows. -/
theorem may_signed_boundary_of_source (B : MayContext Syn)
    (hB : MaySourceResults Syn B) : B.SignedBoundary := by
  letI := B.leftShift
  letI := B.rightShift
  letI := B.leftExact
  letI := B.rightExact
  intro T U n a b hab
  rcases hB T U with ⟨P⟩
  rcases P.lift n a b hab with ⟨z, hza, hzb⟩
  refine ⟨z ≫ P.j3, ?_, ?_⟩
  · change b ≫ (T.g ▷ U.Y) = (z ≫ P.j3) ≫ (T.Z ◁ U.f)
    rw [← hzb, Category.assoc, P.other_square, Category.assoc]
  · have hs : a ≫ (U.map (tensorLeft T.X)).h =
        -((z ≫ P.j3) ≫ (T.map (tensorRight U.X)).h) := by
      rw [← hza, Category.assoc, P.boundary]
      simp only [Preadditive.comp_neg, Category.assoc]
    simp only [connectingHomomorphism, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      hs, Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp]
    rfl

end
end KIP126.Main.Literature.SourceComparisons
