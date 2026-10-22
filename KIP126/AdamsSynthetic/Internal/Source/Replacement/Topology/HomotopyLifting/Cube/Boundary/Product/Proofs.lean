module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyLifting.Cube.Boundary.Product.Data
import Mathlib.Topology.ContinuousMap.Basic

@[expose] section

namespace KIP126.Topology.HomotopyLifting

open CategoryTheory CategoryTheory.Limits _root_.Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The two endpoint parameters form a compact subspace of the interval. -/
instance intervalBoundaryObject_compactSpace : CompactSpace intervalBoundaryObject := by
  exact isCompact_iff_compactSpace.mp
    ((isClosed_singleton (x := (0 : I))).union
      (isClosed_singleton (x := (1 : I)))).isCompact

/-- The two actual boundary pieces agree on their actual intersection. -/
theorem cubeBoundaryProduct_comm (n : ℕ) :
    cubeBoundaryProductTop.{u} n ≫ cubeBoundaryProductEndInclusion n =
      cubeBoundaryProductLeft n ≫ cubeBoundaryProductSideInclusion n := by
  rfl

/-- The end-face coordinates agree with the fixed successor-cube homeomorphism. -/
theorem cubeBoundaryProductEndInclusion_coordinates (n : ℕ)
    (x : cubeBoundaryProductEnds.{u} n) :
    cubeObjectSuccHomeomorph n
      (cubeBoundaryInclusion (n+1) (cubeBoundaryProductEndInclusion n x)) =
      (x.1.val, x.2) := rfl

/-- The side coordinates agree with the fixed successor-cube homeomorphism. -/
theorem cubeBoundaryProductSideInclusion_coordinates (n : ℕ)
    (x : cubeBoundaryProductSide.{u} n) :
    cubeObjectSuccHomeomorph n
      (cubeBoundaryInclusion (n+1) (cubeBoundaryProductSideInclusion n x)) =
      (x.1, cubeBoundaryInclusion n x.2) := rfl

/-- Each end face is included injectively in the full boundary. -/
theorem cubeBoundaryProductEndInclusion_injective (n : ℕ) :
    Function.Injective (cubeBoundaryProductEndInclusion.{u} n) := by
  intro x y h
  have he := congrArg (fun z => cubeObjectSuccHomeomorph n (cubeBoundaryInclusion (n+1) z)) h
  change (x.1.val,x.2) = (y.1.val,y.2) at he
  exact Prod.ext (Subtype.ext (congrArg (fun p : I × cubeObject.{u} n => p.1) he)) (congrArg (fun p : I × cubeObject.{u} n => p.2) he)

/-- The whole side boundary is included injectively in the full boundary. -/
theorem cubeBoundaryProductSideInclusion_injective (n : ℕ) :
    Function.Injective (cubeBoundaryProductSideInclusion.{u} n) := by
  intro x y h
  have he := congrArg (fun z => cubeObjectSuccHomeomorph n (cubeBoundaryInclusion (n+1) z)) h
  change (x.1,cubeBoundaryInclusion n x.2) = (y.1,cubeBoundaryInclusion n y.2) at he
  exact Prod.ext (congrArg (fun p : I × cubeObject.{u} n => p.1) he)
    ((cubeBoundaryInclusion_isClosedEmbedding n).injective (congrArg (fun p : I × cubeObject.{u} n => p.2) he))

/-- Every successor-boundary point belongs to an end face or the side boundary. -/
theorem cubeBoundaryProduct_jointly_surjective (n : ℕ)
    (z : cubeBoundaryObject.{u} (n+1)) :
    (∃ x, cubeBoundaryProductEndInclusion n x = z) ∨
      (∃ y, cubeBoundaryProductSideInclusion n y = z) := by
  obtain ⟨j,hj⟩ := z.down.property
  refine Fin.cases ?_ (fun k hk => ?_) j hj
  · intro h0
    left
    refine ⟨(⟨z.down.val 0,h0⟩,ULift.up (fun k => z.down.val k.succ)), ?_⟩
    apply ULift.ext
    apply Subtype.ext
    funext k
    exact Fin.cases rfl (fun _ => rfl) k
  · right
    refine ⟨(z.down.val 0,ULift.up ⟨fun k => z.down.val k.succ, k,hk⟩), ?_⟩
    apply ULift.ext
    apply Subtype.ext
    funext l
    exact Fin.cases rfl (fun _ => rfl) l

/-- The intersection of the two pieces is exactly the product of their boundaries. -/
theorem cubeBoundaryProduct_intersection (n : ℕ)
    (x : cubeBoundaryProductEnds.{u} n) (y : cubeBoundaryProductSide.{u} n)
    (h : cubeBoundaryProductEndInclusion n x = cubeBoundaryProductSideInclusion n y) :
    ∃ z, cubeBoundaryProductTop n z = x ∧ cubeBoundaryProductLeft n z = y := by
  have he := congrArg (fun z => cubeObjectSuccHomeomorph n (cubeBoundaryInclusion (n+1) z)) h
  change (x.1.val,x.2) = (y.1,cubeBoundaryInclusion n y.2) at he
  refine ⟨(x.1,y.2), ?_, ?_⟩
  · exact Prod.ext rfl (congrArg (fun p : I × cubeObject.{u} n => p.2) he).symm
  · exact Prod.ext (congrArg (fun p : I × cubeObject.{u} n => p.1) he) rfl

/-- The two end faces are a closed subspace of the original full boundary. -/
theorem cubeBoundaryProductEndInclusion_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding (cubeBoundaryProductEndInclusion.{u} n) := by
  letI : CompactSpace (cubeBoundaryProductEnds.{u} n) :=
    inferInstanceAs (CompactSpace (intervalBoundaryObject × ULift.{u} (Fin n → I)))
  letI : T2Space (cubeBoundaryObject.{u} (n+1)) :=
    inferInstanceAs (T2Space (ULift.{u} (↥(_root_.Cube.boundary (Fin (n+1))))))
  exact (cubeBoundaryProductEndInclusion n).hom.continuous.isClosedEmbedding
    (cubeBoundaryProductEndInclusion_injective n)

/-- The side boundary is a closed subspace of the original full boundary. -/
theorem cubeBoundaryProductSideInclusion_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding (cubeBoundaryProductSideInclusion.{u} n) := by
  letI : CompactSpace (cubeBoundaryProductSide.{u} n) :=
    inferInstanceAs (CompactSpace (I × cubeBoundaryObject.{u} n))
  letI : T2Space (cubeBoundaryObject.{u} (n+1)) :=
    inferInstanceAs (T2Space (ULift.{u} (↥(_root_.Cube.boundary (Fin (n+1))))))
  exact (cubeBoundaryProductSideInclusion n).hom.continuous.isClosedEmbedding
    (cubeBoundaryProductSideInclusion_injective n)

/-- The actual full successor boundary is the topological pushout of its end
faces and side boundary, including the zero-dimensional empty-boundary case. -/
theorem cubeBoundaryProduct_isPushout (n : ℕ) :
    IsPushout (cubeBoundaryProductTop.{u} n) (cubeBoundaryProductLeft n)
      (cubeBoundaryProductEndInclusion n) (cubeBoundaryProductSideInclusion n) := by
  classical
  letI : CompactSpace (cubeBoundaryProductEnds.{u} n) :=
    inferInstanceAs (CompactSpace (intervalBoundaryObject × ULift.{u} (Fin n → I)))
  letI : CompactSpace (cubeBoundaryProductSide.{u} n) :=
    inferInstanceAs (CompactSpace (I × cubeBoundaryObject.{u} n))
  letI : T2Space (cubeBoundaryObject.{u} (n+1)) :=
    inferInstanceAs (T2Space (ULift.{u} (↥(_root_.Cube.boundary (Fin (n+1))))))
  let q : C(cubeBoundaryProductEnds.{u} n ⊕ cubeBoundaryProductSide.{u} n,
      cubeBoundaryObject.{u} (n+1)) :=
    ⟨Sum.elim (cubeBoundaryProductEndInclusion n) (cubeBoundaryProductSideInclusion n),
      continuous_sum_dom.mpr ⟨(cubeBoundaryProductEndInclusion n).hom.continuous,
        (cubeBoundaryProductSideInclusion n).hom.continuous⟩⟩
  have hq : IsQuotientMap q := .of_surjective_continuous (by
    intro z
    rcases cubeBoundaryProduct_jointly_surjective n z with ⟨x,hx⟩ | ⟨y,hy⟩
    · exact ⟨Sum.inl x,hx⟩
    · exact ⟨Sum.inr y,hy⟩) q.continuous
  let g (s : PushoutCocone (cubeBoundaryProductTop.{u} n) (cubeBoundaryProductLeft n)) :
      C(cubeBoundaryProductEnds.{u} n ⊕ cubeBoundaryProductSide.{u} n,s.pt) :=
    ⟨Sum.elim s.inl s.inr,
      continuous_sum_dom.mpr ⟨s.inl.hom.continuous,s.inr.hom.continuous⟩⟩
  have hg (s : PushoutCocone (cubeBoundaryProductTop.{u} n) (cubeBoundaryProductLeft n)) :
      Function.FactorsThrough (g s) q := by
    rintro (x|x) (y|y) h
    · change s.inl x = s.inl y
      exact congrArg s.inl (cubeBoundaryProductEndInclusion_injective n h)
    · change s.inl x = s.inr y
      obtain ⟨z,rfl,rfl⟩ := cubeBoundaryProduct_intersection n x y h
      exact ConcreteCategory.congr_hom s.condition z
    · change s.inr x = s.inl y
      obtain ⟨z,rfl,rfl⟩ := cubeBoundaryProduct_intersection n y x h.symm
      exact (ConcreteCategory.congr_hom s.condition z).symm
    · change s.inr x = s.inr y
      exact congrArg s.inr (cubeBoundaryProductSideInclusion_injective n h)
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk _ _ (cubeBoundaryProduct_comm.{u} n))
  refine PushoutCocone.IsColimit.mk _
    (fun s => TopCat.ofHom (hq.lift (g s) (hg s))) ?_ ?_ ?_
  · intro s
    ext x
    exact DFunLike.congr_fun (hq.lift_comp (g s) (hg s)) (Sum.inl x)
  · intro s
    ext y
    exact DFunLike.congr_fun (hq.lift_comp (g s) (hg s)) (Sum.inr y)
  · intro s m hm₁ hm₂
    ext z
    rcases cubeBoundaryProduct_jointly_surjective n z with ⟨x,rfl⟩ | ⟨y,rfl⟩
    · exact (ConcreteCategory.congr_hom hm₁ x).trans
        (DFunLike.congr_fun (hq.lift_comp (g s) (hg s)) (Sum.inl x)).symm
    · exact (ConcreteCategory.congr_hom hm₂ y).trans
        (DFunLike.congr_fun (hq.lift_comp (g s) (hg s)) (Sum.inr y)).symm

end KIP126.Topology.HomotopyLifting
