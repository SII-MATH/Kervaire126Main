module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.MappingCylinder.Diagram.Contraction.Data
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.MappingCylinder.Diagram.Proofs

@[expose] section

namespace KIP126.Topology.MappingCylinder
open CategoryTheory CategoryTheory.Limits
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem contractionTime_zero_left (t : I) : contractionTime (0,t) = t := by
  apply Subtype.ext; simp [contractionTime]
@[simp] theorem contractionTime_one_left (t : I) : contractionTime (1,t) = 1 := by
  apply Subtype.ext; simp [contractionTime]
@[simp] theorem contractionTime_zero_right (s : I) : contractionTime (s,0) = s := by
  apply Subtype.ext; simp [contractionTime]
@[simp] theorem contractionTime_one_right (s : I) : contractionTime (s,1) = 1 := by
  apply Subtype.ext; simp [contractionTime]

/-- The mapping-cylinder collapse has an actual natural deformation,
with its full source, target, and cylinder formulas retained. -/
theorem exists_natural_contraction {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) :
    ∃ H : ∀ n, (ContinuousMap.id ((diagram η).obj n)).Homotopy
      (((projection η).app n ≫ (targetInclusion η).app n).hom),
      (∀ n s x, H n (s,(sourceInclusion η).app n x) = (cylinderInclusion η).app n (x,s)) ∧
      (∀ n s y, H n (s,(targetInclusion η).app n y) = (targetInclusion η).app n y) ∧
      (∀ n s x t, H n (s,(cylinderInclusion η).app n (x,t)) =
        (cylinderInclusion η).app n (x,contractionTime (s,t))) ∧
      ∀ n m (k : n ⟶ m) s x, H m (s,(diagram η).map k x) = (diagram η).map k (H n (s,x)) := by
  have hstage (n : ℕ) : ∃ H : (ContinuousMap.id ((diagram η).obj n)).Homotopy
      (((projection η).app n ≫ (targetInclusion η).app n).hom),
      (∀ s x, H (s,(sourceInclusion η).app n x) = (cylinderInclusion η).app n (x,s)) ∧
      (∀ s y, H (s,(targetInclusion η).app n y) = (targetInclusion η).app n y) ∧
      ∀ s x t, H (s,(cylinderInclusion η).app n (x,t)) =
        (cylinderInclusion η).app n (x,contractionTime (s,t)) := by
    let a : C(F.obj n,C(I,(diagram η).obj n)) := ((cylinderInclusion η).app n).hom.curry
    let b : C(G.obj n,C(I,(diagram η).obj n)) :=
      (((targetInclusion η).app n).hom.comp ContinuousMap.fst).curry
    let v : C(F.obj n ⊕ G.obj n,C(I,(diagram η).obj n)) :=
      ⟨Sum.elim a b,a.continuous.sumElim b.continuous⟩
    let HV : ((ContinuousMap.id ((diagram η).obj n)).comp ((vertexInclusion η).app n).hom).Homotopy
        (((projection η).app n ≫ (targetInclusion η).app n).hom.comp ((vertexInclusion η).app n).hom) := {
      toContinuousMap := v.uncurry.comp ContinuousMap.prodSwap
      map_zero_left := by
        intro x
        cases x with
        | inl x => exact cylinder_zero η n x
        | inr y => rfl
      map_one_left := by
        intro x
        cases x with
        | inl x => exact (cylinder_one η n x).trans (congrArg ((targetInclusion η).app n) (projection_vertex η n (Sum.inl x)).symm)
        | inr y => exact (congrArg ((targetInclusion η).app n) (projection_vertex η n (Sum.inr y))).symm }
    let HC : ((ContinuousMap.id ((diagram η).obj n)).comp ((cylinderInclusion η).app n).hom).Homotopy
        (((projection η).app n ≫ (targetInclusion η).app n).hom.comp ((cylinderInclusion η).app n).hom) := {
      toContinuousMap := ((cylinderInclusion η).app n).hom.comp
        ⟨fun z => (z.2.1,contractionTime (z.1,z.2.2)),continuous_snd.fst.prodMk
          (contractionTime.continuous.comp (continuous_fst.prodMk continuous_snd.snd))⟩
      map_zero_left := by
        rintro ⟨x,t⟩
        change (cylinderInclusion η).app n (x,contractionTime (0,t)) = _
        rw [contractionTime_zero_left]
        rfl
      map_one_left := by
        rintro ⟨x,t⟩
        change (cylinderInclusion η).app n (x,contractionTime (1,t)) =
          (targetInclusion η).app n ((projection η).app n ((cylinderInclusion η).app n (x,t)))
        rw [contractionTime_one_left,cylinder_one,projection_cylinder] }
    obtain ⟨H,hHV,hHC⟩ := exists_homotopy_of_topological_pushout (diagram_isPushout η n)
      (ContinuousMap.id _) (((projection η).app n ≫ (targetInclusion η).app n).hom) HV HC
      (by
        intro s x
        cases x with
        | inl x =>
          change (cylinderInclusion η).app n (x,s) = (cylinderInclusion η).app n (x,contractionTime (s,0))
          rw [contractionTime_zero_right]
        | inr x =>
          change (targetInclusion η).app n (η.app n x) = (cylinderInclusion η).app n (x,contractionTime (s,1))
          rw [contractionTime_one_right,cylinder_one])
    exact ⟨H,fun s x => hHV s (Sum.inl x),fun s y => hHV s (Sum.inr y),fun s x t => hHC s (x,t)⟩
  choose H hHsrc hHtgt hHcyl using hstage
  refine ⟨H,hHsrc,hHtgt,hHcyl,?_⟩
  intro n m k s x
  have hs (a : F.obj n) : (sourceInclusion η).app m (F.map k a) =
      (diagram η).map k ((sourceInclusion η).app n a) :=
    ConcreteCategory.congr_hom ((sourceInclusion η).naturality k) a
  have ht (b : G.obj n) : (targetInclusion η).app m (G.map k b) =
      (diagram η).map k ((targetInclusion η).app n b) :=
    ConcreteCategory.congr_hom ((targetInclusion η).naturality k) b
  have hc (a : F.obj n) (t : I) : (cylinderInclusion η).app m (F.map k a,t) =
      (diagram η).map k ((cylinderInclusion η).app n (a,t)) :=
    ConcreteCategory.congr_hom ((cylinderInclusion η).naturality k) (a,t)
  obtain ⟨z,rfl⟩ | ⟨⟨a,t⟩,rfl⟩ := Types.eq_or_eq_of_isPushout ((diagram_isPushout η n).map (forget TopCat)) x
  · cases z with
    | inl a =>
      change H m (s,(diagram η).map k ((sourceInclusion η).app n a)) = (diagram η).map k (H n (s,(sourceInclusion η).app n a))
      rw [← hs a,hHsrc,hHsrc]
      exact ConcreteCategory.congr_hom ((cylinderInclusion η).naturality k) (a,s)
    | inr b =>
      change H m (s,(diagram η).map k ((targetInclusion η).app n b)) = (diagram η).map k (H n (s,(targetInclusion η).app n b))
      rw [← ht b,hHtgt,hHtgt]
      exact ConcreteCategory.congr_hom ((targetInclusion η).naturality k) b
  · change H m (s,(diagram η).map k ((cylinderInclusion η).app n (a,t))) = (diagram η).map k (H n (s,(cylinderInclusion η).app n (a,t)))
    rw [← hc a t,hHcyl,hHcyl]
    exact ConcreteCategory.congr_hom ((cylinderInclusion η).naturality k) (a,contractionTime (s,t))

end KIP126.Topology.MappingCylinder
