module

public import KIP126.Def.Topology.HomotopyExtension.Predicates
public import KIP126.Def.Topology.Ball.HomotopyExtension.Proofs
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.Topology.CWComplex.Abstract.Basic

@[expose] public section

namespace KIP126.Topology.HomotopyExtension

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Homotopy extension is exactly lifting against actual path evaluation. -/
theorem hasHomotopyExtension_iff_lifting {A B : TopCat.{u}} (i : A ⟶ B) :
    HasHomotopyExtension i ↔ ∀ Y : TopCat.{u},
      HasLiftingProperty i (pathEvaluationZero Y) := by
  constructor
  · intro h Y
    constructor
    intro p f sq
    obtain ⟨H, hH0, hHi⟩ := h Y f.hom p.hom.uncurry (by
      intro a
      exact ConcreteCategory.congr_hom sq.w a)
    exact CommSq.HasLift.mk' {
      l := TopCat.ofHom H.curry
      fac_left := by ext a t; exact hHi a t
      fac_right := by ext b; exact hH0 b }
  · intro h Y f p hp
    haveI := h Y
    let sq : CommSq (TopCat.ofHom p.curry) i (pathEvaluationZero Y) (TopCat.ofHom f) :=
      ⟨by ext a; exact hp a⟩
    refine ⟨sq.lift.hom.uncurry, ?_, ?_⟩
    · intro b
      exact ConcreteCategory.congr_hom sq.fac_right b
    · intro a t
      exact congrArg (fun q : C(I, Y) => q t) (ConcreteCategory.congr_hom sq.fac_left a)

/-- Homotopy extension is invariant under a commuting isomorphism of arrows. -/
theorem hasHomotopyExtension_iff_of_arrow_iso {A B A' B' : TopCat.{u}}
    {i : A ⟶ B} {i' : A' ⟶ B'} (e : Arrow.mk i ≅ Arrow.mk i') :
    HasHomotopyExtension i ↔ HasHomotopyExtension i' := by
  simp only [hasHomotopyExtension_iff_lifting]
  exact forall_congr' (fun Y => HasLiftingProperty.iff_of_arrow_iso_left e (pathEvaluationZero Y))

/-- Every actual Euclidean disk-boundary inclusion has homotopy extension. -/
theorem diskBoundaryInclusion_hasHomotopyExtension (n : ℕ) :
    HasHomotopyExtension (TopCat.diskBoundaryInclusion.{u} n) := by
  intro Y f p hp
  let f' : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, Y) :=
    f.comp ⟨ULift.up, continuous_uliftUp⟩
  let p' : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × I, Y) :=
    p.comp ⟨fun z => (ULift.up z.1, z.2),
      (continuous_uliftUp.comp continuous_fst).prodMk continuous_snd⟩
  obtain ⟨H, hH0, hHi⟩ := Ball.boundary_homotopy_extension f' p'
    (fun x => hp (ULift.up x))
  refine ⟨H.comp ⟨fun z => (z.1.down, z.2),
    (continuous_uliftDown.comp continuous_fst).prodMk continuous_snd⟩, ?_, ?_⟩
  · intro b
    exact hH0 b.down
  · intro a t
    exact hHi a.down t

/-- Homotopy extension survives all the genuine attachments and the
sequential colimit of a relative CW complex. -/
theorem relativeCWComplex_hasHomotopyExtension {A B : TopCat.{u}} {i : A ⟶ B}
    (c : TopCat.RelativeCWComplex i) : HasHomotopyExtension i := by
  apply (hasHomotopyExtension_iff_lifting i).mpr
  intro Y
  let W : MorphismProperty TopCat.{u} :=
    MorphismProperty.ofHoms (fun n => TopCat.diskBoundaryInclusion.{u} n)
  have hp : W.rlp (pathEvaluationZero Y) := by
    intro S T j hj
    cases hj with
    | mk n =>
      exact (hasHomotopyExtension_iff_lifting _).mp
        (diskBoundaryInclusion_hasHomotopyExtension n) Y
  have hc : ∀ s : c.Cells, W (TopCat.RelativeCWComplex.basicCell s.j s.i) :=
    fun s => MorphismProperty.ofHoms.mk s.j
  have hi : W.rlp.llp i :=
    W.transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp ℕ i
      (c.transfiniteCompositionOfShape' hc).mem
  exact hi (pathEvaluationZero Y) hp

/-- A categorical coproduct of actual homotopy-extension maps again has
homotopy extension, independently of the chosen coproduct presentation. -/
theorem hasHomotopyExtension_of_coproduct
    {ι : Type u} {A B : ι → TopCat.{u}} (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, HasHomotopyExtension (f i))
    (cA : Cofan A) (cB : Cofan B) (hA : IsColimit cA) (hB : IsColimit cB)
    (m : cA.pt ⟶ cB.pt) (hm : ∀ i, cA.inj i ≫ m = f i ≫ cB.inj i) :
    HasHomotopyExtension m := by
  apply (hasHomotopyExtension_iff_lifting m).mpr
  intro Y
  let W := MorphismProperty.ofHoms f
  have hp : W.rlp (pathEvaluationZero Y) := by
    intro S T j hj
    cases hj with
    | mk a => exact (hasHomotopyExtension_iff_lifting _).mp (hf a) Y
  have hc : W.colimitsOfShape (Discrete ι) m :=
    MorphismProperty.colimitsOfShape.mk' _ _ _ _ hA hB
      (Discrete.natTrans (fun a => f a.as)) (fun ⟨a⟩ => MorphismProperty.ofHoms.mk a) m
      (fun ⟨a⟩ => hm a)
  exact W.colimitsOfShape_discrete_le_llp_rlp ι m hc (pathEvaluationZero Y) hp

end KIP126.Topology.HomotopyExtension
