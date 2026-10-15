module

public import KIP126.Def.Topology.HomotopyFiber.Contraction.Cubical
public import KIP126.Def.Topology.HomotopyGroup.ContinuousMap.Data

@[expose] public section

namespace KIP126.Topology
open scoped unitInterval
universe u v w
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A specified continuous comparison is bijective on actual homotopy sets
when it is the projected contraction through an actual based fiber homeomorphism. -/
theorem continuousHomotopyMap_bijective_of_fiber_contraction
    {E : Type w} [TopologicalSpace E]
    (f : C(E,Y)) (e : E) (y : Y) (hy : f e = y)
    (c : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (hc : ∀ t, c (t,e) = e) (hf : HomotopyLifting.HasCubicalLifting f)
    (j : X ≃ₜ {z : E // f z = y}) (x : X) (hj : (j x).val = e)
    (l : C(X,Path y y)) (hl : l x = Path.refl y)
    (hformula : ∀ z t, l z t = f (c (t,(j z).val))) (n : ℕ) :
    Function.Bijective (continuousHomotopyMap l x (Path.refl y) hl n) := by
  subst y
  have hj' : j x = ⟨e,rfl⟩ := Subtype.ext hj
  have hm : continuousHomotopyMap l x (Path.refl (f e)) hl n =
      contractionFiberHomotopyMap f e c hc n ∘ homeomorphHomotopyEquiv j x ⟨e,rfl⟩ hj' n := by
    funext q
    induction q using Quotient.inductionOn with
    | h q =>
      apply congrArg Quotient.mk''
      apply GenLoop.ext
      intro z
      apply Path.ext
      funext t
      exact hformula (q z) t
  rw [hm]
  exact (contractionFiberHomotopyMap_bijective f e c hc hf n).comp
    (homeomorphHomotopyEquiv j x ⟨e,rfl⟩ hj' n).bijective

end KIP126.Topology
