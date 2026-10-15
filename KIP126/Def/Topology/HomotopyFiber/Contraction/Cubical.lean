module

public import KIP126.Def.Topology.HomotopyFiber.Contraction.Proofs

@[expose] public section

section

namespace KIP126.Topology

universe u v
variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- The cubical based map induced by the actual fiber-to-loop comparison. -/
def contractionFiberGenLoop (f : C(E,B)) (e : E)
    (c : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (hc : ∀ t, c (t,e) = e) (n : ℕ)
    (p : GenLoop (Fin n) {x : E // f x = f e} ⟨e,rfl⟩) :
    GenLoop (Fin n) (Path (f e) (f e)) (Path.refl (f e)) :=
  ⟨(contractionFiberLoop f e c).comp p.val,fun z hz =>
    (congrArg (contractionFiberLoop f e c) (p.property z hz)).trans
      (contractionFiberLoop_point f e c hc)⟩

/-- The induced map on the actual cubical homotopy quotient. -/
def contractionFiberHomotopyMap (f : C(E,B)) (e : E)
    (c : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (hc : ∀ t, c (t,e) = e) (n : ℕ) :
    HomotopyGroup.Pi n {x : E // f x = f e} ⟨e,rfl⟩ →
      HomotopyGroup.Pi n (Path (f e) (f e)) (Path.refl (f e)) :=
  Quotient.map (contractionFiberGenLoop f e c hc n) fun _ _ h =>
    h.comp_continuousMap (contractionFiberLoop f e c)

end KIP126.Topology

end

section

namespace KIP126.Topology

open HomotopyLifting
universe u v
variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- A cubical fibration with a strongly contractible total space has the
actual fiber homotopy groups of the based loop space. The map is the
projection of the specified contraction, in every dimension including zero. -/
theorem contractionFiberHomotopyMap_bijective (f : C(E,B)) (e : E)
    (c : ContinuousMap.Homotopy (ContinuousMap.const E e) (ContinuousMap.id E))
    (hc : ∀ t, c (t,e) = e) (hf : HasCubicalLifting f) (n : ℕ) :
    Function.Bijective (contractionFiberHomotopyMap f e c hc n) := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with
    | h p =>
      induction q using Quotient.inductionOn with
      | h q =>
        intro hpq
        apply Quotient.sound
        exact contractionFiberLoop_homotopy_injective f e c hc _ (hf.cylinder n)
          p.val q.val p.property q.property (Quotient.exact hpq)
  · intro q
    induction q using Quotient.inductionOn with
    | h q =>
      obtain ⟨α,hα,hH⟩ := contractionFiberLoop_homotopy_surjective f e c hc _ (hf n)
        q.val q.property
      refine ⟨Quotient.mk'' ⟨α,hα⟩,Quotient.sound ?_⟩
      exact hH.symm

end KIP126.Topology

end
