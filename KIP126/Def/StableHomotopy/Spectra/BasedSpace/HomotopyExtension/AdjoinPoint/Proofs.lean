module

public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.AdjoinPoint.Data
public import KIP126.Def.Topology.HomotopyExtension.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory
open KIP126.Topology.HomotopyExtension
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Adjoining the same disjoint basepoint preserves actual homotopy
extension, including homotopies which move that point. -/
theorem adjoinPointMap_hasHomotopyExtension {A B : TopCat.{u}}
    (i : A ⟶ B) (hi : HasHomotopyExtension i) :
    HasHomotopyExtension (TopCat.ofHom (adjoinPointMap i).map) := by
  intro Y f p hp
  let fB : C(B, Y) := f.comp ⟨Sum.inl, continuous_inl⟩
  let pA : C(A × I, Y) := p.comp ⟨fun q => (Sum.inl q.1, q.2),
    (continuous_inl.comp continuous_fst).prodMk continuous_snd⟩
  obtain ⟨H, hH0, hHi⟩ := hi Y fB pA (fun a => hp (Sum.inl a))
  let P : C(I, Y) := p.comp ⟨fun t => (Sum.inr PUnit.unit, t),
    continuous_const.prodMk continuous_id⟩
  let Hc : C(B ⊕ PUnit, C(I, Y)) :=
    ⟨Sum.elim H.curry (fun _ => P), H.curry.continuous.sumElim continuous_const⟩
  refine ⟨Hc.uncurry, ?_, ?_⟩
  · intro b
    cases b with
    | inl b => exact hH0 b
    | inr b => exact hp (Sum.inr b)
  · intro a t
    cases a with
    | inl a => exact hHi a t
    | inr a => rfl

end KIP126.StableHomotopy.Spectra.BasedSpace
