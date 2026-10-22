module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.Proofs

@[expose] section

namespace KIP126.Topology.SequentialColimit

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Homotopy extension rectifies a homotopy-coherent sequential family
into strictly compatible maps. The chosen comparison homotopies satisfy
an exact concatenation formula on every previous stage. -/
theorem exists_strict_family_of_homotopy_coherent
    (F : ℕ ⥤ TopCat.{u})
    (hF : ∀ n, HomotopyExtension.HasHomotopyExtension (F.map (homOfLE (Nat.le_succ n))))
    {Y : TopCat.{u}} (f : ∀ n, C(F.obj n,Y))
    (H : ∀ n, (f n).Homotopy ((f (n+1)).comp (F.map (homOfLE (Nat.le_succ n))).hom)) :
    ∃ (g : ∀ n, C(F.obj n,Y)) (K : ∀ n, (g n).Homotopy (f n)),
      (∀ n (x : F.obj n), g (n+1) (F.map (homOfLE (Nat.le_succ n)) x) = g n x) ∧
      ∀ n (t : I) (x : F.obj n),
        K (n+1) (t,F.map (homOfLE (Nat.le_succ n)) x) = ((K n).trans (H n)) (t,x) := by
  classical
  let S (n : ℕ) := Σ g : C(F.obj n,Y), g.Homotopy (f n)
  have hstep (n : ℕ) (s : S n) : ∃ s' : S (n+1),
      (∀ x : F.obj n, s'.1 (F.map (homOfLE (Nat.le_succ n)) x) = s.1 x) ∧
      ∀ (t : I) (x : F.obj n), s'.2 (t,F.map (homOfLE (Nat.le_succ n)) x) =
        (s.2.trans (H n)) (t,x) := by
    let C := s.2.trans (H n)
    let p := C.symm.toContinuousMap.comp ContinuousMap.prodSwap
    obtain ⟨E,hE,hEi⟩ := hF n Y (f (n+1)) p (fun x => C.symm.apply_zero x)
    let g : C(F.obj (n+1),Y) := E.comp
      ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 1))
    let K : g.Homotopy (f (n+1)) := {
      toFun := fun z => E (z.2,unitInterval.symm z.1)
      continuous_toFun := E.continuous.comp
        (continuous_snd.prodMk (unitInterval.continuous_symm.comp continuous_fst))
      map_zero_left := by intro x; simp [g]
      map_one_left := by intro x; simpa using hE x }
    refine ⟨⟨g,K⟩,?_,?_⟩
    · intro x
      exact (hEi x 1).trans (C.symm.apply_one x)
    · intro t x
      change E (F.map (homOfLE (Nat.le_succ n)) x,unitInterval.symm t) = C (t,x)
      rw [hEi]
      change C (unitInterval.symm (unitInterval.symm t),x) = C (t,x)
      rw [unitInterval.symm_symm]
  choose next hnext using hstep
  let s : ∀ n, S n := fun n => Nat.rec ⟨f 0,ContinuousMap.Homotopy.refl (f 0)⟩
    (fun n s => next n s) n
  refine ⟨fun n => (s n).1,fun n => (s n).2,?_,?_⟩
  · intro n x
    exact (hnext n (s n)).1 x
  · intro n t x
    exact (hnext n (s n)).2 t x

end KIP126.Topology.SequentialColimit
