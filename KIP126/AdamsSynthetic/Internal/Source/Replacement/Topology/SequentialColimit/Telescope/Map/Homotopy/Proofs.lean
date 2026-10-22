module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Map.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Homotopy.Proofs

@[expose] section

namespace KIP126.Topology.SequentialColimit
open CategoryTheory CategoryTheory.Limits
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- A specified natural family of stage homotopies induces a genuine
homotopy of the strict telescope maps, retaining all cylinder parameters. -/
theorem exists_telescope_map_homotopy {F G : ℕ ⥤ TopCat.{u}} (η θ : F ⟶ G)
    (D E : telescope F ⟶ telescope G)
    (hD : ∀ n t x, D (telescopeStageCylinder F n (t,x)) = telescopeStageCylinder G n (t,η.app n x))
    (hE : ∀ n t x, E (telescopeStageCylinder F n (t,x)) = telescopeStageCylinder G n (t,θ.app n x))
    (H : ∀ n, (η.app n).hom.Homotopy (θ.app n).hom)
    (hH : ∀ n s x, H (n+1) (s,F.map (homOfLE (Nat.le_succ n)) x) =
      G.map (homOfLE (Nat.le_succ n)) (H n (s,x))) :
    ∃ K : D.hom.Homotopy E.hom,
      (∀ n s x, K (s,telescopeStageInclusion F n x) = telescopeStageInclusion G n (H n (s,x))) ∧
      ∀ n s t x, K (s,telescopeStageCylinder F n (t,x)) = telescopeStageCylinder G n (t,H n (s,x)) := by
  have hDv (n : ℕ) (x : F.obj n) : D (telescopeStageInclusion F n x) = telescopeStageInclusion G n (η.app n x) := by
    rw [← telescopeStageCylinder_zero F n x,hD,telescopeStageCylinder_zero]
  have hEv (n : ℕ) (x : F.obj n) : E (telescopeStageInclusion F n x) = telescopeStageInclusion G n (θ.app n x) := by
    rw [← telescopeStageCylinder_zero F n x,hE,telescopeStageCylinder_zero]
  let HV (n : ℕ) : (D.hom.comp (telescopeStageInclusion F n).hom).Homotopy
      (E.hom.comp (telescopeStageInclusion F n).hom) := {
    toContinuousMap := (telescopeStageInclusion G n).hom.comp (H n).toContinuousMap
    map_zero_left := fun x => (congrArg (telescopeStageInclusion G n) ((H n).apply_zero x)).trans (hDv n x).symm
    map_one_left := fun x => (congrArg (telescopeStageInclusion G n) ((H n).apply_one x)).trans (hEv n x).symm }
  let HC (n : ℕ) : (D.hom.comp (telescopeStageCylinder F n)).Homotopy
      (E.hom.comp (telescopeStageCylinder F n)) := {
    toContinuousMap := (telescopeStageCylinder G n).comp
      ⟨fun z => (z.2.1,H n (z.1,z.2.2)),continuous_snd.fst.prodMk
        ((H n).continuous.comp (continuous_fst.prodMk continuous_snd.snd))⟩
    map_zero_left := by
      rintro ⟨t,x⟩
      exact (congrArg (fun y => telescopeStageCylinder G n (t,y)) ((H n).apply_zero x)).trans (hD n t x).symm
    map_one_left := by
      rintro ⟨t,x⟩
      exact (congrArg (fun y => telescopeStageCylinder G n (t,y)) ((H n).apply_one x)).trans (hE n t x).symm }
  exact exists_telescope_homotopy F D.hom E.hom HV HC
    (fun n s x => telescopeStageCylinder_zero G n (H n (s,x)))
    (fun n s x => (telescopeStageCylinder_one G n (H n (s,x))).trans
      (congrArg (telescopeStageInclusion G (n+1)) (hH n s x).symm))

end KIP126.Topology.SequentialColimit
