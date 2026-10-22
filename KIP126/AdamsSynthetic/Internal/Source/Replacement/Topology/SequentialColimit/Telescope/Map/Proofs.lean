module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Proofs

@[expose] section

namespace KIP126.Topology.SequentialColimit

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- A strict morphism of actual sequences induces a continuous telescope
map preserving every stage and the entire interval of every stage cylinder. -/
theorem exists_telescope_map {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) :
    ∃ d : telescope F ⟶ telescope G,
      (∀ n (x : F.obj n), d (telescopeStageInclusion F n x) =
        telescopeStageInclusion G n (η.app n x)) ∧
      ∀ n (t : I) (x : F.obj n), d (telescopeStageCylinder F n (t,x)) =
        telescopeStageCylinder G n (t,η.app n x) := by
  let f (n : ℕ) : C(F.obj n,telescope G) := (η.app n ≫ telescopeStageInclusion G n).hom
  let H (n : ℕ) : (f n).Homotopy ((f (n+1)).comp (F.map (homOfLE (Nat.le_succ n))).hom) := {
    toContinuousMap := (telescopeStageCylinder G n).comp
      ⟨fun z => (z.1,η.app n z.2),continuous_fst.prodMk ((η.app n).hom.continuous.comp continuous_snd)⟩
    map_zero_left := fun x => telescopeStageCylinder_zero G n (η.app n x)
    map_one_left := fun x => (telescopeStageCylinder_one G n (η.app n x)).trans
      (congrArg (telescopeStageInclusion G (n+1))
        (ConcreteCategory.congr_hom (η.naturality (homOfLE (Nat.le_succ n))) x).symm) }
  exact exists_telescope_desc F f H

/-- Any actual cocone has a continuous telescope comparison that collapses
every stage cylinder to the specified cocone map, at every interval time. -/
theorem exists_telescope_cocone_comparison (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) :
    ∃ p : telescope F ⟶ c.pt,
      (∀ n (x : F.obj n), p (telescopeStageInclusion F n x) = c.ι.app n x) ∧
      ∀ n (t : I) (x : F.obj n), p (telescopeStageCylinder F n (t,x)) = c.ι.app n x := by
  let H (n : ℕ) : (c.ι.app n).hom.Homotopy
      ((c.ι.app (n+1)).hom.comp (F.map (homOfLE (Nat.le_succ n))).hom) :=
    (ContinuousMap.Homotopy.refl (c.ι.app n).hom).cast rfl
      (congrArg TopCat.Hom.hom (c.w (homOfLE (Nat.le_succ n)))).symm
  exact exists_telescope_desc F (fun n => (c.ι.app n).hom) H

end KIP126.Topology.SequentialColimit
