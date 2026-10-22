module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Comparison.Injectivity.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Map.Proofs
import Mathlib.Topology.Homotopy.Equiv

@[expose] section

namespace KIP126.Topology.SequentialColimit

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The specified cylinder-collapsing comparison from an actual telescope
to an actual colimit of closed HEP maps is a genuine homotopy equivalence.
Its forward map is exactly the original comparison. -/
theorem exists_telescope_comparison_homotopyEquiv
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ n, HomotopyExtension.HasHomotopyExtension (F.map (homOfLE (Nat.le_succ n))))
    (hclosed : ∀ n, _root_.Topology.IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    (p : telescope F ⟶ c.pt)
    (hp : ∀ n (t : I) (x : F.obj n), p (telescopeStageCylinder F n (t,x)) = c.ι.app n x) :
    ∃ E : ContinuousMap.HomotopyEquiv (telescope F) c.pt, E.toFun = p.hom := by
  obtain ⟨r,hr⟩ := telescope_comparison_precomp_homotopic_surjective F c hc hF p hp (𝟙 (telescope F))
  have h : ((p.hom.comp r.hom).comp p.hom).Homotopic
      ((ContinuousMap.id c.pt).comp p.hom) :=
    (ContinuousMap.Homotopic.refl p.hom).comp hr
  obtain ⟨H⟩ := h
  have hright := telescope_comparison_precomp_homotopic_injective F c hc hF hclosed p hp
    (p.hom.comp r.hom) (ContinuousMap.id c.pt) H
  exact ⟨⟨p.hom,r.hom,hr,hright⟩,rfl⟩

/-- An actual telescope of closed HEP maps is homotopy equivalent to any
actual colimit. The equivalence preserves every original stage map and
collapses each entire stage cylinder to that same colimit map. -/
theorem exists_telescope_colimit_homotopyEquiv
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ n, HomotopyExtension.HasHomotopyExtension (F.map (homOfLE (Nat.le_succ n))))
    (hclosed : ∀ n, _root_.Topology.IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    : ∃ E : ContinuousMap.HomotopyEquiv (telescope F) c.pt,
      (∀ n (x : F.obj n), E (telescopeStageInclusion F n x) = c.ι.app n x) ∧
      ∀ n (t : I) (x : F.obj n), E (telescopeStageCylinder F n (t,x)) = c.ι.app n x := by
  obtain ⟨p,hpv,hpc⟩ := exists_telescope_cocone_comparison F c
  obtain ⟨E,hE⟩ := exists_telescope_comparison_homotopyEquiv F c hc hF hclosed p hpc
  refine ⟨E,?_,?_⟩
  · intro n x
    rw [hE]
    exact hpv n x
  · intro n t x
    rw [hE]
    exact hpc n t x

end KIP126.Topology.SequentialColimit
