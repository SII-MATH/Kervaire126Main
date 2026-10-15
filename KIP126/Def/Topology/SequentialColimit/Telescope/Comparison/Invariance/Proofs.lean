module

public import KIP126.Def.Topology.SequentialColimit.Telescope.Map.HomotopyEquivalence.Proofs
public import KIP126.Def.Topology.SequentialColimit.Telescope.Comparison.Equivalence.Proofs

@[expose] public section

namespace KIP126.Topology.SequentialColimit
open CategoryTheory CategoryTheory.Limits _root_.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- A strict comparison of actual colimits of closed HEP sequences is
an actual homotopy equivalence whenever its specified stage maps are.
The resulting equivalence retains the original colimit comparison. -/
theorem exists_colimit_homotopyEquiv_of_level
    {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G)
    (e : ∀ n, ContinuousMap.HomotopyEquiv (F.obj n) (G.obj n))
    (he : ∀ n, (e n).toFun = (η.app n).hom)
    (cF : Cocone F) (cG : Cocone G) (hcF : IsColimit cF) (hcG : IsColimit cG)
    (hF : ∀ n, HomotopyExtension.HasHomotopyExtension (F.map (homOfLE (Nat.le_succ n))))
    (hFc : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    (hG : ∀ n, HomotopyExtension.HasHomotopyExtension (G.map (homOfLE (Nat.le_succ n))))
    (hGc : ∀ n, IsClosedEmbedding (G.map (homOfLE (Nat.le_succ n))))
    (D : cF.pt ⟶ cG.pt) (hD : ∀ n, cF.ι.app n ≫ D = η.app n ≫ cG.ι.app n) :
    ∃ E : ContinuousMap.HomotopyEquiv cF.pt cG.pt, E.toFun = D.hom := by
  obtain ⟨pF,_,hpF⟩ := exists_telescope_cocone_comparison F cF
  obtain ⟨pG,_,hpG⟩ := exists_telescope_cocone_comparison G cG
  obtain ⟨EF,hEF⟩ := exists_telescope_comparison_homotopyEquiv F cF hcF hF hFc pF hpF
  obtain ⟨EG,hEG⟩ := exists_telescope_comparison_homotopyEquiv G cG hcG hG hGc pG hpG
  obtain ⟨T,_,hT⟩ := exists_telescope_map η
  obtain ⟨ET,hET⟩ := exists_telescope_map_homotopyEquiv η e he T hT
  have hsquare : pF ≫ D = T ≫ pG := by
    apply telescope_hom_ext F
    intro n t x
    change D (pF (telescopeStageCylinder F n (t,x))) = pG (T (telescopeStageCylinder F n (t,x)))
    rw [hpF,hT,hpG]
    exact ConcreteCategory.congr_hom (hD n) x
  let E := (EF.symm.trans ET).trans EG
  have hto : E.toFun = D.hom.comp (pF.hom.comp EF.invFun) := by
    change EG.toFun.comp (ET.toFun.comp EF.invFun) = _
    rw [hEG,hET]
    ext x
    exact (ConcreteCategory.congr_hom hsquare (EF.invFun x)).symm
  have h : E.toFun.Homotopic D.hom := by
    rw [hto]
    have hright := EF.right_inv
    rw [hEF] at hright
    exact (ContinuousMap.Homotopic.refl D.hom).comp hright
  refine ⟨⟨D.hom,E.invFun,?_,?_⟩,rfl⟩
  · exact ((ContinuousMap.Homotopic.refl E.invFun).comp h.symm).trans E.left_inv
  · exact (h.symm.comp (ContinuousMap.Homotopic.refl E.invFun)).trans E.right_inv

end KIP126.Topology.SequentialColimit
