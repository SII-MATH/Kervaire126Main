module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Map.HomotopyEquivalence.ClosedHEP.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Map.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.MappingCylinder.Diagram.Contraction.Proofs

@[expose] section

namespace KIP126.Topology.SequentialColimit
open CategoryTheory CategoryTheory.Limits
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- A strict map of arbitrary actual topological sequences whose stage
maps are genuine homotopy equivalences induces an actual telescope
homotopy equivalence. Its forward map is exactly the specified strict
cylinder-preserving telescope comparison. -/
theorem exists_telescope_map_homotopyEquiv
    {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G)
    (e : ∀ n, ContinuousMap.HomotopyEquiv (F.obj n) (G.obj n))
    (he : ∀ n, (e n).toFun = (η.app n).hom)
    (D : telescope F ⟶ telescope G)
    (hD : ∀ n t x, D (telescopeStageCylinder F n (t,x)) = telescopeStageCylinder G n (t,η.app n x)) :
    ∃ E : ContinuousMap.HomotopyEquiv (telescope F) (telescope G), E.toFun = D.hom := by
  let M := MappingCylinder.diagram η
  let i := MappingCylinder.sourceInclusion η
  let p := MappingCylinder.projection η
  let s := MappingCylinder.targetInclusion η
  obtain ⟨H,_,_,_,hH⟩ := MappingCylinder.exists_natural_contraction η
  have hpi (n : ℕ) (x : F.obj n) : p.app n (i.app n x) = η.app n x :=
    MappingCylinder.projection_vertex η n (Sum.inl x)
  have hps (n : ℕ) (x : G.obj n) : p.app n (s.app n x) = x :=
    MappingCylinder.projection_vertex η n (Sum.inr x)
  let ep (n : ℕ) : ContinuousMap.HomotopyEquiv (M.obj n) (G.obj n) := {
    toFun := (p.app n).hom
    invFun := (s.app n).hom
    left_inv := ⟨(H n).symm⟩
    right_inv := by
      have hh : (p.app n).hom.comp (s.app n).hom = ContinuousMap.id (G.obj n) := by
        ext x
        exact hps n x
      rw [hh] }
  let ei' (n : ℕ) := (e n).trans (ep n).symm
  have hif (n : ℕ) : (i.app n).hom.Homotopic (ei' n).toFun := by
    have hh : ((p.app n ≫ s.app n).hom).comp (i.app n).hom = (ei' n).toFun := by
      ext x
      change s.app n (p.app n (i.app n x)) = s.app n ((e n).toFun x)
      rw [hpi,he]
    exact ⟨((H n).compContinuousMap (i.app n).hom).cast rfl hh⟩
  let ei (n : ℕ) : ContinuousMap.HomotopyEquiv (F.obj n) (M.obj n) := {
    toFun := (i.app n).hom
    invFun := (ei' n).invFun
    left_inv := ((ContinuousMap.Homotopic.refl (ei' n).invFun).comp (hif n)).trans (ei' n).left_inv
    right_inv := ((hif n).comp (ContinuousMap.Homotopic.refl (ei' n).invFun)).trans (ei' n).right_inv }
  obtain ⟨Ti,_,hTi⟩ := exists_telescope_map i
  obtain ⟨Ei,hEi⟩ := exists_telescope_map_homotopyEquiv_of_closedHEP i
    (MappingCylinder.sourceInclusion_hasHomotopyExtension η)
    (MappingCylinder.sourceInclusion_isClosedEmbedding η) ei (fun _ => rfl) Ti hTi
  obtain ⟨Tp,_,hTp⟩ := exists_telescope_map p
  obtain ⟨Ts,_,hTs⟩ := exists_telescope_map s
  have hsp : Ts ≫ Tp = 𝟙 (telescope G) := by
    apply telescope_hom_ext G
    intro n t x
    change Tp (Ts (telescopeStageCylinder G n (t,x))) = telescopeStageCylinder G n (t,x)
    rw [hTs,hTp,hps]
  obtain ⟨K,_,_⟩ := exists_telescope_map_homotopy (𝟙 M) (p ≫ s) (𝟙 (telescope M)) (Tp ≫ Ts)
    (fun _ _ _ => rfl)
    (by intro n t x; change Ts (Tp _) = _; rw [hTp,hTs]; rfl)
    H (fun n t x => hH n (n+1) (homOfLE (Nat.le_succ n)) t x)
  let Ep : ContinuousMap.HomotopyEquiv (telescope M) (telescope G) := {
    toFun := Tp.hom
    invFun := Ts.hom
    left_inv := ⟨K.symm⟩
    right_inv := by
      have hh : Tp.hom.comp Ts.hom = ContinuousMap.id (telescope G) := congrArg TopCat.Hom.hom hsp
      rw [hh] }
  have hcomp : Ti ≫ Tp = D := by
    apply telescope_hom_ext F
    intro n t x
    change Tp (Ti (telescopeStageCylinder F n (t,x))) = D (telescopeStageCylinder F n (t,x))
    rw [hTi,hTp,hD,hpi]
  refine ⟨Ei.trans Ep,?_⟩
  change Tp.hom.comp Ei.toFun = D.hom
  rw [hEi]
  exact congrArg TopCat.Hom.hom hcomp

/-- Every strict natural transformation of actual sequences that is an
actual homotopy equivalence at each stage has a telescope homotopy
equivalence retaining all original stage and cylinder comparisons. -/
theorem exists_telescope_homotopyEquiv_of_level
    {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G)
    (e : ∀ n, ContinuousMap.HomotopyEquiv (F.obj n) (G.obj n))
    (he : ∀ n, (e n).toFun = (η.app n).hom) :
    ∃ E : ContinuousMap.HomotopyEquiv (telescope F) (telescope G),
      (∀ n x, E (telescopeStageInclusion F n x) = telescopeStageInclusion G n (η.app n x)) ∧
      ∀ n t x, E (telescopeStageCylinder F n (t,x)) = telescopeStageCylinder G n (t,η.app n x) := by
  obtain ⟨D,hDv,hDc⟩ := exists_telescope_map η
  obtain ⟨E,hE⟩ := exists_telescope_map_homotopyEquiv η e he D hDc
  refine ⟨E,?_,?_⟩
  · intro n x
    rw [hE]
    exact hDv n x
  · intro n t x
    rw [hE]
    exact hDc n t x

end KIP126.Topology.SequentialColimit
