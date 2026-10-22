module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Map.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.HomotopyEquivalence.Extension.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.CylinderCorner.Homotopy.Proofs

@[expose] section

namespace KIP126.Topology.SequentialColimit
open CategoryTheory CategoryTheory.Limits _root_.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- A strict telescope comparison whose stage maps are closed HEP homotopy
equivalences is an actual homotopy equivalence with the specified forward
map. Its inverse and composite homotopy retain the full cylinder squares. -/
theorem exists_telescope_map_homotopyEquiv_of_closedHEP
    {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G)
    (hi : ∀ n, HomotopyExtension.HasHomotopyExtension (η.app n))
    (hc : ∀ n, IsClosedEmbedding (η.app n))
    (e : ∀ n, ContinuousMap.HomotopyEquiv (F.obj n) (G.obj n))
    (he : ∀ n, (e n).toFun = (η.app n).hom)
    (D : telescope F ⟶ telescope G)
    (hD : ∀ n t x, D (telescopeStageCylinder F n (t,x)) = telescopeStageCylinder G n (t,η.app n x)) :
    ∃ E : ContinuousMap.HomotopyEquiv (telescope F) (telescope G), E.toFun = D.hom := by
  classical
  have hn (n : ℕ) (x : F.obj n) : η.app (n+1) (F.map (homOfLE (Nat.le_succ n)) x) =
      G.map (homOfLE (Nat.le_succ n)) (η.app n x) :=
    ConcreteCategory.congr_hom (η.naturality (homOfLE (Nat.le_succ n))) x
  have hDv (n : ℕ) (x : F.obj n) : D (telescopeStageInclusion F n x) = telescopeStageInclusion G n (η.app n x) := by
    rw [← telescopeStageCylinder_zero F n x,hD,telescopeStageCylinder_zero]
  have hs (n : ℕ) := (hi n).exists_strong_deformation_retraction (hc n) (e n) (he n)
  choose r hr H hH using hs
  have hr' (n : ℕ) (x : F.obj n) : r n (η.app n x) = x := ContinuousMap.congr_fun (hr n) x
  let f (n : ℕ) : C(G.obj n,telescope F) := (telescopeStageInclusion F n).hom.comp (r n)
  let C (n : ℕ) : ((f n).comp (η.app n).hom).Homotopy
      (((f (n+1)).comp (G.map (homOfLE (Nat.le_succ n))).hom).comp (η.app n).hom) := {
    toContinuousMap := telescopeStageCylinder F n
    map_zero_left := fun x => (telescopeStageCylinder_zero F n x).trans (congrArg (telescopeStageInclusion F n) (hr' n x).symm)
    map_one_left := fun x => by
      apply (telescopeStageCylinder_one F n x).trans
      change telescopeStageInclusion F (n+1) (F.map (homOfLE (Nat.le_succ n)) x) =
        telescopeStageInclusion F (n+1) (r (n+1) (G.map (homOfLE (Nat.le_succ n)) (η.app n x)))
      rw [← hn n x,hr'] }
  have hk (n : ℕ) := (hi n).exists_homotopy_extension_of_homotopyEquiv (hc n) (e n) (he n)
    (f n) ((f (n+1)).comp (G.map (homOfLE (Nat.le_succ n))).hom) (C n)
  choose K hK using hk
  obtain ⟨R,hRv,hRc⟩ := exists_telescope_desc G f K
  have hleft : R.hom.comp D.hom = ContinuousMap.id (telescope F) := by
    suffices D ≫ R = 𝟙 (telescope F) from congrArg TopCat.Hom.hom this
    apply telescope_hom_ext F
    intro n t x
    change R (D (telescopeStageCylinder F n (t,x))) = telescopeStageCylinder F n (t,x)
    rw [hD,hRc]
    exact hK n t x
  let HV (n : ℕ) : ((ContinuousMap.id (telescope G)).comp (telescopeStageInclusion G n).hom).Homotopy
      ((D.hom.comp R.hom).comp (telescopeStageInclusion G n).hom) := {
    toContinuousMap := (telescopeStageInclusion G n).hom.comp (H n).toContinuousMap
    map_zero_left := fun y => congrArg (telescopeStageInclusion G n) ((H n).apply_zero y)
    map_one_left := fun y => by
      change telescopeStageInclusion G n (H n (1,y)) = D (R (telescopeStageInclusion G n y))
      rw [(H n).apply_one,hRv]
      exact (hDv n (r n y)).symm }
  have hVH (n : ℕ) (s : I) (x : F.obj n) : HV n (s,η.app n x) = telescopeStageInclusion G n (η.app n x) :=
    congrArg (telescopeStageInclusion G n) (hH n s x)
  have hsquares (n : ℕ) : ∃ L :
      ((ContinuousMap.id (telescope G)).comp (telescopeStageCylinder G n)).Homotopy
        ((D.hom.comp R.hom).comp (telescopeStageCylinder G n)),
      (∀ s y, L (s,(0,y)) = HV n (s,y)) ∧
      ∀ s y, L (s,(1,y)) = HV (n+1) (s,G.map (homOfLE (Nat.le_succ n)) y) := by
    let q : C(G.obj n × I,telescope G) := (telescopeStageCylinder G n).comp ContinuousMap.prodSwap
    let q' : C(G.obj n × I,telescope G) := (D.hom.comp R.hom).comp q
    have hside : q.comp ((η.app n).hom.prodMap (ContinuousMap.id I)) =
        q'.comp ((η.app n).hom.prodMap (ContinuousMap.id I)) := by
      ext ⟨x,t⟩
      change telescopeStageCylinder G n (t,η.app n x) = D (R (telescopeStageCylinder G n (t,η.app n x)))
      rw [hRc,hK]
      exact (hD n t x).symm
    let HA := (ContinuousMap.Homotopy.refl
      (q.comp ((η.app n).hom.prodMap (ContinuousMap.id I)))).cast rfl hside
    have hq0 : q.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 0)) = (telescopeStageInclusion G n).hom := by
      ext y
      exact telescopeStageCylinder_zero G n y
    have hq1 : q.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 1)) =
        (telescopeStageInclusion G (n+1)).hom.comp (G.map (homOfLE (Nat.le_succ n))).hom := by
      ext y
      exact telescopeStageCylinder_one G n y
    let H0 := (HV n).cast hq0.symm (congrArg (fun k => (D.hom.comp R.hom).comp k) hq0).symm
    let H1 := ((HV (n+1)).compContinuousMap (G.map (homOfLE (Nat.le_succ n))).hom).cast
      hq1.symm (congrArg (fun k => (D.hom.comp R.hom).comp k) hq1).symm
    obtain ⟨J,hJa,hJ0,hJ1⟩ := HomotopyExtension.exists_cylinderCorner_homotopy (η.app n) (hc n)
      q q' HA H0 H1
      (by
        intro s x
        change telescopeStageCylinder G n (0,η.app n x) = HV n (s,η.app n x)
        rw [telescopeStageCylinder_zero,hVH])
      (by
        intro s x
        change telescopeStageCylinder G n (1,η.app n x) =
          HV (n+1) (s,G.map (homOfLE (Nat.le_succ n)) (η.app n x))
        rw [telescopeStageCylinder_one,← hn n x,hVH])
    obtain ⟨ec,hec⟩ := (hi n).exists_cylinderCorner_homotopyEquiv (hc n) (e n) (he n)
    obtain ⟨L,hL⟩ := ((hi n).cylinderCorner (hc n)).exists_homotopy_extension_of_homotopyEquiv
      (HomotopyExtension.cylinderCornerMap_isClosedEmbedding (η.app n) (hc n)) ec hec q q' J
    refine ⟨L.compContinuousMap ContinuousMap.prodSwap,?_,?_⟩
    · intro s y
      exact (hL s ⟨(y,0),Or.inr (Or.inl rfl)⟩).trans (hJ0 s y)
    · intro s y
      exact (hL s ⟨(y,1),Or.inr (Or.inr rfl)⟩).trans (hJ1 s y)
  choose L hL0 hL1 using hsquares
  obtain ⟨T,_,_⟩ := exists_telescope_homotopy G (ContinuousMap.id _) (D.hom.comp R.hom) HV L hL0 hL1
  exact ⟨⟨D.hom,R.hom,by rw [hleft],⟨T.symm⟩⟩,rfl⟩

end KIP126.Topology.SequentialColimit
