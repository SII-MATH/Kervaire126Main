module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Coproduct.Homotopy.Small.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.Homotopy.Proofs

@[expose] section

namespace KIP126.Topology.SequentialColimit

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Stage homotopies together with actual compatible cylinder squares
assemble to a telescope homotopy. Both one- and two-parameter data are
retained exactly, so stage homotopies alone are never silently glued. -/
theorem exists_telescope_homotopy (F : ℕ ⥤ TopCat.{u}) {Y : TopCat.{u}}
    (f g : C(telescope F,Y))
    (H : ∀ n, (f.comp (telescopeStageInclusion F n).hom).Homotopy
      (g.comp (telescopeStageInclusion F n).hom))
    (K : ∀ n, (f.comp (telescopeStageCylinder F n)).Homotopy
      (g.comp (telescopeStageCylinder F n)))
    (hzero : ∀ n (t : I) (x : F.obj n), K n (t,(0,x)) = H n (t,x))
    (hone : ∀ n (t : I) (x : F.obj n), K n (t,(1,x)) =
      H (n+1) (t,F.map (homOfLE (Nat.le_succ n)) x)) :
    ∃ L : f.Homotopy g,
      (∀ n (t : I) (x : F.obj n), L (t,telescopeStageInclusion F n x) = H n (t,x)) ∧
      ∀ n (t s : I) (x : F.obj n),
        L (t,telescopeStageCylinder F n (s,x)) = K n (t,(s,x)) := by
  obtain ⟨HA,hA⟩ := exists_homotopy_of_topological_cofan (ι := ℕ) (A := fun n => F.obj n) (Y := Y)
    (TopCat.sigmaCofan (fun n => F.obj n)) (TopCat.sigmaCofanIsColimit (fun n => F.obj n))
    (f.comp (telescopeVertexInclusion F).hom) (g.comp (telescopeVertexInclusion F).hom) (fun n => (H n).cast rfl rfl)
  let k (n : ℕ) : C(F.obj n × (I × I),Y) := (K n).toContinuousMap.comp
    ⟨fun z => (z.2.1,(z.2.2,z.1)),continuous_snd.fst.prodMk (continuous_snd.snd.prodMk continuous_fst)⟩
  let p : C(telescopeVertices F,C(I × I,Y)) :=
    ⟨fun x => (k x.1).curry x.2,continuous_sigma (fun n => (k n).curry.continuous)⟩
  let HC : (f.comp (telescopeCylinderInclusion F).hom).Homotopy
      (g.comp (telescopeCylinderInclusion F).hom) := {
    toContinuousMap := p.uncurry.comp
      ⟨fun z => (z.2.2,(z.1,z.2.1)),continuous_snd.snd.prodMk (continuous_fst.prodMk continuous_snd.fst)⟩
    map_zero_left := by rintro ⟨s,n,x⟩; exact (K n).apply_zero (s,x)
    map_one_left := by rintro ⟨s,n,x⟩; exact (K n).apply_one (s,x) }
  have hw (t : I) (z : telescopeEnds F) :
      HA (t,telescopeAttachingMap F z) = HC (t,telescopeEndpointMap F z) := by
    rcases z with ⟨n,x⟩ | ⟨n,x⟩
    · exact (hA n t x).trans (hzero n t x).symm
    · exact (hA (n+1) t (F.map (homOfLE (Nat.le_succ n)) x)).trans (hone n t x).symm
  obtain ⟨L,hLV,hLC⟩ := exists_homotopy_of_topological_pushout (telescope_isPushout F) f g HA HC hw
  refine ⟨L,?_,?_⟩
  · intro n t x
    exact (hLV t ⟨n,x⟩).trans (hA n t x)
  · intro n t s x
    exact hLC t (s,⟨n,x⟩)

end KIP126.Topology.SequentialColimit
