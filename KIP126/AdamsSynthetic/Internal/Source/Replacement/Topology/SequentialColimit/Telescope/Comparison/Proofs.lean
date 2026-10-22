module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Rectification.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Triangle.Proofs

@[expose] section

namespace KIP126.Topology.SequentialColimit

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- For an actual sequence of HEP maps, every telescope map is homotopic
to one factoring through the actual colimit comparison. The homotopy is
constructed from strictified stage maps and explicit cylinder triangles. -/
theorem telescope_comparison_precomp_homotopic_surjective
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ n, HomotopyExtension.HasHomotopyExtension (F.map (homOfLE (Nat.le_succ n))))
    (p : telescope F ⟶ c.pt)
    (hp : ∀ n (t : I) (x : F.obj n), p (telescopeStageCylinder F n (t,x)) = c.ι.app n x)
    {Y : TopCat.{u}} (d : telescope F ⟶ Y) :
    ∃ r : c.pt ⟶ Y, (r.hom.comp p.hom).Homotopic d.hom := by
  let f (n : ℕ) : C(F.obj n,Y) := (telescopeStageInclusion F n ≫ d).hom
  let H (n : ℕ) : (f n).Homotopy ((f (n+1)).comp (F.map (homOfLE (Nat.le_succ n))).hom) := {
    toContinuousMap := d.hom.comp (telescopeStageCylinder F n)
    map_zero_left := fun x => congrArg d (telescopeStageCylinder_zero F n x)
    map_one_left := fun x => congrArg d (telescopeStageCylinder_one F n x) }
  obtain ⟨g,K,hg,hK⟩ := exists_strict_family_of_homotopy_coherent F hF f H
  have hgs (n : ℕ) : F.map (homOfLE (Nat.le_succ n)) ≫ TopCat.ofHom (g (n+1)) = TopCat.ofHom (g n) := by
    ext x
    exact hg n x
  have hgn {n m : ℕ} (h : n ≤ m) : F.map (homOfLE h) ≫ TopCat.ofHom (g m) = TopCat.ofHom (g n) := by
    induction m,h using Nat.le_induction with
    | base => simp
    | succ m h ih =>
      rw [show homOfLE (by omega : n ≤ m+1) = homOfLE h ≫ homOfLE (Nat.le_succ m) from rfl,
        CategoryTheory.Functor.map_comp,Category.assoc,hgs,ih]
  let cg : Cocone F := {
    pt := Y
    ι := { app := fun n => TopCat.ofHom (g n)
           naturality := fun n m k => by
             change F.map k ≫ TopCat.ofHom (g m) = TopCat.ofHom (g n) ≫ 𝟙 Y
             rw [Category.comp_id]
             rw [show k = homOfLE (leOfHom k) from Subsingleton.elim _ _]
             exact hgn (leOfHom k) } }
  let r := hc.desc cg
  have hr (n : ℕ) (x : F.obj n) : r (c.ι.app n x) = g n x :=
    ConcreteCategory.congr_hom (hc.fac cg n) x
  have hpv (n : ℕ) (x : F.obj n) : p (telescopeStageInclusion F n x) = c.ι.app n x := by
    rw [← telescopeStageCylinder_zero F n x]
    exact hp n 0 x
  have hv (n : ℕ) : (r.hom.comp p.hom).comp (telescopeStageInclusion F n).hom = g n := by
    ext x
    exact (congrArg r (hpv n x)).trans (hr n x)
  let KH (n : ℕ) := (K n).cast (hv n).symm rfl
  have ht (n : ℕ) := exists_homotopy_concat_triangle (K n) (H n)
  choose L hL0 hL1 using ht
  have hvC (n : ℕ) : (r.hom.comp p.hom).comp (telescopeStageCylinder F n) =
      (g n).comp ContinuousMap.snd := by
    ext ⟨s,x⟩
    exact (congrArg r (hp n s x)).trans (hr n x)
  let KL (n : ℕ) := (L n).cast (hvC n).symm rfl
  obtain ⟨J,_,_⟩ := exists_telescope_homotopy F (r.hom.comp p.hom) d.hom KH KL
    (fun n t x => hL0 n t x) (fun n t x => (hL1 n t x).trans (hK n t x).symm)
  exact ⟨r,⟨J⟩⟩

end KIP126.Topology.SequentialColimit
