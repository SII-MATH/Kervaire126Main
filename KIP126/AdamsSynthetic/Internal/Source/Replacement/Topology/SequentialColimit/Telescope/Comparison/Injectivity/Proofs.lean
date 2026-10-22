module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.Telescope.Comparison.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.CylinderCorner.Extension.Proofs

@[expose] section

namespace KIP126.Topology.SequentialColimit

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- For a sequence of closed HEP maps, a homotopy after the actual telescope
comparison descends to a homotopy on the actual colimit. The proof retains
relative two-parameter homotopies while recursively correcting the stage
homotopies to agree strictly. -/
theorem telescope_comparison_precomp_homotopic_injective
    (F : ℕ ⥤ TopCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ n, HomotopyExtension.HasHomotopyExtension (F.map (homOfLE (Nat.le_succ n))))
    (hclosed : ∀ n, _root_.Topology.IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    (p : telescope F ⟶ c.pt)
    (hp : ∀ n (t : I) (x : F.obj n), p (telescopeStageCylinder F n (t,x)) = c.ι.app n x)
    {Y : TopCat.{u}} (f g : C(c.pt,Y))
    (L : (f.comp p.hom).Homotopy (g.comp p.hom)) : f.Homotopic g := by
  classical
  have hpv (n : ℕ) (x : F.obj n) : p (telescopeStageInclusion F n x) = c.ι.app n x := by
    rw [← telescopeStageCylinder_zero F n x]
    exact hp n 0 x
  let fn (n : ℕ) := f.comp (c.ι.app n).hom
  let gn (n : ℕ) := g.comp (c.ι.app n).hom
  let S (n : ℕ) : Set (I × F.obj n) := {z | z.1 = 0 ∨ z.1 = 1}
  let H (n : ℕ) : (fn n).Homotopy (gn n) := {
    toContinuousMap := L.toContinuousMap.comp
      ⟨fun z => (z.1,telescopeStageInclusion F n z.2),
        continuous_fst.prodMk ((telescopeStageInclusion F n).hom.continuous.comp continuous_snd)⟩
    map_zero_left := fun x => (L.apply_zero _).trans (congrArg f (hpv n x))
    map_one_left := fun x => (L.apply_one _).trans (congrArg g (hpv n x)) }
  let C (n : ℕ) : (H n).toContinuousMap.HomotopyRel
      ((H (n+1)).toContinuousMap.comp
        ⟨fun z => (z.1,F.map (homOfLE (Nat.le_succ n)) z.2),
          continuous_fst.prodMk ((F.map (homOfLE (Nat.le_succ n))).hom.continuous.comp continuous_snd)⟩)
      (S n) := {
    toHomotopy := {
      toContinuousMap := L.toContinuousMap.comp
        ⟨fun z => (z.2.1,telescopeStageCylinder F n (z.1,z.2.2)),
          continuous_snd.fst.prodMk ((telescopeStageCylinder F n).continuous.comp
            (continuous_fst.prodMk continuous_snd.snd))⟩
      map_zero_left := by rintro ⟨t,x⟩; exact congrArg (fun y => L (t,y)) (telescopeStageCylinder_zero F n x)
      map_one_left := by rintro ⟨t,x⟩; exact congrArg (fun y => L (t,y)) (telescopeStageCylinder_one F n x) }
    prop' := by
      rintro s ⟨t,x⟩ (ht | ht)
      · change t = 0 at ht
        subst t
        change L (0,telescopeStageCylinder F n (s,x)) = L (0,telescopeStageInclusion F n x)
        rw [L.apply_zero,L.apply_zero]
        exact congrArg f ((hp n s x).trans (hpv n x).symm)
      · change t = 1 at ht
        subst t
        change L (1,telescopeStageCylinder F n (s,x)) = L (1,telescopeStageInclusion F n x)
        rw [L.apply_one,L.apply_one]
        exact congrArg g ((hp n s x).trans (hpv n x).symm) }
  let T (n : ℕ) := Σ K : (fn n).Homotopy (gn n),
    K.toContinuousMap.HomotopyRel (H n).toContinuousMap (S n)
  have hstep (n : ℕ) (z : T n) : ∃ z' : T (n+1),
      ∀ (t : I) (x : F.obj n), z'.1 (t,F.map (homOfLE (Nat.le_succ n)) x) = z.1 (t,x) := by
    let J := (z.2.trans (C n)).symm
    let q := (H (n+1)).toContinuousMap.comp ContinuousMap.prodSwap
    let a : C((F.obj n × I) × I,Y) := J.toContinuousMap.comp
      ⟨fun w => (w.2,(w.1.2,w.1.1)),continuous_snd.prodMk (continuous_fst.snd.prodMk continuous_fst.fst)⟩
    obtain ⟨E,hE,hEi,hE0,hE1⟩ := (hF n).exists_endpoint_extension (hclosed n) Y q a
      (fun x t => J.apply_zero (t,x))
      (fun x s => J.eq_fst s (Or.inl rfl))
      (fun x s => J.eq_fst s (Or.inr rfl))
    let K : (fn (n+1)).Homotopy (gn (n+1)) := {
      toContinuousMap := E.comp
        ⟨fun w => ((w.2,w.1),1),(continuous_snd.prodMk continuous_fst).prodMk continuous_const⟩
      map_zero_left := fun x => (hE0 x 1).trans ((H (n+1)).apply_zero x)
      map_one_left := fun x => (hE1 x 1).trans ((H (n+1)).apply_one x) }
    let R : K.toContinuousMap.HomotopyRel (H (n+1)).toContinuousMap (S (n+1)) := {
      toHomotopy := {
        toContinuousMap := E.comp
          ⟨fun w => ((w.2.2,w.2.1),unitInterval.symm w.1),
            (continuous_snd.snd.prodMk continuous_snd.fst).prodMk
              (unitInterval.continuous_symm.comp continuous_fst)⟩
        map_zero_left := by
          rintro ⟨t,x⟩
          change E ((x,t),unitInterval.symm 0) = E ((x,t),1)
          rw [unitInterval.symm_zero]
        map_one_left := by
          rintro ⟨t,x⟩
          change E ((x,t),unitInterval.symm 1) = (H (n+1)) (t,x)
          rw [unitInterval.symm_one]
          exact hE x t }
      prop' := by
        rintro s ⟨t,x⟩ (ht | ht)
        · change t = 0 at ht
          subst t
          exact (hE0 x (unitInterval.symm s)).trans (hE0 x 1).symm
        · change t = 1 at ht
          subst t
          exact (hE1 x (unitInterval.symm s)).trans (hE1 x 1).symm }
    refine ⟨⟨K,R⟩,?_⟩
    intro t x
    exact (hEi x t 1).trans (J.apply_one (t,x))
  choose next hnext using hstep
  let z : ∀ n, T n := fun n => Nat.rec
    ⟨H 0,ContinuousMap.HomotopyRel.refl (H 0).toContinuousMap (S 0)⟩
    (fun n z => next n z) n
  let k (n : ℕ) : F.obj n ⟶ TopCat.of C(I,Y) :=
    TopCat.ofHom ((z n).1.toContinuousMap.comp ContinuousMap.prodSwap).curry
  have hks (n : ℕ) : F.map (homOfLE (Nat.le_succ n)) ≫ k (n+1) = k n := by
    ext x t
    exact hnext n (z n) t x
  have hkn {n m : ℕ} (h : n ≤ m) : F.map (homOfLE h) ≫ k m = k n := by
    induction m,h using Nat.le_induction with
    | base => simp
    | succ m h ih =>
      rw [show homOfLE (by omega : n ≤ m+1) = homOfLE h ≫ homOfLE (Nat.le_succ m) from rfl,
        CategoryTheory.Functor.map_comp,Category.assoc,hks,ih]
  let ck : Cocone F := {
    pt := TopCat.of C(I,Y)
    ι := { app := k
           naturality := fun n m h => by
             change F.map h ≫ k m = k n ≫ 𝟙 _
             rw [Category.comp_id,show h = homOfLE (leOfHom h) from Subsingleton.elim _ _]
             exact hkn (leOfHom h) } }
  let d := hc.desc ck
  let E : C(c.pt × I,Y) := d.hom.uncurry
  have hD (n : ℕ) (x : F.obj n) (t : I) : E (c.ι.app n x,t) = (z n).1 (t,x) :=
    congrArg (fun p : C(I,Y) => p t) (ConcreteCategory.congr_hom (hc.fac ck n) x)
  have hzero : TopCat.ofHom (E.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 0))) =
      TopCat.ofHom f := by
    apply hc.hom_ext
    intro n
    ext x
    exact (hD n x 0).trans ((z n).1.apply_zero x)
  have hone : TopCat.ofHom (E.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 1))) =
      TopCat.ofHom g := by
    apply hc.hom_ext
    intro n
    ext x
    exact (hD n x 1).trans ((z n).1.apply_one x)
  exact ⟨{
    toContinuousMap := E.comp ContinuousMap.prodSwap
    map_zero_left := ConcreteCategory.congr_hom hzero
    map_one_left := ConcreteCategory.congr_hom hone }⟩

end KIP126.Topology.SequentialColimit
