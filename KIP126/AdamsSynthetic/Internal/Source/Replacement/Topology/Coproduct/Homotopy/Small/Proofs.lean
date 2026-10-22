module

import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.Homotopy.Basic

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u v

set_option backward.isDefEq.respectTransparency false

/-- Prescribed homotopies on every summand of an actual topological
coproduct glue continuously and retain their exact summand values. -/
theorem exists_homotopy_of_topological_cofan
    {ι : Type v} {A : ι → TopCat.{u}} (c : Cofan A) (hc : IsColimit c)
    {Y : TopCat.{u}} (F G : C(c.pt,Y))
    (HA : ∀ j, (F.comp (c.inj j).hom).Homotopy (G.comp (c.inj j).hom)) :
    ∃ H : F.Homotopy G,
      ∀ j (t : I) (x : A j), H (t,c.inj j x) = HA j (t,x) := by
  let p (j : ι) : A j ⟶ TopCat.of C(I,Y) :=
    TopCat.ofHom ((HA j).toContinuousMap.comp ContinuousMap.prodSwap).curry
  let d := hc.desc (Cofan.mk _ p)
  let E : C(c.pt × I,Y) := d.hom.uncurry
  have hA (j : ι) (t : I) (x : A j) : E (c.inj j x,t) = HA j (t,x) :=
    congrArg (fun p : C(I,Y) => p t)
      (ConcreteCategory.congr_hom (hc.fac (Cofan.mk _ p) ⟨j⟩) x)
  have h0 : TopCat.ofHom (Y := Y)
      (E.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 0))) =
      TopCat.ofHom (X := c.pt) (Y := Y) F := by
    apply hc.hom_ext
    rintro ⟨j⟩
    ext x
    exact (hA j 0 x).trans ((HA j).apply_zero x)
  have h1 : TopCat.ofHom (Y := Y)
      (E.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 1))) =
      TopCat.ofHom (X := c.pt) (Y := Y) G := by
    apply hc.hom_ext
    rintro ⟨j⟩
    ext x
    exact (hA j 1 x).trans ((HA j).apply_one x)
  exact ⟨{
    toFun := fun z => E (z.2,z.1)
    continuous_toFun := E.continuous.comp (continuous_snd.prodMk continuous_fst)
    map_zero_left := ConcreteCategory.congr_hom h0
    map_one_left := ConcreteCategory.congr_hom h1 },hA⟩

end KIP126.Topology
