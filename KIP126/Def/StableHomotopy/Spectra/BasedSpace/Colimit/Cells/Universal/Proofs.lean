module

public import KIP126.Def.StableHomotopy.Spectra.BasedSpace.Under.Data
public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.BasedSpace

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u w
variable {α : Type w} {A B : α → BasedSpace.{u}} {g : ∀ i, A i ⟶ B i}
  {X Y : BasedSpace.{u}} {f : X ⟶ Y} (c : AttachCells.{u} g f)

set_option backward.isDefEq.respectTransparency false

/-- The based attachment already has the universal property for arbitrary
continuous target maps: their value on the old basepoint determines the
target basepoint and forces all cell maps to preserve it. -/
theorem exists_continuous_desc_of_attachCells (T : TopCat.{u}) (a : C(X,T))
    (b : ∀ i : c.ι, C(B (c.π i),T))
    (hw : ∀ i x, a ((c.cofan₁.inj i ≫ c.g₁).map x) = b i ((g (c.π i)).map x)) :
    ∃ l : C(Y,T), l.comp f.map = a ∧ ∀ i, l.comp (c.cell i).map = b i := by
  let Z : BasedSpace.{u} := ⟨T,a X.point⟩
  let a' : X ⟶ Z := ⟨a,rfl⟩
  let b' (i : c.ι) : B (c.π i) ⟶ Z :=
    ⟨b i, by
      have h := hw i (A (c.π i)).point
      rw [(c.cofan₁.inj i ≫ c.g₁).point, (g (c.π i)).point] at h
      exact h.symm⟩
  let bd := Cofan.IsColimit.desc c.isColimit₂ b'
  have hb : c.g₁ ≫ a' = c.m ≫ bd := by
    apply Cofan.IsColimit.hom_ext c.isColimit₁
    intro i
    rw [← Category.assoc, ← Category.assoc, c.hm i]
    simp only [Category.assoc, bd, Cofan.IsColimit.fac]
    apply Hom.ext
    apply ContinuousMap.ext
    exact hw i
  let l := c.isPushout.desc a' bd hb
  refine ⟨l.map, congrArg Hom.map (c.isPushout.inl_desc a' bd hb), ?_⟩
  intro i
  have hi : c.cell i ≫ l = b' i := by
    rw [AttachCells.cell_def, Category.assoc]
    dsimp only [l]
    rw [c.isPushout.inr_desc]
    exact Cofan.IsColimit.fac c.isColimit₂ b' i
  exact congrArg Hom.map hi

/-- Actual continuous maps out of a based attachment are determined by
the old space and all its cells, even without a specified target point. -/
theorem continuousMap_ext_of_attachCells (T : TopCat.{u}) (a b : C(Y,T))
    (h₀ : a.comp f.map = b.comp f.map)
    (h : ∀ i, a.comp (c.cell i).map = b.comp (c.cell i).map) : a = b := by
  let Z : BasedSpace.{u} := ⟨T,a Y.point⟩
  have hb : b Y.point = a Y.point := by
    have hh := congrArg (fun k : C(X,T) => k X.point) h₀
    simpa only [ContinuousMap.comp_apply, f.point] using hh.symm
  let a' : Y ⟶ Z := ⟨a,rfl⟩
  let b' : Y ⟶ Z := ⟨b,hb⟩
  apply congrArg Hom.map (c.hom_ext (φ := a') (φ' := b') ?_ ?_)
  · exact Hom.ext h₀
  · intro i
    exact Hom.ext (h i)

end KIP126.StableHomotopy.Spectra.BasedSpace
