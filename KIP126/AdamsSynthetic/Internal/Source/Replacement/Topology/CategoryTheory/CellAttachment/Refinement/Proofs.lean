module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.CategoryTheory.CellAttachment.Extension.Proofs

@[expose] section

namespace KIP126.Foundation.CellAttachment

open _root_.CategoryTheory _root_.CategoryTheory.Limits HomotopicalAlgebra

universe w v u t t'

set_option backward.isDefEq.respectTransparency false

/-- Refining every old cell by its specified actual cell attachment gives
an attachment by the new generators of the same original map. The new cells
are indexed by the dependent sum of the old cells and their specified refinements. -/
theorem nonempty_refinement {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
    {α : Type t} {A B : α → C} {g : ∀ i, A i ⟶ B i}
    {α' : Type t'} {A' B' : α' → C} {g' : ∀ i, A' i ⟶ B' i}
    {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f)
    (d : ∀ i, AttachCells.{w} g' (g i)) : Nonempty (AttachCells.{w} g' f) := by
  classical
  let J := Σ j : c.ι, (d (c.π j)).ι
  let π : J → α' := fun z => (d (c.π z.1)).π z.2
  let S : J → C := fun z => A' (π z)
  let T : J → C := fun z => B' (π z)
  let u (z : J) : S z ⟶ X :=
    (d (c.π z.1)).cofan₁.inj z.2 ≫ (d (c.π z.1)).g₁ ≫ c.cofan₁.inj z.1 ≫ c.g₁
  let v (z : J) : T z ⟶ Y := (d (c.π z.1)).cell z.2 ≫ c.cell z.1
  let m : ∐ S ⟶ ∐ T := _root_.CategoryTheory.Limits.Sigma.map (fun z => g' (π z))
  let top : ∐ S ⟶ X := Sigma.desc u
  let bottom : ∐ T ⟶ Y := Sigma.desc v
  have hc (j : c.ι) : c.cofan₁.inj j ≫ c.g₁ ≫ f = g (c.π j) ≫ c.cell j := by
    rw [c.isPushout.w,c.hm_assoc,AttachCells.cell_def]
  have hd (j : c.ι) (k : (d (c.π j)).ι) :
      (d (c.π j)).cofan₁.inj k ≫ (d (c.π j)).g₁ ≫ g (c.π j) =
        g' ((d (c.π j)).π k) ≫ (d (c.π j)).cell k := by
    rw [(d (c.π j)).isPushout.w,(d (c.π j)).hm_assoc,AttachCells.cell_def]
  have hw : top ≫ f = m ≫ bottom := by
    apply Sigma.hom_ext
    intro z
    simp only [top,bottom,m,Sigma.ι_desc_assoc,Sigma.ι_map_assoc,Sigma.ι_desc]
    dsimp only [u,v,π]
    rw [Category.assoc,Category.assoc,Category.assoc,hc]
    simpa only [Category.assoc] using congrArg (fun a => a ≫ c.cell z.1) (hd z.1 z.2)
  have hdesc (s : PushoutCocone top m) :
      ∃ q : Y ⟶ s.pt, f ≫ q = s.inl ∧ ∀ z, v z ≫ q = Sigma.ι T z ≫ s.inr := by
    have hcell (j : c.ι) :
        ∃ b : B (c.π j) ⟶ s.pt,
          g (c.π j) ≫ b = c.cofan₁.inj j ≫ c.g₁ ≫ s.inl ∧
          ∀ k, (d (c.π j)).cell k ≫ b = Sigma.ι T ⟨j,k⟩ ≫ s.inr := by
      apply exists_desc (d (c.π j)) (c.cofan₁.inj j ≫ c.g₁ ≫ s.inl)
        (fun k => Sigma.ι T ⟨j,k⟩ ≫ s.inr)
      intro k
      have hh := congrArg (fun a => Sigma.ι S ⟨j,k⟩ ≫ a) s.condition
      simpa only [top,m,Sigma.ι_desc_assoc,Sigma.ι_map_assoc,u,Category.assoc] using hh
    choose b hb hbcell using hcell
    obtain ⟨q,hq,hqc⟩ := exists_desc c s.inl b (fun j => (hb j).symm)
    refine ⟨q,hq,?_⟩
    intro z
    dsimp only [v]
    rw [Category.assoc,hqc,hbcell]
  have huniq {Z : C} (q r : Y ⟶ Z) (h₀ : f ≫ q = f ≫ r)
      (hcell : ∀ z, v z ≫ q = v z ≫ r) : q = r := by
    apply c.hom_ext h₀
    intro j
    apply (d (c.π j)).hom_ext
    · calc
        g (c.π j) ≫ (c.cell j ≫ q) = (c.cofan₁.inj j ≫ c.g₁ ≫ f) ≫ q := by
          rw [hc,Category.assoc]
        _ = (c.cofan₁.inj j ≫ c.g₁ ≫ f) ≫ r := by
          simpa only [Category.assoc] using congrArg (fun a => c.cofan₁.inj j ≫ c.g₁ ≫ a) h₀
        _ = g (c.π j) ≫ (c.cell j ≫ r) := by rw [hc,Category.assoc]
    · intro k
      simpa only [v,Category.assoc] using hcell ⟨j,k⟩
  have hp : IsPushout top m f bottom := by
    apply IsPushout.of_isColimit (c := PushoutCocone.mk f bottom hw)
    refine PushoutCocone.IsColimit.mk _ (fun s => (hdesc s).choose)
      (fun s => (hdesc s).choose_spec.1) ?_ ?_
    · intro s
      apply Sigma.hom_ext
      intro z
      simpa only [bottom,Sigma.ι_desc_assoc] using (hdesc s).choose_spec.2 z
    · intro s q hq₀ hqcell
      apply huniq q (hdesc s).choose (hq₀.trans (hdesc s).choose_spec.1.symm)
      intro z
      have hh := congrArg (fun a => Sigma.ι T z ≫ a) hqcell
      have hh' : v z ≫ q = Sigma.ι T z ≫ s.inr := by
        simpa only [bottom,Sigma.ι_desc_assoc] using hh
      exact hh'.trans ((hdesc s).choose_spec.2 z).symm
  exact ⟨{
    ι := J
    π := π
    cofan₁ := Cofan.mk (∐ S) (Sigma.ι S)
    cofan₂ := Cofan.mk (∐ T) (Sigma.ι T)
    isColimit₁ := coproductIsCoproduct S
    isColimit₂ := coproductIsCoproduct T
    m := m
    hm z := Sigma.ι_map (fun z => g' (π z)) z
    g₁ := top
    g₂ := bottom
    isPushout := hp }⟩

end KIP126.Foundation.CellAttachment
