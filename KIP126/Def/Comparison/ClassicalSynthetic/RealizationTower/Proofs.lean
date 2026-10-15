module

public import KIP126.Def.Comparison.ClassicalSynthetic.RealizationTower.Data
public import KIP126.Def.ClassicalAdams.TowerVanishing.Proofs
public import KIP126.Def.StableHomotopy.Context.Suspension.Proofs
public import KIP126.Def.StableHomotopy.Context.Connecting.Desuspension.Proofs

@[expose] public section
/-! A realization map on Adams pages, induced by the ACTUAL exact strong
monoidal functor. The layer map is a formula in F.map, F's monoidal maps,
the coefficient identification and the tower identification. There is no
freely supplied map of E1/E2 groups. This is the direction of tau inversion
in BHS, SynRevAdams.tex (before Theorem `thm:synth-ASS`).

The comparisons are structural model data; existence and compatibility
proofs are separate obligations. No BHS differential or survivor is assumed.
-/
namespace KIP126.Comparison.ClassicalSynthetic.RealizationTower
open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {S : Type u} [StableHomotopyCategory.{u, v} S]
  [HasFunctorialCofiber (C := S)]
  {C : Type w} [StableHomotopyCategory.{w, v} C]
  [HasFunctorialCofiber (C := C)]
  (F : S ⥤ C) [F.Monoidal] [F.CommShift ℤ] [F.Additive]
  {HS : S} {HC : C} (unitS : 𝟙_ S ⟶ HS) (unitC : 𝟙_ C ⟶ HC)
  (coefficient : F.obj HS ≅ HC)

variable {F unitS unitC coefficient Y X}
  {base : F.obj Y ≅ X} (P : Comparison F unitS unitC coefficient Y X base)

omit [F.Additive] in
/-- The specified adjacent-stage squares give every transition square.
This uses the same tower-factorization argument as the geometric Adams
representative proofs, on the already defined realization comparison. -/
theorem towerMap_naturality (a b : ℕ) (hab : a ≤ b) :
    F.map (adamsTowerMap unitS Y a b hab) ≫ (P.tower a).hom =
      (P.tower b).hom ≫ adamsTowerMap unitC X a b hab := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [adamsTowerMap_succ unitS Y a b hab, adamsTowerMap_succ unitC X a b hab, F.map_comp,
      Category.assoc, ih, ← Category.assoc, P.step, Category.assoc]

/-- The three triangle equations imply preservation of the ACTUAL
cycle and boundary submodules, at every finite page. -/
theorem e1Map_mem_cycles (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (a : adamsE1 unitS Y s t) (ha : a ∈ adamsCycles unitS Y r hr s t) :
    e1Map P s t a ∈ adamsCycles unitC X r hr s t := by
  obtain ⟨b, hb⟩ := ha
  obtain ⟨c, hc⟩ := (homotopyDesuspend_bijective (adamsTowerAt unitS Y (s+r)) (t-s)).2 b
  have hs : c ≫ (adamsTowerMapAt unitS Y (s+1) (s+r) (by omega))⟦(1 : ℤ)⟧' =
      a ≫ HasFunctorialCofiber.cofibδ (adamsTowerMapAt unitS Y s (s+1) (by omega)) := by
    apply (homotopyDesuspend_bijective (adamsTowerAt unitS Y (s+1)) (t-s)).1
    rw [homotopyDesuspend_postcompose, hc]
    change b ≫ adamsTowerMapAt unitS Y (s+1) (s+r) _ =
      connectingHomomorphism (HoCofiberSequence.ofMorphism
        (adamsTowerMapAt unitS Y s (s+1) (by omega))) (t-s) a at hb
    rw [connectingHomomorphism_eq_desuspend] at hb
    exact hb
  have ht : (F.commShiftIso (1 : ℤ)).hom.app (adamsTowerAt unitS Y (s+r)) ≫
      ((P.tower (s+r).toNat).hom)⟦(1 : ℤ)⟧' ≫
      (adamsTowerMapAt unitC X (s+1) (s+r) (by omega))⟦(1 : ℤ)⟧' =
    F.map ((adamsTowerMapAt unitS Y (s+1) (s+r) (by omega))⟦(1 : ℤ)⟧') ≫
      (F.commShiftIso (1 : ℤ)).hom.app (adamsTowerAt unitS Y (s+1)) ≫
      ((P.tower (s+1).toNat).hom)⟦(1 : ℤ)⟧' := by
    rw [← Functor.map_comp]
    change _ ≫ (shiftFunctor C (1 : ℤ)).map
      ((P.tower (s+r).toNat).hom ≫ adamsTowerMap unitC X (s+1).toNat (s+r).toNat _) = _
    rw [← towerMap_naturality P, Functor.map_comp, ← Category.assoc]
    erw [← (F.commShiftIso (1 : ℤ)).hom.naturality]
    simp only [Functor.comp_map, adamsTowerMapAt, adamsTowerAt, Category.assoc]
  let d := (sphereIso F (t-s)).inv ≫ F.map c ≫
    (F.commShiftIso (1 : ℤ)).hom.app (adamsTowerAt unitS Y (s+r)) ≫
      ((P.tower (s+r).toNat).hom)⟦(1 : ℤ)⟧'
  have hd : d ≫ (adamsTowerMapAt unitC X (s+1) (s+r) (by omega))⟦(1 : ℤ)⟧' =
      e1Map P s t a ≫ HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt unitC X s (s+1) (by omega)) := by
    change ((sphereIso F (t-s)).inv ≫ F.map c ≫ _ ≫ _) ≫ _ =
      ((sphereIso F (t-s)).inv ≫ F.map a ≫ _) ≫ _
    simp only [Category.assoc]
    rw [ht, ← F.map_comp_assoc, hs, F.map_comp]
    rw [P.connecting]
    simp only [Category.assoc]
  refine ⟨homotopyDesuspend (adamsTowerAt unitC X (s+r)) (t-s) d, ?_⟩
  change homotopyDesuspend (adamsTowerAt unitC X (s+r)) (t-s) d ≫
    adamsTowerMapAt unitC X (s+1) (s+r) _ =
      connectingHomomorphism (HoCofiberSequence.ofMorphism
        (adamsTowerMapAt unitC X s (s+1) (by omega))) (t-s) (e1Map P s t a)
  rw [connectingHomomorphism_eq_desuspend, ← homotopyDesuspend_postcompose, hd]
  rfl

theorem e1Map_mem_boundaries (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (a : adamsE1 unitS Y s t) (ha : a ∈ adamsBoundaries unitS Y r hr s t) :
    e1Map P s t a ∈ adamsBoundaries unitC X r hr s t := by
  obtain ⟨b, hb, rfl⟩ := ha
  refine ⟨(sphereIso F (t-s)).inv ≫ F.map b ≫ (P.tower s.toNat).hom, ?_, ?_⟩
  · change ((sphereIso F (t-s)).inv ≫ F.map b ≫ (P.tower s.toNat).hom) ≫
      adamsTowerMap unitC X (s-r+1).toNat s.toNat _ = 0
    change b ≫ adamsTowerMap unitS Y (s-r+1).toNat s.toNat _ = 0 at hb
    rw [Category.assoc, Category.assoc, ← towerMap_naturality P,
      ← Category.assoc (F.map b), ← F.map_comp, hb, F.map_zero,
      CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
  · change ((sphereIso F (t-s)).inv ≫ F.map b ≫ (P.tower s.toNat).hom) ≫
      HasFunctorialCofiber.cofibι (adamsTowerMapAt unitC X s (s+1) _) =
      (sphereIso F (t-s)).inv ≫ F.map (b ≫
        HasFunctorialCofiber.cofibι (adamsTowerMapAt unitS Y s (s+1) _)) ≫ _
    rw [F.map_comp]
    simp only [Category.assoc]
    rw [P.cofiber]

end
end KIP126.Comparison.ClassicalSynthetic.RealizationTower
