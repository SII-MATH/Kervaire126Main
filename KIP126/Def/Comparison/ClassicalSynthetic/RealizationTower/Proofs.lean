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

omit [HasFunctorialCofiber (C := S)] [HasFunctorialCofiber (C := C)]
  [F.CommShift ℤ] [F.Additive] in
private theorem mapped_adamsUnit
    (hunit : CoefficientUnitCompatible F unitS unitC coefficient)
    (Z : S) (Z' : C) (e : F.obj Z ⟶ Z') :
    F.map (adamsUnit unitS Z) ≫ (Functor.Monoidal.μIso F HS Z).inv ≫
      (coefficient.hom ⊗ₘ e) = e ≫ adamsUnit unitC Z' := by
  change (Functor.LaxMonoidal.ε F) ≫ F.map unitS ≫ coefficient.hom = unitC at hunit
  simp only [adamsUnit, F.map_comp, Functor.Monoidal.map_leftUnitor_inv,
    Functor.Monoidal.μIso_inv, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  simp only [Functor.Monoidal.μ_δ_assoc]
  rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom, Category.id_comp, Category.id_comp]
  rw [Category.assoc (Functor.LaxMonoidal.ε F), hunit]
  simp only [tensorHom_def]
  simpa only [adamsUnit, Category.assoc] using (adamsUnit_naturality unitC e).symm

omit [HasFunctorialCofiber (C := C)] in
open CategoryTheory.Pretriangulated in
private theorem triangle_iso₂₃ (T T' : Triangle C)
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (e₂ : T.obj₂ ≅ T'.obj₂) (e₃ : T.obj₃ ≅ T'.obj₃)
    (comm : T.mor₂ ≫ e₃.hom = e₂.hom ≫ T'.mor₂) :
    ∃ e : T ≅ T', e.hom.hom₂ = e₂.hom ∧ e.hom.hom₃ = e₃.hom := by
  let r := isoTriangleOfIso₁₂ T.rotate T'.rotate (rot_of_distTriang _ hT)
    (rot_of_distTriang _ hT') e₂ e₃ comm
  let e := (rotate C).preimageIso r
  have he : (rotate C).map e.hom = r.hom := (rotate C).map_preimage r.hom
  refine ⟨e, ?_, ?_⟩
  · have h := congrArg TriangleMorphism.hom₁ he
    simpa [r] using h
  · have h := congrArg TriangleMorphism.hom₂ he
    simpa [r] using h

open CategoryTheory.Pretriangulated in
private theorem comparison_step [F.IsTriangulated]
    (hunit : CoefficientUnitCompatible F unitS unitC coefficient)
    (Y : S) (X : C) (n : ℕ)
    (e : F.obj (adamsTower unitS Y n) ≅ adamsTower unitC X n) :
    ∃ e' : F.obj (adamsTower unitS Y (n+1)) ≅ adamsTower unitC X (n+1),
      F.map (adamsTowerStep unitS Y n) ≫ e.hom = e'.hom ≫ adamsTowerStep unitC X n ∧
      ((Functor.Monoidal.μIso F HS (adamsTower unitS Y n)).inv ≫
        (coefficient.hom ⊗ₘ e.hom)) ≫
          (adamsFiberTriangle (adamsUnit unitC (adamsTower unitC X n))).mor₃ =
        F.map (adamsFiberTriangle (adamsUnit unitS (adamsTower unitS Y n))).mor₃ ≫
          (F.commShiftIso (1 : ℤ)).hom.app (adamsTower unitS Y (n+1)) ≫
            (shiftFunctor C (1 : ℤ)).map e'.hom := by
  let T := adamsFiberTriangle (adamsUnit unitS (adamsTower unitS Y n))
  let T' := adamsFiberTriangle (adamsUnit unitC (adamsTower unitC X n))
  let eL : F.obj (HS ⊗ adamsTower unitS Y n) ≅ HC ⊗ adamsTower unitC X n :=
    (Functor.Monoidal.μIso F HS (adamsTower unitS Y n)).symm ≪≫ (coefficient ⊗ᵢ e)
  have hc : (F.mapTriangle.obj T).mor₂ ≫ eL.hom = e.hom ≫ T'.mor₂ :=
    mapped_adamsUnit F unitS unitC coefficient hunit _ _ e.hom
  obtain ⟨a, ha₂, ha₃⟩ := triangle_iso₂₃ (F.mapTriangle.obj T) T'
    (F.map_distinguished T (adamsFiberTriangle_distinguished _))
    (adamsFiberTriangle_distinguished _) e eL hc
  refine ⟨Triangle.π₁.mapIso a, ?_, ?_⟩
  · have h := a.hom.comm₁
    change F.map T.mor₁ ≫ a.hom.hom₂ = a.hom.hom₁ ≫ T'.mor₁ at h
    dsimp only [T, T'] at h
    rw [adamsFiberTriangle_mor₁, adamsFiberTriangle_mor₁, ha₂,
      F.map_neg, Preadditive.neg_comp, Preadditive.comp_neg] at h
    exact neg_injective h
  · have h := a.hom.comm₃
    change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
      (shiftFunctor C (1 : ℤ)).map a.hom.hom₁ = a.hom.hom₃ ≫ T'.mor₃ at h
    rw [ha₃, Category.assoc] at h
    exact h.symm

/-- Existence for an exact strong monoidal functor, with its coefficient
unit compatibility visible. This is a construction/comparison theorem,
not an assertion of a selected differential. -/
theorem exists_comparison [F.IsTriangulated]
    (hunit : CoefficientUnitCompatible F unitS unitC coefficient)
    (base : F.obj Y ≅ X) :
    Nonempty (Comparison F unitS unitC coefficient Y X base) := by
  let e : TowerIdentifications F unitS unitC Y X :=
    fun n => Nat.rec base (fun n e => (comparison_step F unitS unitC coefficient hunit Y X n e).choose) n
  have he (n : ℕ) : F.map (adamsTowerStep unitS Y n) ≫ (e n).hom =
      (e (n+1)).hom ≫ adamsTowerStep unitC X n :=
    (comparison_step F unitS unitC coefficient hunit Y X n (e n)).choose_spec.1
  have hδ (n : ℕ) :
      ((Functor.Monoidal.μIso F HS (adamsTower unitS Y n)).inv ≫
        (coefficient.hom ⊗ₘ (e n).hom)) ≫
          (adamsFiberTriangle (adamsUnit unitC (adamsTower unitC X n))).mor₃ =
        F.map (adamsFiberTriangle (adamsUnit unitS (adamsTower unitS Y n))).mor₃ ≫
          (F.commShiftIso (1 : ℤ)).hom.app (adamsTower unitS Y (n+1)) ≫
            (shiftFunctor C (1 : ℤ)).map (e (n+1)).hom :=
    (comparison_step F unitS unitC coefficient hunit Y X n (e n)).choose_spec.2
  refine ⟨{ tower := e, zero := rfl, unit := hunit, step := he, cofiber := ?_, connecting := ?_ }⟩
  · intro s
    by_cases hs : 0 ≤ s
    · lift s to ℕ using hs with n hn
      subst s
      simp only [layerMap, Int.natCast_nonneg, dite_true, Int.toNat_natCast]
      change F.map (HasFunctorialCofiber.cofibι (adamsTowerMapAt unitS Y (n:ℤ) ((n:ℤ)+1) _)) ≫
        (F.map (adamsLayerIso unitS Y n).hom ≫
          (Functor.Monoidal.μIso F HS (adamsTower unitS Y n)).inv ≫
            (coefficient.hom ⊗ₘ (e n).hom) ≫ (adamsLayerIso unitC X n).inv) = _
      rw [← F.map_comp_assoc, adamsLayerIso_ι]
      have hm := congrArg (fun f => f ≫ (adamsLayerIso unitC X n).inv)
        (mapped_adamsUnit F unitS unitC coefficient hunit _ _ (e n).hom)
      simp only [Category.assoc] at hm
      rw [hm, ← adamsLayerIso_ι unitC X n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · exact (adamsLayerAt_isZero_of_negative unitC X s (by omega)).eq_of_tgt _ _
  · intro s
    by_cases hs : 0 ≤ s
    · lift s to ℕ using hs with n hn
      subst s
      simp only [layerMap, Int.natCast_nonneg, dite_true, Int.toNat_natCast]
      change layerMapNat F unitS unitC coefficient Y X e n ≫
        HasFunctorialCofiber.cofibδ (adamsTowerMapAt unitC X (n:ℤ) ((n:ℤ)+1) _) =
        F.map (HasFunctorialCofiber.cofibδ (adamsTowerMapAt unitS Y (n:ℤ) ((n:ℤ)+1) _)) ≫
          (F.commShiftIso (1 : ℤ)).hom.app (adamsTower unitS Y (n+1)) ≫
            (shiftFunctor C (1 : ℤ)).map (e (n+1)).hom
      rw [adamsLayerIso_δ, adamsLayerIso_δ]
      simp only [layerMapNat, F.map_neg, F.map_comp, Preadditive.comp_neg,
        Preadditive.neg_comp, Category.assoc, Iso.inv_hom_id_assoc, neg_inj]
      rw [← Category.assoc (Functor.Monoidal.μIso F HS (adamsTower unitS Y n)).inv, hδ]
    · exact (F.map_isZero (adamsLayerAt_isZero_of_negative unitS Y s (by omega))).eq_of_src _ _

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
