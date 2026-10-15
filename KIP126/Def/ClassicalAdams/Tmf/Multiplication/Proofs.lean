module

public import KIP126.Def.ClassicalAdams.Tmf.Multiplication.Data
public import KIP126.Def.ClassicalAdams.TowerLongLayer.Lifting.Proofs
public import KIP126.Def.ClassicalAdams.Moss.Composition.CoefficientCycles.Layer.Proofs

@[expose] public section

namespace KIP126.Classical.Adams.Tmf

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (T : Mon C) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ] [MonoidalPreadditive C]

/-- The prescribed first-group product preserves second cycles. This is the
algebra-object analogue of the actual Moss layer kernel calculation, not an
assumed multiplication on a quotient page. Its proof is deferred. -/
theorem firstMultiplication_mem_secondCycles (s t s' t' : ℕ)
    (a : adamsCycles H.unit T.X 2 (by decide) s t)
    (b : adamsCycles H.unit T.X 2 (by decide) s' t') :
    firstMultiplication H T R s t s' t' a.val b.val ∈
      adamsCycles H.unit T.X 2 (by decide)
        ((s + s' : ℕ) : ℤ) ((t + t' : ℕ) : ℤ) := by
  set_option backward.isDefEq.respectTransparency false in
    have cycle_boundary (p q : ℕ) (x : adamsCycles H.unit T.X 2 (by decide) p q) :
        x.val ≫ HasFunctorialCofiber.cofibδ
          (adamsTowerMapAt H.unit T.X (p : ℤ) ((p : ℤ) + 1) (by omega)) ≫
        (HasFunctorialCofiber.cofibι
          (adamsTowerMapAt H.unit T.X ((p : ℤ) + 1) (((p : ℤ) + 1) + 1)
            (by omega)))⟦(1 : ℤ)⟧' = 0 := by
      obtain ⟨z, hz⟩ := (adamsCycles_mem_iff_longLayer H.unit T.X 2 (by decide)
        p q x.val).mp x.property
      change z ≫ adamsLongLayerProjection H.unit T.X 2 (by decide) p = x.val at hz
      rw [← hz, Category.assoc, Moss.longLayerTwoProjection_firstBoundary_eq_zero,
        Limits.comp_zero]
    have cycle_of_boundary (p q : ℕ) (x : adamsE1 H.unit T.X p q)
        (hx : x ≫ HasFunctorialCofiber.cofibδ
          (adamsTowerMapAt H.unit T.X (p : ℤ) ((p : ℤ) + 1) (by omega)) ≫
        (HasFunctorialCofiber.cofibι
          (adamsTowerMapAt H.unit T.X ((p : ℤ) + 1) (((p : ℤ) + 1) + 1)
            (by omega)))⟦(1 : ℤ)⟧' = 0) :
        x ∈ adamsCycles H.unit T.X 2 (by decide) p q := by
      apply (adamsCycles_mem_iff_longLayer H.unit T.X 2 (by decide) p q x).mpr
      change ∃ z, z ≫ adamsLongLayerProjection H.unit T.X 2 (by decide) p = x
      apply (adamsLongLayerProjection_lift_iff H.unit T.X 2 (by decide) p x).mpr
      let U := adamsLayerTriangle H.unit T.X ((p : ℤ) + 1)
      have hU := adamsLayerTriangle_distinguished H.unit T.X ((p : ℤ) + 1)
      have hz : (x ≫ HasFunctorialCofiber.cofibδ
          (adamsTowerMapAt H.unit T.X (p : ℤ) ((p : ℤ) + 1) (by omega))) ≫
          ((shiftFunctor (Pretriangulated.Triangle C) (1 : ℤ)).obj U).mor₂ = 0 := by
        simpa [Pretriangulated.Triangle.shiftFunctor, U, adamsLayerTriangle, Pretriangulated.Triangle.mk, adamsLayerAt,
          Category.assoc] using hx
      obtain ⟨y, hy⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _
        (Pretriangulated.Triangle.shift_distinguished U hU (1 : ℤ)) _ hz
      have hy' : x ≫ HasFunctorialCofiber.cofibδ
          (adamsTowerMapAt H.unit T.X (p : ℤ) ((p : ℤ) + 1) (by omega)) =
          (-y) ≫ U.mor₁⟦(1 : ℤ)⟧' := by
        simpa [Pretriangulated.Triangle.shiftFunctor, Preadditive.comp_neg, Preadditive.neg_comp] using hy
      have he : ∃ z : Sphere ((q : ℤ) - p) ⟶ U.obj₁⟦(1 : ℤ)⟧,
          z ≫ U.mor₁⟦(1 : ℤ)⟧' = x ≫ HasFunctorialCofiber.cofibδ
            (adamsTowerMapAt H.unit T.X (p : ℤ) ((p : ℤ) + 1) (by omega)) :=
        ⟨-y, hy'.symm⟩
      convert he using 1 <;> congr 2
    apply cycle_of_boundary (s+s') (t+t')
    have hp : ((a.val ⊗ₘ b.val) ≫
        ((adamsLayerIso H.unit T.X s).hom ⊗ₘ (adamsLayerIso H.unit T.X s').hom) ≫
        mod2CoefficientPairing H R (stageMultiplication H T s s') ≫
        (adamsLayerIso H.unit T.X (s'+s)).inv) ≫
        HasFunctorialCofiber.cofibδ
          (adamsTowerMapAt H.unit T.X ((s'+s : ℕ) : ℤ) (((s'+s : ℕ) : ℤ) + 1) (by omega)) ≫
        (HasFunctorialCofiber.cofibι
          (adamsTowerMapAt H.unit T.X (((s'+s : ℕ) : ℤ) + 1)
            ((((s'+s : ℕ) : ℤ) + 1) + 1) (by omega)))⟦(1 : ℤ)⟧' = 0 := by
      apply (Moss.layerFirstBoundary_eq_zero_iff_unit_equalizer H R T.X (s'+s) _).mpr
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      simp only [← Category.assoc, tensorHom_comp_tensorHom]
      exact Moss.coefficientPairing_preserves_unit_equalizer H R _ _ _
        ((Moss.layerFirstBoundary_eq_zero_iff_unit_equalizer H R T.X s a.val).mp
          (cycle_boundary s t a))
        ((Moss.layerFirstBoundary_eq_zero_iff_unit_equalizer H R T.X s' b.val).mp
          (cycle_boundary s' t' b))
    have boundary_transport {U : C} (i j : ℤ) (h : i = j)
        (x : U ⟶ adamsLayerAt H.unit T.X i)
        (hx : x ≫ HasFunctorialCofiber.cofibδ
            (adamsTowerMapAt H.unit T.X i (i + 1) (by omega)) ≫
          (HasFunctorialCofiber.cofibι
            (adamsTowerMapAt H.unit T.X (i + 1) ((i + 1) + 1) (by omega)))⟦(1 : ℤ)⟧' = 0) :
        x ≫ eqToHom (congrArg (adamsLayerAt H.unit T.X) h) ≫
          HasFunctorialCofiber.cofibδ
            (adamsTowerMapAt H.unit T.X j (j + 1) (by omega)) ≫
          (HasFunctorialCofiber.cofibι
            (adamsTowerMapAt H.unit T.X (j + 1) ((j + 1) + 1) (by omega)))⟦(1 : ℤ)⟧' = 0 := by
      subst j
      simpa only [eqToHom_refl, Category.id_comp] using hx
    have hq := boundary_transport ((s'+s : ℕ) : ℤ) ((s+s' : ℕ) : ℤ) (by omega) _ hp
    let w := eqToHom (congrArg (Sphere (C := C))
        (show ((t+t' : ℕ) : ℤ) - ((s+s' : ℕ) : ℤ) =
          ((t : ℤ) - s) + ((t' : ℤ) - s') by omega)) ≫
      (sphereTensorIsoFromRightShift (C := C) ((t : ℤ) - s) ((t' : ℤ) - s')).inv
    change (w ≫ (a.val ⊗ₘ b.val) ≫ layerMultiplication H T R s s') ≫ _ ≫ _ = 0
    simpa only [layerMultiplication, Category.assoc, Limits.comp_zero] using
      congrArg (fun f => w ≫ f) hq

end KIP126.Classical.Adams.Tmf
