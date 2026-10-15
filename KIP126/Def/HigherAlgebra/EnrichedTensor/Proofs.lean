module

public import KIP126.Def.HigherAlgebra.EnrichedTensor.Predicates

@[expose] public section

/-! Property statements for the actual enriched finite tensor operations.
The proofs remain separate from the data; they do not select a model. -/

namespace KIP126.HigherAlgebra.EnrichedTensor

open CategoryTheory MonoidalCategory Operad

universe u v

variable {M : Type u} [Category.{v} M]
  [EnrichedOrdinaryCategory TopCat.{v} M]

theorem arrow_point {X Y : M} (f : X ⟶ Y) : arrow (point f) = f := by
  apply (eHomEquiv TopCat.{v}).injective
  simp only [arrow, Equiv.apply_symm_apply]
  ext x
  cases x
  rfl

theorem point_arrow {X Y : M} (f : MappingSpace X Y) : point (arrow f) = f := by
  simp only [point, arrow, Equiv.apply_symm_apply]
  rfl

variable [MonoidalCategory M]

/-- The coloured finite tensor equations imply every endomorphism operad law
for the operations computed from those tensors. -/
theorem endomorphismLaws (P : Presentation M) (hP : TensorLaws P) (X : M) :
    EndomorphismLaws P X := by
  have ar_inj {A B : M} {f g : MappingSpace A B} (h : arrow f = arrow g) : f = g := by
    simpa only [point_arrow] using congrArg (fun k : A ⟶ B => point k) h
  have ar_rel {I J : FintypeCat.{0}} (e : I ≃ J) (f : P.Op X I) :
      arrow (P.relabel X e f) = (P.tensorRelabel e (fun _ => X)).inv ≫ arrow f := by
    apply (eHomEquiv TopCat.{v}).injective
    ext x
    cases x
    simp [arrow, Presentation.relabel, Iso.eHomCongr, eHomWhiskerRight,
      eHomEquiv_comp]
    rfl
  have ar_comp (I : FintypeCat.{0}) (J : I → FintypeCat.{0})
      (f : P.Op X I) (g : (i : I) → P.Op X (J i)) :
      arrow (P.compose X I J (f, g)) =
        (P.flatten I J (fun _ _ => X)).hom ≫
          P.map I (fun i => arrow (g i)) ≫ arrow f := by
    apply (eHomEquiv TopCat.{v}).injective
    ext x
    cases x
    simp [arrow, point, Presentation.compose, Presentation.map, eHomEquiv_comp,
      eHomWhiskerRight]
    rfl
  have ar_unit : arrow (P.unit X) = (P.oneIso (fun _ => X)).hom := arrow_point _
  constructor
  · intro I x
    apply ar_inj
    rw [ar_rel, ← cancel_epi (P.tensorRelabel (Equiv.refl I) (fun _ => X)).hom]
    rw [Iso.hom_inv_id_assoc, hP.relabel_id, Category.id_comp]
  · intro I J K e f x
    apply ar_inj
    rw [ar_rel, ar_rel, ar_rel,
      ← cancel_epi (P.tensorRelabel (e.trans f) (fun _ => X)).hom]
    rw [Iso.hom_inv_id_assoc, hP.relabel_comp]
    simp
  · intro I x
    apply ar_inj
    rw [ar_rel, ar_comp, ar_unit,
      ← cancel_epi (P.tensorRelabel (Arity.leftUnit I) (fun _ => X)).hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [hP.map_one, ← Category.assoc, hP.flatten_left_unit]
  · intro I x
    apply ar_inj
    rw [ar_rel, ar_comp,
      ← cancel_epi (P.tensorRelabel (Arity.rightUnit I) (fun _ => X)).hom]
    simp only [Iso.hom_inv_id_assoc, ar_unit]
    rw [← Category.assoc, hP.flatten_right_unit]
  · intro I J K x y z
    apply ar_inj
    rw [ar_rel, ar_comp, ar_comp, ar_comp,
      ← cancel_epi (P.tensorRelabel (Arity.assoc I J K) (fun _ => X)).hom]
    simp only [Iso.hom_inv_id_assoc]
    simp only [ar_comp]
    slice_lhs 2 3 =>
      rw [hP.flatten_naturality I J (fun i j => P.tensorObj (K i j) (fun _ => X))
        (fun _ _ => X) (fun i j => arrow (z i j))]
    slice_lhs 1 2 => rw [hP.flatten_assoc I J K (fun _ _ _ => X)]
    simp only [hP.map_comp, Category.assoc]
  · intro I I' e J x y
    apply ar_inj
    rw [ar_rel, ar_comp, ar_comp, ar_rel,
      ← cancel_epi (P.tensorRelabel (Arity.outer e J) (fun _ => X)).hom]
    simp only [Iso.hom_inv_id_assoc]
    slice_rhs 1 2 => rw [← hP.flatten_outer e J (fun _ _ => X)]
    slice_rhs 2 3 => rw [← hP.relabel_naturality]
    simp
  · intro I J J' e x y
    apply ar_inj
    rw [ar_rel, ar_comp, ar_comp,
      ← cancel_epi (P.tensorRelabel (Arity.inner I e) (fun _ => X)).hom]
    simp only [Iso.hom_inv_id_assoc, ar_rel]
    simp only [hP.map_comp, Category.assoc]
    slice_rhs 1 2 => rw [← hP.flatten_inner I J J' e (fun _ _ => X)]
    simp only [Category.assoc, ← hP.map_comp, Iso.hom_inv_id,
      hP.map_id, Category.id_comp]

end KIP126.HigherAlgebra.EnrichedTensor
