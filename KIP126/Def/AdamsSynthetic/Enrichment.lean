module

public import KIP126.Def.AdamsSynthetic.Coherence
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Polynomial.Basic

@[expose] section
set_option backward.isDefEq.respectTransparency false

/-! The deformation parameter has weight -1.  Accordingly the enrichment
lives on the total weight-graded Hom, with degree-zero morphisms the actual
underlying category.  A polynomial action on each ungraded Hom separately
would erase that degree and is not the contract supplied here. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.Synthetic.Context
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]

public abbrev WeightHom (X Y : Syn) (w : ℤ) :=
  (SyntheticCategory.biShift (0,w)).obj X ⟶ Y

public abbrev TotalWeightHom (X Y : Syn) := DirectSum ℤ (WeightHom X Y)

/-- Inclusion of an actual morphism of specified weight into total Hom. -/
public noncomputable def weightHomInclusion {X Y : Syn} (w : ℤ) :
    WeightHom X Y w →+ TotalWeightHom X Y :=
  DirectSum.of (WeightHom X Y) w

/-- The actual composition, through the already selected suspension comparison. -/
public noncomputable def weightHomComp {X Y Z : Syn} {a b : ℤ}
    (f : WeightHom X Y a) (g : WeightHom Y Z b) : WeightHom X Z (a+b) :=
  (biShiftAddIso (0,a) (0,b) (0,a+b) (by ext <;> simp)).inv.app X ≫
    (SyntheticCategory.biShift (0,b)).map f ≫ g

/-- λ acts by the actual deformation map and lowers the source weight by one. -/
public noncomputable def weightHomLambda {X Y : Syn} {w : ℤ}
    (f : WeightHom X Y w) : WeightHom X Y (w-1) :=
  (biShiftAddIso (0,w) (0,-1) (0,w-1) (by ext <;> simp [sub_eq_add_neg])).inv.app X ≫
    SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,w)).obj X) ≫ f

/-- An enrichment on the total actual graded Hom. Its scalar action is tied
to λ, its composition to actual shifted composition, and its units to the
specified zero-shift comparison. No global enriched category is postulated. -/
public structure GradedLambdaEnrichment (Syn : Type u) [SyntheticCategory.{u,v} Syn] where
  coherence : BiShiftCoherence Syn
  shiftAdditive : ∀ p : ℤ × ℤ, (SyntheticCategory.biShift p : Syn ⥤ Syn).Additive
  module : ∀ X Y : Syn, Module (Polynomial ℤ) (TotalWeightHom X Y)
  lambda_smul : ∀ (X Y : Syn) (w : ℤ) (f : WeightHom X Y w),
    letI := module X Y
    (Polynomial.X : Polynomial ℤ) • weightHomInclusion w f =
      weightHomInclusion (w-1) (weightHomLambda f)
  compose : ∀ X Y Z : Syn,
    letI := module X Y
    letI := module Y Z
    letI := module X Z
    TotalWeightHom Y Z →ₗ[Polynomial ℤ]
      TotalWeightHom X Y →ₗ[Polynomial ℤ] TotalWeightHom X Z
  compose_homogeneous : ∀ (X Y Z : Syn) (a b : ℤ)
      (f : WeightHom X Y a) (g : WeightHom Y Z b),
    compose X Y Z (weightHomInclusion b g) (weightHomInclusion a f) =
      weightHomInclusion (a+b) (weightHomComp f g)

namespace GradedLambdaEnrichment
variable (E : GradedLambdaEnrichment Syn)

/-- Ordinary morphisms are included using the chosen degree-zero identity. -/
public noncomputable def underlyingHom {X Y : Syn} (f : X ⟶ Y) : TotalWeightHom X Y :=
  weightHomInclusion 0 (SyntheticCategory.biShift_zero.hom.app X ≫ f)

/-- Scalar bilinearity is a consequence of the supplied linear composition. -/
public theorem compose_lambda_right (X Y Z : Syn)
    (g : TotalWeightHom Y Z) (f : TotalWeightHom X Y) :
    letI := E.module X Y
    letI := E.module Y Z
    letI := E.module X Z
    E.compose X Y Z g ((Polynomial.X : Polynomial ℤ) • f) =
      (Polynomial.X : Polynomial ℤ) • E.compose X Y Z g f := by
  letI := E.module X Y
  letI := E.module Y Z
  letI := E.module X Z
  exact (E.compose X Y Z g).map_smul _ _

public theorem compose_lambda_left (X Y Z : Syn)
    (g : TotalWeightHom Y Z) (f : TotalWeightHom X Y) :
    letI := E.module X Y
    letI := E.module Y Z
    letI := E.module X Z
    E.compose X Y Z ((Polynomial.X : Polynomial ℤ) • g) f =
      (Polynomial.X : Polynomial ℤ) • E.compose X Y Z g f := by
  letI := E.module X Y
  letI := E.module Y Z
  letI := E.module X Z
  exact LinearMap.congr_fun ((E.compose X Y Z).map_smul (Polynomial.X : Polynomial ℤ) g) f
end GradedLambdaEnrichment
end KIP126.AdamsSynthetic

namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.Synthetic.Context
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]

private theorem homogeneous_regrade {X Y Z : Syn} (a b m : ℤ) (hab : a+b=m)
    (f : WeightHom X Y a) (g : WeightHom Y Z b) :
    weightHomInclusion (a+b) (weightHomComp f g) =
      weightHomInclusion m ((biShiftAddIso (0,a) (0,b) (0,m)
        (by ext <;> simp [hab])).inv.app X ≫ (SyntheticCategory.biShift (0,b)).map f ≫ g) := by
  subst m
  rfl

private theorem homogeneous_left_unit (coh : BiShiftCoherence Syn)
    {X Y : Syn} (a : ℤ) (f : WeightHom X Y a) :
    weightHomInclusion (a+0)
      (weightHomComp f (SyntheticCategory.biShift_zero.hom.app Y)) =
        weightHomInclusion a f := by
  rw [homogeneous_regrade a 0 a (add_zero a)]
  apply congrArg (weightHomInclusion a)
  rw [SyntheticCategory.biShift_zero.hom.naturality]
  rw [← coh.right_unit (0,a) X]
  exact Iso.inv_hom_id_app_assoc (biShiftAddIso (0,a) 0 (0,a) (add_zero _)) X f

private theorem homogeneous_right_unit (coh : BiShiftCoherence Syn)
    {X Y : Syn} (a : ℤ) (f : WeightHom X Y a) :
    weightHomInclusion (0+a)
      (weightHomComp (SyntheticCategory.biShift_zero.hom.app X) f) =
        weightHomInclusion a f := by
  rw [homogeneous_regrade 0 a a (zero_add a)]
  apply congrArg (weightHomInclusion a)
  rw [← coh.left_unit (0,a) X]
  exact Iso.inv_hom_id_app_assoc (biShiftAddIso 0 (0,a) (0,a) (zero_add _)) X f

private theorem homogeneous_assoc (coh : BiShiftCoherence Syn)
    {W X Y Z : Syn} (a b c : ℤ)
    (f : WeightHom W X a) (g : WeightHom X Y b) (h : WeightHom Y Z c) :
    weightHomInclusion ((a+b)+c) (weightHomComp (weightHomComp f g) h) =
      weightHomInclusion (a+(b+c)) (weightHomComp f (weightHomComp g h)) := by
  rw [homogeneous_regrade (a+b) c (a+(b+c)) (add_assoc a b c)]
  apply congrArg (weightHomInclusion (a+(b+c)))
  let eab := biShiftAddIso (Syn := Syn) (0,a) (0,b) (0,a+b) (by ext <;> simp)
  let ebc := biShiftAddIso (Syn := Syn) (0,b) (0,c) (0,b+c) (by ext <;> simp)
  let eabc := biShiftAddIso (Syn := Syn) (0,a+b) (0,c) (0,a+(b+c)) (by ext <;> simp [add_assoc])
  let eabc' := biShiftAddIso (Syn := Syn) (0,a) (0,b+c) (0,a+(b+c)) (by ext <;> simp)
  have hi : ((SyntheticCategory.biShift (0,c)).mapIso (eab.app W) ≪≫ eabc.app W) =
      (ebc.app ((SyntheticCategory.biShift (0,a)).obj W) ≪≫ eabc'.app W) := by
    apply Iso.ext
    exact coh.associativity (0,a) (0,b) (0,c) (0,a+b) (0,b+c) (0,a+(b+c))
      (by ext <;> simp) (by ext <;> simp)
      (by ext <;> simp [add_assoc]) (by ext <;> simp) W
  have hinv : eabc.inv.app W ≫ (SyntheticCategory.biShift (0,c)).map (eab.inv.app W) =
      eabc'.inv.app W ≫ ebc.inv.app ((SyntheticCategory.biShift (0,a)).obj W) :=
    congrArg Iso.inv hi
  change eabc.inv.app W ≫ (SyntheticCategory.biShift (0,c)).map
      (eab.inv.app W ≫ (SyntheticCategory.biShift (0,b)).map f ≫ g) ≫ h =
    eabc'.inv.app W ≫ (SyntheticCategory.biShift (0,b+c)).map f ≫
      ebc.inv.app X ≫ (SyntheticCategory.biShift (0,c)).map g ≫ h
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (eabc.inv.app W), hinv]
  rw [Category.assoc]
  have hn : (SyntheticCategory.biShift (0,b+c)).map f ≫ ebc.inv.app X =
      ebc.inv.app ((SyntheticCategory.biShift (0,a)).obj W) ≫
        (SyntheticCategory.biShift (0,c)).map ((SyntheticCategory.biShift (0,b)).map f) :=
    ebc.inv.naturality f
  rw [← Category.assoc (ebc.inv.app ((SyntheticCategory.biShift (0,a)).obj W)), ← hn]
  simp only [Category.assoc]
namespace GradedLambdaEnrichment
variable (E : GradedLambdaEnrichment Syn)

/-- Units on arbitrary total Hom elements follow from the actual homogeneous
composition and the supplied suspension unit coherence. -/
public theorem left_unit (X Y : Syn) (f : TotalWeightHom X Y) :
    E.compose X Y Y (weightHomInclusion 0 (SyntheticCategory.biShift_zero.hom.app Y)) f = f := by
  letI := E.module X Y
  letI := E.module Y Y
  induction f using DirectSum.induction_on with
  | zero => exact map_zero _
  | of a f =>
    exact (E.compose_homogeneous X Y Y a 0 f _).trans (homogeneous_left_unit E.coherence a f)
  | add x y hx hy => simp only [map_add, hx, hy]

public theorem right_unit (X Y : Syn) (f : TotalWeightHom X Y) :
    E.compose X X Y f (weightHomInclusion 0 (SyntheticCategory.biShift_zero.hom.app X)) = f := by
  letI := E.module X X
  letI := E.module X Y
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | of a f =>
    exact (E.compose_homogeneous X X Y 0 a _ f).trans (homogeneous_right_unit E.coherence a f)
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Associativity is derived by additive induction from actual shifted-map
composition and the same suspension associativity constraint. -/
public theorem assoc (W X Y Z : Syn) (f : TotalWeightHom W X)
    (g : TotalWeightHom X Y) (h : TotalWeightHom Y Z) :
    E.compose W Y Z h (E.compose W X Y g f) =
      E.compose W X Z (E.compose X Y Z h g) f := by
  letI := E.module W X
  letI := E.module X Y
  letI := E.module Y Z
  letI := E.module W Y
  letI := E.module X Z
  letI := E.module W Z
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f f' hf hf' => simp only [map_add, hf, hf']
  | of a f =>
    induction g using DirectSum.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add g g' hg hg' => simp only [map_add, LinearMap.add_apply, hg, hg']
    | of b g =>
      induction h using DirectSum.induction_on with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add h h' hh hh' => simp only [map_add, LinearMap.add_apply, hh, hh']
      | of c h =>
        change E.compose W Y Z (weightHomInclusion c h)
          (E.compose W X Y (weightHomInclusion b g) (weightHomInclusion a f)) =
          E.compose W X Z (E.compose X Y Z (weightHomInclusion c h) (weightHomInclusion b g))
            (weightHomInclusion a f)
        rw [E.compose_homogeneous, E.compose_homogeneous,
          E.compose_homogeneous, E.compose_homogeneous]
        exact homogeneous_assoc E.coherence a b c f g h
end GradedLambdaEnrichment
end KIP126.AdamsSynthetic
