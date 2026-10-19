module

import KIP126.AdamsSynthetic.Quotients
import KIP126.AdamsSynthetic.SphereTensor
import KIP126.Literature.May
import KIP126.Literature.Standard

/- Review evidence only. These are candidate types, not implementations or
new assumptions installed in any production proof. -/

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v

namespace KIP126.InterfaceReview.MHLambdaTensor

variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- Ordinary suspension comparison induced by the same quotient/tensor
isomorphism and the right-tensor shift comparison used by May. -/
noncomputable def quotientSuspensionIso
    (rightShift : ∀ W : Syn, (tensorRight W).CommShift ℤ)
    (quotientIso : ∀ (X : Syn) (n : ℕ),
      X ⊗ XModLambdaN (𝟙_ Syn) n ≅ XModLambdaN X n)
    (X : Syn) (n : ℕ) :
    XModLambdaN (X⟦(1 : ℤ)⟧) n ≅ (XModLambdaN X n)⟦(1 : ℤ)⟧ := by
  letI := rightShift (XModLambdaN (𝟙_ Syn) n)
  exact (quotientIso (X⟦(1 : ℤ)⟧) n).symm ≪≫
    ((tensorRight (XModLambdaN (𝟙_ Syn) n)).commShiftIso (1 : ℤ)).app X ≪≫
    (shiftFunctor Syn (1 : ℤ)).mapIso (quotientIso X n)

/-- The actual left-tensor suspension comparison followed by the chosen
vertical quotient comparison. Naturality in X is a separate field below. -/
noncomputable def suspendedVerticalIso
    (leftShift : ∀ W : Syn, (tensorLeft W).CommShift ℤ)
    (verticalIso : ∀ (X : Syn) (i n : ℕ),
      X ⊗ (SyntheticCategory.biShift (0,-(i : ℤ))).obj
          (XModLambdaN (𝟙_ Syn) n) ≅
        (SyntheticCategory.biShift (0,-(i : ℤ))).obj (XModLambdaN X n))
    (X : Syn) (i n : ℕ) :
    X ⊗ ((SyntheticCategory.biShift (0,-(i : ℤ))).obj
        (XModLambdaN (𝟙_ Syn) n))⟦(1 : ℤ)⟧ ≅
      ((SyntheticCategory.biShift (0,-(i : ℤ))).obj
        (XModLambdaN X n))⟦(1 : ℤ)⟧ := by
  letI := leftShift X
  exact ((tensorLeft X).commShiftIso (1 : ℤ)).app
      ((SyntheticCategory.biShift (0,-(i : ℤ))).obj
        (XModLambdaN (𝟙_ Syn) n)) ≪≫
    (shiftFunctor Syn (1 : ℤ)).mapIso (verticalIso X i n)

/-- The directly sufficient structural comparison, parameterized by the
actual existing tensor shift choices. There is no MH conclusion or common
representative among the fields. -/
structure LambdaQuotientTensorCompatibility
    (Q : LambdaQuotientSystem Syn)
    (leftShift : ∀ W : Syn, (tensorLeft W).CommShift ℤ)
    (rightShift : ∀ W : Syn, (tensorRight W).CommShift ℤ) where
  quotientIso : ∀ (X : Syn) (n : ℕ),
    X ⊗ XModLambdaN (𝟙_ Syn) n ≅ XModLambdaN X n
  verticalIso : ∀ (X : Syn) (i n : ℕ),
    X ⊗ (SyntheticCategory.biShift (0,-(i : ℤ))).obj
        (XModLambdaN (𝟙_ Syn) n) ≅
      (SyntheticCategory.biShift (0,-(i : ℤ))).obj (XModLambdaN X n)
  quotient_natural : ∀ {X Y : Syn} (f : X ⟶ Y) (n : ℕ),
    (f ▷ XModLambdaN (𝟙_ Syn) n) ≫ (quotientIso Y n).hom =
      (quotientIso X n).hom ≫ XModLambdaN.map f n
  vertical_natural : ∀ {X Y : Syn} (f : X ⟶ Y) (i n : ℕ),
    (f ▷ (SyntheticCategory.biShift (0,-(i : ℤ))).obj
        (XModLambdaN (𝟙_ Syn) n)) ≫ (verticalIso Y i n).hom =
      (verticalIso X i n).hom ≫
        (SyntheticCategory.biShift (0,-(i : ℤ))).map (XModLambdaN.map f n)
  suspended_vertical_natural : ∀ {X Y : Syn} (f : X ⟶ Y) (i n : ℕ),
    (f ▷ ((SyntheticCategory.biShift (0,-(i : ℤ))).obj
        (XModLambdaN (𝟙_ Syn) n))⟦(1 : ℤ)⟧) ≫
          (suspendedVerticalIso leftShift verticalIso Y i n).hom =
      (suspendedVerticalIso leftShift verticalIso X i n).hom ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0,-(i : ℤ))).map (XModLambdaN.map f n))
  quotient_incl : ∀ (X : Syn) (n : ℕ),
    (X ◁ XModLambdaN.incl (𝟙_ Syn) n) ≫ (quotientIso X n).hom =
      (ρ_ X).hom ≫ XModLambdaN.incl X n
  lambda_triangle : ∀ (X : Syn) {i j : ℕ} (hi : 0 < i) (hij : i < j),
    (X ◁ ((Q.tower (𝟙_ Syn)).triangle hi hij).lambdaMap) ≫
        (quotientIso X j).hom =
      (verticalIso X i (j-i)).hom ≫ ((Q.tower X).triangle hi hij).lambdaMap
  rho_triangle : ∀ (X : Syn) {i j : ℕ} (hi : 0 < i) (hij : i < j),
    (X ◁ ((Q.tower (𝟙_ Syn)).triangle hi hij).rho) ≫
        (quotientIso X i).hom =
      (quotientIso X j).hom ≫ ((Q.tower X).triangle hi hij).rho
  delta_triangle : ∀ (X : Syn) {i j : ℕ} (hi : 0 < i) (hij : i < j),
    letI := leftShift X
    (X ◁ ((Q.tower (𝟙_ Syn)).triangle hi hij).delta) ≫
        ((tensorLeft X).commShiftIso (1 : ℤ)).hom.app
          ((SyntheticCategory.biShift (0,-(i : ℤ))).obj
            (XModLambdaN (𝟙_ Syn) (j-i))) ≫
        (shiftFunctor Syn (1 : ℤ)).map (verticalIso X i (j-i)).hom =
      (quotientIso X i).hom ≫ ((Q.tower X).triangle hi hij).delta
  suspension_incl : ∀ (X : Syn) (n : ℕ),
    XModLambdaN.incl (X⟦(1 : ℤ)⟧) n ≫
        (quotientSuspensionIso rightShift quotientIso X n).hom =
      (shiftFunctor Syn (1 : ℤ)).map (XModLambdaN.incl X n)

/-- A separate lower-level diagnostic condition on the existing chosen
sphere/tensor comparison, rather than a replacement comparison. This is a
possible producer-side route to the preceding record, not an extra MH
hypothesis. -/
def ExistingSphereTensorPreservesLambda : Prop :=
  ∀ (n : ℕ) (X : Syn),
    (biShift_eq_tensor_Smn 0 (-(n : ℤ)) X).hom ≫
        (lambdaPow n (𝟙_ Syn) ▷ X) ≫ (λ_ X).hom = lambdaPow n X

/-- The stronger May lifting input needed for arbitrary bigraded sphere
domains. The existing pushpull maps, squares, signs, and shift choices are
retained; only the quantified domain of the lift is enlarged. -/
def UniversalMayLift
    (B : KIP126.Literature.Route.MayContext Syn)
    (T U : HoCofiberSequence (C := Syn))
    (P : KIP126.Literature.Route.MayPushpullData Syn B T U) : Prop :=
  ∀ (W : Syn) (a : W ⟶ T.X ⊗ U.Z) (b : W ⟶ T.Y ⊗ U.Y),
    a ≫ (T.f ▷ U.Z) = b ≫ (T.Y ◁ U.g) →
    ∃ z : W ⟶ P.vertex, z ≫ P.j1 = a ∧ z ≫ P.j2 = b

/- Candidate fixed producer theorem types. These are type checks, with no
declaration or proof of either existence statement. -/
#check LambdaQuotientTensorCompatibility
#check quotientSuspensionIso
#check ExistingSphereTensorPreservesLambda
#check UniversalMayLift

/- Exact candidate producer types on the fixed project objects. `Type`
and `Prop` below only name the requested type, and assert no inhabitant. -/
def FixedCompatibilityType : Type 1 :=
  LambdaQuotientTensorCompatibility.{1,0}
    KIP126.AdamsSynthetic.Standard.quotients
    KIP126.Literature.Standard.may_leftShift
    KIP126.Literature.Standard.may_rightShift

def FixedUniversalMayType : Prop :=
  ∀ (T U : HoCofiberSequence (C := KIP126.AdamsSynthetic.Standard.SyntheticSpectrum)),
    ∃ P : KIP126.Literature.Route.MayPushpullData
        KIP126.AdamsSynthetic.Standard.SyntheticSpectrum
        KIP126.Literature.Standard.mayData T U,
      UniversalMayLift KIP126.Literature.Standard.mayData T U P

#check FixedCompatibilityType
#check FixedUniversalMayType

end KIP126.InterfaceReview.MHLambdaTensor

/- Conditional transport research. This is not installed in a production
interface and introduces no inhabitant of the structural input types. -/
namespace KIP126.InterfaceReview.MHLambdaTensor
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
noncomputable section
universe uT vT
variable {Syn : Type uT} [SyntheticCategory.{uT,vT} Syn]
  [HasFunctorialCofiber (C := Syn)]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private def transportRotate (N : HoCofiberSequence (C := Syn)) :
    HoCofiberSequence (C := Syn) where
  X := N.Y
  Y := N.Z
  Z := N.X⟦(1:ℤ)⟧
  f := N.g
  g := N.h
  h := -(shiftFunctor Syn (1:ℤ)).map N.f
  distinguished := rot_of_distTriang _ N.distinguished

private def transportUnitRotate (Q : LambdaQuotientSystem Syn)
    {i j : ℕ} (hi : 0 < i) (hij : i < j) : HoCofiberSequence (C := Syn) :=
  let L := (Q.tower (𝟙_ Syn)).triangle hi hij
  { X := XModLambdaN (𝟙_ Syn) j
    Y := XModLambdaN (𝟙_ Syn) i
    Z := ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN (𝟙_ Syn) (j-i)))⟦(1:ℤ)⟧
    f := L.rho
    g := L.delta
    h := -(shiftFunctor Syn (1:ℤ)).map L.lambdaMap
    distinguished := rot_of_distTriang _ L.distinguished }

private abbrev verticalSuspensionIso
    (M : KIP126.Literature.Route.MayContext Syn)
    (Q : LambdaQuotientSystem Syn)
    (C : LambdaQuotientTensorCompatibility Q M.leftShift M.rightShift)
    (X : Syn) (i n : ℕ) :=
  suspendedVerticalIso M.leftShift C.verticalIso X i n

/-- Structural conditional lemma only: no MH conclusion is among the
inputs, and all quotient maps in the conclusion are the prescribed maps. -/
private theorem finite_may_fixed_transport
    (M : KIP126.Literature.Route.MayContext Syn)
    (Q : LambdaQuotientSystem Syn)
    (C : LambdaQuotientTensorCompatibility Q M.leftShift M.rightShift)
    (hMay : ∀ T U : HoCofiberSequence (C := Syn),
      ∃ P : KIP126.Literature.Route.MayPushpullData Syn M T U,
        UniversalMayLift M T U P)
    (N : HoCofiberSequence (C := Syn))
    {i j : ℕ} (hi : 0 < i) (hij : i < j) (W : Syn)
    (a : W ⟶ XModLambdaN N.Z i)
    (b : W ⟶ (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN N.Y (j-i)))⟦(1:ℤ)⟧))
    (hab : a ≫ ((Q.tower N.Z).triangle hi hij).delta =
      b ≫ (shiftFunctor Syn (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.map N.g (j-i)))) :
    ∃ c : W ⟶ XModLambdaN (N.X⟦(1:ℤ)⟧) j,
      c ≫ (Q.tower (N.X⟦(1:ℤ)⟧)).rho i j hij.le =
        a ≫ XModLambdaN.map N.h i ∧
      c ≫ XModLambdaN.map ((shiftFunctor Syn (1:ℤ)).map N.f) j ≫
          (quotientSuspensionIso M.rightShift C.quotientIso N.Y j).hom =
        -(b ≫ (shiftFunctor Syn (1:ℤ)).map
          ((Q.tower N.Y).triangle hi hij).lambdaMap) := by
  letI := M.leftShift
  letI := M.rightShift
  letI := M.leftExact
  letI := M.rightExact
  let F := SyntheticCategory.biShift (Syn := Syn) (0,-(i:ℤ))
  let L := (Q.tower (𝟙_ Syn)).triangle hi hij
  let U := transportUnitRotate Q hi hij
  let bt : W ⟶ N.Y ⊗ U.Z :=
    b ≫ (verticalSuspensionIso M Q C N.Y i (j-i)).inv
  let aTensor : W ⟶ N.Z ⊗ U.Y := a ≫ (C.quotientIso N.Z i).inv
  have hbt : bt ≫ (N.g ▷ U.Z) = aTensor ≫ (N.Z ◁ U.g) := by
    apply (cancel_mono (verticalSuspensionIso M Q C N.Z i (j-i)).hom).mp
    dsimp only [bt,aTensor,U,transportUnitRotate]
    rw [Category.assoc,C.suspended_vertical_natural N.g i (j-i)]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
    have hδ := C.delta_triangle N.Z hi hij
    change (N.Z ◁ L.delta) ≫ (verticalSuspensionIso M Q C N.Z i (j-i)).hom =
      (C.quotientIso N.Z i).hom ≫ ((Q.tower N.Z).triangle hi hij).delta at hδ
    rw [hδ]
    simp only [Iso.inv_hom_id_assoc]
    exact hab.symm
  obtain ⟨P,hP⟩ := hMay (transportRotate N) U
  obtain ⟨v,hvb,hva⟩ := hP W bt aTensor hbt
  let ct : W ⟶ N.X⟦(1:ℤ)⟧ ⊗ U.X := v ≫ P.j3
  have hfirst : ct ≫ (N.X⟦(1:ℤ)⟧ ◁ L.rho) = aTensor ≫ (N.h ▷ U.Y) := by
    change (v ≫ P.j3) ≫ ((transportRotate N).Z ◁ U.f) =
      aTensor ≫ ((transportRotate N).g ▷ U.Y)
    rw [←hva]
    simp only [Category.assoc,P.other_square]
  have hsecond : ct ≫ ((shiftFunctor Syn (1:ℤ)).map N.f ▷ U.X) ≫
        ((tensorRight U.X).commShiftIso (1:ℤ)).hom.app N.Y =
      -(bt ≫ (N.Y ◁ (shiftFunctor Syn (1:ℤ)).map L.lambdaMap) ≫
        ((tensorLeft N.Y).commShiftIso (1:ℤ)).hom.app U.X) := by
    have hb := congrArg (fun z => v ≫ z) P.boundary
    rw [Preadditive.comp_neg,←Category.assoc,hvb] at hb
    dsimp only [HoCofiberSequence.map,transportRotate,transportUnitRotate,U] at hb
    simp only [Functor.map_neg,Preadditive.neg_comp,Preadditive.comp_neg,neg_neg] at hb
    simpa [ct,Category.assoc,U,transportUnitRotate,L] using hb.symm
  refine ⟨ct ≫ (C.quotientIso (N.X⟦(1:ℤ)⟧) j).hom,?_,?_⟩
  · rw [Category.assoc,←(Q.tower _).triangle_rho hi hij,
      ←C.rho_triangle _ hi hij,←Category.assoc,hfirst,Category.assoc,
      ]
    erw [C.quotient_natural]
    simp only [aTensor,Category.assoc,Iso.inv_hom_id_assoc]
  · have hleft :
        bt ≫ (N.Y ◁ (shiftFunctor Syn (1:ℤ)).map L.lambdaMap) ≫
          ((tensorLeft N.Y).commShiftIso (1:ℤ)).hom.app U.X ≫
          (shiftFunctor Syn (1:ℤ)).map (C.quotientIso N.Y j).hom =
        b ≫ (shiftFunctor Syn (1:ℤ)).map
          ((Q.tower N.Y).triangle hi hij).lambdaMap := by
      have hn := ((tensorLeft N.Y).commShiftIso (1:ℤ)).hom.naturality L.lambdaMap
      change (N.Y ◁ (shiftFunctor Syn (1:ℤ)).map L.lambdaMap) ≫
          ((tensorLeft N.Y).commShiftIso (1:ℤ)).hom.app U.X =
        ((tensorLeft N.Y).commShiftIso (1:ℤ)).hom.app (F.obj (XModLambdaN (𝟙_ Syn) (j-i))) ≫
          (shiftFunctor Syn (1:ℤ)).map (N.Y ◁ L.lambdaMap) at hn
      calc
        _ = bt ≫ ((tensorLeft N.Y).commShiftIso (1:ℤ)).hom.app
              (F.obj (XModLambdaN (𝟙_ Syn) (j-i))) ≫
              (shiftFunctor Syn (1:ℤ)).map (N.Y ◁ L.lambdaMap) ≫
              (shiftFunctor Syn (1:ℤ)).map (C.quotientIso N.Y j).hom := by
          simpa only [Category.assoc] using
            congrArg (fun z => bt ≫ z ≫
              (shiftFunctor Syn (1:ℤ)).map (C.quotientIso N.Y j).hom) hn
        _ = bt ≫ ((tensorLeft N.Y).commShiftIso (1:ℤ)).hom.app
              (F.obj (XModLambdaN (𝟙_ Syn) (j-i))) ≫
              (shiftFunctor Syn (1:ℤ)).map (C.verticalIso N.Y i (j-i)).hom ≫
              (shiftFunctor Syn (1:ℤ)).map ((Q.tower N.Y).triangle hi hij).lambdaMap := by
          rw [←Functor.map_comp,C.lambda_triangle,Functor.map_comp]
        _ = _ := by
          rw [←Category.assoc
            (((tensorLeft N.Y).commShiftIso (1:ℤ)).hom.app
              (F.obj (XModLambdaN (𝟙_ Syn) (j-i))))
            ((shiftFunctor Syn (1:ℤ)).map (C.verticalIso N.Y i (j-i)).hom)
            ((shiftFunctor Syn (1:ℤ)).map ((Q.tower N.Y).triangle hi hij).lambdaMap)]
          change bt ≫ (verticalSuspensionIso M Q C N.Y i (j-i)).hom ≫ _ = _
          simp only [bt,Category.assoc,Iso.inv_hom_id_assoc]
    have hright :
        (C.quotientIso (N.X⟦(1:ℤ)⟧) j).hom ≫
          XModLambdaN.map ((shiftFunctor Syn (1:ℤ)).map N.f) j ≫
          (quotientSuspensionIso M.rightShift C.quotientIso N.Y j).hom =
        ((shiftFunctor Syn (1:ℤ)).map N.f ▷ U.X) ≫
          ((tensorRight U.X).commShiftIso (1:ℤ)).hom.app N.Y ≫
          (shiftFunctor Syn (1:ℤ)).map (C.quotientIso N.Y j).hom := by
      rw [←Category.assoc,←C.quotient_natural]
      simp only [quotientSuspensionIso,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,
        Functor.mapIso_hom,Category.assoc,Iso.hom_inv_id_assoc]
      rfl
    simp only [Category.assoc]
    erw [hright]
    have hs := congrArg (fun z => z ≫
      (shiftFunctor Syn (1:ℤ)).map (C.quotientIso N.Y j).hom) hsecond
    simpa only [Category.assoc,Preadditive.neg_comp,hleft] using hs

end
end KIP126.InterfaceReview.MHLambdaTensor

#print axioms KIP126.InterfaceReview.MHLambdaTensor.finite_may_fixed_transport
