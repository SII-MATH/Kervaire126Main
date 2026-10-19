module

import all KIP126.ProofTools.GeneralizedMahowald.FiniteMay3x3
import all KIP126.ProofTools.GeneralizedMahowald.FiniteComparison
import KIP126.Literature.Standard.FiniteQuotientNormalized

/-! Signed finite May representatives from the proved fixed quotient row.
The Literature theorem supplies its inclusion-compatible suspension comparison.
All maps in the conclusion are the existing selected finite quotient maps. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- The existing normalized no-return statement in the raw objects of the
normalized triangle. The chosen zero bigraded shift is transported explicitly.
No spherewise equality is promoted to equality of arbitrary morphisms. -/
private theorem normalized_triangle_relative_no_return
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (m w : ℤ)
    (b : BiHom m w (((SyntheticCategory.biShift (0,-(A:ℤ))).obj
      (XModLambdaN (normalizedTriangle model T he).obj₂ B))⟦(1:ℤ)⟧))
    (z : (((SyntheticCategory.biShift (0,-(A:ℤ))).obj
      (XModLambdaN (normalizedTriangle model T he).obj₂ B))⟦(1:ℤ)⟧) ⟶
      XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) A) :
    b ≫ z = 0 := by
  let ef : ℤ := normalizedExponent model.classicalTower T.f
  let Xν := model.nu.functor.obj (T.X.obj model.auxiliary)
  let Yν := model.nu.functor.obj (T.Y.obj model.auxiliary)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(A:ℤ))
  let eY : Yν ≅ (SyntheticCategory.biShift (0,0)).obj Yν :=
    (SyntheticCategory.biShift_zero (Syn:=SyntheticSpectrum)).symm.app Yν
  let eB := (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
    (F.mapIso ((model.quotients.functoriality.functor B).mapIso eY))
  let eC : ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) ≅
      (SyntheticCategory.biShift (1,ef+0)).obj Xν :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app
      ((SyntheticCategory.biShift (0,ef)).obj Xν) ≪≫
    (biShiftAddIso (0,ef) (1,0) (1,ef+0) (by ext <;> simp)).app Xν
  have hz := normalized_finite_no_return T.X T.Y _ ef 0 (Int.natCast_nonneg _)
    eC B A hB hA m w (b ≫ eB.hom) (eB.inv ≫ z)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hz

/-- The same raw finite representative has both signed prescribed images.
The fixed Literature row supplies the distinguished triangle; no common-lift
conclusion is supplied as an input. The output uses an arbitrary inclusion-compatible
suspension comparison, by spherewise comparison independence. -/
private theorem finite_may_at_normalized_triangle
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (m w : ℤ)
    (eyN : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (A+B) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (A+B))⟦(1:ℤ)⟧)
    (heyN : XModLambdaN.incl _ (A+B) ≫ eyN.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (XModLambdaN.incl (normalizedTriangle model T he).obj₂ (A+B)))
    (a : BiHom m w (XModLambdaN (normalizedTriangle model T he).obj₃ A))
    (b : BiHom m w (((SyntheticCategory.biShift (0,-(A:ℤ))).obj
      (XModLambdaN (normalizedTriangle model T he).obj₂ ((A+B)-A)))⟦(1:ℤ)⟧))
    (hab : a ≫ ((model.quotients.tower (normalizedTriangle model T he).obj₃).triangle
        hA (show A < A+B by omega)).delta =
      b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(A:ℤ))).map
          (XModLambdaN.map (normalizedTriangle model T he).mor₂ ((A+B)-A)))) :
    ∃ c : BiHom m w (XModLambdaN ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧) (A+B)),
      c ≫ (model.quotients.tower ((normalizedTriangle model T he).obj₁⟦(1:ℤ)⟧)).rho
          A (A+B) (by omega) = a ≫ XModLambdaN.map (normalizedTriangle model T he).mor₃ A ∧
      c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (normalizedTriangle model T he).mor₁) (A+B) ≫ eyN.hom =
        -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((model.quotients.tower (normalizedTriangle model T he).obj₂).triangle
            hA (show A < A+B by omega)).lambdaMap) := by
  letI := model.exactness.syntheticTriangulated
  let V := normalizedTriangle model T he
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(A:ℤ))
  let LZ := (model.quotients.tower V.obj₃).triangle hA (show A < A+B by omega)
  let LY := (model.quotients.tower V.obj₂).triangle hA (show A < A+B by omega)
  obtain ⟨ey₀, hey₀, hRow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row T he hT (A+B) (by omega)
  have hSquare : LY.lambdaMap ≫ XModLambdaN.map V.mor₂ (A+B) =
      F.map (XModLambdaN.map V.mor₂ ((A+B)-A)) ≫ LZ.lambdaMap :=
    ((model.quotients.natural V.mor₂).lambda_naturality hA (show A < A+B by omega)).symm
  have hRho : XModLambdaN.map V.mor₃ (A+B) ≫
      (model.quotients.tower (V.obj₁⟦(1:ℤ)⟧)).rho A (A+B) (by omega) =
        LZ.rho ≫ XModLambdaN.map V.mor₃ A := by
    rw [(model.quotients.tower V.obj₃).triangle_rho hA (show A < A+B by omega)]
    exact ((model.quotients.natural V.mor₃).rho_naturality (show A ≤ A+B by omega)).symm
  obtain ⟨c, hc, hck⟩ := ThreeByThree.common_lift_of_no_return
    (F.map (XModLambdaN.map V.mor₂ ((A+B)-A))) LZ.lambdaMap LY.lambdaMap
    (XModLambdaN.map V.mor₂ (A+B)) (XModLambdaN.map V.mor₃ (A+B))
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (A+B) ≫
      ey₀.hom)) LZ.rho LZ.delta (XModLambdaN.map V.mor₃ A)
    ((model.quotients.tower (V.obj₁⟦(1:ℤ)⟧)).rho A (A+B) (by omega))
    LZ.distinguished hRow hSquare hRho
    (fun b z => normalized_triangle_relative_no_return T he A ((A+B)-A) hA
      (by omega) m w b z) a b hab
  refine ⟨c, hc, ?_⟩
  have hSigned : c ≫ XModLambdaN.map
      ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (A+B) ≫ ey₀.hom =
        -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map LY.lambdaMap) := by
    apply neg_eq_iff_eq_neg.mp
    simpa only [Preadditive.comp_neg, Category.assoc] using hck
  have hCompare := finite_nu_suspension_comparisons_equal_on_spheres T.Y (A+B) (by omega)
    ey₀ eyN hey₀ heyN m w
    (c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (A+B))
  have hCompare' : c ≫ XModLambdaN.map
      ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (A+B) ≫ ey₀.hom =
      c ≫ XModLambdaN.map
        ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (A+B) ≫ eyN.hom := by
    simpa only [Category.assoc] using hCompare
  exact hCompare'.symm.trans hSigned

/-- Transport the entire common-lift function through one short quotient
length equality. This avoids separate transports of its dependent inputs
and the two image equations. -/
private theorem finite_may_transport_short_length
    {Y Z Cg S : SyntheticSpectrum} (F : SyntheticSpectrum ⥤ SyntheticSpectrum)
    (A N D E : ℕ) (hDE : D=E) (g : Y ⟶ Z)
    (rho : XModLambdaN Cg N ⟶ XModLambdaN Cg A)
    (h : XModLambdaN Z A ⟶ XModLambdaN Cg A)
    (f : XModLambdaN Cg N ⟶ (XModLambdaN Y N)⟦(1:ℤ)⟧)
    (delta : XModLambdaN Z A ⟶ (F.obj (XModLambdaN Z D))⟦(1:ℤ)⟧)
    (lambda : F.obj (XModLambdaN Y D) ⟶ XModLambdaN Y N)
    (H : ∀ (a : S ⟶ XModLambdaN Z A)
      (b : S ⟶ (F.obj (XModLambdaN Y D))⟦(1:ℤ)⟧),
      a ≫ delta = b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (F.map (XModLambdaN.map g D)) →
      ∃ c : S ⟶ XModLambdaN Cg N,
        c ≫ rho = a ≫ h ∧ c ≫ f = -(b ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map lambda)) :
    let deltaE : XModLambdaN Z A ⟶ (F.obj (XModLambdaN Z E))⟦(1:ℤ)⟧ :=
      Eq.mp (congrArg (fun d => XModLambdaN Z A ⟶
        (F.obj (XModLambdaN Z d))⟦(1:ℤ)⟧) hDE) delta
    let lambdaE : F.obj (XModLambdaN Y E) ⟶ XModLambdaN Y N :=
      Eq.mp (congrArg (fun d => F.obj (XModLambdaN Y d) ⟶ XModLambdaN Y N) hDE) lambda
    ∀ (a : S ⟶ XModLambdaN Z A)
      (b : S ⟶ (F.obj (XModLambdaN Y E))⟦(1:ℤ)⟧),
      a ≫ deltaE = b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (F.map (XModLambdaN.map g E)) →
      ∃ c : S ⟶ XModLambdaN Cg N,
        c ≫ rho = a ≫ h ∧ c ≫ f = -(b ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map lambdaE) := by
  subst E
  exact H

/-- The full finite May function with the short quotient length written B,
including the same dependent delta/lambda transports as the public target. -/
private theorem finite_may_at_normalized_triangle_explicit_lengths
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (m w : ℤ)
    (eyN : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (A+B) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (A+B))⟦(1:ℤ)⟧)
    (heyN : XModLambdaN.incl _ (A+B) ≫ eyN.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (XModLambdaN.incl (normalizedTriangle model T he).obj₂ (A+B))) :
    let V := normalizedTriangle model T he
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(A:ℤ))
    let LZ := (model.quotients.tower V.obj₃).triangle hA (show A < A+B by omega)
    let LY := (model.quotients.tower V.obj₂).triangle hA (show A < A+B by omega)
    let delta : XModLambdaN V.obj₃ A ⟶ (F.obj (XModLambdaN V.obj₃ B))⟦(1:ℤ)⟧ := by
      simpa only [Nat.add_sub_cancel_left] using LZ.delta
    let lambdaY : F.obj (XModLambdaN V.obj₂ B) ⟶ XModLambdaN V.obj₂ (A+B) := by
      simpa only [Nat.add_sub_cancel_left] using LY.lambdaMap
    ∀ (a : BiHom m w (XModLambdaN V.obj₃ A))
      (b : BiHom m w ((F.obj (XModLambdaN V.obj₂ B))⟦(1:ℤ)⟧)),
      a ≫ delta = b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (F.map (XModLambdaN.map V.mor₂ B)) →
      ∃ c : BiHom m w (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (A+B)),
        c ≫ (model.quotients.tower (V.obj₁⟦(1:ℤ)⟧)).rho A (A+B) (by omega) =
          a ≫ XModLambdaN.map V.mor₃ A ∧
        c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁)
            (A+B) ≫ eyN.hom =
          -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map lambdaY) := by
  let V := normalizedTriangle model T he
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(A:ℤ))
  exact finite_may_transport_short_length F A (A+B) ((A+B)-A) B
    (Nat.add_sub_cancel_left A B) V.mor₂
    ((model.quotients.tower (V.obj₁⟦(1:ℤ)⟧)).rho A (A+B) (by omega))
    (XModLambdaN.map V.mor₃ A)
    (XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (A+B) ≫ eyN.hom)
    ((model.quotients.tower V.obj₃).triangle hA (show A < A+B by omega)).delta
    ((model.quotients.tower V.obj₂).triangle hA (show A < A+B by omega)).lambdaMap
    (by
      intro a b hab
      obtain ⟨c,hc,hcf⟩ := finite_may_at_normalized_triangle T he hT A B hA hB
        m w eyN heyN a b hab
      exact ⟨c,hc,by simpa only [Category.assoc] using hcf⟩)

end
end KIP126.ProofTools.Internal.Mahowald
