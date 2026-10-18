module
public import KIP126.ProofTools.Operations
import all KIP126.Main.Internal.AlphaOne.Coherence
/-! The quotient/shift transport of NuFifth:1850–1903, bbac1fc05843 (MIT),
reusing the already proved lambda/shift coherence. -/
@[expose] section
namespace KIP126.Main.Internal.NuThree
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Main.Internal.AlphaOne KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
private theorem quotient_shift_iso (a : ℤ × ℤ) (A : SyntheticSpectrum) (q : ℕ) :
    ∃ e : (SyntheticCategory.biShift a).obj (XModLambdaN A q) ≅
      XModLambdaN ((SyntheticCategory.biShift a).obj A) q,
      (SyntheticCategory.biShift a).map (XModLambdaN.incl A q) ≫ e.hom =
      XModLambdaN.incl ((SyntheticCategory.biShift a).obj A) q := by
  letI := model.exactness.shiftCommShift a
  letI := model.exactness.shiftExact a
  let T := Triangle.mk (lambdaPow q A)
    (HasFunctorialCofiber.cofibι (lambdaPow q A))
    (HasFunctorialCofiber.cofibδ (lambdaPow q A))
  let U := Triangle.mk (lambdaPow q ((SyntheticCategory.biShift a).obj A))
    (HasFunctorialCofiber.cofibι (lambdaPow q ((SyntheticCategory.biShift a).obj A)))
    (HasFunctorialCofiber.cofibδ (lambdaPow q ((SyntheticCategory.biShift a).obj A)))
  let c : ((SyntheticCategory.biShift a).mapTriangle.obj T).obj₁ ≅ U.obj₁ :=
    (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree q) A).symm
  have hc : ((SyntheticCategory.biShift a).mapTriangle.obj T).mor₁ ≫ (Iso.refl _).hom =
      c.hom ≫ U.mor₁ := by
    change (SyntheticCategory.biShift a).map (lambdaPow q A) ≫ 𝟙 _ =
      (shiftSwap a (KIP126.Synthetic.Context.lambdaDegree q) A).inv ≫
        lambdaPow q ((SyntheticCategory.biShift a).obj A)
    rw [lambda_pow_shift model.quotients.coherence]
    simp only [Iso.inv_hom_id_assoc,Category.comp_id]
  let E := CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂
    ((SyntheticCategory.biShift a).mapTriangle.obj T) U
    ((SyntheticCategory.biShift a).map_distinguished T (HasFunctorialCofiber.cofib_distinguished _))
    (HasFunctorialCofiber.cofib_distinguished _) c (Iso.refl _) hc
  refine ⟨Triangle.π₃.mapIso E, ?_⟩
  have hh : (SyntheticCategory.biShift a).map (HasFunctorialCofiber.cofibι (lambdaPow q A)) ≫
      E.hom.hom₃ = E.hom.hom₂ ≫
      HasFunctorialCofiber.cofibι (lambdaPow q ((SyntheticCategory.biShift a).obj A)) := E.hom.comm₂
  have he₂ : E.hom.hom₂ = 𝟙 _ :=
    CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂_hom_hom₂ _ _ _ _ _ _ _
  rw [he₂,Category.id_comp] at hh
  exact hh
private theorem q3_sphere_shift_transport :
    ∃ κ : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 3 ≅
      (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 3),
      XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 3 ≫ κ.hom =
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3) ∧
      ∀ x : BiHom 125 134 (XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 3),
        (susp_invariance 122 130 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 3)).symm
          (x ≫ κ.hom) = 0 ↔ x = 0 := by
  obtain ⟨e, he⟩ := quotient_shift_iso (3,4) (S_0_0:SyntheticSpectrum) 3
  refine ⟨e.symm, ?_, ?_⟩
  · change XModLambdaN.incl ((SyntheticCategory.biShift (3,4)).obj (S_0_0:SyntheticSpectrum)) 3 ≫ e.inv = _
    have hh := congrArg (fun f => f ≫ e.inv) he
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using hh.symm
  · intro x
    let S : BiHom 122 130 (XModLambdaN (S_0_0:SyntheticSpectrum) 3) ≃+
        BiHom 125 134 ((SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 3)) :=
      { toEquiv := susp_invariance 122 130 3 4 _
        map_add' := susp_invariance_add 122 130 3 4 _ }
    let E := (biHomTargetIso 125 134 e.symm).trans S.symm
    exact E.map_eq_zero_iff
end
end KIP126.Main.Internal.NuThree
