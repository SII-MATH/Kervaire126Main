module
import all KIP126.Def.ProofTools.GeneralizedMahowald.Coherence

/-! The actual absolute-boundary square for AimPaper Theorem 6.1.
The square is induced by quotient naturality and the fixed suspension
comparison; its commutativity does not assume any crossing conclusion. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic
noncomputable section
set_option backward.isDefEq.respectTransparency false

private def absoluteBoundary {Syn : Type*} [SyntheticCategory Syn]
    [HasFunctorialCofiber (C := Syn)] (A : Syn) (q : ℕ) :
    XModLambdaN A q ⟶ (SyntheticCategory.biShift (1,-(q:ℤ))).obj A :=
  XModLambdaN.proj A q ≫ (Mahowald.biSuspensionIso q A).inv

private theorem absoluteBoundary_natural {Syn : Type*} [SyntheticCategory Syn]
    [HasFunctorialCofiber (C := Syn)] {A B : Syn} (f : A ⟶ B) (q : ℕ) :
    XModLambdaN.map f q ≫ absoluteBoundary B q =
      absoluteBoundary A q ≫ (SyntheticCategory.biShift (1,-(q:ℤ))).map f := by
  apply (cancel_mono (Mahowald.biSuspensionIso q B).hom).mp
  simp only [absoluteBoundary,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [Mahowald.biSuspensionIso_natural]
  simpa only [Category.assoc,Iso.inv_hom_id_assoc] using XModLambdaN.proj_naturality f q

end
end KIP126.ProofTools.Internal.Leibniz
