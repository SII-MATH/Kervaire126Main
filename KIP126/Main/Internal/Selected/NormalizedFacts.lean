module
public import KIP126.Def.Computation.Table.Values
import all KIP126.Main.Internal.Selected.NormalizedTable

@[expose] section
namespace KIP126.Main.Internal.Selected.Normalized
open CategoryTheory KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model)
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem sphere_eq : sphere = model.classical.sphere := sequence_eq .sphere

private def label (p : ℤ×ℤ) (x : model.classical.sphere.Page 2 p) : sphere.Page 2 p :=
  (eqToHom (congrArg (fun E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ) => E.Page 2 p)
    sphere_eq.symm)) x

private theorem label_basis (s t i : ℕ) :
    label (s,t) (KIP126.Computation.Table.basis .sphere s t i) = basis .sphere s t i := rfl

private theorem survival (p : ℤ×ℤ) (x : model.classical.sphere.Page 2 p)
    (hx : NonzeroSurvival model.classical.sphere p x) : NonzeroSurvival sphere p (label p x) := by
  have tr (E E' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (h : E=E')
      (x : E.Page 2 p) (hx : NonzeroSurvival E p x) :
      NonzeroSurvival E' p ((eqToHom (congrArg (fun A => A.Page 2 p) h)) x) := by
    subst E'
    simpa only [eqToHom_refl,ModuleCat.id_apply] using hx
  exact tr _ _ sphere_eq.symm x hx

private theorem nonzero_differential (r : ℤ) (p q : ℤ×ℤ)
    (x : model.classical.sphere.Page 2 p) (y : model.classical.sphere.Page 2 q)
    (hx : HasNonzeroDifferential model.classical.sphere r p q x y) :
    HasNonzeroDifferential sphere r p q (label p x) (label q y) := by
  have tr (E E' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (h : E=E')
      (x : E.Page 2 p) (y : E.Page 2 q) (hx : HasNonzeroDifferential E r p q x y) :
      HasNonzeroDifferential E' r p q
        ((eqToHom (congrArg (fun A => A.Page 2 p) h)) x)
        ((eqToHom (congrArg (fun A => A.Page 2 q) h)) y) := by
    subst E'
    simpa only [eqToHom_refl,ModuleCat.id_apply] using hx
  exact tr _ _ sphere_eq.symm x y hx

private theorem correction_permanent : NonzeroSurvival sphere (13,137) (basis .sphere 13 137 1) := by
  rw [← label_basis, KIP126.Computation.Table.basis_correction]
  exact survival _ _ KIP126.Computation.Standard.correction_permanent

private theorem u_permanent : NonzeroSurvival sphere (10,134) (basis .sphere 10 134 4) := by
  rw [← label_basis, KIP126.Computation.Table.basis_U]
  exact survival _ _ KIP126.Computation.Standard.u_permanent

private theorem d3_h4_x109 : HasNonzeroDifferential sphere 3 (13,137) (16,139)
    (basis .sphere 13 137 2)
    (label (16,139) (KIP126.Computation.Standard.product
      KIP126.Computation.Standard.h1 (KIP126.Computation.Standard.atom .x_122_15_2))) := by
  rw [← label_basis, KIP126.Computation.Table.basis_h4_x109]
  exact nonzero_differential _ _ _ _ _ KIP126.Computation.Standard.d3_h4_x109_12

end
end KIP126.Main.Internal.Selected.Normalized
