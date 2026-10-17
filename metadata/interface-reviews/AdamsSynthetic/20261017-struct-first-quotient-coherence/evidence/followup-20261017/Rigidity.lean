module

import KIP126.AdamsSynthetic.Standard.ClassicalSupport

namespace KIP126.AdamsSynthetic.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Kervaire.Route

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Negative classical filtration implies the corresponding actual first
quotient homotopy group vanishes. This uses the existing upstream comparison
and negative-page responsibility, rather than either compatibility target. -/
private theorem first_quotient_negative
    (X : ClassicalObject) (a s t : ℤ) (hs : s < 0) :
    Subsingleton (BiHom (t-s) (t+a)
      (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1)) := by
  letI := classical_page_negative X 2 s t hs
  refine ⟨fun f g => (model.firstQuotient X a s t).injective ?_⟩
  exact Subsingleton.elim _ _

/-- The same vanishing on the actual unshifted quotient, transported using
the actual quotient functor and its fixed zero-shift isomorphism. -/
private theorem unshifted_first_quotient_negative
    (X : ClassicalObject) (m w : ℤ) (hwm : w-m < 0) :
    Subsingleton (BiHom m w
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)) := by
  let e := (model.quotients.functoriality.functor 1).mapIso
    (SyntheticCategory.biShift_zero.app
      (model.nu.functor.obj (X.obj model.auxiliary)))
  letI : Subsingleton (BiHom m w
      (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1)) := by
    convert first_quotient_negative X 0 (w-m) w hwm using 1
    congr 1 <;> omega
  refine ⟨fun f g => (biHomTargetIso m w e.symm).injective ?_⟩
  exact Subsingleton.elim
    (α := BiHom m w
      (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1)) _ _

private def sphere_lambda_boundary_iso :
    ((SyntheticCategory.biShift (0,-1)).obj
      (model.nu.functor.obj (SphereSpectrum (C := Spectrum))))⟦(1 : ℤ)⟧ ≅
        Smn 1 (-1) (Syn := SyntheticSpectrum) :=
  (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).symm.app _ ≪≫
    (SyntheticCategory.biShift (1,0)).mapIso
      ((SyntheticCategory.biShift (0,-1)).mapIso model.nu.unitIso) ≪≫
    (SyntheticCategory.biShift_comp (0,-1) (1,0)).app S_0_0

/-- The possible boundary error from nu of the classical sphere to any
selected first quotient is zero. The source sphere is essential here. -/
private theorem sphere_boundary_to_first_quotient_subsingleton
    (X : ClassicalObject) :
    Subsingleton
      (((SyntheticCategory.biShift (0,-1)).obj
        (model.nu.functor.obj (SphereSpectrum (C := Spectrum))))⟦(1 : ℤ)⟧ ⟶
          XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) := by
  letI := unshifted_first_quotient_negative X 1 (-1) (by omega)
  refine ⟨fun f g => (cancel_epi sphere_lambda_boundary_iso.inv).mp ?_⟩
  exact Subsingleton.elim
    (α := BiHom 1 (-1)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)) _ _

/-- A generic cofiber cancellation theorem with its exact source-orthogonality
premise. This is a proved local helper, not an added target assumption. -/
private theorem cofiber_incl_cancel_of_subsingleton
    {C : Type*} [StableHomotopyCategory C] [HasFunctorialCofiber (C := C)]
    {A B R : C} (f : A ⟶ B) [Subsingleton (A⟦(1 : ℤ)⟧ ⟶ R)]
    (u v : HasFunctorialCofiber.cofib f ⟶ R)
    (h : HasFunctorialCofiber.cofibι f ≫ u =
      HasFunctorialCofiber.cofibι f ≫ v) : u = v := by
  have hz : HasFunctorialCofiber.cofibι f ≫ (u-v) = 0 := by
    rw [Preadditive.comp_sub, h, sub_self]
  obtain ⟨d, hd⟩ := Triangle.yoneda_exact₃
    (Triangle.mk f (HasFunctorialCofiber.cofibι f)
      (HasFunctorialCofiber.cofibδ f))
    (HasFunctorialCofiber.cofib_distinguished f) (u-v) hz
  have hd0 : d = 0 := @Subsingleton.elim (A⟦(1 : ℤ)⟧ ⟶ R) _ d 0
  have huv : u-v = 0 := by rw [hd, hd0, comp_zero]
  exact sub_eq_zero.mp huv

/-- For the nu-sphere source, the generic orthogonality is supplied by actual
negative classical filtration. The target may be any selected nu-object. -/
private theorem sphere_first_quotient_incl_cancel
    (X : ClassicalObject)
    (u v : XModLambdaN (model.nu.functor.obj (SphereSpectrum (C := Spectrum))) 1 ⟶
      XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)
    (h : XModLambdaN.incl _ 1 ≫ u = XModLambdaN.incl _ 1 ≫ v) : u = v := by
  letI := sphere_boundary_to_first_quotient_subsingleton X
  apply cofiber_incl_cancel_of_subsingleton _ u v h

/-- Pure object-level shift arithmetic moves the lambda boundary through an
arbitrary synthetic shift. No ESS comparison or separation is used. -/
private def lambda_boundary_shift_iso (δ : ℤ × ℤ) (Y : SyntheticSpectrum) :
    ((SyntheticCategory.biShift (0,-1)).obj
      ((SyntheticCategory.biShift δ).obj Y))⟦(1 : ℤ)⟧ ≅
        (SyntheticCategory.biShift δ).obj
          (((SyntheticCategory.biShift (0,-1)).obj Y)⟦(1 : ℤ)⟧) := by
  let left :
      ((SyntheticCategory.biShift (0,-1)).obj
        ((SyntheticCategory.biShift δ).obj Y))⟦(1 : ℤ)⟧ ≅
      (SyntheticCategory.biShift ((δ + (0,-1)) + (1,0))).obj Y :=
    (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift (1,0)).mapIso
        ((SyntheticCategory.biShift_comp δ (0,-1)).app Y) ≪≫
      (SyntheticCategory.biShift_comp (δ + (0,-1)) (1,0)).app Y
  have hbase : ((0 : ℤ),(-1 : ℤ)) + (1,0) = (1,-1) := by ext <;> simp
  let base : ((SyntheticCategory.biShift (0,-1)).obj Y)⟦(1 : ℤ)⟧ ≅
      (SyntheticCategory.biShift (1,-1)).obj Y :=
    (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift_comp (0,-1) (1,0)).app Y ≪≫
      eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj Y) hbase)
  let right :
      (SyntheticCategory.biShift δ).obj
          (((SyntheticCategory.biShift (0,-1)).obj Y)⟦(1 : ℤ)⟧) ≅
      (SyntheticCategory.biShift ((1,-1) + δ)).obj Y :=
    (SyntheticCategory.biShift δ).mapIso base ≪≫
      (SyntheticCategory.biShift_comp (1,-1) δ).app Y
  have hgrade : (δ + (0,-1)) + (1,0) = (1,-1) + δ := by
    ext <;> simp <;> omega
  exact left ≪≫ eqToIso
    (congrArg (fun p => (SyntheticCategory.biShift p).obj Y) hgrade) ≪≫ right.symm

private theorem shifted_sphere_boundary_to_first_quotient_subsingleton
    (X : ClassicalObject) (δ : ℤ × ℤ) :
    Subsingleton
      (((SyntheticCategory.biShift (0,-1)).obj
        ((SyntheticCategory.biShift δ).obj
          (model.nu.functor.obj (SphereSpectrum (C := Spectrum)))))⟦(1 : ℤ)⟧ ⟶
        (SyntheticCategory.biShift δ).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)) := by
  letI := sphere_boundary_to_first_quotient_subsingleton X
  let e := lambda_boundary_shift_iso δ
    (model.nu.functor.obj (SphereSpectrum (C := Spectrum)))
  refine ⟨fun f g => (cancel_epi e.inv).mp ?_⟩
  apply (SyntheticCategory.biShift_fullyFaithful δ).homEquiv.symm.injective
  exact Subsingleton.elim
    (α := ((SyntheticCategory.biShift (0,-1)).obj
      (model.nu.functor.obj (SphereSpectrum (C := Spectrum))))⟦(1 : ℤ)⟧ ⟶
        XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) _ _

private theorem shifted_sphere_first_quotient_incl_cancel
    (X : ClassicalObject) (δ : ℤ × ℤ)
    (u v : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (SphereSpectrum (C := Spectrum)))) 1 ⟶
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (h : XModLambdaN.incl _ 1 ≫ u = XModLambdaN.incl _ 1 ≫ v) : u = v := by
  letI := shifted_sphere_boundary_to_first_quotient_subsingleton X δ
  exact cofiber_incl_cancel_of_subsingleton _ u v h

/-- In particular, for X=sphere the arbitrary inclusion-compatible epsilon
is unique for every synthetic shift delta, not only the two target shifts. -/
private theorem sphere_quotient_shift_iso_unique
    (δ : ℤ × ℤ)
    (ε₀ ε₁ : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (SphereSpectrum (C := Spectrum)))) 1 ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (SphereSpectrum (C := Spectrum))) 1))
    (h₀ : XModLambdaN.incl _ 1 ≫ ε₀.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ 1))
    (h₁ : XModLambdaN.incl _ 1 ≫ ε₁.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ 1)) : ε₀ = ε₁ := by
  apply Iso.ext
  exact shifted_sphere_first_quotient_incl_cancel .sphere δ ε₀.hom ε₁.hom
    (h₀.trans h₁.symm)

#print axioms sphere_quotient_shift_iso_unique

end
end KIP126.AdamsSynthetic.Standard
