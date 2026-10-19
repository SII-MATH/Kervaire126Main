module

import all KIP126.ProofTools.GeneralizedMahowald.QuotientShift
import all KIP126.ProofTools.GeneralizedMahowald.NoReturn

/-! Spherewise coherence for ordinary-suspension quotient comparisons.

Only inclusion compatibility is imposed on the chosen comparisons.  The
fixed finite no-return window then proves the comparison equations on actual
sphere representatives, without uniqueness of arbitrary cone fillings.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
set_option Elab.async false

private theorem suspension_preserves_sphere_congruence
    (U V : SyntheticSpectrum) (f g : U ⟶ V)
    (hfg : ∀ (m w : ℤ) (c : BiHom m w U), c ≫ f = c ≫ g)
    (m w : ℤ) (c : BiHom m w (U⟦(1:ℤ)⟧)) :
    c ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map f =
      c ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map g := by
  let κ := SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1
  have h := shift_preserves_sphere_congruence U V (1,0) f g hfg m w
    (c ≫ κ.inv.app U)
  have h' := congrArg (fun z => z ≫ κ.hom.app V) h
  simp only [Category.assoc] at h'
  rw [κ.hom.naturality f,κ.hom.naturality g] at h'
  simpa only [Iso.inv_hom_id_app_assoc] using h'

/-- Spherewise uniqueness for maps out of a finite quotient passes to
ordinary suspension through any inclusion-compatible source comparison. -/
private theorem suspension_quotient_sphere_congruence
    (U V : SyntheticSpectrum) (q i : ℕ)
    (e : XModLambdaN (U⟦(1:ℤ)⟧) q ≅ (XModLambdaN U q)⟦(1:ℤ)⟧)
    (he : XModLambdaN.incl _ q ≫ e.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl U q))
    (huniq : ∀ (f g : XModLambdaN U q ⟶ XModLambdaN V i),
      XModLambdaN.incl U q ≫ f = XModLambdaN.incl U q ≫ g →
      ∀ (m w : ℤ) (c : BiHom m w (XModLambdaN U q)), c ≫ f = c ≫ g)
    (f g : XModLambdaN (U⟦(1:ℤ)⟧) q ⟶ (XModLambdaN V i)⟦(1:ℤ)⟧)
    (hfg : XModLambdaN.incl _ q ≫ f = XModLambdaN.incl _ q ≫ g)
    (m w : ℤ) (c : BiHom m w (XModLambdaN (U⟦(1:ℤ)⟧) q)) :
    c ≫ f = c ≫ g := by
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let ff := Functor.FullyFaithful.ofFullyFaithful S
  let f₀ := ff.preimage (e.inv ≫ f)
  let g₀ := ff.preimage (e.inv ≫ g)
  have hf : S.map f₀ = e.inv ≫ f := ff.map_preimage _
  have hg : S.map g₀ = e.inv ≫ g := ff.map_preimage _
  have h₀ : XModLambdaN.incl U q ≫ f₀ = XModLambdaN.incl U q ≫ g₀ := by
    apply ff.map_injective
    rw [Functor.map_comp,Functor.map_comp,hf,hg,←he]
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using hfg
  have h := suspension_preserves_sphere_congruence _ _ f₀ g₀
    (huniq f₀ g₀ h₀) m w (c ≫ e.hom)
  rw [hf,hg] at h
  simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h

/-- Inclusion-compatible maps between finite quotients of the same shifted
native object agree on sphere representatives, also across restriction. -/
private theorem vertical_quotient_maps_equal_on_spheres
    (X : ClassicalObject) (e : ℤ) (i q : ℕ) (hi : 0 < i) (hiq : i ≤ q)
    (f g : XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q ⟶
      XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) i)
    (hfg : XModLambdaN.incl _ q ≫ f = XModLambdaN.incl _ q ≫ g)
    (m w : ℤ) (c : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)) : c ≫ f = c ≫ g := by
  letI := model.exactness.shiftCommShift (0,e)
  letI := model.exactness.shiftExact (0,e)
  obtain ⟨eq,hq,_⟩ := quotient_shift_exists model.quotients.coherence (0,e) q
    (model.nu.functor.obj (X.obj model.auxiliary))
  obtain ⟨ei,_,_⟩ := quotient_shift_exists model.quotients.coherence (0,e) i
    (model.nu.functor.obj (X.obj model.auxiliary))
  have h := shifted_quotient_sphere_congruence X X (0,e) i q hi hiq eq hq
    (f ≫ ei.hom) (g ≫ ei.hom)
    (by simpa only [←Category.assoc] using congrArg (fun z => z ≫ ei.hom) hfg) m w c
  exact (cancel_mono ei.hom).mp (by simpa only [Category.assoc] using h)

/-- Every two inclusion-compatible ordinary-suspension comparisons have
the same action on every actual sphere representative. -/
private theorem finite_suspension_comparisons_equal_on_spheres
    (X : ClassicalObject) (e : ℤ) (q : ℕ) (hq : 0 < q)
    (e₁ e₂ : XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) q ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q)⟦(1:ℤ)⟧)
    (h₁ : XModLambdaN.incl _ q ≫ e₁.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
    (h₂ : XModLambdaN.incl _ q ≫ e₂.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
    (m w : ℤ) (c : BiHom m w (XModLambdaN
      (((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) q)) :
    c ≫ e₁.hom = c ≫ e₂.hom := by
  exact suspension_quotient_sphere_congruence _ _ q q e₁ h₁
    (fun f g hfg m w c => vertical_quotient_maps_equal_on_spheres X e q q hq le_rfl
      f g hfg m w c) e₁.hom e₂.hom (h₁.trans h₂.symm) m w c

/-- The same choice independence for the native, unshifted target object.
The chosen zero bigraded shift is not identified definitionally with it. -/
private theorem finite_nu_suspension_comparisons_equal_on_spheres
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (e₁ e₂ : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) q ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)⟦(1:ℤ)⟧)
    (h₁ : XModLambdaN.incl _ q ≫ e₁.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
    (h₂ : XModLambdaN.incl _ q ≫ e₂.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
    (m w : ℤ) (c : BiHom m w
      (XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) q)) :
    c ≫ e₁.hom = c ≫ e₂.hom := by
  exact suspension_quotient_sphere_congruence _ _ q q e₁ h₁
    (fun f g hfg m w c => quotient_nu_maps_equal_on_spheres X X q hq
      f g hfg m w c) e₁.hom e₂.hom (h₁.trans h₂.symm) m w c

/-- Arbitrary inclusion-compatible comparisons commute on spheres with
the actual quotient of a suspended normalized map. -/
private theorem finite_suspension_normalized_map_on_spheres
    (X Y : ClassicalObject) (k : ℕ) (hk : k ≤ 1) (q : ℕ) (hq : 0 < q)
    (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
      model.nu.functor.obj (Y.obj model.auxiliary))
    (ex : XModLambdaN (((SyntheticCategory.biShift (0,(k:ℤ))).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) q ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,(k:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q)⟦(1:ℤ)⟧)
    (ey : XModLambdaN ((model.nu.functor.obj (Y.obj model.auxiliary))⟦(1:ℤ)⟧) q ≅
      (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ q ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
    (hey : XModLambdaN.incl _ q ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
    (m w : ℤ) (c : BiHom m w (XModLambdaN
      (((SyntheticCategory.biShift (0,(k:ℤ))).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) q)) :
    c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map f) q ≫ ey.hom =
      c ≫ ex.hom ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map f q) := by
  apply suspension_quotient_sphere_congruence _ _ q q ex hex
    (fun a b hab m w c => normalized_quotient_maps_equal_on_spheres X Y k hk q hq
      a b hab m w c)
  rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,hey,
    ←Category.assoc,hex,←Functor.map_comp,←Functor.map_comp,XModLambdaN.incl_naturality]

/-- The ordinary-suspension restriction square holds on sphere maps for
arbitrary inclusion-compatible comparisons at both quotient lengths. -/
private theorem finite_suspension_restriction_on_spheres
    (X : ClassicalObject) (e : ℤ) (i q : ℕ) (hi : 0 < i) (hiq : i ≤ q)
    (ei : XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) i ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) i)⟦(1:ℤ)⟧)
    (eq : XModLambdaN (((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) q ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q)⟦(1:ℤ)⟧)
    (hei : XModLambdaN.incl _ i ≫ ei.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ i))
    (heq : XModLambdaN.incl _ q ≫ eq.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
    (m w : ℤ) (c : BiHom m w (XModLambdaN
      (((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))⟦(1:ℤ)⟧) q)) :
    c ≫ (model.quotients.tower _).rho i q hiq ≫ ei.hom =
      c ≫ eq.hom ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((model.quotients.tower _).rho i q hiq) := by
  apply suspension_quotient_sphere_congruence _ _ q i eq heq
    (fun f g hfg m w c => vertical_quotient_maps_equal_on_spheres X e i q hi hiq
      f g hfg m w c)
  rw [←Category.assoc,(model.quotients.tower _).rho_quotient hiq,hei,
    ←Category.assoc,heq,←Functor.map_comp,(model.quotients.tower _).rho_quotient hiq]

end
end KIP126.ProofTools.Internal.Mahowald

#print axioms KIP126.ProofTools.Internal.Mahowald.finite_suspension_comparisons_equal_on_spheres
#print axioms KIP126.ProofTools.Internal.Mahowald.finite_nu_suspension_comparisons_equal_on_spheres
#print axioms KIP126.ProofTools.Internal.Mahowald.finite_suspension_normalized_map_on_spheres
#print axioms KIP126.ProofTools.Internal.Mahowald.finite_suspension_restriction_on_spheres
