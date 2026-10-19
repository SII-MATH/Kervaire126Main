module

import all KIP126.Literature.Standard.FiniteQuotientGhosts
import all KIP126.Literature.Standard.FiniteQuotientPositive

/-! Whitehead reflection only on the constructed finite sphere-cell objects.
Spheres are not assumed to detect arbitrary synthetic objects or arrows. -/

@[expose] section
namespace KIP126.Literature.Standard.Internal.GhostResearch
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

private theorem spherewise_shift_injective
    {D E : SyntheticSpectrum} (f : D ⟶ E)
    (hf : ∀ m w : ℤ, Function.Injective (fun a : BiHom m w D => a ≫ f))
    (m w : ℤ) : Function.Injective
      (fun a : BiHom m w (D⟦(1:ℤ)⟧) => a ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map f) := by
  intro a b hab
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let ff := Functor.FullyFaithful.ofFullyFaithful S
  let e : (Smn (Syn:=SyntheticSpectrum) (m-1) w)⟦(1:ℤ)⟧ ≅ Smn m w :=
    positive_sphere_suspension_iso (m-1) w ≪≫ eqToIso (by congr 1; omega)
  let a0 := ff.preimage (e.hom ≫ a)
  let b0 := ff.preimage (e.hom ≫ b)
  have ha0 : S.map a0 = e.hom ≫ a := ff.map_preimage _
  have hb0 : S.map b0 = e.hom ≫ b := ff.map_preimage _
  have h0 : a0 ≫ f = b0 ≫ f := by
    apply ff.map_injective
    rw [Functor.map_comp,Functor.map_comp,ha0,hb0]
    simpa only [Category.assoc] using congrArg (fun z => e.hom ≫ z) hab
  have hab0 : a0=b0 := hf (m-1) w h0
  apply (cancel_epi e.hom).mp
  rw [←ha0,←hb0,hab0]

private theorem spherewise_bijective_cofiber_zero
    {D E : SyntheticSpectrum} (f : D ⟶ E)
    (hf : ∀ m w : ℤ, Function.Bijective (fun a : BiHom m w D => a ≫ f))
    (m w : ℤ) (a : BiHom m w (HasFunctorialCofiber.cofib f)) : a=0 := by
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished f
  have hzero : (a ≫ T.mor₃) ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map f=0 := by
    change (a ≫ T.mor₃) ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map T.mor₁=0
    rw [Category.assoc,comp_distTriang_mor_zero₃₁ T hT,comp_zero]
  have hap : a ≫ T.mor₃=0 :=
    spherewise_shift_injective f (fun m w => (hf m w).1) m w
      (by simpa only [zero_comp] using hzero)
  obtain ⟨b,hb⟩ := T.coyoneda_exact₃ hT a hap
  obtain ⟨c,hc⟩ := (hf m w).2 b
  rw [hb,←hc,Category.assoc]
  change c ≫ (T.mor₁ ≫ T.mor₂)=0
  rw [comp_distTriang_mor_zero₁₂ T hT,comp_zero]

private theorem ghostPower_identity (D : SyntheticSpectrum) (n : ℕ) :
    ghostPower (𝟙 D) n = 𝟙 D := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ghostPower,ih,Category.comp_id]

/-- The cofiber is a constructed finite cell object. Its identity is a
ghost only after all its sphere groups have been proved zero. -/
private theorem finite_cells_reflect_spherewise_iso
    {D E : SyntheticSpectrum} {n l : ℕ}
    (hD : SphereCells D n) (hE : SphereCells E l) (f : D ⟶ E)
    (hf : ∀ m w : ℤ, Function.Bijective (fun a : BiHom m w D => a ≫ f)) :
    IsIso f := by
  let T := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished f
  have hK : SphereCells (HasFunctorialCofiber.cofib f) (l+n) :=
    SphereCells.middle T.rotate (rot_of_distTriang T hT) l n hE
      (sphereCells_ordinaryShift 1 hD)
  have hghost : SphereGhost (𝟙 (HasFunctorialCofiber.cofib f)) := by
    intro m w a
    rw [Category.comp_id]
    exact spherewise_bijective_cofiber_zero f hf m w a
  have hzero := sphereCells_ghostBound hK _ _ hghost (𝟙 _)
  rw [ghostPower_identity,Category.comp_id] at hzero
  have hK0 : IsZero (HasFunctorialCofiber.cofib f) := (IsZero.iff_id_eq_zero _).mpr hzero
  exact (T.isZero₃_iff_isIso₁ hT).mp hK0

end
end KIP126.Literature.Standard.Internal.GhostResearch
