module
import all KIP126.ProofTools.StretchingRepresentatives
import KIP126.AdamsComputation.Standard
import KIP126.AdamsComputation.Table.Dimensions
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! Sphere automorphisms act trivially after the first lambda quotient.
The actual sphere E2 coordinates in degree (0,0) identify its first quotient
with the two-element additive group. Transport through the fixed quotient
shift comparison proves the statement for every bigraded sphere and every
target. This removes the choice of suspension comparison on Q1 labels in
AimPaper Remark `rmk:qvoewfj`; no characteristic-two claim is made about
unquotiented homotopy groups. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private def sphere_first_quotient_f2 :
    ((S_0_0 : SyntheticSpectrum) ⟶ XModLambdaN S_0_0 1) ≃+ ZMod 2 := by
  let z : Smn (Syn:=SyntheticSpectrum) 0 0 ≅ S_0_0 := SyntheticCategory.biShift_zero.app _
  let e : ((S_0_0 : SyntheticSpectrum) ⟶ XModLambdaN S_0_0 1) ≃+
      BiHom 0 0 (XModLambdaN S_0_0 1) :=
    { toFun := fun a => z.hom ≫ a
      invFun := fun a => z.inv ≫ a
      left_inv := by intro a; simp
      right_inv := by intro a; simp
      map_add' := by intro a b; simp }
  let c := sphereFirstQuotient model.nu model.quotients.functoriality model.firstQuotient 0 0
  have hn : KIP126.Computation.Standard.archive.basisCount 0 0 = 1 :=
    (KIP126.Computation.Table.archive_dimension 0 0 (by decide)).trans (by rfl)
  let d : model.classical.sphere.Page 2 (0,0) ≃ₗ[ℤ] (Fin 1 →₀ ZMod 2) :=
    hn ▸ KIP126.Computation.Standard.coordinates 0 0 (by decide)
  exact e.trans (c.toAddEquiv.trans (d.toAddEquiv.trans
    (Finsupp.uniqueLinearEquiv ℤ (ZMod 2) (0 : Fin 1)).toAddEquiv))

private theorem additive_automorphism_f2_identity {A : Type*} [AddGroup A]
    (e : A ≃+ ZMod 2) (f : A ≃+ A) (x : A) : f x=x := by
  let g : ZMod 2 ≃+ ZMod 2 := e.symm.trans (f.trans e)
  have hcases : ∀ z : ZMod 2, z=0 ∨ z=1 := by decide
  have h1 : g 1=1 := by
    rcases hcases (g 1) with h | h
    · have hz : (1:ZMod 2)=0 := g.injective (h.trans (map_zero g).symm)
      exact False.elim (by norm_num at hz)
    · exact h
  have hh : ∀ z : ZMod 2, g z=z := by
    intro z
    rcases hcases z with rfl | rfl
    · exact map_zero g
    · exact h1
  apply e.injective
  simpa only [g,AddEquiv.trans_apply,AddEquiv.symm_apply_apply] using hh (e x)

private theorem sphere_automorphism_first_quotient
    (u : (S_0_0 : SyntheticSpectrum) ≅ S_0_0)
    (a : (S_0_0 : SyntheticSpectrum) ⟶ XModLambdaN S_0_0 1) :
    u.hom ≫ a = a := by
  let f : ((S_0_0 : SyntheticSpectrum) ⟶ XModLambdaN S_0_0 1) ≃+
      ((S_0_0 : SyntheticSpectrum) ⟶ XModLambdaN S_0_0 1) :=
    { toFun := fun a => u.hom ≫ a
      invFun := fun a => u.inv ≫ a
      left_inv := by intro a; simp
      right_inv := by intro a; simp
      map_add' := by intro a b; simp }
  exact additive_automorphism_f2_identity sphere_first_quotient_f2 f a


private theorem bigraded_sphere_automorphism_first_quotient (m w : ℤ)
    (u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w) :
    u.hom ≫ XModLambdaN.incl (Smn m w) 1 = XModLambdaN.incl (Smn m w) 1 := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (m,w)
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (m,w)
  let u0 : (S_0_0 : SyntheticSpectrum) ≅ S_0_0 := ff.preimageIso u
  have hu : F.map u0.hom = u.hom := ff.map_preimage _
  have h0 := sphere_automorphism_first_quotient u0 (XModLambdaN.incl S_0_0 1)
  letI := model.exactness.shiftCommShift (m,w)
  letI := model.exactness.shiftExact (m,w)
  obtain ⟨Q,hQ,_⟩ := KIP126.ProofTools.Internal.quotient_shift_exists
    model.quotients.coherence (m,w) 1 (S_0_0 : SyntheticSpectrum)
  apply (cancel_mono Q.hom).mp
  dsimp only [Smn] at u ⊢
  rw [Category.assoc,hQ,←hu,←F.map_comp,h0]

private theorem sphere_automorphism_quotient_projection (m w : ℤ)
    (u : Smn (Syn:=SyntheticSpectrum) m w ≅ Smn m w)
    (A : SyntheticSpectrum) (a : BiHom m w A) :
    u.hom ≫ a ≫ XModLambdaN.incl A 1 = a ≫ XModLambdaN.incl A 1 := by
  rw [XModLambdaN.incl_naturality,←Category.assoc,
    bigraded_sphere_automorphism_first_quotient m w u]

end
end KIP126.ProofTools.Internal.Leibniz
