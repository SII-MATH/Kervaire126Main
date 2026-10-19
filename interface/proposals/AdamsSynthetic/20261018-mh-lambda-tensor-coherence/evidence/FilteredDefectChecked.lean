module
import all KIP126.ProofTools.GeneralizedMahowald.MayCorrection
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionDetection

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The whole prequotient defect acts on the finite representative without
assuming additivity of familyPageMap in its map argument. -/
private theorem finite_detected_whole_defect
    (A B C D : SyntheticObject)
    (incl : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (K J : B.obj model.nu model.auxiliary ⟶ D.obj model.nu model.auxiliary)
    (d : A.obj model.nu model.auxiliary ⟶ C.obj model.nu model.auxiliary)
    (h : C.obj model.nu model.auxiliary ⟶ D.obj model.nu model.auxiliary)
    (R : A.obj model.nu model.auxiliary ⟶ D.obj model.nu model.auxiliary)
    (hedge : incl ≫ K - incl ≫ J = d ≫ h - R)
    (p : Tridegree)
    (x : (model.family.obj (A.obj model.nu model.auxiliary)).E₂ p)
    (alpha : BiHom (p.2.1-p.1) p.2.2 (B.obj model.nu model.auxiliary))
    (halpha : Detects (model.convergence B) p
      (familyPageMap model.family incl 2 p x) alpha) :
    Detects (model.convergence D) p
      (familyPageMap model.family (d ≫ h - R) 2 p x)
      (alpha ≫ K - alpha ≫ J) := by
  have hm := detects_map B D (K-J) p _ alpha halpha
  have hlabel : familyPageMap model.family (K-J) 2 p
      (familyPageMap model.family incl 2 p x) =
      familyPageMap model.family (d ≫ h-R) 2 p x := by
    rw [←ModuleCat.comp_apply,family_page_comp,Preadditive.comp_sub,hedge]
  rw [hlabel,Preadditive.comp_sub] at hm
  exact hm

/-- The precise residual range problem when the synchronized source a is
kept fixed. It is weaker than requiring a May lift for every prescribed b.
The subgroup V will be the source's next filtration piece. -/
private theorem fixed_source_signed_repair_iff
    {B C D H Z : Type*} [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup H] [AddCommGroup Z]
    (rho : C →+ H) (f : C →+ D) (lam : B →+ D) (g : B →+ Z)
    (V : AddSubgroup B) (b0 : B) (c0 : C) :
    (∃ b c, b-b0 ∈ V ∧ g b = g b0 ∧ rho c = rho c0 ∧ f c = -(lam b)) ↔
    ∃ v z, v ∈ V ∧ g v = 0 ∧ rho z = 0 ∧
      f z + lam v = -(f c0 + lam b0) := by
  constructor
  · rintro ⟨b,c,hv,hg,hr,hf⟩
    refine ⟨b-b0,c-c0,hv,?_,?_,?_⟩
    · rw [map_sub,hg,sub_self]
    · rw [map_sub,hr,sub_self]
    · rw [map_sub,map_sub,hf]
      abel
  · rintro ⟨v,z,hv,hg,hr,he⟩
    refine ⟨b0+v,c0+z,?_,?_,?_,?_⟩
    · simpa only [add_sub_cancel_left] using hv
    · rw [map_add,hg,add_zero]
    · rw [map_add,hr,add_zero]
    · rw [map_add,map_add]
      calc
        f c0 + f z = f c0 + (f z + lam v) - lam v := by abel
        _ = f c0 + (-(f c0 + lam b0)) - lam v := by rw [he]
        _ = -(lam b0 + lam v) := by abel

end
end KIP126.ProofTools.Internal.Mahowald

#print axioms KIP126.ProofTools.Internal.Mahowald.finite_detected_whole_defect
#print axioms KIP126.ProofTools.Internal.Mahowald.fixed_source_signed_repair_iff
