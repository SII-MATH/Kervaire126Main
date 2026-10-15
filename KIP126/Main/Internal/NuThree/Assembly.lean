module
import all KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.SectionSeven.NormalizedNu
import all KIP126.Main.Internal.NuThree.Actual
import all KIP126.Main.Internal.NuThree.Shift
import all KIP126.Main.Internal.NuFifth.Lift
import all KIP126.Main.SectionSeven.NuFifthAction
/-! Original NuFifth:1916–1956,3509–3525 assembly, bbac1fc05843 (MIT). -/
@[expose] section
namespace KIP126.Main.Internal.NuThree
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.Main.Internal KIP126.Main.SectionSeven KIP126.Main.SectionSeven.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
private theorem nu_three_actual_relation_and_unique :
    (∀u v:BiHom 122 130 (XModLambdaN (S_0_0:SyntheticSpectrum) 3),u≠0→v≠0→u=v) ∧
    ∃ κ : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 3 ≅
      (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 3),
      XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 3≫κ.hom =
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 3) ∧
    ∃ (x : BiHom 122 130 (XModLambdaN (S_0_0:SyntheticSpectrum) 3))
      (y : BiHom 125 134 (XModLambdaN (S_0_0:SyntheticSpectrum) 3)),
      x≠0 ∧ FiniteDetected 3 (by decide) 8 130 0 KIP126.Computation.Standard.X x ∧
      FiniteDetected 3 (by decide) 11 136 2 KIP126.Computation.Standard.Y y ∧
      (susp_invariance 122 130 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 3) x)≫κ.inv≫
        XModLambdaN.map hopfNu 3=y := by
  obtain ⟨a,b,hab,hb⟩ := nu_three_actual_map_relation
  have hbn : b≠0 := nonzero_detection_ne_zero (.quotient 3 .sphere) (11,136,134) _ b hb
  have han : a≠0 := by
    intro hz
    exact hbn (hab.symm.trans (by rw [hz,zero_comp]))
  obtain ⟨κ,hκ,hκn⟩ := q3_sphere_shift_transport
  let x := (susp_invariance 122 130 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 3)).symm (a≫κ.hom)
  have hxn : x≠0 := by
    intro hz
    exact han ((hκn a).mp hz)
  have hx := nu_three_nonzero_detects_x x hxn
  refine ⟨nu_three_nonzero_unique,κ,hκ,x,b,hxn,hx,hb,?_⟩
  have he : (susp_invariance 122 130 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 3)) x=a≫κ.hom :=
    Equiv.apply_symm_apply _ _
  rw [he,Category.assoc,κ.hom_inv_id_assoc]
  exact hab

/-- The same actual Q3 relation, extracted as in Kervaire126 f2f790267. -/
private theorem nu_extension_in_third_quotient :
    ∃ (x : BiHom 122 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 3))
      (y : BiHom 125 134 (XModLambdaN (S_0_0 : SyntheticSpectrum) 3)),
      FiniteDetected 3 (by decide) 8 130 0 KIP126.Computation.Standard.X x ∧
      FiniteDetected 3 (by decide) 11 136 2 KIP126.Computation.Standard.Y y ∧
      sphereAction hopfNu x = y := by
  obtain ⟨hu,κ,hκ,x,y,hxn,hx,hy,hxy⟩ := nu_three_actual_relation_and_unique
  refine ⟨x,y,hx,hy,?_⟩
  exact (q3_sphere_action_actual_map hu κ hκ hopfNu x hxn).trans hxy

private theorem nu_extension_in_fifth_quotient :
    NuExtension5 KIP126.Computation.Standard.X KIP126.Computation.Standard.Y hopfNu := by
  exact NuFifth.nu_five_of_three hopfNu KIP126.Literature.Standard.nuCofiber_normalized_label
    nu_extension_in_third_quotient
end
end KIP126.Main.Internal.NuThree
