module
public import KIP126.AdamsSynthetic.Standard
public import KIP126.AdamsSynthetic.Standard.Filtration
/-! The zero-object tower argument of the pinned NuFifth:971–1038,
adapted to the same abstract tower and its full ambient comparison. -/
@[expose] section
namespace KIP126.Main.Internal.NuThree
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard (model Spectrum)
open CategoryTheory.Pretriangulated
open scoped ZeroObject
noncomputable section
set_option backward.isDefEq.respectTransparency false
private theorem classical_zero_page (p : ℤ × ℤ) :
    Subsingleton ((model.classical.obj (0 : Spectrum)).Page 2 p) := by
  let B := KIP126.AdamsSynthetic.Standard.closedBackground
  letI := B.symmetric
  let H := model.coefficients.object
  letI := B.tensorShift H
  letI := B.tensorExact H
  let T := model.classicalTower.tower (0 : Spectrum)
  have hz (n : ℕ) : IsZero (T.stage n) := by
    induction n with
    | zero => exact (isZero_zero Spectrum).of_iso T.zeroIso
    | succ n ih =>
      have hh : IsZero (H ⊗ T.stage n) :=
        ((tensorRight H).map_isZero ih).of_iso (β_ H (T.stage n))
      have hc : IsZero (HasFunctorialCofiber.cofib (T.map (Nat.le_succ n))) :=
        hh.of_iso (T.layerIso n)
      exact Triangle.isZero₁_of_isZero₂₃ _
        (HasFunctorialCofiber.cofib_distinguished (T.map (Nat.le_succ n))) ih hc
  have hl : IsZero (T.layer p.1) := by
    apply Triangle.isZero₃_of_isZero₁₂ _
      (HasFunctorialCofiber.cofib_distinguished (T.mapAt (show p.1 ≤ p.1+1 by omega)))
    · exact hz (p.1+1).toNat
    · exact hz p.1.toNat
  haveI : Subsingleton (T.FirstPage p) := ⟨fun a b => hl.eq_of_tgt a b⟩
  haveI : Subsingleton (T.cycles 2 (by decide) p) := inferInstance
  let D := (model.classical.obj (0 : Spectrum)).ssData p
  let e := (model.classicalTower.sequence (0 : Spectrum)).ambient p
  haveI : Subsingleton D.V := Function.Injective.subsingleton e.toLinearEquiv.injective
  haveI : Subsingleton (Subobject.underlying.obj (D.Z 0) : ModuleCat ℤ) :=
    Function.Injective.subsingleton ((ModuleCat.mono_iff_injective (D.Z 0).arrow).mp inferInstance)
  letI : Epi (D.pageπ 0) := coequalizer.π_epi
  haveI : Subsingleton (D.page 0) :=
    Function.Surjective.subsingleton ((ModuleCat.epi_iff_surjective (D.pageπ 0)).mp inferInstance)
  simpa only [KIP126.Core.SpectralSequence.Page,model.classical.firstPage,sub_self,
    Int.toNat_zero,Nat.cast_zero] using (inferInstance : Subsingleton (D.page 0))

private theorem classical_page_zero {X Y : Spectrum} (p : ℤ × ℤ)
    (x : (model.classical.obj X).Page 2 p) : model.classical.pageMap (0 : X ⟶ Y) 2 p x=0 := by
  have hf : (0 : X ⟶ Y) = (0 : X ⟶ (0 : Spectrum)) ≫ (0 : (0 : Spectrum) ⟶ Y) := by simp
  rw [hf]
  change ((model.classical.map ((0 : X ⟶ (0 : Spectrum)) ≫ (0 : (0 : Spectrum) ⟶ Y))).pageMap 2 p) x=0
  rw [model.classical.map_comp]
  rw [SpectralSequenceMorphism.pageMap_comp,ConcreteCategory.comp_apply]
  haveI := classical_zero_page p
  rw [Subsingleton.elim (((model.classical.map (0 : X ⟶ (0 : Spectrum))).pageMap 2 p) x) 0,map_zero]
end
end KIP126.Main.Internal.NuThree
