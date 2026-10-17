import KIP126.AdamsSynthetic.ESSShift
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
theorem separated_shift (D : Model C Syn) (X : SyntheticObject) (δ : ℤ × ℤ)
    (S : SyntheticESSShiftComparison D δ)
    (hsep : HomotopySeparated D.syntheticTower (X.obj D.nu D.auxiliary)) :
    HomotopySeparated D.syntheticTower ((SyntheticCategory.biShift δ).obj
      (X.obj D.nu D.auxiliary)) := by
  intro m w a ha
  let p : ℤ × ℤ := (m-δ.1,w-δ.2)
  have hp : p+δ=(m,w) := by ext <;> simp [p]
  let e : FilteredPieceIso (D.convergence X).filtration
      (D.convergence (.shift δ X)).filtration p (m,w) :=
    hp ▸ S.filtered X p
  have hb : e.ambient.inv a = 0 := by
    apply hsep p.1 p.2 (e.ambient.inv a)
    intro s
    have hmem : a ∈ ModuleCat.subobjectModule _
        ((D.convergence (.shift δ X)).filtration.F s (m,w)) := by
      simpa only [SyntheticTowerConvergence.filtration,
        SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
        FiltrationAtLeast, SyntheticObject.obj] using ha s
    obtain ⟨x,hx⟩ := hmem
    have hcomm := ConcreteCategory.congr_hom (e.symm.level_arrow s) x
    simp only [ModuleCat.comp_apply, FilteredPieceIso.symm] at hcomm
    have hm : e.ambient.inv a ∈ ModuleCat.subobjectModule _
        ((D.convergence X).filtration.F s p) := by
      refine ⟨(e.level s).inv x,?_⟩
      change ((D.convergence X).filtration.F (s:ℤ) p).arrow ((e.level s).inv x) = e.ambient.inv a
      simpa only [hx, Iso.symm_hom] using hcomm
    simpa only [SyntheticTowerConvergence.filtration,
      SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hm
  apply (ModuleCat.mono_iff_injective e.ambient.inv).mp inferInstance
  simpa only [map_zero] using hb
