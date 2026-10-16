module
public import KIP126.ProofTools.Operations
public import KIP126.Literature
import all KIP126.Main.Internal.Selected.LambdaOperations
/-! NuNinth:974–1197, bbac1fc05843 (MIT). The old canonical tower lift
argument is expressed through the same actual filtered shift comparison.
Its graded map is definitionally the given convergence transport. -/
@[expose] section
namespace KIP126.Main.Internal.NuNinth
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model SyntheticSpectrum)
open KIP126.ProofTools.Operations
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
private def weightShiftHom {m w : ℤ} {A : SyntheticSpectrum} (k : ℤ) (a : BiHom m w A) :
    BiHom m (w+k) ((SyntheticCategory.biShift (0,k)).obj A) :=
  (biShiftAddIso (m,w) (0,k) (m,w+k) (by ext <;> simp)).inv.app S_0_0 ≫
    (SyntheticCategory.biShift (0,k)).map a

private theorem shift_graded (X : SyntheticObject) (δ p : ℤ×ℤ) (s : ℤ)
    (S : SyntheticESSShiftComparison model δ)
    (e : ((model.family.obj (X.obj model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (aa : (Subobject.underlying.obj ((model.convergence X).filtration.F s p) : ModuleCat ℤ))
    (he : (towerGradedIso (model.convergence X) p s).hom e =
      (model.convergence X).filtration.toAssociatedGraded s p aa) :
    ∃ bb : (Subobject.underlying.obj ((model.convergence (.shift δ X)).filtration.F s (p+δ)) : ModuleCat ℤ),
      ((model.convergence (.shift δ X)).filtration.F s (p+δ)).arrow bb =
        shiftHomotopyClass δ p (((model.convergence X).filtration.F s p).arrow aa) ∧
      (towerGradedIso (model.convergence (.shift δ X)) (p+δ) s).hom
        ((towerInfinityIso (model.convergence X) (model.convergence (.shift δ X)) (S.filtered X p) s).hom e) =
      (model.convergence (.shift δ X)).filtration.toAssociatedGraded s (p+δ) bb := by
  let F := S.filtered X p
  refine ⟨(F.level s).hom aa,?_,?_⟩
  · exact (ConcreteCategory.congr_hom (F.level_arrow s) aa).trans (S.ambient_eq X p _)
  · change ((towerGradedIso (model.convergence X) p s).hom ≫ (F.gradedIso s).hom ≫
      (towerGradedIso (model.convergence (.shift δ X)) (p+δ) s).inv ≫
        (towerGradedIso (model.convergence (.shift δ X)) (p+δ) s).hom) e = _
    rw [Iso.inv_hom_id,Category.comp_id]
    change (F.gradedIso s).hom ((towerGradedIso (model.convergence X) p s).hom e)=_
    rw [he]
    exact ConcreteCategory.congr_hom (F.projection_comm s) aa

private theorem map_graded (X Y : SyntheticObject)
    (f : X.obj model.nu model.auxiliary ⟶ Y.obj model.nu model.auxiliary)
    (i : Tridegree)
    (e : ((model.family.obj (X.obj model.nu model.auxiliary)).sequence.ssData i).eInfty)
    (aa : (Subobject.underlying.obj ((model.convergence X).filtration.F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ))
    (he : ((model.convergence X).identification i).hom e =
      (model.convergence X).filtration.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) aa) :
    ∃ bb : (Subobject.underlying.obj ((model.convergence Y).filtration.F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ),
      ((model.convergence Y).filtration.F i.1 (i.2.1-i.1,i.2.2)).arrow bb =
        ((model.convergence X).filtration.F i.1 (i.2.1-i.1,i.2.2)).arrow aa ≫ f ∧
      ((model.convergence Y).identification i).hom ((model.family.map f).eInftyMap i e) =
      (model.convergence Y).filtration.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) bb := by
  let M := model.convergentMap X Y f
  let bb := (M.filteredMap.compat i.1 (i.2.1-i.1,i.2.2)).choose aa
  have hb : ((model.convergence Y).filtration.F i.1 (i.2.1-i.1,i.2.2)).arrow bb =
      ((model.convergence X).filtration.F i.1 (i.2.1-i.1,i.2.2)).arrow aa ≫ f := by
    have h := ConcreteCategory.congr_hom (M.filteredMap.compat i.1 (i.2.1-i.1,i.2.2)).choose_spec aa
    change _ = M.filteredMap.map _ _ at h
    exact h.trans (ConcreteCategory.congr_hom (M.filteredMap_map _) _)
  refine ⟨bb,hb,?_⟩
  have hn := grade_natural X Y f i aa bb hb.symm
  have hx : ((model.convergence X).identification i).inv
      ((model.convergence X).filtration.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) aa)=e := by
    rw [←he]
    exact ((model.convergence X).identification i).toLinearEquiv.symm_apply_apply e
  rw [hx] at hn
  exact (congrArg ((model.convergence Y).identification i).hom hn).symm.trans
    (((model.convergence Y).identification i).toLinearEquiv.apply_symm_apply _)
end
end KIP126.Main.Internal.NuNinth
