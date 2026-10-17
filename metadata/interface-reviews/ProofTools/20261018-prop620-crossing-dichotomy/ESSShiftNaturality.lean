module
public import KIP126.ProofTools.Language
import all KIP126.ProofTools.ConvergenceOperations
@[expose] section
namespace KIP126.ProofTools.Paper
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityGradedTransportComm
    {A B A' B' : (ℤ × ℤ) → ModuleCat.{0} ℤ}
    {F : Filtration A} {G : Filtration B} {F' : Filtration A'} {G' : Filtration B'}
    {f : FilteredMorphism F G} {f' : FilteredMorphism F' G'}
    {p q : ℤ × ℤ} (e : FilteredMapTransport f f' p q) (s : ℤ) :
    f.inducedGrMap s p ≫ (e.target.gradedIso s).hom =
      (e.source.gradedIso s).hom ≫ f'.inducedGrMap s q := by
  have level_comm : (f.compat s p).choose ≫ (e.target.level s).hom =
      (e.source.level s).hom ≫ (f'.compat s q).choose := by
    apply (cancel_mono (G'.F s q).arrow).mp
    simp only [Category.assoc]
    rw [e.target.level_arrow, (f'.compat s q).choose_spec]
    rw [← Category.assoc, (f.compat s p).choose_spec, Category.assoc,
      ← e.map_comm]
    simpa only [Category.assoc] using congrArg (fun a => a ≫ f'.map q)
      (e.source.level_arrow s).symm
  haveI : Epi (F.toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
  apply (cancel_epi (F.toAssociatedGraded s p)).mp
  rw [← Category.assoc, f.quotient_naturality, Category.assoc,
    e.target.projection_comm, ← Category.assoc, level_comm]
  rw [Category.assoc, ← f'.quotient_naturality, ← Category.assoc,
    ← e.source.projection_comm]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityTowerGradedNatural
    {Syn : Type 1} [SyntheticCategory.{1,0} Syn]
    [HasFunctorialCofiber (C := Syn)]
    {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
    {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
    (cx : SyntheticTowerConvergence P X) (cy : SyntheticTowerConvergence P Y)
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s : ℤ) :
    (F.map g).eInftyMap (s,p.1+s,p.2) ≫ (towerGradedIso cy p s).hom =
      (towerGradedIso cx p s).hom ≫ M.filteredMap.inducedGrMap s p := by
  simpa only [towerGradedIso, infinityGradedIso, SyntheticAdamsFamily.map, SyntheticTowerConvergence.filtration] using
    (infinity_graded_naturality M p s).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem infinityTowerNatural
    {C : Type 1} [StableHomotopyCategory.{1,0} C]
    [HasFunctorialCofiber (C := C)]
    {Syn : Type 1} [SyntheticCategory.{1,0} Syn]
    [HasFunctorialCofiber (C := Syn)]
    (D : Model C Syn) (δ : ℤ × ℤ) (S : SyntheticESSShiftComparison D δ)
    (X Y : SyntheticObject)
    (f : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary)
    (p : ℤ × ℤ) (s : ℤ) :
    (D.family.map f).eInftyMap (s,p.1+s,p.2) ≫
        (towerInfinityIso (D.convergence Y) (D.convergence (.shift δ Y))
          (S.filtered Y p) s).hom =
      (towerInfinityIso (D.convergence X) (D.convergence (.shift δ X))
          (S.filtered X p) s).hom ≫
        (D.family.map ((SyntheticCategory.biShift δ).map f)).eInftyMap
          (s,(p+δ).1+s,(p+δ).2) := by
  let M := D.convergentMap X Y f
  let M' := D.convergentMap (.shift δ X) (.shift δ Y)
    ((SyntheticCategory.biShift δ).map f)
  have h := infinityGradedTransportComm (S.transport X Y f p) s
  change M.filteredMap.inducedGrMap s p ≫ ((S.filtered Y p).gradedIso s).hom =
    ((S.filtered X p).gradedIso s).hom ≫ M'.filteredMap.inducedGrMap s (p+δ) at h
  have hM' : M'.filteredMap.inducedGrMap s (p+δ) =
      (towerGradedIso (D.convergence (.shift δ X)) (p+δ) s).inv ≫
        (D.family.map ((SyntheticCategory.biShift δ).map f)).eInftyMap
          (s,(p+δ).1+s,(p+δ).2) ≫
        (towerGradedIso (D.convergence (.shift δ Y)) (p+δ) s).hom := by
    calc
      _ = (towerGradedIso (D.convergence (.shift δ X)) (p+δ) s).inv ≫
          ((towerGradedIso (D.convergence (.shift δ X)) (p+δ) s).hom ≫
            M'.filteredMap.inducedGrMap s (p+δ)) := by
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = _ := by
        rw [← infinityTowerGradedNatural (D.convergence (.shift δ X))
          (D.convergence (.shift δ Y)) M' (p+δ) s]
  apply (cancel_mono (towerGradedIso (D.convergence (.shift δ Y)) (p+δ) s).hom).mp
  simp only [towerInfinityIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, infinityTowerGradedNatural (D.convergence X) (D.convergence Y) M]
  rw [Category.assoc, h, hM']

end
end KIP126.ProofTools.Paper
