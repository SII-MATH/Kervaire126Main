module

import all KIP126.ProofTools.Paper.SyntheticExtensions.LambdaRho
import all KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.ConvergenceOperations

/-! Strict filtered surjectivity of the actual finite lambda map. The proof
successively lifts the actual associated-graded classes and terminates at
the vanishing top of the finite quotient filtration. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

private theorem finite_lambda_filtered_surjective (Y : ClassicalObject) (N A : ℕ)
    (hA : 0 < A) (hAN : A < N) (m w u : ℤ)
    (hwindow : (A : ℤ) ≤ m+u-w)
    (z : BiHom m w (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) N))
    (hz : FiltrationAtLeast model.syntheticTower u z) :
    ∃ v : BiHom m w ((SyntheticCategory.biShift (0,-(A:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) (N-A))),
      FiltrationAtLeast model.syntheticTower u v ∧
      v ≫ ((model.quotients.tower _).triangle hA hAN).lambdaMap = z := by
  let X : SyntheticObject := .shift (0,-(A:ℤ)) (.quotient (N-A) (.nu Y))
  let Z : SyntheticObject := .quotient N (.nu Y)
  let f := ((model.quotients.tower (model.nu.functor.obj (Y.obj model.auxiliary))).triangle hA hAN).lambdaMap
  let M := model.convergentMap X Z f
  let L : ℤ := N+w-m
  induction hd : (L-u).toNat using Nat.strong_induction_on generalizing u z with
  | h d ih =>
    by_cases htop : L ≤ u
    · have hzero : z=0 := finite_high_filtration_zero Y N (by omega) m w u
        (by dsimp [L] at htop; omega) z hz
      refine ⟨0, ?_, ?_⟩
      · exact (model.syntheticTower.filtrationSubmodule _ u (m,w)).zero_mem
      · simpa only [Limits.zero_comp] using hzero.symm
    · obtain ⟨zr,hzr⟩ := filtration_representative_exists model.syntheticTower
        (Z.obj model.nu model.auxiliary) (m,w) u z hz
      have hsurj := KIP126.ProofTools.Paper.finite_lambda_infinity_surjective
        Y N A hA hAN u (m+u) w hwindow
      have hrange : (infinityGradedIso (model.convergence Z) (m,w) u).inv
          ((model.syntheticTower.filtration (Z.obj model.nu model.auxiliary)).toAssociatedGraded
            u (m,w) zr) ∈ Set.range ((model.family.functor.map f).eInftyMap
              (u,m+u,w)).hom := hsurj _
      obtain ⟨v,hv,hrem⟩ := (infinity_image_iff_lift M (m,w) u zr).mp hrange
      change BiHom m w ((SyntheticCategory.biShift (0,-(A:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) (N-A))) at v
      rw [hzr] at hrem
      have hd' : (L-(u+1)).toNat < d := by omega
      obtain ⟨v',hv',heq⟩ := ih (L-(u+1)).toNat hd' (u+1)
        (by omega) (z-v≫f) hrem rfl
      refine ⟨v+v', ?_, ?_⟩
      · exact (model.syntheticTower.filtrationSubmodule _ u (m,w)).add_mem hv
          (model.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) hv')
      · change (v+v')≫f=z
        rw [Preadditive.add_comp,heq]
        abel

private theorem filtered_shift_mem (X : SyntheticObject) (δ p : ℤ×ℤ) (u : ℤ)
    (a : BiHom p.1 p.2 (X.obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower u a) :
    FiltrationAtLeast model.syntheticTower u
      (((essShift δ).filtered X p).ambient.hom a) := by
  obtain ⟨ar,har⟩ := filtration_representative_exists model.syntheticTower
    (X.obj model.nu model.auxiliary) p u a ha
  let E := (essShift δ).filtered X p
  have hm : E.ambient.hom a ∈ ModuleCat.subobjectModule _
      ((model.convergence (.shift δ X)).filtration.F u (p+δ)) := by
    refine ⟨(E.level u).hom ar,?_⟩
    have he := ConcreteCategory.congr_hom (E.level_arrow u) ar
    simpa only [ModuleCat.comp_apply,har] using he
  simpa only [SyntheticTowerConvergence.filtration,SyntheticTowerPresentation.filtration,
    OrderIso.apply_symm_apply,FiltrationAtLeast] using hm

private theorem filtered_shift_inv_mem (X : SyntheticObject) (δ p : ℤ×ℤ) (u : ℤ)
    (a : BiHom (p+δ).1 (p+δ).2 ((SyntheticObject.shift δ X).obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower u a) :
    FiltrationAtLeast model.syntheticTower u
      (((essShift δ).filtered X p).ambient.inv a) := by
  obtain ⟨ar,har⟩ := filtration_representative_exists model.syntheticTower
    ((SyntheticObject.shift δ X).obj model.nu model.auxiliary) (p+δ) u a ha
  let E := (essShift δ).filtered X p
  have hm : E.ambient.inv a ∈ ModuleCat.subobjectModule _
      ((model.convergence X).filtration.F u p) := by
    refine ⟨(E.level u).inv ar,?_⟩
    have he := ConcreteCategory.congr_hom (E.symm.level_arrow u) ar
    simpa only [ModuleCat.comp_apply,FilteredPieceIso.symm,Iso.symm_hom,har] using he
  simpa only [SyntheticTowerConvergence.filtration,SyntheticTowerPresentation.filtration,
    OrderIso.apply_symm_apply,FiltrationAtLeast] using hm

private theorem filtered_surjectivity_shift (X Y : SyntheticObject)
    (f : X.obj model.nu model.auxiliary ⟶ Y.obj model.nu model.auxiliary)
    (δ p : ℤ×ℤ) (u : ℤ)
    (hlift : ∀ a : BiHom p.1 p.2 (Y.obj model.nu model.auxiliary),
      FiltrationAtLeast model.syntheticTower u a →
      ∃ b : BiHom p.1 p.2 (X.obj model.nu model.auxiliary),
        FiltrationAtLeast model.syntheticTower u b ∧ b≫f=a)
    (a : BiHom (p+δ).1 (p+δ).2 ((SyntheticObject.shift δ Y).obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower u a) :
    ∃ b : BiHom (p+δ).1 (p+δ).2 ((SyntheticObject.shift δ X).obj model.nu model.auxiliary),
      FiltrationAtLeast model.syntheticTower u b ∧
      b≫(SyntheticCategory.biShift δ).map f=a := by
  let E := (essShift δ).transport X Y f p
  obtain ⟨b,hb,heq⟩ := hlift (E.target.ambient.inv a)
    (filtered_shift_inv_mem Y δ p u a ha)
  refine ⟨E.source.ambient.hom b,filtered_shift_mem X δ p u b hb,?_⟩
  have he := ConcreteCategory.congr_hom E.map_comm b
  simp only [ModuleCat.comp_apply,ConvergentMap.filteredMap_map] at he
  change E.source.ambient.hom b ≫ (SyntheticCategory.biShift δ).map f =
    E.target.ambient.hom (b≫f) at he
  rw [heq] at he
  exact he.trans (E.target.ambient.toLinearEquiv.apply_symm_apply a)

private theorem finite_lambda_filtered_surjective_shift (Y : ClassicalObject) (N A : ℕ)
    (hA : 0 < A) (hAN : A < N) (δ p : ℤ×ℤ) (u : ℤ)
    (hwindow : (A : ℤ) ≤ p.1+u-p.2)
    (z : BiHom (p+δ).1 (p+δ).2
      ((SyntheticObject.shift δ (.quotient N (.nu Y))).obj model.nu model.auxiliary))
    (hz : FiltrationAtLeast model.syntheticTower u z) :
    ∃ v : BiHom (p+δ).1 (p+δ).2
        ((SyntheticObject.shift δ (.shift (0,-(A:ℤ))
          (.quotient (N-A) (.nu Y)))).obj model.nu model.auxiliary),
      FiltrationAtLeast model.syntheticTower u v ∧
      v ≫ (SyntheticCategory.biShift δ).map
        ((model.quotients.tower _).triangle hA hAN).lambdaMap = z := by
  exact filtered_surjectivity_shift (.shift (0,-(A:ℤ)) (.quotient (N-A) (.nu Y)))
    (.quotient N (.nu Y)) _ δ p u
    (fun a ha => finite_lambda_filtered_surjective Y N A hA hAN p.1 p.2 u hwindow a ha) z hz

end
end KIP126.ProofTools.Internal.Mahowald
