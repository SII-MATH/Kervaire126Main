module

public import KIP126.ProofTools.Operations
import all KIP126.ProofTools.ConvergenceOperations

@[expose] section
namespace Prop620ShortReindex
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

private theorem tower_extension_reindexed
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (k m target : ℤ) (h : target = k+m)
    (x : ((F.obj X).sequence.ssData (k,p.1+k,p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (target,p.1+target,p.2)).eInfty) :
    TowerExtensionEquation M p k m x
      ((eqToHom (congrArg
        (fun d => ((F.obj Y).sequence.ssData (d,p.1+d,p.2)).eInfty) h)) y) ↔
      0 ≤ m ∧ ∃
        (a : (Subobject.underlying.obj ((P.filtration X).F k p) : ModuleCat.{v} ℤ))
        (b : (Subobject.underlying.obj ((P.filtration Y).F target p) : ModuleCat.{v} ℤ)),
        ((P.filtration X).F k p).arrow a ≫ g =
          ((P.filtration Y).F target p).arrow b ∧
        (P.filtration X).toAssociatedGraded k p a = (infinityGradedIso cx p k).hom x ∧
        (P.filtration Y).toAssociatedGraded target p b =
          (infinityGradedIso cy p target).hom y := by
  subst target
  simpa only [eqToHom_refl, ModuleCat.id_apply] using tower_extension_iff M p k m x y

#print axioms tower_extension_reindexed
end
end Prop620ShortReindex
