module

public import KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.GeneralizedLeibniz.Filtration

/-!
# Actual essential no-crossing and a common source representative

The two maps in this file have the same actual source object, source tower,
and source convergence.  The stem and synthetic weight `p` are fixed for the
whole crossing triangle.  This is stronger than a crossing assertion merely
about classical labels in a finite page window.

Only the independently proved filtration-correction lemmas are used; no
generalized Leibniz or generalized Mahowald law is invoked.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {E : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit E} {X Y Z : Syn}
  {cx : SyntheticTowerConvergence P X}
  {cy : SyntheticTowerConvergence P Y}
  {cz : SyntheticTowerConvergence P Z}

/-- Excludes actual essential extensions in the full higher-source triangle.
The target labels need not be nonzero: essentiality is modulo the entire
actual target solution space, as in `TowerEssentialExtension`.
-/
public def ActualNoCrossing {g : X ⟶ Y}
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ) : Prop :=
  ∀ u v : ℤ, s < u → u ≤ v → v ≤ s+n →
    ∀ x y, ¬TowerEssentialExtension M p u (v-u) x y

/-- One actual no-crossing condition suffices to synchronize the two
extension equations.  The witness `ar` is shared by the two actual image
equations, rather than independently chosen for the two target labels.

The length-zero and zero-label cases are included.  Nonnegative lengths
are inherited from the two extension equations.
-/
private theorem actual_common_source_frames
    {f : X ⟶ Y} {g : X ⟶ Z}
    (Mf : ConvergentMap E f cx.toConvergence cy.toConvergence)
    (Mg : ConvergentMap E g cx.toConvergence cz.toConvergence)
    (p : ℤ × ℤ) (s n m : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (z : ((E.obj Z).sequence.ssData (s+m,p.1+(s+m),p.2)).eInfty)
    (hf : TowerExtensionEquation Mf p s n x y)
    (hg : TowerExtensionEquation Mg p s m x z)
    (hnc : ActualNoCrossing Mf p s n ∨ ActualNoCrossing Mg p s m) :
    ∃ (ar : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ))
      (br : (Subobject.underlying.obj ((P.filtration Y).F (s+n) p) : ModuleCat.{v} ℤ))
      (cr : (Subobject.underlying.obj ((P.filtration Z).F (s+m) p) : ModuleCat.{v} ℤ)),
      (P.filtration X).toAssociatedGraded s p ar = (infinityGradedIso cx p s).hom x ∧
      (P.filtration Y).toAssociatedGraded (s+n) p br = (infinityGradedIso cy p (s+n)).hom y ∧
      (P.filtration Z).toAssociatedGraded (s+m) p cr = (infinityGradedIso cz p (s+m)).hom z ∧
      ((P.filtration X).F s p).arrow ar ≫ f = ((P.filtration Y).F (s+n) p).arrow br ∧
      ((P.filtration X).F s p).arrow ar ≫ g = ((P.filtration Z).F (s+m) p).arrow cr := by
  rcases hnc with hnf | hng
  · obtain ⟨_,ar,cr,he,ha,hc⟩ := (tower_extension_iff Mg p s m x z).mp hg
    obtain ⟨br,he',hb⟩ := Leibniz.tower_target_of_any_source_frame Mf p s n x y hf hnf ar ha
    exact ⟨ar,br,cr,ha,hb,hc,he',he⟩
  · obtain ⟨_,ar,br,he,ha,hb⟩ := (tower_extension_iff Mf p s n x y).mp hf
    obtain ⟨cr,he',hc⟩ := Leibniz.tower_target_of_any_source_frame Mg p s m x z hg hng ar ha
    exact ⟨ar,br,cr,ha,hb,hc,he,he'⟩

/-- Actual homotopy classes extracted from the shared frame.  All three
filtration memberships, all three labels, and both image equations use the
same witnesses.  This is the form consumed by representative-level MH.
-/
public theorem actual_common_source_representative
    {f : X ⟶ Y} {g : X ⟶ Z}
    (Mf : ConvergentMap E f cx.toConvergence cy.toConvergence)
    (Mg : ConvergentMap E g cx.toConvergence cz.toConvergence)
    (p : ℤ × ℤ) (s n m : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (z : ((E.obj Z).sequence.ssData (s+m,p.1+(s+m),p.2)).eInfty)
    (hf : TowerExtensionEquation Mf p s n x y)
    (hg : TowerExtensionEquation Mg p s m x z)
    (hnc : ActualNoCrossing Mf p s n ∨ ActualNoCrossing Mg p s m) :
    ∃ (a : BiHom p.1 p.2 X) (b : BiHom p.1 p.2 Y) (c : BiHom p.1 p.2 Z),
      a ∈ P.filtrationSubmodule X s p ∧
      b ∈ P.filtrationSubmodule Y (s+n) p ∧
      c ∈ P.filtrationSubmodule Z (s+m) p ∧
      (∃ ar : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ),
        ((P.filtration X).F s p).arrow ar = a ∧
        (P.filtration X).toAssociatedGraded s p ar = (infinityGradedIso cx p s).hom x) ∧
      (∃ br : (Subobject.underlying.obj ((P.filtration Y).F (s+n) p) : ModuleCat.{v} ℤ),
        ((P.filtration Y).F (s+n) p).arrow br = b ∧
        (P.filtration Y).toAssociatedGraded (s+n) p br = (infinityGradedIso cy p (s+n)).hom y) ∧
      (∃ cr : (Subobject.underlying.obj ((P.filtration Z).F (s+m) p) : ModuleCat.{v} ℤ),
        ((P.filtration Z).F (s+m) p).arrow cr = c ∧
        (P.filtration Z).toAssociatedGraded (s+m) p cr = (infinityGradedIso cz p (s+m)).hom z) ∧
      a ≫ f = b ∧ a ≫ g = c := by
  obtain ⟨ar,br,cr,ha,hb,hc,haf,hag⟩ :=
    actual_common_source_frames Mf Mg p s n m x y z hf hg hnc
  refine ⟨((P.filtration X).F s p).arrow ar,
    ((P.filtration Y).F (s+n) p).arrow br,
    ((P.filtration Z).F (s+m) p).arrow cr,?_,?_,?_,
    ⟨ar,rfl,ha⟩,⟨br,rfl,hb⟩,⟨cr,rfl,hc⟩,haf,hag⟩
  · have hm : ((P.filtration X).F s p).arrow ar ∈
        ModuleCat.subobjectModule _ ((P.filtration X).F s p) := ⟨ar,rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hm
  · have hm : ((P.filtration Y).F (s+n) p).arrow br ∈
        ModuleCat.subobjectModule _ ((P.filtration Y).F (s+n) p) := ⟨br,rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hm
  · have hm : ((P.filtration Z).F (s+m) p).arrow cr ∈
        ModuleCat.subobjectModule _ ((P.filtration Z).F (s+m) p) := ⟨cr,rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hm

end
end KIP126.ProofTools.Internal.Mahowald
