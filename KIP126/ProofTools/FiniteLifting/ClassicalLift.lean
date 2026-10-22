module

import all KIP126.ProofTools.Paper.NuNumericalExtensions
import all KIP126.ProofTools.MahowaldLeibniz.Bockstein
import all KIP126.ProofTools.GeneralizedMahowald.ActualNoCrossing
import all KIP126.ProofTools.Paper.OriginalStatements

@[expose] section
namespace KIP126.ProofTools.Internal.FiniteLifting
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.AdamsSynthetic.Standard (model Spectrum SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem regrade_comp_map {A B : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
    (a : BiHom m w A) (f : A ⟶ B) :
    homotopyRegrade hm hw (a ≫ f) = homotopyRegrade hm hw a ≫ f := by
  subst m'; subst w'; rfl

/-- A finite crossing-free extension transports any full source grade to
the specified finite target. No full target lift is assumed. -/
private theorem finite_target_of_full_source
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : FiniteExtensionWitness model X Y f page n s t x y)
    (source : ((model.family.obj ((extensionSourceObject model X Y f).obj
      model.nu model.auxiliary)).sequence.ssData
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f)).eInfty)
    (hsource : HasInfinityRepresentative _ 2 _
      (infiniteSourceForExtension model X Y f s t x) source)
    (hnc : ActualNoCrossing
      (model.convergentMap (.quotient (page-1) (extensionSourceObject model X Y f))
        (.quotient (page-1) (.nu Y)) (finiteExtensionMap model X Y f (page-1)))
      (t-s,t+normalizedExponent model.classicalTower f) s n) :
    ∃ a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      ((extensionSourceObject model X Y f).obj model.nu model.auxiliary),
      Detects (model.convergence (extensionSourceObject model X Y f))
        (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
        (infiniteSourceForExtension model X Y f s t x)
        (homotopyRegrade (by dsimp; omega) rfl a) ∧
      Detects (model.convergence (.quotient (page-1) (.nu Y)))
        (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f)
        (finiteTargetForExtension model X Y f (page-1) n s t W.length_lower y)
        (homotopyRegrade (by dsimp; omega) rfl
          ((a ≫ (model.normalizedMap X Y f).map) ≫ XModLambdaN.incl _ (page-1))) := by
  let A := extensionSourceObject model X Y f
  let p : ℤ × ℤ := (t-s,t+normalizedExponent model.classicalTower f)
  let F := model.syntheticTower.filtration (A.obj model.nu model.auxiliary)
  haveI : Epi (F.toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s p)).mp
    inferInstance ((infinityGradedIso (model.convergence A) p s).hom source)
  let a : BiHom p.1 p.2 (A.obj model.nu model.auxiliary) := (F.F s p).arrow ar
  have had := source_frame_detects (model.convergence A) p s source _ hsource ar har
  have haq := detects_map A (.quotient (page-1) A) (XModLambdaN.incl _ (page-1))
    (s,p.1+s,p.2) _ _ had
  have hlabel : familyPageMap model.family (XModLambdaN.incl (A.obj model.nu model.auxiliary) (page-1))
      2 (s,p.1+s,p.2) (infiniteSourceForExtension model X Y f s t x) =
      finiteSourceForExtension model X Y f (page-1) s t x := by
    unfold infiniteSourceForExtension finiteSourceForExtension finiteNuLabel
    rw [←page_regrade]
    rfl
  have haq' : Detects (model.convergence (.quotient (page-1) A))
      (s,p.1+s,p.2) (finiteSourceForExtension model X Y f (page-1) s t x)
      ((homotopyRegrade (by dsimp; omega) rfl a) ≫ XModLambdaN.incl _ (page-1)) := by
    exact (congrArg (fun z => Detects (model.convergence (.quotient (page-1) A))
      (s,p.1+s,p.2) z
      ((homotopyRegrade (by dsimp; omega) rfl a) ≫ XModLambdaN.incl _ (page-1))) hlabel).mp haq
  rw [←regrade_comp_map] at haq'
  obtain ⟨source',hsource',arq,harq,hgarq⟩ := frame_of_source_detects
    (model.convergence (.quotient (page-1) A)) p s _
    (a ≫ XModLambdaN.incl _ (page-1)) haq'
  have hs : source'=W.source := hsource'.unique W.source_rep
  rw [hs] at hgarq
  obtain ⟨br,hbr,hgbr⟩ := tower_target_of_any_source_frame
    (model.convergentMap (.quotient (page-1) A) (.quotient (page-1) (.nu Y))
      (finiteExtensionMap model X Y f (page-1))) p s n W.source W.target
    W.equation hnc arq hgarq
  have hb := source_frame_detects (model.convergence (.quotient (page-1) (.nu Y)))
    p (s+n) W.target _ W.target_rep br hgbr
  rw [←hbr,harq] at hb
  have hnat : (a ≫ XModLambdaN.incl _ (page-1)) ≫
      finiteExtensionMap model X Y f (page-1) =
      (a ≫ (model.normalizedMap X Y f).map) ≫ XModLambdaN.incl _ (page-1) := by
    change (a ≫ XModLambdaN.incl
        ((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f:ℤ))).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) (page-1)) ≫
        XModLambdaN.map (model.normalizedMap X Y f).map (page-1) =
      (a ≫ (model.normalizedMap X Y f).map) ≫ XModLambdaN.incl _ (page-1)
    simpa only [Category.assoc] using
      congrArg (fun z => a ≫ z)
        (XModLambdaN.incl_naturality (model.normalizedMap X Y f).map (page-1)).symm
  rw [hnat] at hb
  exact ⟨a,had,hb⟩

/-- The finite target becomes permanent and the same full source and actual
normalized image define an infinite extension. The source hypothesis is
existence of its actual E-infinity label, not a prescribed full representative. -/
private theorem finite_extension_to_infinite
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (hx : IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) (s,t) x)
    (W : FiniteExtensionWitness model X Y f page n s t x y)
    (source : ((model.family.obj ((extensionSourceObject model X Y f).obj
      model.nu model.auxiliary)).sequence.ssData
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f)).eInfty)
    (hsource : HasInfinityRepresentative _ 2 _
      (infiniteSourceForExtension model X Y f s t x) source)
    (hnc : ActualNoCrossing
      (model.convergentMap (.quotient (page-1) (extensionSourceObject model X Y f))
        (.quotient (page-1) (.nu Y)) (finiteExtensionMap model X Y f (page-1)))
      (t-s,t+normalizedExponent model.classicalTower f) s n) :
    IsPermanentCycle (model.classical.obj (Y.obj model.auxiliary)) (s+n,t+n) y ∧
      InfiniteExtension model X Y f n s t x y := by
  obtain ⟨a,ha,hb⟩ := finite_target_of_full_source X Y f page n s t x y W source hsource hnc
  let e : ℤ := normalizedExponent model.classicalTower f
  have hw : 0 ≤ (t+n)-(t+e) ∧ (t+n)-(t+e)<((page-1:ℕ):ℤ) := by
    have := W.length_lower
    have := W.length_upper
    have := W.page_ge_two
    constructor <;> dsimp [e] <;> omega
  have hq : 0<page-1 := by have := W.page_ge_two; omega
  have hi : (s+n,(t-s)+(s+n),t+e)=(s+n,t+n,t+e) := by
    ext <;> dsimp <;> omega
  have hb' := detects_transport hi _ _ hb
  have htarget : regradeE2 hi
      (finiteTargetForExtension model X Y f (page-1) n s t W.length_lower y) =
      (model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) (page-1)).pageMap
        2 (s+n,t+n,t+e) (nuWeightLabel model Y (s+n) (t+n) (t+e) (by omega) y) := by
    have hproj : familyPageMap model.family
        (XModLambdaN.incl (model.nu.functor.obj (Y.obj model.auxiliary)) (page-1))
        2 (s+n,(t-s)+(s+n),t+e)
        (infiniteTargetForExtension model X Y f n s t W.length_lower y) =
        finiteTargetForExtension model X Y f (page-1) n s t W.length_lower y := by
      unfold infiniteTargetForExtension finiteTargetForExtension finiteTargetLabel
      rw [←page_regrade]
      rfl
    rw [←hproj,page_regrade]
    congr 1
    exact eq_of_heq ((regradeE2_heq hi _).trans
      (infinite_target_nuWeight_heq X Y f n s t W.length_lower y))
  rw [htarget] at hb'
  rw [normalized_homotopy_regrade_trans,regrade_comp_map] at hb'
  let b : BiHom ((t+n)-(s+n)) (t+e) (model.nu.functor.obj (Y.obj model.auxiliary)) :=
    homotopyRegrade (by omega) rfl (a ≫ (model.normalizedMap X Y f).map)
  have hbfinite : Detects (model.convergence (.quotient (page-1) (.nu Y)))
      (s+n,t+n,t+e)
      ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) (page-1)).pageMap
        2 (s+n,t+n,t+e) (nuWeightLabel model Y (s+n) (t+n) (t+e) (by omega) y))
      (b ≫ XModLambdaN.incl _ (page-1)) := hb'
  have hy := finite_target_from_full_lift_is_permanent Y (page-1) hq (s+n) (t+n) (t+e)
    hw y b hbfinite
  have hbfull := finite_projection_detects_reflect Y (page-1) hq (s+n) (t+n) (t+e)
    hw y b hbfinite
  have hs : (s,(t-s)+s,t+e)=(s,t,t+e) := by simp
  have ha' := detects_transport hs _ _ ha
  have hsourceLabel : regradeE2 hs (infiniteSourceForExtension model X Y f s t x) =
      regradeE2 (by simp [e]) (model.comparison.nuE2 X (normalizedExponent model.classicalTower f) s t 0 x) := by
    unfold infiniteSourceForExtension
    rw [normalized_regrade_trans]
  rw [hsourceLabel,normalized_homotopy_regrade_trans] at ha'
  dsimp only [e,homotopyRegrade] at ha'
  have hpair : fullDetectedPairAt X Y n s t x y (normalizedExponent model.classicalTower f)
      (model.normalizedMap X Y f).map := by
    refine ⟨W.length_lower,a,a ≫ (model.normalizedMap X Y f).map,?_,hbfull,rfl⟩
    exact ha'
  have hyp := permanent_cycle_of_member Y (s+n,t+n) y hy
  exact ⟨hyp,actual_detected_pair_infinite X Y f n s t x y hx hyp hpair⟩

/-- Classical permanence of the source supplies the required full source
grade. Neither a target permanent-cycle premise nor a target lift occurs. -/
private theorem finite_extension_of_permanent_to_infinite
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (hx : IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) (s,t) x)
    (W : FiniteExtensionWitness model X Y f page n s t x y)
    (hnc : ActualNoCrossing
      (model.convergentMap (.quotient (page-1) (extensionSourceObject model X Y f))
        (.quotient (page-1) (.nu Y)) (finiteExtensionMap model X Y f (page-1)))
      (t-s,t+normalizedExponent model.classicalTower f) s n) :
    IsPermanentCycle (model.classical.obj (Y.obj model.auxiliary)) (s+n,t+n) y ∧
      InfiniteExtension model X Y f n s t x y := by
  obtain ⟨source,hsource⟩ := shifted_full_source_exists X
    (normalizedExponent model.classicalTower f) s t x
    (permanent_member_of_cycle X (s,t) x hx)
  have hi : (s,t,t+(normalizedExponent model.classicalTower f:ℤ)-(0:ℕ)) =
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f) := by simp
  have hs := representative_transport hi _ _ hsource
  exact finite_extension_to_infinite X Y f page n s t x y hx W _ hs hnc

/-- Realization transports the complete synthetic extension to one classical
source representative and its actual image, with both specified detections. -/
private theorem finite_extension_of_permanent_to_classical
    (R : RealizationCoordinates model)
    (hcomp : LambdaInversionAdamsComparison model R)
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (hx : IsPermanentCycle (model.classical.obj (X.obj model.auxiliary)) (s,t) x)
    (W : FiniteExtensionWitness model X Y f page n s t x y)
    (hnc : ActualNoCrossing
      (model.convergentMap (.quotient (page-1) (extensionSourceObject model X Y f))
        (.quotient (page-1) (.nu Y)) (finiteExtensionMap model X Y f (page-1)))
      (t-s,t+normalizedExponent model.classicalTower f) s n) :
    IsPermanentCycle (model.classical.obj (Y.obj model.auxiliary)) (s+n,t+n) y ∧
      InfiniteExtension model X Y f n s t x y ∧
      ∃ a : HomotopyGroup (t-s) (X.obj model.auxiliary),
        ClassicalDetects (model.classicalConvergence X) (s,t) x a ∧
        ClassicalDetects (model.classicalConvergence Y) (s+n,t+n) y
          (eqToHom (congrArg (Sphere (C := Spectrum))
            (show (t+n)-(s+n)=t-s by omega)) ≫ a ≫ f) := by
  obtain ⟨hy,he⟩ := finite_extension_of_permanent_to_infinite X Y f page n s t x y hx W hnc
  refine ⟨hy,he,?_⟩
  exact KIP126.ProofTools.Paper.infiniteExtension_to_classicalExtension model R hcomp X Y f n s t
    ⟨x,permanent_member_of_cycle X (s,t) x hx⟩
    ⟨y,permanent_member_of_cycle Y (s+n,t+n) y hy⟩ he

end
end KIP126.ProofTools.Internal.FiniteLifting
