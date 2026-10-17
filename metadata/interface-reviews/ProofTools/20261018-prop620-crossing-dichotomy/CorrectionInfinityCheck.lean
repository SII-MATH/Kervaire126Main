module

public import KIP126.ProofTools.Paper.ExtensionIndeterminacy
public import KIP126.ProofTools.Paper.ExtensionRepresentatives
import all KIP126.ProofTools.Paper.ExtensionIndeterminacy
import all KIP126.ProofTools.Paper.ExtensionRepresentatives
import all KIP126.ProofTools.ConvergenceOperations
import all KIP126.ProofTools.StretchingRepresentatives
import all KIP126.ProofTools.GeneralizedLeibniz.Filtration
import all KIP126.ProofTools.GeneralizedMahowald.QuotientShift
import all KIP126.ProofTools.Paper.ExtensionEssentialSource

/-! A fixed-target nonliftable short extension, or a crossing in the same
later synthetic extension spectral sequence. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace KIP126.ProofTools.Paper
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section

/-- This is the cycle-set difference branch, retaining the specified original
target. It is separate from the classical crossing predicate of Definition 5.9. -/
@[expose] public def FiniteExtensionNonliftableShortTo (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ) (x y)
    (Wearly : FiniteExtensionWitness model X Y f rEarlier n s t x y) : Prop :=
  ∃ a : ℕ, 0 < a ∧ (a:ℤ) ≤ n-normalizedExponent model.classicalTower f ∧
    ∃ x' : Ambient model X (s+a,(t-s)+(s+a)),
      x' ∈ cycles model X (((rEarlier-1:ℕ):ℤ)-a) (s+a,(t-s)+(s+a)) ∧
      x' ∉ cycles model X (((rLater-1:ℕ):ℤ)-a) (s+a,(t-s)+(s+a)) ∧
      ∃ z,
        HasInfinityRepresentative _ 2 _
          (finiteExtensionCorrectionLabel X Y f (rEarlier-1) s t a x') z ∧
        TowerExtensionEquation (model.convergentMap
          (.quotient (rEarlier-1) (extensionSourceObject model X Y f))
          (.quotient (rEarlier-1) (.nu Y)) (finiteExtensionMap model X Y f (rEarlier-1)))
          (t-s,t+normalizedExponent model.classicalTower f) (s+a) (n-a) z
          ((eqToHom (congrArg (fun d =>
            ((model.family.obj ((SyntheticObject.quotient (rEarlier-1) (.nu Y)).obj
              model.nu model.auxiliary)).sequence.ssData
              (d,(t-s)+d,t+normalizedExponent model.classicalTower f)).eInfty)
            (show s+n = (s+a)+(n-a) by omega))) Wearly.target)

/-- A leading source that lifts through the actual square cannot support an
essential short early extension when all late higher-source crossings vanish. -/
private theorem essential_short_source_not_in_range
    (Al Bl Ae Be : SyntheticObject)
    (gl : Al.obj model.nu model.auxiliary ⟶ Bl.obj model.nu model.auxiliary)
    (ge : Ae.obj model.nu model.auxiliary ⟶ Be.obj model.nu model.auxiliary)
    (ra : Al.obj model.nu model.auxiliary ⟶ Ae.obj model.nu model.auxiliary)
    (rb : Bl.obj model.nu model.auxiliary ⟶ Be.obj model.nu model.auxiliary)
    (hsquare : ra ≫ ge = gl ≫ rb) (p : ℤ × ℤ) (s n u d : ℤ)
    (hn : 0 ≤ n) (hu : s < u) (htarget : u+d=s+n)
    (hcross : ExtensionNoCrossingRange (model.convergentMap Al Bl gl) p s n s)
    (xe : ((model.family.obj (Ae.obj model.nu model.auxiliary)).sequence.ssData
      (u,p.1+u,p.2)).eInfty)
    (ye : ((model.family.obj (Be.obj model.nu model.auxiliary)).sequence.ssData
      (u+d,p.1+(u+d),p.2)).eInfty)
    (he : TowerEssentialExtension (model.convergentMap Ae Be ge) p u d xe ye)
    (xl : ((model.family.obj (Al.obj model.nu model.auxiliary)).sequence.ssData
      (u,p.1+u,p.2)).eInfty)
    (hxl : (model.family.map ra).eInftyMap (u,p.1+u,p.2) xl = xe) : False := by
  let FL := model.syntheticTower.filtration (Al.obj model.nu model.auxiliary)
  let FE := model.syntheticTower.filtration (Ae.obj model.nu model.auxiliary)
  let GE := model.syntheticTower.filtration (Be.obj model.nu model.auxiliary)
  let IL := infinityGradedIso (model.convergence Al) p u
  let IE := infinityGradedIso (model.convergence Ae) p u
  haveI : Epi (FL.toAssociatedGraded u p) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective (FL.toAssociatedGraded u p)).mp
    inferInstance (IL.hom xl)
  let α := (FL.F u p).arrow ar
  have hα : α ∈ model.syntheticTower.filtrationSubmodule (Al.obj model.nu model.auxiliary) u p := by
    have hm : α ∈ ModuleCat.subobjectModule _ (FL.F u p) := ⟨ar,rfl⟩
    simpa only [FL,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hm
  have hαnext := model.syntheticTower.filtrationSubmodule_antitone _ p
    (show s+1 ≤ u by omega) hα
  have hgl := image_correction_in_next (model.convergentMap Al Bl gl) p s n s
    (by omega) hcross α hαnext
    (map_preserves_filtration (model.convergentMap Al Bl gl) p s α
      (model.syntheticTower.filtrationSubmodule_antitone _ p (by omega) hα))
  have hαe := map_preserves_filtration (model.convergentMap Al Ae ra) p u α hα
  obtain ⟨ae,hae⟩ := filtration_representative_exists model.syntheticTower
    (Ae.obj model.nu model.auxiliary) p u (α≫ra) hαe
  have hg := representative_grade_naturality (model.convergentMap Al Ae ra) p u ar ae hae.symm
  rw [har] at hg
  have hc : IL.inv (IL.hom xl)=xl := IL.toLinearEquiv.symm_apply_apply xl
  rw [hc] at hg
  have hge : IE.inv (FE.toAssociatedGraded u p ae)=xe := hg.trans hxl
  have hax : FE.toAssociatedGraded u p ae = IE.hom xe :=
    (IE.toLinearEquiv.apply_symm_apply _).symm.trans (congrArg IE.hom hge)
  have hhigh : (α≫ra)≫ge ∈
      model.syntheticTower.filtrationSubmodule (Be.obj model.nu model.auxiliary) (u+d+1) p := by
    have hh := map_preserves_filtration (model.convergentMap Bl Be rb) p (s+n+1) (α≫gl) hgl
    simpa only [Category.assoc,hsquare,htarget] using hh
  have hlow := model.syntheticTower.filtrationSubmodule_antitone _ p
    (show u+d ≤ u+d+1 by omega) hhigh
  obtain ⟨be,hbe⟩ := filtration_representative_exists model.syntheticTower
    (Be.obj model.nu model.auxiliary) p (u+d) ((α≫ra)≫ge) hlow
  have hzero : GE.toAssociatedGraded (u+d) p be = 0 := by
    have hh := (element_grade_equal_iff GE (u+d) p be 0).mpr (by
      rw [hbe,map_zero,sub_zero]
      simpa only [GE,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hhigh)
    simpa only [map_zero] using hh
  apply ((tower_essential_iff_no_zero _ _ _ _ _ _ he.1).mp he)
  apply (tower_extension_iff (model.convergentMap Ae Be ge) p u d xe 0).mpr
  refine ⟨((tower_extension_iff _ _ _ _ _ _).mp he.1).1,ae,be,?_,hax,?_⟩
  · rw [hae,hbe]
  · simpa only [map_zero] using hzero

private theorem infinity_map_eq_of_homotopy_eq
    (A B : SyntheticObject)
    (f g : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (p : ℤ × ℤ) (s : ℤ)
    (hfg : ∀ a : BiHom p.1 p.2 (A.obj model.nu model.auxiliary), a≫f=a≫g)
    (z : ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty) :
    (model.family.map f).eInftyMap (s,p.1+s,p.2) z =
      (model.family.map g).eInftyMap (s,p.1+s,p.2) z := by
  let FA := model.syntheticTower.filtration (A.obj model.nu model.auxiliary)
  let FB := model.syntheticTower.filtration (B.obj model.nu model.auxiliary)
  let IA := infinityGradedIso (model.convergence A) p s
  haveI : Epi (FA.toAssociatedGraded s p) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨ar,har⟩ := (ModuleCat.epi_iff_surjective (FA.toAssociatedGraded s p)).mp
    inferInstance (IA.hom z)
  let α := (FA.F s p).arrow ar
  have hα : α ∈ model.syntheticTower.filtrationSubmodule (A.obj model.nu model.auxiliary) s p := by
    have hh : α ∈ ModuleCat.subobjectModule _ (FA.F s p) := ⟨ar,rfl⟩
    simpa only [FA,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hh
  obtain ⟨br,hbr⟩ := filtration_representative_exists model.syntheticTower
    (B.obj model.nu model.auxiliary) p s (α≫f)
    (map_preserves_filtration (model.convergentMap A B f) p s α hα)
  have hf := representative_grade_naturality (model.convergentMap A B f) p s ar br hbr.symm
  have hg := representative_grade_naturality (model.convergentMap A B g) p s ar br
    ((hfg α).symm.trans hbr.symm)
  rw [har] at hf hg
  have hc : IA.inv (IA.hom z)=z := IA.toLinearEquiv.symm_apply_apply z
  rw [hc] at hf hg
  exact hf.symm.trans hg

private theorem correction_rho_square_infinity (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (i q : ℕ) (hi : 0 < i) (hiq : i ≤ q) (p : ℤ × ℤ) (u : ℤ)
    (z : ((model.family.obj ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj
      model.nu model.auxiliary)).sequence.ssData (u,p.1+u,p.2)).eInfty) :
    (model.family.map (correctionShiftIso X Y f i).hom).eInftyMap _
      ((model.family.map ((model.quotients.tower ((extensionSourceObject model X Y f).obj
        model.nu model.auxiliary)).rho i q hiq)).eInftyMap _ z) =
    (model.family.map ((SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f : ℤ))).map
      ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho i q hiq))).eInftyMap _
      ((model.family.map (correctionShiftIso X Y f q).hom).eInftyMap _ z) := by
  let ra := (model.quotients.tower ((extensionSourceObject model X Y f).obj
    model.nu model.auxiliary)).rho i q hiq
  let rn := (model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho i q hiq
  have hh := infinity_map_eq_of_homotopy_eq
    (.quotient q (extensionSourceObject model X Y f))
    (.shift (0,(normalizedExponent model.classicalTower f : ℤ)) (.quotient i (.nu X)))
    (ra≫(correctionShiftIso X Y f i).hom)
    ((correctionShiftIso X Y f q).hom≫
      (SyntheticCategory.biShift (0,(normalizedExponent model.classicalTower f : ℤ))).map rn)
    p u (fun c => by
      simpa only [ra,rn,extensionSourceObject,SyntheticObject.obj,Category.assoc] using
        KIP126.ProofTools.Internal.Mahowald.quotient_shift_restriction_on_spheres X
          (0,(normalizedExponent model.classicalTower f : ℤ)) i q hi hiq
          (correctionShiftIso X Y f i) (correctionShiftIso X Y f q)
          (correctionShiftIso_incl X Y f i) (correctionShiftIso_incl X Y f q) p.1 p.2 c) z
  dsimp only [ra,rn] at hh
  simp only [SyntheticAdamsFamily.map_comp,SpectralSequenceMorphism.eInftyMap_comp,
    ModuleCat.comp_apply] at hh
  exact hh

private theorem correction_unshifted_label_rho (X : ClassicalObject)
    (i q : ℕ) (hiq : i ≤ q) (u v : ℤ) (a : ℕ) (x : Ambient model X (u,v)) :
    familyPageMap model.family
      ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho i q hiq)
      2 (u,v,v-a) (finiteTargetLabel model X q u v a x) =
      finiteTargetLabel model X i u v a x := by
  unfold finiteTargetLabel
  have hh := congrArg (fun g => familyPageMap model.family g 2 (u,v,v-a))
    ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).rho_quotient hiq)
  rw [←family_page_comp] at hh
  exact ConcreteCategory.congr_hom hh (targetNuLabel model X u v a x)

private theorem target_weight_label (X : ClassicalObject) (u v : ℤ) (a : ℕ)
    (x : Ambient model X (u,v)) :
    nuWeightLabel model X u v (v-a) (by omega) x = targetNuLabel model X u v a x := by
  have hk : (v-(v-(a:ℤ))).toNat=a := by omega
  have transport (b c : ℕ) (he : b=c) (hi : (u,v,v-b)=(u,v,v-c)) :
      regradeE2 hi (targetNuLabel model X u v b x) = targetNuLabel model X u v c x := by
    subst c
    rfl
  exact transport _ a hk _

private theorem unshifted_label_infinity_exists (X : ClassicalObject)
    (q : ℕ) (hq : 0 < q) (u v : ℤ) (a : ℕ) (ha : a < q)
    (x : Ambient model X (u,v)) (hx : x∈cycles model X ((q:ℤ)-a) (u,v)) :
    ∃ z : ((model.family.obj ((SyntheticObject.quotient q (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData (u,v,v-a)).eInfty,
      HasInfinityRepresentative _ 2 _ (finiteTargetLabel model X q u v a x) z := by
  let P := KIP126.Literature.Standard.infinityFiniteWindow X q hq (u,v) (v-a)
    (by constructor <;> omega)
  have hx' : x∈cycles model X ((q:ℤ)-v+(v-a)) (u,v) := by convert hx using 1 <;> congr 1 <;> omega
  let c := subquotientClass (cycles model X ((q:ℤ)-v+(v-a)) (u,v))
    (boundaries model X (1+v-(v-a)) (u,v)) ⟨x,hx'⟩
  let z := P.symm c
  have he := (KIP126.Literature.Standard.eInfinity_finite_labels X q hq u v (v-a)
    (by constructor <;> omega) x z).mpr ⟨hx',P.apply_symm_apply c⟩
  rw [target_weight_label] at he
  exact ⟨z,he⟩

private def correctionInfinity (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (s t : ℤ) (a : ℕ)
    (z : ((model.family.obj ((SyntheticObject.quotient q (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
      (s+a,(t-s)+(s+a),((t-s)+(s+a))-a)).eInfty) :
    ((model.family.obj ((SyntheticObject.quotient q (extensionSourceObject model X Y f)).obj
      model.nu model.auxiliary)).sequence.ssData
      (s+a,(t-s)+(s+a),t+normalizedExponent model.classicalTower f)).eInfty := by
  let e : ℤ := normalizedExponent model.classicalTower f
  let u : ℤ := s+a
  let p : ℤ × ℤ := (t-s,((t-s)+(s+a))-a)
  let z0 : ((model.family.obj ((SyntheticObject.quotient q (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData (u,p.1+u,p.2)).eInfty := z
  let I := towerInfinityIso (F := model.family) (P := model.syntheticTower) (model.convergence (.quotient q (.nu X)))
    (model.convergence (.shift (0,e) (.quotient q (.nu X))))
    ((essShift (0,e)).filtered (.quotient q (.nu X)) p) u
  let zs : ((model.family.obj ((SyntheticObject.shift (0,e) (.quotient q (.nu X))).obj
      model.nu model.auxiliary)).sequence.ssData (u,(p+(0,e)).1+u,(p+(0,e)).2)).eInfty := I.hom z0
  let hdeg : (u,(p+(0,e)).1+u,(p+(0,e)).2) =
      (s+a,(t-s)+(s+a),t+normalizedExponent model.classicalTower f) := by
    ext <;> dsimp [p,u,e] <;> omega
  let zt := (eqToHom (congrArg (fun i => ((model.family.obj
    ((SyntheticObject.shift (0,e) (.quotient q (.nu X))).obj
      model.nu model.auxiliary)).sequence.ssData i).eInfty) hdeg)) zs
  exact (model.family.map (correctionShiftIso X Y f q).inv).eInftyMap (s+a,(t-s)+(s+a),t+normalizedExponent model.classicalTower f) zt

private theorem correctionInfinity_represents (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (s t : ℤ) (a : ℕ) (x : Ambient model X (s+a,(t-s)+(s+a)))
    (z : ((model.family.obj ((SyntheticObject.quotient q (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
      (s+a,(t-s)+(s+a),((t-s)+(s+a))-a)).eInfty)
    (hz : HasInfinityRepresentative _ 2 _ (finiteTargetLabel model X q (s+a) ((t-s)+(s+a)) a x) z) :
    HasInfinityRepresentative _ 2 _ (finiteExtensionCorrectionLabel X Y f q s t a x)
      (correctionInfinity X Y f q s t a z) := by
  let e : ℤ := normalizedExponent model.classicalTower f
  let u : ℤ := s+a
  let p : ℤ × ℤ := (t-s,((t-s)+(s+a))-a)
  let I := towerInfinityIso (F := model.family) (P := model.syntheticTower)
    (model.convergence (.quotient q (.nu X)))
    (model.convergence (.shift (0,e) (.quotient q (.nu X))))
    ((essShift (0,e)).filtered (.quotient q (.nu X)) p) u
  let hdeg : (u,(p+(0,e)).1+u,(p+(0,e)).2) =
      (s+a,(t-s)+(s+a),t+normalizedExponent model.classicalTower f) := by
    ext <;> dsimp [p,u,e] <;> omega
  let zt := (eqToHom (congrArg (fun i => ((model.family.obj
    ((SyntheticObject.shift (0,e) (.quotient q (.nu X))).obj
      model.nu model.auxiliary)).sequence.ssData i).eInfty) hdeg)) (I.hom z)
  have hs := ((essShift (0,e)).representative_iff
    (.quotient q (.nu X)) 2 (by decide) p u
    (finiteTargetLabel model X q (s+a) ((t-s)+(s+a)) a x) z).mp hz
  have hs' := infinity_representative_regrade hdeg _ _ hs
  have hm := family_infinity_representative_map (correctionShiftIso X Y f q).inv
    (s+a,(t-s)+(s+a),t+normalizedExponent model.classicalTower f) _ zt hs'
  exact hm

end
end KIP126.ProofTools.Paper
