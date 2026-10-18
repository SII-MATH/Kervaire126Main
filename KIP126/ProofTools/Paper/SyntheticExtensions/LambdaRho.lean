module

public import KIP126.ProofTools.Language
import all KIP126.ProofTools.GeneralizedLeibniz.Filtration
import all KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.StretchingRepresentatives

/-! AimPaper Proposition 4.2 (`prop:9770ae6e`). The actual λ and ρ maps
have no essential extensions of positive length. Essentiality uses the full
homogeneous target indeterminacy of `TowerExtensionEquation`.
The fixed Literature E∞ presentations and their map comparisons remain
upstream dependencies. -/

section
namespace KIP126.ProofTools.Paper
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

section General
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {E : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit E} {A B : Syn} {g : A ⟶ B}
  {ca : SyntheticTowerConvergence P A} {cb : SyntheticTowerConvergence P B}

private theorem zero_source_not_essential
    (M : ConvergentMap E g ca.toConvergence cb.toConvergence)
    (p : ℤ × ℤ) (s d : ℤ) (hd : 0 ≤ d)
    (y : ((E.obj B).sequence.ssData (s+d,p.1+(s+d),p.2)).eInfty) :
    ¬ TowerEssentialExtension M p s d 0 y := by
  intro h
  apply ((tower_essential_iff_no_zero M p s d 0 y h.1).mp h)
  apply (tower_extension_iff M p s d 0 0).mpr
  refine ⟨hd,0,0,?_,?_,?_⟩ <;> simp

private theorem zero_target_not_essential
    (M : ConvergentMap E g ca.toConvergence cb.toConvergence)
    (p : ℤ × ℤ) (s d : ℤ)
    (x : ((E.obj A).sequence.ssData (s,p.1+s,p.2)).eInfty) :
    ¬ TowerEssentialExtension M p s d x 0 := by
  intro h
  exact ((tower_essential_iff_no_zero M p s d x 0 h.1).mp h) h.1

private theorem not_essential_of_source_injective
    (M : ConvergentMap E g ca.toConvergence cb.toConvergence)
    (p : ℤ × ℤ) (s d : ℤ) (hd : 0 < d)
    (hf : Function.Injective ((E.functor.map g).eInftyMap (s,p.1+s,p.2)).hom)
    (x : ((E.obj A).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj B).sequence.ssData (s+d,p.1+(s+d),p.2)).eInfty) :
    ¬ TowerEssentialExtension M p s d x y := by
  intro h
  obtain ⟨_,ar,br,hab,hx,_⟩ := (tower_extension_iff M p s d x y).mp h.1
  have ha : ((P.filtration A).F s p).arrow ar ∈ P.filtrationSubmodule A s p := by
    have hh : ((P.filtration A).F s p).arrow ar ∈
        ModuleCat.subobjectModule _ ((P.filtration A).F s p) := ⟨ar,rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hh
  have hb : ((P.filtration A).F s p).arrow ar ≫ g ∈ P.filtrationSubmodule B (s+1) p := by
    apply P.filtrationSubmodule_antitone B p (show s+1 ≤ s+d by omega)
    have hh : ((P.filtration A).F s p).arrow ar ≫ g ∈
        ModuleCat.subobjectModule _ ((P.filtration B).F (s+d) p) := ⟨br,hab.symm⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hh
  have hn := next_filtration_of_infinity_injective M p s hf _ ha hb
  have hz : (P.filtration A).toAssociatedGraded s p ar = 0 := by
    have hh := (element_grade_equal_iff (P.filtration A) s p ar 0).mpr (by
      simpa only [map_zero,sub_zero,SyntheticTowerPresentation.filtration,
        OrderIso.apply_symm_apply] using hn)
    simpa only [map_zero] using hh
  have hx0 : x = 0 := (infinityGradedIso ca p s).toLinearEquiv.injective
    (hx.symm.trans (hz.trans (map_zero _).symm))
  subst x
  exact zero_source_not_essential M p s d (by omega) y h

private theorem not_essential_of_target_surjective
    (M : ConvergentMap E g ca.toConvergence cb.toConvergence)
    (p : ℤ × ℤ) (s d : ℤ) (hd : 0 < d)
    (hf : Function.Surjective ((E.functor.map g).eInftyMap (s+d,p.1+(s+d),p.2)).hom)
    (x : ((E.obj A).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj B).sequence.ssData (s+d,p.1+(s+d),p.2)).eInfty) :
    ¬ TowerEssentialExtension M p s d x y := by
  intro h
  obtain ⟨_,ar,br,hab,hx,hy⟩ := (tower_extension_iff M p s d x y).mp h.1
  have hrange : (infinityGradedIso cb p (s+d)).inv
      ((P.filtration B).toAssociatedGraded (s+d) p br) ∈
        Set.range ((E.functor.map g).eInftyMap (s+d,p.1+(s+d),p.2)).hom :=
    hf _
  obtain ⟨c,hc,hbc⟩ := (infinity_image_iff_lift M p (s+d) br).mp hrange
  have hcs := P.filtrationSubmodule_antitone A p (show s ≤ s+d by omega) hc
  have hcs1 := P.filtrationSubmodule_antitone A p (show s+1 ≤ s+d by omega) hc
  let a : BiHom p.1 p.2 A := ((P.filtration A).F s p).arrow ar
  have ha : a ∈ P.filtrationSubmodule A s p := by
    have hh : a ∈ ModuleCat.subobjectModule _ ((P.filtration A).F s p) := ⟨ar,rfl⟩
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hh
  obtain ⟨ar',har'⟩ := filtration_representative_exists P A p s (a-c)
    ((P.filtrationSubmodule A s p).sub_mem ha hcs)
  have hnew : (a-c) ≫ g ∈ P.filtrationSubmodule B (s+d+1) p := by
    simpa only [a,Preadditive.sub_comp,hab] using hbc
  obtain ⟨br',hbr'⟩ := filtration_representative_exists P B p (s+d) ((a-c)≫g)
    (P.filtrationSubmodule_antitone B p (show s+d≤s+d+1 by omega) hnew)
  apply ((tower_essential_iff_no_zero M p s d x y h.1).mp h)
  apply (tower_extension_iff M p s d x 0).mpr
  refine ⟨by omega,ar',br',by rw [har',hbr'],?_,?_⟩
  · have hdiff : ((P.filtration A).F s p).arrow ar -
        ((P.filtration A).F s p).arrow ar' ∈
        ModuleCat.subobjectModule _ ((P.filtration A).F (s+1) p) := by
      rw [har']
      simpa only [a,sub_sub_cancel,SyntheticTowerPresentation.filtration,
        OrderIso.apply_symm_apply] using hcs1
    exact ((element_grade_equal_iff (P.filtration A) s p ar ar').mpr hdiff).symm.trans hx
  · have hdiff : ((P.filtration B).F (s+d) p).arrow br' -
        ((P.filtration B).F (s+d) p).arrow
          (0 : (Subobject.underlying.obj ((P.filtration B).F (s+d) p) : ModuleCat.{v} ℤ)) ∈
        ModuleCat.subobjectModule _ ((P.filtration B).F (s+d+1) p) := by
      rw [hbr',map_zero,sub_zero]
      simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hnew
    have hh := (element_grade_equal_iff (P.filtration B) (s+d) p br' 0).mpr hdiff
    simpa only [map_zero] using hh

end General

private theorem nu_infinity_zero (X : ClassicalObject) (s t w : ℤ) (hw : t < w) :
    IsZero (((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData
      (s,t,w)).eInfty) := by
  haveI : Subsingleton (nuEInftyModel model X (s,t) w) := by
    simp only [nuEInftyModel,show ¬ w ≤ t by omega,ite_false]
    infer_instance
  haveI : Subsingleton (((model.family.nu model.nu (X.obj model.auxiliary)).sequence.ssData
      (s,t,w)).eInfty) :=
    (KIP126.Literature.Standard.eInfinity_nu X (s,t) w).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem rho_nu_infinity_injective (X : ClassicalObject) (n : ℕ) (hn : 0 < n)
    (s t w : ℤ) (hw : t-w < n) :
    Function.Injective ((model.family.quotientProjection
      (model.nu.functor.obj (X.obj model.auxiliary)) n).eInftyMap (s,t,w)) := by
  by_cases hlow : 0 ≤ t-w
  · intro x y hxy
    apply (KIP126.Literature.Standard.infinityNuWindow X (s,t) w (by omega)).injective
    apply subquotientMap_injective (permanentCycles_le_cycles model X (s,t) ((n:ℤ)-t+w))
    have hx := KIP126.Literature.Standard.eInfinity_rho_nu X n hn (s,t) w ⟨hlow,hw⟩ x
    have hy := KIP126.Literature.Standard.eInfinity_rho_nu X n hn (s,t) w ⟨hlow,hw⟩ y
    rw [hxy] at hx
    exact hx.symm.trans hy
  · have hsub := ModuleCat.isZero_iff_subsingleton.mp (nu_infinity_zero X s t w (by omega))
    intro x y _
    exact @Subsingleton.elim _ hsub x y

private theorem rho_finite_no_positive (X : ClassicalObject) (n m : ℕ)
    (hn : 0 < n) (hnm : n ≤ m) (p : ℤ × ℤ) (s d : ℤ) (hd : 0 < d)
    (x : ((model.family.obj ((SyntheticObject.quotient m (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj ((SyntheticObject.quotient n (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
      (s+d,p.1+(s+d),p.2)).eInfty) :
    ¬ TowerEssentialExtension
      (model.convergentMap (.quotient m (.nu X)) (.quotient n (.nu X))
        ((model.quotients.tower _).rho n m hnm)) p s d x y := by
  by_cases hw : p.1+s-p.2 < n
  · exact not_essential_of_source_injective _ p s d hd
      (rho_infty_injective X n m hn hnm s (p.1+s) p.2 hw) x y
  · have hz := Internal.Mahowald.finite_infinity_zero_outside X n hn
      (s+d) (p.1+(s+d)) p.2 (by omega)
    have hsub := ModuleCat.isZero_iff_subsingleton.mp hz
    have hy : y=0 := @Subsingleton.elim _ hsub _ _
    subst y
    exact zero_target_not_essential _ p s d x

private theorem rho_infinite_no_positive (X : ClassicalObject) (n : ℕ)
    (hn : 0 < n) (p : ℤ × ℤ) (s d : ℤ) (hd : 0 < d)
    (x : ((model.family.obj ((SyntheticObject.nu X).obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj ((SyntheticObject.quotient n (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
      (s+d,p.1+(s+d),p.2)).eInfty) :
    ¬ TowerEssentialExtension
      (model.convergentMap (.nu X) (.quotient n (.nu X))
        (XModLambdaN.incl _ n)) p s d x y := by
  by_cases hw : p.1+s-p.2 < n
  · exact not_essential_of_source_injective _ p s d hd
      (rho_nu_infinity_injective X n hn s (p.1+s) p.2 hw) x y
  · have hz := Internal.Mahowald.finite_infinity_zero_outside X n hn
      (s+d) (p.1+(s+d)) p.2 (by omega)
    have hsub := ModuleCat.isZero_iff_subsingleton.mp hz
    have hy : y=0 := @Subsingleton.elim _ hsub _ _
    subst y
    exact zero_target_not_essential _ p s d x

private theorem subquotient_surjective_of_eq {R A : Type*} [Ring R]
    [AddCommGroup A] [Module R A] {Z Z' B B' : Submodule R A}
    (hZ : Z ≤ Z') (hB : B ≤ B') (h : Z=Z') :
    Function.Surjective (subquotientMap hZ hB) := by
  subst Z'
  exact subquotientMap_surjective hB

private theorem finite_lambda_coordinates_surjective (X : ClassicalObject) (m n : ℕ)
    (hnm : n < m) (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < (m-n : ℕ)) :
    Function.Surjective (KIP126.Literature.Standard.infinityFiniteLambda X m n hnm (s,t) w) := by
  have heq : (m:ℤ)-t+(w-n) = (m-n:ℕ)-t+w := by omega
  have hs : Function.Surjective
      (quotientMap model X (c := (m-n:ℕ)-t+w) (c' := (m:ℤ)-t+(w-n))
        (b := 1+t-w) (b' := 1+t-(w-n)) (by omega) (by omega) (s,t)) := by
    exact subquotient_surjective_of_eq _
      (boundaries_monotone model X (s,t) (show 1+t-w ≤ 1+t-(w-n) by omega))
      (congrArg (fun c => cycles model X c (s,t)) heq.symm)
  intro y
  obtain ⟨a,ha⟩ := hs (KIP126.Literature.Standard.infinityFiniteWindow X m (by omega)
    (s,t) (w-n) (by omega) y)
  refine ⟨(KIP126.Literature.Standard.infinityFiniteWindow X (m-n) (by omega)
    (s,t) w hw).symm a,?_⟩
  apply (KIP126.Literature.Standard.infinityFiniteWindow X m (by omega)
    (s,t) (w-n) (by omega)).injective
  rw [KIP126.Literature.Standard.eInfinity_lambda_finite X m n hnm (s,t) w hw]
  simpa only [AddEquiv.apply_symm_apply] using ha

private def lambda_source_infinity_iso (A : SyntheticObject) (n : ℕ) (s t w : ℤ) :
    ((model.family.obj (A.obj model.nu model.auxiliary)).sequence.ssData (s,t,w+n)).eInfty ≅
      ((model.family.obj ((SyntheticObject.shift (0,-(n:ℤ)) A).obj model.nu model.auxiliary)).sequence.ssData
        (s,t,w)).eInfty := by
  simpa only [Prod.fst,Prod.snd,add_sub_cancel_right] using
    (infinityShift model KIP126.Literature.Standard.infinityShift_comparison A n (s,t) (w+n))

private theorem finite_lambda_infinity_surjective (X : ClassicalObject) (m n : ℕ)
    (hn : 0 < n) (hnm : n < m) (s t w : ℤ) (hw : (n:ℤ) ≤ t-w) :
    Function.Surjective ((model.family.map
      ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).triangle hn hnm).lambdaMap).eInftyMap
        (s,t,w)) := by
  by_cases htop : t-w < m
  · have hs := finite_lambda_coordinates_surjective X m n hnm s t (w+n) (by omega)
    have hh : Function.Surjective ((model.family.map
        ((model.quotients.tower (model.nu.functor.obj (X.obj model.auxiliary))).triangle hn hnm).lambdaMap).eInftyMap
          (s,t,(w+n)-n)) := by
      intro y
      obtain ⟨z,hz⟩ := hs y
      refine ⟨(infinityShift model KIP126.Literature.Standard.infinityShift_comparison
        (.quotient (m-n) (.nu X)) n (s,t) (w+n)).hom z,?_⟩
      simpa only [KIP126.Literature.Standard.infinityFiniteLambda,
        InfinityShiftCoordinates.finiteLambdaMap,show ¬ n=0 by omega,↓reduceDIte,
        KIP126.Literature.Standard.infinityShiftData,InfinityShiftCoordinates.shift,
        SyntheticAdamsFamily.quotient,SyntheticObject.obj,ModuleCat.comp_apply] using hz
    have he : w+(n:ℤ)-n=w := by omega
    exact he ▸ hh
  · have hz := Internal.Mahowald.finite_infinity_zero_outside X m (by omega) s t w (by omega)
    have hsub := ModuleCat.isZero_iff_subsingleton.mp hz
    intro y
    exact ⟨0,@Subsingleton.elim _ hsub _ _⟩

private theorem infinite_lambda_infinity_surjective (X : ClassicalObject) (n : ℕ)
    (hn : 0 < n) (s t w : ℤ) (hw : (n:ℤ) ≤ t-w) :
    Function.Surjective ((model.family.map
      (lambdaPow n (model.nu.functor.obj (X.obj model.auxiliary)))).eInftyMap (s,t,w)) := by
  have hs := (ModuleCat.epi_iff_surjective
    (KIP126.Literature.Standard.infinityLambda (.nu X) n (s,t) (w+n))).mp
      (KIP126.Literature.Standard.infinityLambda_epi X n (s,t) (w+n) (by omega))
  have hh : Function.Surjective ((model.family.map
      (lambdaPow n (model.nu.functor.obj (X.obj model.auxiliary)))).eInftyMap (s,t,(w+n)-n)) := by
    intro y
    obtain ⟨z,hz⟩ := hs y
    refine ⟨(infinityShift model KIP126.Literature.Standard.infinityShift_comparison
      (.nu X) n (s,t) (w+n)).hom z,?_⟩
    simpa only [KIP126.Literature.Standard.infinityLambda,
      InfinityShiftCoordinates.lambdaMap,show ¬ n=0 by omega,↓reduceDIte,
      KIP126.Literature.Standard.infinityShiftData,InfinityShiftCoordinates.shift,
      SyntheticObject.obj,ModuleCat.comp_apply] using hz
  have he : w+(n:ℤ)-n=w := by omega
  exact he ▸ hh

private theorem lambda_finite_no_positive (X : ClassicalObject) (n m : ℕ)
    (hn : 0 < n) (hnm : n < m) (p : ℤ × ℤ) (s d : ℤ) (hd : 0 < d)
    (x : ((model.family.obj ((SyntheticObject.shift (0,-(n:ℤ))
      (.quotient (m-n) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj ((SyntheticObject.quotient m (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
      (s+d,p.1+(s+d),p.2)).eInfty) :
    ¬ TowerEssentialExtension
      (model.convergentMap (.shift (0,-(n:ℤ)) (.quotient (m-n) (.nu X))) (.quotient m (.nu X))
        ((model.quotients.tower _).triangle hn hnm).lambdaMap) p s d x y := by
  by_cases hw : (n:ℤ) ≤ p.1+(s+d)-p.2
  · exact not_essential_of_target_surjective _ p s d hd
      (finite_lambda_infinity_surjective X m n hn hnm (s+d) (p.1+(s+d)) p.2 hw) x y
  · have hz := Internal.Mahowald.finite_infinity_zero_outside X (m-n) (by omega)
      s (p.1+s) (p.2+n) (by omega)
    have hsub := ModuleCat.isZero_iff_subsingleton.mp
      (hz.of_iso (lambda_source_infinity_iso (.quotient (m-n) (.nu X)) n s (p.1+s) p.2).symm)
    have hx : x=0 := @Subsingleton.elim _ hsub _ _
    subst x
    exact zero_source_not_essential _ p s d (by omega) y

private theorem lambda_infinite_no_positive (X : ClassicalObject) (n : ℕ)
    (hn : 0 < n) (p : ℤ × ℤ) (s d : ℤ) (hd : 0 < d)
    (x : ((model.family.obj ((SyntheticObject.shift (0,-(n:ℤ)) (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj ((SyntheticObject.nu X).obj model.nu model.auxiliary)).sequence.ssData
      (s+d,p.1+(s+d),p.2)).eInfty) :
    ¬ TowerEssentialExtension
      (model.convergentMap (.shift (0,-(n:ℤ)) (.nu X)) (.nu X)
        (lambdaPow n _)) p s d x y := by
  by_cases hw : (n:ℤ) ≤ p.1+(s+d)-p.2
  · exact not_essential_of_target_surjective _ p s d hd
      (infinite_lambda_infinity_surjective X n hn (s+d) (p.1+(s+d)) p.2 hw) x y
  · have hz := nu_infinity_zero X s (p.1+s) (p.2+n) (by omega)
    have hsub := ModuleCat.isZero_iff_subsingleton.mp
      (hz.of_iso (lambda_source_infinity_iso (.nu X) n s (p.1+s) p.2).symm)
    have hx : x=0 := @Subsingleton.elim _ hsub _ _
    subst x
    exact zero_source_not_essential _ p s d (by omega) y

/-- AimPaper Proposition 4.2 for `0 < n < m < ∞`. The first two clauses
exclude every positive-length essential λ/ρ extension; the last two clauses
identify their length-zero equations with their actual E∞ maps; the final
two clauses exclude crossings of those length-zero equations.
A crossing would require the empty interval `s < u ≤ v ≤ s`. -/
public theorem lambda_rho_extension_collapse_finite (X : ClassicalObject)
    (n m : ℕ) (hn : 0 < n) (hnm : n < m) :
    (∀ (p : ℤ × ℤ) (s d : ℤ)
      (x : ((model.family.obj ((SyntheticObject.shift (0,-(n:ℤ))
        (.quotient (m-n) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData
        (s,p.1+s,p.2)).eInfty)
      (y : ((model.family.obj ((SyntheticObject.quotient m (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
        (s+d,p.1+(s+d),p.2)).eInfty),
      TowerEssentialExtension
        (model.convergentMap (.shift (0,-(n:ℤ)) (.quotient (m-n) (.nu X))) (.quotient m (.nu X))
          ((model.quotients.tower _).triangle hn hnm).lambdaMap) p s d x y → d=0) ∧
    (∀ (p : ℤ × ℤ) (s d : ℤ)
      (x : ((model.family.obj ((SyntheticObject.quotient m (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
        (s,p.1+s,p.2)).eInfty)
      (y : ((model.family.obj ((SyntheticObject.quotient n (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
        (s+d,p.1+(s+d),p.2)).eInfty),
      TowerEssentialExtension
        (model.convergentMap (.quotient m (.nu X)) (.quotient n (.nu X))
          ((model.quotients.tower _).rho n m (Nat.le_of_lt hnm))) p s d x y → d=0) ∧
    (∀ (p : ℤ × ℤ) (s : ℤ)
      (x : ((model.family.obj ((SyntheticObject.shift (0,-(n:ℤ))
        (.quotient (m-n) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData
        (s,p.1+s,p.2)).eInfty),
      TowerExtensionEquation
        (model.convergentMap (.shift (0,-(n:ℤ)) (.quotient (m-n) (.nu X))) (.quotient m (.nu X))
          ((model.quotients.tower _).triangle hn hnm).lambdaMap) p s 0 x
        ((eqToHom (by simp) :
          ((model.family.obj (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) m)).sequence.ssData
            (s,p.1+s,p.2)).eInfty ⟶
          ((model.family.obj (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) m)).sequence.ssData
            (s+0,p.1+(s+0),p.2)).eInfty) ((model.family.map
          ((model.quotients.tower _).triangle hn hnm).lambdaMap).eInftyMap (s,p.1+s,p.2) x))) ∧
    (∀ (p : ℤ × ℤ) (s : ℤ)
      (x : ((model.family.obj ((SyntheticObject.quotient m (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
        (s,p.1+s,p.2)).eInfty),
      TowerExtensionEquation
        (model.convergentMap (.quotient m (.nu X)) (.quotient n (.nu X))
          ((model.quotients.tower _).rho n m (Nat.le_of_lt hnm))) p s 0 x
        ((eqToHom (by simp) :
          ((model.family.obj (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n)).sequence.ssData
            (s,p.1+s,p.2)).eInfty ⟶
          ((model.family.obj (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n)).sequence.ssData
            (s+0,p.1+(s+0),p.2)).eInfty) ((model.family.map
          ((model.quotients.tower _).rho n m (Nat.le_of_lt hnm))).eInftyMap (s,p.1+s,p.2) x))) ∧
    (∀ (p : ℤ × ℤ) (s u v : ℤ), s < u → u ≤ v → v ≤ s →
      ∀ (x : ((model.family.obj ((SyntheticObject.shift (0,-(n:ℤ))
          (.quotient (m-n) (.nu X))).obj model.nu model.auxiliary)).sequence.ssData
          (u,p.1+u,p.2)).eInfty)
        (y : ((model.family.obj ((SyntheticObject.quotient m (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
          (u+(v-u),p.1+(u+(v-u)),p.2)).eInfty),
      ¬ TowerEssentialExtension
        (model.convergentMap (.shift (0,-(n:ℤ)) (.quotient (m-n) (.nu X))) (.quotient m (.nu X))
          ((model.quotients.tower _).triangle hn hnm).lambdaMap) p u (v-u) x y) ∧
    (∀ (p : ℤ × ℤ) (s u v : ℤ), s < u → u ≤ v → v ≤ s →
      ∀ (x : ((model.family.obj ((SyntheticObject.quotient m (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
          (u,p.1+u,p.2)).eInfty)
        (y : ((model.family.obj ((SyntheticObject.quotient n (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
          (u+(v-u),p.1+(u+(v-u)),p.2)).eInfty),
      ¬ TowerEssentialExtension
        (model.convergentMap (.quotient m (.nu X)) (.quotient n (.nu X))
          ((model.quotients.tower _).rho n m (Nat.le_of_lt hnm))) p u (v-u) x y) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro p s d x y h
    have hd := ((tower_extension_iff _ p s d x y).mp h.1).1
    by_contra hne
    exact lambda_finite_no_positive X n m hn hnm p s d (by omega) x y h
  · intro p s d x y h
    have hd := ((tower_extension_iff _ p s d x y).mp h.1).1
    by_contra hne
    exact rho_finite_no_positive X n m hn (Nat.le_of_lt hnm) p s d (by omega) x y h
  · intro p s x
    exact towerExtensionEquation_zero _ p s x
  · intro p s x
    exact towerExtensionEquation_zero _ p s x
  · intro p s u v hsu huv hvs
    omega
  · intro p s u v hsu huv hvs
    omega

/-- AimPaper Proposition 4.2 for `0 < n < m = ∞`, on the actual untruncated
ν object. This has the same λ/ρ collapse and actual length-zero formulas
as the finite statement, without a limiting or completeness hypothesis. -/
public theorem lambda_rho_extension_collapse_infinite (X : ClassicalObject)
    (n : ℕ) (hn : 0 < n) :
    (∀ (p : ℤ × ℤ) (s d : ℤ)
      (x : ((model.family.obj ((SyntheticObject.shift (0,-(n:ℤ)) (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
        (s,p.1+s,p.2)).eInfty)
      (y : ((model.family.obj ((SyntheticObject.nu X).obj model.nu model.auxiliary)).sequence.ssData
        (s+d,p.1+(s+d),p.2)).eInfty),
      TowerEssentialExtension
        (model.convergentMap (.shift (0,-(n:ℤ)) (.nu X)) (.nu X)
          (lambdaPow n _)) p s d x y → d=0) ∧
    (∀ (p : ℤ × ℤ) (s d : ℤ)
      (x : ((model.family.obj ((SyntheticObject.nu X).obj model.nu model.auxiliary)).sequence.ssData
        (s,p.1+s,p.2)).eInfty)
      (y : ((model.family.obj ((SyntheticObject.quotient n (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
        (s+d,p.1+(s+d),p.2)).eInfty),
      TowerEssentialExtension
        (model.convergentMap (.nu X) (.quotient n (.nu X))
          (XModLambdaN.incl _ n)) p s d x y → d=0) ∧
    (∀ (p : ℤ × ℤ) (s : ℤ)
      (x : ((model.family.obj ((SyntheticObject.shift (0,-(n:ℤ)) (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
        (s,p.1+s,p.2)).eInfty),
      TowerExtensionEquation
        (model.convergentMap (.shift (0,-(n:ℤ)) (.nu X)) (.nu X) (lambdaPow n _)) p s 0 x
        ((eqToHom (by simp) :
          ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData
            (s,p.1+s,p.2)).eInfty ⟶
          ((model.family.obj (model.nu.functor.obj (X.obj model.auxiliary))).sequence.ssData
            (s+0,p.1+(s+0),p.2)).eInfty)
          ((model.family.map (lambdaPow n _)).eInftyMap (s,p.1+s,p.2) x))) ∧
    (∀ (p : ℤ × ℤ) (s : ℤ)
      (x : ((model.family.obj ((SyntheticObject.nu X).obj model.nu model.auxiliary)).sequence.ssData
        (s,p.1+s,p.2)).eInfty),
      TowerExtensionEquation
        (model.convergentMap (.nu X) (.quotient n (.nu X)) (XModLambdaN.incl _ n)) p s 0 x
        ((eqToHom (by simp) :
          ((model.family.obj (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n)).sequence.ssData
            (s,p.1+s,p.2)).eInfty ⟶
          ((model.family.obj (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) n)).sequence.ssData
            (s+0,p.1+(s+0),p.2)).eInfty)
          ((model.family.map (XModLambdaN.incl _ n)).eInftyMap (s,p.1+s,p.2) x))) ∧
    (∀ (p : ℤ × ℤ) (s u v : ℤ), s < u → u ≤ v → v ≤ s →
      ∀ (x : ((model.family.obj ((SyntheticObject.shift (0,-(n:ℤ)) (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
          (u,p.1+u,p.2)).eInfty)
        (y : ((model.family.obj ((SyntheticObject.nu X).obj model.nu model.auxiliary)).sequence.ssData
          (u+(v-u),p.1+(u+(v-u)),p.2)).eInfty),
      ¬ TowerEssentialExtension
        (model.convergentMap (.shift (0,-(n:ℤ)) (.nu X)) (.nu X) (lambdaPow n _)) p u (v-u) x y) ∧
    (∀ (p : ℤ × ℤ) (s u v : ℤ), s < u → u ≤ v → v ≤ s →
      ∀ (x : ((model.family.obj ((SyntheticObject.nu X).obj model.nu model.auxiliary)).sequence.ssData
          (u,p.1+u,p.2)).eInfty)
        (y : ((model.family.obj ((SyntheticObject.quotient n (.nu X)).obj model.nu model.auxiliary)).sequence.ssData
          (u+(v-u),p.1+(u+(v-u)),p.2)).eInfty),
      ¬ TowerEssentialExtension
        (model.convergentMap (.nu X) (.quotient n (.nu X)) (XModLambdaN.incl _ n)) p u (v-u) x y) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro p s d x y h
    have hd := ((tower_extension_iff _ p s d x y).mp h.1).1
    by_contra hne
    exact lambda_infinite_no_positive X n hn p s d (by omega) x y h
  · intro p s d x y h
    have hd := ((tower_extension_iff _ p s d x y).mp h.1).1
    by_contra hne
    exact rho_infinite_no_positive X n hn p s d (by omega) x y h
  · intro p s x
    exact towerExtensionEquation_zero _ p s x
  · intro p s x
    exact towerExtensionEquation_zero _ p s x
  · intro p s u v hsu huv hvs
    omega
  · intro p s u v hsu huv hvs
    omega

end
end KIP126.ProofTools.Paper
