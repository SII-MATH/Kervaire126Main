module

import all KIP126.ProofTools.Paper.ExtensionIndeterminacy

/-! Private essential-source extraction for the corrected Proposition 6.20.
The specified target and the actual filtered map are retained throughout. -/

@[expose] section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace KIP126.ProofTools.Paper
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.ProofTools.Internal
noncomputable section
universe u v

section Tower
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

/-- Among all higher source representatives hitting a fixed nonzero target,
choose one of maximal source filtration. It gives an essential extension. -/
private theorem tower_essential_shorter_same_target
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ) (hn : 0<n)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((F.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (h : TowerExtensionEquation M p s n x y)
    (hy : y≠0) (hne : ¬TowerEssentialExtension M p s n x y) :
    ∃ a : ℕ, 0<a ∧ (a:ℤ)≤n ∧
      ∃ z : ((F.obj X).sequence.ssData (s+a,p.1+(s+a),p.2)).eInfty,
        TowerEssentialExtension M p (s+a) (n-a) z
          ((eqToHom (congrArg (fun d =>
            ((F.obj Y).sequence.ssData (d,p.1+d,p.2)).eInfty)
            (show s+n=(s+a)+(n-a) by omega))) y) := by
  classical
  let Pred (a : ℕ) : Prop := 0<a ∧ a≤n.toNat ∧ ∃
    (ar : (Subobject.underlying.obj ((P.filtration X).F (s+a) p) : ModuleCat.{v} ℤ))
    (br : (Subobject.underlying.obj ((P.filtration Y).F (s+n) p) : ModuleCat.{v} ℤ)),
    ((P.filtration X).F (s+a) p).arrow ar ≫ g =
      ((P.filtration Y).F (s+n) p).arrow br ∧
    (P.filtration Y).toAssociatedGraded (s+n) p br =
      (infinityGradedIso cy p (s+n)).hom y
  obtain ⟨_,ar1,br1,heq1,hbr1⟩ :=
    (tower_inessential_iff_higher_source_same_target M p s n x y h).mp hne
  have hp1 : Pred 1 := ⟨by decide,by omega,ar1,br1,heq1,hbr1⟩
  let a := Nat.findGreatest Pred n.toNat
  obtain ⟨ha,han,ar,br,heq,hbr⟩ := Nat.findGreatest_spec (P:=Pred)
    (show 1≤n.toNat by omega) hp1
  let I := infinityGradedIso cx p (s+a)
  let z := I.inv ((P.filtration X).toAssociatedGraded (s+a) p ar)
  have haz : (P.filtration X).toAssociatedGraded (s+a) p ar = I.hom z :=
    (I.toLinearEquiv.apply_symm_apply _).symm
  have he : TowerExtensionEquation M p (s+a) (n-a) z
      ((eqToHom (congrArg (fun d =>
        ((F.obj Y).sequence.ssData (d,p.1+d,p.2)).eInfty)
        (show s+n=(s+a)+(n-a) by omega))) y) :=
    (tower_extension_reindexed M p (s+a) (n-a) (s+n) (by omega) z y).mpr
      ⟨by omega,ar,br,heq,haz,hbr⟩
  refine ⟨a,ha,by omega,z,?_⟩
  by_contra hnot
  have he0 := (tower_inessential_iff_zero_source_same_target M p (s+a) (n-a)
    z _ he).mp hnot
  obtain ⟨_,ar0,br0,heq0,har0,hbr0⟩ :=
    (tower_extension_reindexed M p (s+a) (n-a) (s+n) (by omega) 0 y).mp he0
  have hzero : (P.filtration X).toAssociatedGraded (s+a) p ar0=0 := by
    simpa only [map_zero] using har0
  have hmem : ((P.filtration X).F (s+a) p).arrow ar0 ∈
      P.filtrationSubmodule X (s+a+1) p := by
    have hh := ((P.filtration X).toAssociatedGraded_eq_zero_iff (s+a) p ar0).mp hzero
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hh
  have hanext : a+1≤n.toNat := by
    by_contra hgt
    have hae : (a:ℤ)=n := by omega
    have hhigh := map_preserves_filtration M p (s+a+1)
      (((P.filtration X).F (s+a) p).arrow ar0) hmem
    have htarget : ((P.filtration Y).F (s+n) p).arrow br0 ∈
        ModuleCat.subobjectModule _ ((P.filtration Y).F (s+n+1) p) := by
      rw [←heq0]
      simpa only [hae,SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hhigh
    have hbzero := ((P.filtration Y).toAssociatedGraded_eq_zero_iff (s+n) p br0).mpr htarget
    apply hy
    apply (infinityGradedIso cy p (s+n)).toLinearEquiv.injective
    change (infinityGradedIso cy p (s+n)).hom y =
      (infinityGradedIso cy p (s+n)).hom 0
    rw [←hbr0,map_zero,hbzero]
  have hmem' : ((P.filtration X).F (s+a) p).arrow ar0 ∈
      P.filtrationSubmodule X (s+((a+1:ℕ):ℤ)) p := by
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hmem
  obtain ⟨arn,harn⟩ := filtration_representative_exists P X p (s+((a+1:ℕ):ℤ))
    (((P.filtration X).F (s+a) p).arrow ar0) hmem'
  have hpnext : Pred (a+1) := by
    refine ⟨by omega,hanext,arn,br0,?_,hbr0⟩
    rw [harn]
    exact heq0
  have hamax := Nat.le_findGreatest (P:=Pred) hanext hpnext
  change a+1≤a at hamax
  omega

end Tower

open KIP126.Classical.Adams KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal.Leibniz

/-- The actual finite normalized map admits an essential higher-source
extension to the same nonzero target. Its source is labelled by a classical
cycle in the precise finite quotient window. -/
private theorem finiteExtension_essential_shorter_source (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t : ℤ) (x y)
    (W : FiniteExtensionWitness model X Y f r n s t x y)
    (hy : W.target≠0) (hne : ¬W.Essential) :
    ∃ a : ℕ, 0<a ∧
      (a:ℤ)≤n-normalizedExponent model.classicalTower f ∧
      ∃ x' : Ambient model X (s+a,(t-s)+(s+a)),
        x' ∈ cycles model X (((r-1:ℕ):ℤ)-(a:ℤ)) (s+a,(t-s)+(s+a)) ∧
        ∃ z,
          HasInfinityRepresentative _ 2 _
            (finiteExtensionCorrectionLabel X Y f (r-1) s t a x') z ∧
          TowerEssentialExtension (model.convergentMap
            (.quotient (r-1) (extensionSourceObject model X Y f))
            (.quotient (r-1) (.nu Y)) (finiteExtensionMap model X Y f (r-1)))
            (t-s,t+normalizedExponent model.classicalTower f) (s+a) (n-a) z
            ((eqToHom (congrArg (fun d =>
              ((model.family.obj ((SyntheticObject.quotient (r-1) (.nu Y)).obj
                model.nu model.auxiliary)).sequence.ssData
                (d,(t-s)+d,t+normalizedExponent model.classicalTower f)).eInfty)
              (show s+n=(s+a)+(n-a) by omega))) W.target) := by
  let p : ℤ × ℤ := (t-s,t+normalizedExponent model.classicalTower f)
  let M := model.convergentMap
    (.quotient (r-1) (extensionSourceObject model X Y f))
    (.quotient (r-1) (.nu Y)) (finiteExtensionMap model X Y f (r-1))
  have hstrict := inessential_length_strict X Y f r n s t x y W hy hne
  have hn : 0<n := by omega
  obtain ⟨a,ha,han,z,hess⟩ := tower_essential_shorter_same_target M p s n hn
    W.source W.target W.equation hy hne
  have hq : 0<r-1 := by have := W.page_ge_two; omega
  have htargetbound : s+(a:ℤ)+normalizedExponent model.classicalTower f ≤ s+n := by
    have H := finite_crossing_target_bound X Y f (r-1) hq s t (s+a) (s+n)
      (by omega) (by omega)
    have hlen : (s+n)-(s+(a:ℤ))=n-a := by omega
    rw [hlen] at H
    exact H z _ hess
  have han' : (a:ℤ)≤n-normalizedExponent model.classicalTower f := by omega
  have haq : a<r-1 := by have := W.length_upper; have := W.page_ge_two; omega
  obtain ⟨x',hx',hz⟩ := correction_label_exists X Y f (r-1) hq s t a haq z
  exact ⟨a,ha,han',x',hx',z,hz,hess⟩

end
end KIP126.ProofTools.Paper

#print axioms KIP126.ProofTools.Paper.tower_essential_shorter_same_target
#print axioms KIP126.ProofTools.Paper.finiteExtension_essential_shorter_source
