module
import all KIP126.ProofTools.GeneralizedMahowald.HSourceSelection
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingFinite
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionDetection
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2200000

private theorem source_detects_reindex (X : ClassicalObject) (q : ℕ) (e s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.shift (0,e) (.nu X))))
      (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x)) a) :
    Detects (model.convergence (.quotient q (.shift (0,e) (.nu X))))
      (s,(t-s)+s,t+e) (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x))
      (homotopyRegrade (by dsimp; omega) rfl a) := by
  have h := detects_transport (show (s,t,t+e)=(s,(t-s)+s,t+e) by simp) _ _ ha
  have comp {A : SyntheticAdamsSS} {i j k : Tridegree} (hij : i=j) (hjk : j=k)
      (z : A.E₂ i) : regradeE2 hjk (regradeE2 hij z)=regradeE2 (hij.trans hjk) z := by
    subst j; subst k; rfl
  rw [comp] at h
  exact h

private theorem extension_at_source_of_normalized_source
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t : ℤ) (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : FiniteExtensionWitness model X Y f r n s t x y)
    (aZ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)))
    (ah : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      ((SyntheticObject.quotient (r-1) (extensionSourceObject model X Y f)).obj model.nu model.auxiliary))
    (hah : Detects (model.convergence (.quotient (r-1) (extensionSourceObject model X Y f)))
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
      (finiteSourceForExtension model X Y f (r-1) s t x)
      (homotopyRegrade (by dsimp; omega) rfl ah))
    (hu : FiniteSourceUnshifts X Y f (r-1) s t aZ ah)
    (hnc : Leibniz.TowerNoCrossing (model.convergentMap
      (.quotient (r-1) (extensionSourceObject model X Y f)) (.quotient (r-1) (.nu Y))
      (finiteExtensionMap model X Y f (r-1)))
      (t-s,t+normalizedExponent model.classicalTower f) s n) :
    FiniteExtensionAtSource X Y f r n s t x y W aZ := by
  let p := (t-s,t+normalizedExponent model.classicalTower f)
  obtain ⟨xs,hxs,ar,har,hgar⟩ := frame_of_source_detects
    (model.convergence (.quotient (r-1) (extensionSourceObject model X Y f))) p s _ ah hah
  have hsame := hxs.unique W.source_rep
  rw [hsame] at hgar
  obtain ⟨br,hab,hgbr⟩ := Leibniz.tower_target_of_any_source_frame
    (model.convergentMap (.quotient (r-1) (extensionSourceObject model X Y f))
      (.quotient (r-1) (.nu Y)) (finiteExtensionMap model X Y f (r-1)))
      p s n W.source W.target W.equation hnc ar hgar
  have ht := source_frame_detects (model.convergence (.quotient (r-1) (.nu Y)))
    p (s+n) W.target _ W.target_rep br hgbr
  rw [←hab,har] at ht
  exact ⟨ah,hah,ht,hu⟩

private theorem transfer_finite_source (X : ClassicalObject) (q : ℕ) (e e' s t : ℤ)
    (he : e=e') (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t+e') (XModLambdaN ((SyntheticCategory.biShift (0,e')).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.shift (0,e') (.nu X))))
      (s,t,t+e') (regradeE2 (by simp) (finiteNuLabel model X q e' s t 0 x)) a) :
    ∃ b : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q),
      Detects (model.convergence (.quotient q (.shift (0,e) (.nu X))))
        (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x)) b ∧
      ((congrArg (fun z : ℤ => BiHom (t-s) (t+z)
          (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
            (model.nu.functor.obj (X.obj model.auxiliary))) q)) he).mp b)=a := by
  subst e'
  exact ⟨a,ha,rfl⟩

private theorem shift_class_sub (δ p : ℤ×ℤ) {A : SyntheticSpectrum}
    (a b : BiHom p.1 p.2 A) :
    shiftHomotopyClass δ p (a-b)=shiftHomotopyClass δ p a-shiftHomotopyClass δ p b := by
  simp only [shiftHomotopyClass,Functor.map_sub,Preadditive.comp_sub]

private theorem homotopy_regrade_sub {A : SyntheticSpectrum} {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') (a b : BiHom m w A) :
    homotopyRegrade hm hw (a-b)=homotopyRegrade hm hw a-homotopyRegrade hm hw b := by
  subst m'; subst w'; rfl

private theorem finite_extension_at_source_minimal_positive
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t : ℤ) (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : FiniteExtensionWitness model X Y f r n s t x y)
    (hn : n ≤ normalizedExponent model.classicalTower f)
    (he : normalizedExponent model.classicalTower f=1)
    (aZ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)))
    (haZ : Detects (model.convergence (.quotient (r-1) (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X (r-1) s t 0 x)) aZ) :
    FiniteExtensionAtSource X Y f r n s t x y W aZ := by
  let p := (t-s,t+normalizedExponent model.classicalTower f)
  obtain ⟨_,ar,br,hab,hax,hby⟩ := (tower_extension_iff _ p s n W.source W.target).mp W.equation
  let ah : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      ((SyntheticObject.quotient (r-1) (extensionSourceObject model X Y f)).obj model.nu model.auxiliary) := ((model.syntheticTower.filtration
    ((SyntheticObject.quotient (r-1) (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).F s p).arrow ar
  have hsource := source_frame_detects
    (model.convergence (.quotient (r-1) (extensionSourceObject model X Y f))) p s
    W.source _ W.source_rep ar hax
  have htarget := source_frame_detects (model.convergence (.quotient (r-1) (.nu Y))) p (s+n)
    W.target _ W.target_rep br hby
  rw [←hab] at htarget
  change Detects (model.convergence (.quotient (r-1) (extensionSourceObject model X Y f)))
    (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
    (finiteSourceForExtension model X Y f (r-1) s t x)
    (homotopyRegrade (by dsimp; omega) rfl ah) at hsource
  have source_reindex (e : ℤ)
      (a : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (r-1)))
      (ha : Detects (model.convergence (.quotient (r-1) (.shift (0,e) (.nu X))))
        (s,(t-s)+s,t+e) (regradeE2 (by simp) (finiteNuLabel model X (r-1) e s t 0 x))
        (homotopyRegrade (by dsimp; omega) rfl a)) :
      Detects (model.convergence (.quotient (r-1) (.shift (0,e) (.nu X))))
        (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel model X (r-1) e s t 0 x)) a := by
    have H := detects_transport
      (show (s,(t-s)+s,t+e)=(s,t,t+e) by congr 2; omega) _ _ ha
    have e2_comp {A : SyntheticAdamsSS} {u v w : Tridegree}
        (huv : u=v) (hvw : v=w) (z : A.E₂ u) :
        regradeE2 hvw (regradeE2 huv z)=regradeE2 (huv.trans hvw) z := by
      subst v; subst w; rfl
    have hcomp {m m' m'' w w' w'' : ℤ} {A : SyntheticSpectrum}
        (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
        (b : BiHom m w A) :
        homotopyRegrade hm' hw' (homotopyRegrade hm hw b) =
          homotopyRegrade (hm.trans hm') (hw.trans hw') b := by
      subst m'; subst m''; subst w'; subst w''; rfl
    rw [e2_comp,hcomp] at H
    exact H
  have hs0 := source_reindex (normalizedExponent model.classicalTower f) ah hsource
  have heZ : (normalizedExponent model.classicalTower f : ℤ)=1 := by omega
  have cast_source (e : ℤ) (heZ : e=1)
      (a : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (r-1)))
      (ha : Detects (model.convergence (.quotient (r-1) (.shift (0,e) (.nu X))))
        (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel model X (r-1) e s t 0 x)) a) :
      Detects (model.convergence (.quotient (r-1) (.shift (0,1) (.nu X))))
        (s,t,t+1) (regradeE2 (by simp) (finiteNuLabel model X (r-1) 1 s t 0 x))
        ((congrArg (fun z : ℤ => BiHom (t-s) (t+z) (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) (r-1))) heZ).mp a) := by
    subst e
    exact ha
  let ah1 : BiHom (t-s) (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (r-1)) := by
    exact ((congrArg (fun z : ℤ => BiHom (t-s) (t+z) (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (r-1))) heZ).mp ah)
  have hsource1 : Detects (model.convergence (.quotient (r-1) (.shift (0,1) (.nu X))))
      (s,t,t+1) (regradeE2 (by simp) (finiteNuLabel model X (r-1) 1 s t 0 x)) ah1 := by
    exact cast_source _ heZ ah hs0
  obtain ⟨ε,hε,a₀,_,ha₀,hback⟩ := positive_finite_source_unshifted X (r-1)
    (by have := W.page_ge_two; omega) s t x ah1 hsource1
  change homotopyRegrade (by simp) rfl
    (shiftHomotopyClass (0,1) (t-s,t) a₀)≫ε.inv=ah1 at hback
  let ahNew : BiHom (t-s) (t+1) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (r-1)) :=
    homotopyRegrade (by simp) rfl (shiftHomotopyClass (0,1) (t-s,t) aZ)≫ε.inv
  have hd := detects_sub_filtration (model.convergence (.quotient (r-1) (.nu X)))
    (s,t,t) haZ ha₀
  have hshift := (Leibniz.shift_filtration_iff (.quotient (r-1) (.nu X))
    (0,1) (t-s,t) (s+1) (aZ-a₀)).mpr hd
  have hshift' : FiltrationAtLeast model.syntheticTower (s+1)
      (homotopyRegrade (m' := t-s) (w' := t+1) (by simp) rfl
        (shiftHomotopyClass (0,1) (t-s,t) (aZ-a₀))) :=
    (Leibniz.regrade_filtration_iff _ _ _ _).mpr hshift
  have hmap := map_preserves_filtration (model.convergentMap
    (.shift (0,1) (.quotient (r-1) (.nu X)))
    (.quotient (r-1) (.shift (0,1) (.nu X))) ε.inv)
    (t-s,t+1) (s+1) _ hshift'
  have hdiff : FiltrationAtLeast model.syntheticTower (s+1) (ahNew-ah1) := by
    rw [←hback]
    dsimp only [ahNew]
    rw [←Preadditive.sub_comp,←homotopy_regrade_sub,←shift_class_sub]
    exact hmap
  have hNew := detects_of_high_difference (.quotient (r-1) (.shift (0,1) (.nu X)))
    (s,t,t+1) _ ah1 ahNew hsource1 hdiff
  obtain ⟨ahActual,hahActual,hcast⟩ := transfer_finite_source X (r-1)
    (normalizedExponent model.classicalTower f) 1 s t heZ x ahNew hNew
  apply extension_at_source_of_normalized_source X Y f r n s t x y W aZ ahActual
  · exact source_detects_reindex X (r-1) _ s t x ahActual hahActual
  · exact Or.inr ⟨he,ε,hε,hcast.symm⟩
  · exact Leibniz.minimal_length_finite_tower_no_crossing X Y f (r-1)
      (by have := W.page_ge_two; omega) s t n hn

private theorem finite_extension_at_source_minimal_zero
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t : ℤ) (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : FiniteExtensionWitness model X Y f r n s t x y)
    (hn : n ≤ normalizedExponent model.classicalTower f)
    (he : normalizedExponent model.classicalTower f=0)
    (aZ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)))
    (haZ : Detects (model.convergence (.quotient (r-1) (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X (r-1) s t 0 x)) aZ) :
    FiniteExtensionAtSource X Y f r n s t x y W aZ := by
  let p := (t-s,t+normalizedExponent model.classicalTower f)
  obtain ⟨_,ar,br,hab,hax,hby⟩ := (tower_extension_iff _ p s n W.source W.target).mp W.equation
  let ah : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      ((SyntheticObject.quotient (r-1) (extensionSourceObject model X Y f)).obj model.nu model.auxiliary) := ((model.syntheticTower.filtration
    ((SyntheticObject.quotient (r-1) (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).F s p).arrow ar
  have hsource := source_frame_detects
    (model.convergence (.quotient (r-1) (extensionSourceObject model X Y f))) p s
    W.source _ W.source_rep ar hax
  have htarget := source_frame_detects (model.convergence (.quotient (r-1) (.nu Y))) p (s+n)
    W.target _ W.target_rep br hby
  rw [←hab] at htarget
  change Detects (model.convergence (.quotient (r-1) (extensionSourceObject model X Y f)))
    (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
    (finiteSourceForExtension model X Y f (r-1) s t x)
    (homotopyRegrade (by dsimp; omega) rfl ah) at hsource
  have source_reindex (e : ℤ)
      (a : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (r-1)))
      (ha : Detects (model.convergence (.quotient (r-1) (.shift (0,e) (.nu X))))
        (s,(t-s)+s,t+e) (regradeE2 (by simp) (finiteNuLabel model X (r-1) e s t 0 x))
        (homotopyRegrade (by dsimp; omega) rfl a)) :
      Detects (model.convergence (.quotient (r-1) (.shift (0,e) (.nu X))))
        (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel model X (r-1) e s t 0 x)) a := by
    have H := detects_transport
      (show (s,(t-s)+s,t+e)=(s,t,t+e) by congr 2; omega) _ _ ha
    have e2_comp {A : SyntheticAdamsSS} {u v w : Tridegree}
        (huv : u=v) (hvw : v=w) (z : A.E₂ u) :
        regradeE2 hvw (regradeE2 huv z)=regradeE2 (huv.trans hvw) z := by
      subst v; subst w; rfl
    have hcomp {m m' m'' w w' w'' : ℤ} {A : SyntheticSpectrum}
        (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
        (b : BiHom m w A) :
        homotopyRegrade hm' hw' (homotopyRegrade hm hw b) =
          homotopyRegrade (hm.trans hm') (hw.trans hw') b := by
      subst m'; subst m''; subst w'; subst w''; rfl
    rw [e2_comp,hcomp] at H
    exact H
  have hs0 := source_reindex (normalizedExponent model.classicalTower f) ah hsource
  have heZ : (normalizedExponent model.classicalTower f : ℤ)=0 := by omega
  have cast_source (e : ℤ) (heZ : e=0)
      (a : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) (r-1)))
      (ha : Detects (model.convergence (.quotient (r-1) (.shift (0,e) (.nu X))))
        (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel model X (r-1) e s t 0 x)) a) :
      Detects (model.convergence (.quotient (r-1) (.shift (0,0) (.nu X))))
        (s,t,t+0) (regradeE2 (by simp) (finiteNuLabel model X (r-1) 0 s t 0 x))
        ((congrArg (fun z : ℤ => BiHom (t-s) (t+z) (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) (r-1))) heZ).mp a) := by
    subst e
    exact ha
  let ah1 : BiHom (t-s) (t+0) (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (r-1)) := by
    exact ((congrArg (fun z : ℤ => BiHom (t-s) (t+z) (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (r-1))) heZ).mp ah)
  have hsource1 : Detects (model.convergence (.quotient (r-1) (.shift (0,0) (.nu X))))
      (s,t,t+0) (regradeE2 (by simp) (finiteNuLabel model X (r-1) 0 s t 0 x)) ah1 := by
    exact cast_source _ heZ ah hs0
  obtain ⟨a₀,_,ha₀,hback⟩ := zero_finite_source_unshifted X (r-1)
    (by have := W.page_ge_two; omega) s t x ah1 hsource1
  change homotopyRegrade rfl (show t=t+0 by simp) a₀≫
    XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) (r-1)=ah1 at hback
  let ahNew : BiHom (t-s) (t+0) (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) (r-1)) :=
    homotopyRegrade rfl (by simp) aZ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) (r-1)
  have hd := detects_sub_filtration (model.convergence (.quotient (r-1) (.nu X)))
    (s,t,t) haZ ha₀
  have hshift' : FiltrationAtLeast model.syntheticTower (s+1)
      (homotopyRegrade rfl (show t=t+0 by simp) (aZ-a₀)) :=
    (Leibniz.regrade_filtration_iff _ _ _ _).mpr hd
  have hmap := map_preserves_filtration (model.convergentMap
    (.quotient (r-1) (.nu X)) (.quotient (r-1) (.shift (0,0) (.nu X)))
    (XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) (r-1)))
    (t-s,t+0) (s+1) _ hshift'
  have hdiff : FiltrationAtLeast model.syntheticTower (s+1) (ahNew-ah1) := by
    rw [←hback]
    dsimp only [ahNew]
    rw [←Preadditive.sub_comp,←homotopy_regrade_sub]
    exact hmap
  have hNew := detects_of_high_difference (.quotient (r-1) (.shift (0,0) (.nu X)))
    (s,t,t+0) _ ah1 ahNew hsource1 hdiff
  obtain ⟨ahActual,hahActual,hcast⟩ := transfer_finite_source X (r-1)
    (normalizedExponent model.classicalTower f) 0 s t heZ x ahNew hNew
  apply extension_at_source_of_normalized_source X Y f r n s t x y W aZ ahActual
  · exact source_detects_reindex X (r-1) _ s t x ahActual hahActual
  · exact Or.inl ⟨he,hcast.symm⟩
  · exact Leibniz.minimal_length_finite_tower_no_crossing X Y f (r-1)
      (by have := W.page_ge_two; omega) s t n hn

/-- At the normalization length, every prescribed detecting source has the
original finite extension's specified target. The normalized source is rebuilt
from that same source and its exact inverse-shift relation is retained. -/
private theorem finite_extension_at_source_minimal
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t : ℤ) (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : FiniteExtensionWitness model X Y f r n s t x y)
    (hn : n ≤ normalizedExponent model.classicalTower f)
    (aZ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)))
    (haZ : Detects (model.convergence (.quotient (r-1) (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X (r-1) s t 0 x)) aZ) :
    FiniteExtensionAtSource X Y f r n s t x y W aZ := by
  by_cases he : normalizedExponent model.classicalTower f=0
  · exact finite_extension_at_source_minimal_zero X Y f r n s t x y W hn he aZ haZ
  · have he1 : normalizedExponent model.classicalTower f=1 := by
      have := normalizedExponent_le_one model.classicalTower f
      omega
    exact finite_extension_at_source_minimal_positive X Y f r n s t x y W hn he1 aZ haZ

end
end KIP126.ProofTools.Internal.Mahowald
