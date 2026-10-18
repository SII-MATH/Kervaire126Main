module
import all KIP126.ProofTools.GeneralizedMahowald.HSource
import all KIP126.ProofTools.GeneralizedMahowald.Synchronization
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

private theorem finite_extension_source_sync_positive
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r q : ℕ) (hq : 0<q) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : FiniteExtensionWitness model X Y f r n s t x y)
    (he : normalizedExponent model.classicalTower f = 1)
    (hnc : NoCrossingOn model X ((r-1:ℕ)+q) r (s,t))
    (aZ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)))
    (haZ : Detects (model.convergence (.quotient (r-1) (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X (r-1) s t 0 x)) aZ) :
    ∃ ah : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
        ((SyntheticObject.quotient (r-1) (extensionSourceObject model X Y f)).obj model.nu model.auxiliary),
      Detects (model.convergence (.quotient (r-1) (extensionSourceObject model X Y f)))
        (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
        (finiteSourceForExtension model X Y f (r-1) s t x)
        (homotopyRegrade (by dsimp; omega) rfl ah) ∧
      Detects (model.convergence (.quotient (r-1) (.nu Y)))
        (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f)
        (finiteTargetForExtension model X Y f (r-1) n s t W.length_lower y)
        (homotopyRegrade (by dsimp; omega) rfl (ah≫finiteExtensionMap model X Y f (r-1))) ∧
      ∃ ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) (r-1) ≅
        (SyntheticCategory.biShift (0,1)).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)),
        XModLambdaN.incl _ (r-1)≫ε.hom =
          (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (r-1)) ∧
        ∃ a₀ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)),
          Detects (model.convergence (.quotient (r-1) (.nu X))) (s,t,t)
            (regradeE2 (by simp) (finiteTargetLabel model X (r-1) s t 0 x)) a₀ ∧
          a₀ ≫ ((model.quotients.tower _).triangle
            (show 0<r-1 by have := W.page_ge_two; omega)
            (show r-1<r-1+q by omega)).delta =
            aZ ≫ ((model.quotients.tower _).triangle
              (show 0<r-1 by have := W.page_ge_two; omega)
              (show r-1<r-1+q by omega)).delta ∧
          homotopyRegrade (show ((t-s,t)+(0,1)).1=t-s by simp)
            (show ((t-s,t)+(0,1)).2=t+1 by rfl) (shiftHomotopyClass (0,1) (t-s,t) a₀)≫ε.inv =
            ((congrArg (fun z : ℤ => BiHom (t-s) (t+z)
              (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
                (model.nu.functor.obj (X.obj model.auxiliary))) (r-1)))
              (show (normalizedExponent model.classicalTower f : ℤ)=1 by omega)).mp ah) := by
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
  have hnc' : NoCrossingOn model X ((r-1:ℕ)+q) ((r-1:ℕ)+1) (s,t) := by
    have hr := W.page_ge_two
    convert hnc using 1
    omega
  have hδ := relative_boundary_equal_of_no_crossing X (r-1) q
    (by have := W.page_ge_two; omega) hq s t hnc' a₀ aZ
    (detects_sub_filtration (model.convergence (.quotient (r-1) (.nu X))) (s,t,t) ha₀ haZ)
  exact ⟨ah,hsource,htarget,ε,hε,a₀,ha₀,hδ,hback⟩

private theorem finite_extension_source_sync_zero
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r q : ℕ) (hq : 0<q) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : FiniteExtensionWitness model X Y f r n s t x y)
    (he : normalizedExponent model.classicalTower f = 0)
    (hnc : NoCrossingOn model X ((r-1:ℕ)+q) r (s,t))
    (aZ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)))
    (haZ : Detects (model.convergence (.quotient (r-1) (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X (r-1) s t 0 x)) aZ) :
    ∃ ah : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
        ((SyntheticObject.quotient (r-1) (extensionSourceObject model X Y f)).obj model.nu model.auxiliary),
      Detects (model.convergence (.quotient (r-1) (extensionSourceObject model X Y f)))
        (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
        (finiteSourceForExtension model X Y f (r-1) s t x)
        (homotopyRegrade (by dsimp; omega) rfl ah) ∧
      Detects (model.convergence (.quotient (r-1) (.nu Y)))
        (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f)
        (finiteTargetForExtension model X Y f (r-1) n s t W.length_lower y)
        (homotopyRegrade (by dsimp; omega) rfl (ah≫finiteExtensionMap model X Y f (r-1))) ∧
      ∃ a₀ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)),
          Detects (model.convergence (.quotient (r-1) (.nu X))) (s,t,t)
            (regradeE2 (by simp) (finiteTargetLabel model X (r-1) s t 0 x)) a₀ ∧
          a₀ ≫ ((model.quotients.tower _).triangle
            (show 0<r-1 by have := W.page_ge_two; omega)
            (show r-1<r-1+q by omega)).delta =
            aZ ≫ ((model.quotients.tower _).triangle
              (show 0<r-1 by have := W.page_ge_two; omega)
              (show r-1<r-1+q by omega)).delta ∧
          homotopyRegrade rfl (show t=t+0 by simp) a₀≫
            XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) (r-1) =
            ((congrArg (fun z : ℤ => BiHom (t-s) (t+z)
              (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
                (model.nu.functor.obj (X.obj model.auxiliary))) (r-1)))
              (show (normalizedExponent model.classicalTower f : ℤ)=0 by omega)).mp ah) := by
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
  have hnc' : NoCrossingOn model X ((r-1:ℕ)+q) ((r-1:ℕ)+1) (s,t) := by
    have hr := W.page_ge_two
    convert hnc using 1
    omega
  have hδ := relative_boundary_equal_of_no_crossing X (r-1) q
    (by have := W.page_ge_two; omega) hq s t hnc' a₀ aZ
    (detects_sub_filtration (model.convergence (.quotient (r-1) (.nu X))) (s,t,t) ha₀ haZ)
  exact ⟨ah,hsource,htarget,a₀,ha₀,hδ,hback⟩

/- Records the actual inverse shift, separately at the two possible
normalized exponents. This is a conclusion, never an added hypothesis. -/
private def FiniteSourceUnshifts
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (k : ℕ) (s t : ℤ)
    (a₀ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) k))
    (ah : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      ((SyntheticObject.quotient k (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)) : Prop :=
    (∃ he : normalizedExponent model.classicalTower f = 0,
      homotopyRegrade rfl (show t=t+0 by simp) a₀≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) k =
        ((congrArg (fun z : ℤ => BiHom (t-s) (t+z)
          (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
            (model.nu.functor.obj (X.obj model.auxiliary))) k))
          (show (normalizedExponent model.classicalTower f : ℤ)=0 by omega)).mp ah)) ∨
    (∃ he : normalizedExponent model.classicalTower f = 1,
      ∃ ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) k ≅
        (SyntheticCategory.biShift (0,1)).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) k),
        XModLambdaN.incl _ k≫ε.hom =
          (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ k) ∧
        homotopyRegrade (show ((t-s,t)+(0,1)).1=t-s by simp)
          (show ((t-s,t)+(0,1)).2=t+1 by rfl)
          (shiftHomotopyClass (0,1) (t-s,t) a₀)≫ε.inv =
          ((congrArg (fun z : ℤ => BiHom (t-s) (t+z)
            (XModLambdaN ((SyntheticCategory.biShift (0,z)).obj
              (model.nu.functor.obj (X.obj model.auxiliary))) k))
            (show (normalizedExponent model.classicalTower f : ℤ)=1 by omega)).mp ah))

private def FiniteExtensionAtSource
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : FiniteExtensionWitness model X Y f r n s t x y)
    (a₀ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1))) : Prop :=
    ∃ ah : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
        ((SyntheticObject.quotient (r-1) (extensionSourceObject model X Y f)).obj model.nu model.auxiliary),
      Detects (model.convergence (.quotient (r-1) (extensionSourceObject model X Y f)))
        (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
        (finiteSourceForExtension model X Y f (r-1) s t x)
        (homotopyRegrade (by dsimp; omega) rfl ah) ∧
      Detects (model.convergence (.quotient (r-1) (.nu Y)))
        (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f)
        (finiteTargetForExtension model X Y f (r-1) n s t W.length_lower y)
        (homotopyRegrade (by dsimp; omega) rfl (ah≫finiteExtensionMap model X Y f (r-1))) ∧
      FiniteSourceUnshifts X Y f (r-1) s t a₀ ah

private theorem finite_extension_source_sync
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r q : ℕ) (hq : 0<q) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : FiniteExtensionWitness model X Y f r n s t x y)
    (hnc : NoCrossingOn model X ((r-1:ℕ)+q) r (s,t))
    (aZ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)))
    (haZ : Detects (model.convergence (.quotient (r-1) (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X (r-1) s t 0 x)) aZ) :
    ∃ a₀ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)),
      Detects (model.convergence (.quotient (r-1) (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel model X (r-1) s t 0 x)) a₀ ∧
      a₀ ≫ ((model.quotients.tower _).triangle
        (show 0<r-1 by have := W.page_ge_two; omega)
        (show r-1<r-1+q by omega)).delta =
        aZ ≫ ((model.quotients.tower _).triangle
          (show 0<r-1 by have := W.page_ge_two; omega)
          (show r-1<r-1+q by omega)).delta ∧
      FiniteExtensionAtSource X Y f r n s t x y W a₀ := by
  by_cases he : normalizedExponent model.classicalTower f = 0
  · obtain ⟨ah,hs,ht,a₀,ha₀,hδ,hback⟩ :=
      finite_extension_source_sync_zero X Y f r q hq n s t x y W he hnc aZ haZ
    exact ⟨a₀,ha₀,hδ,ah,hs,ht,Or.inl ⟨he,hback⟩⟩
  · have he1 : normalizedExponent model.classicalTower f = 1 := by
      have := normalizedExponent_le_one model.classicalTower f
      omega
    obtain ⟨ah,hs,ht,ε,hε,a₀,ha₀,hδ,hback⟩ :=
      finite_extension_source_sync_positive X Y f r q hq n s t x y W he1 hnc aZ haZ
    exact ⟨a₀,ha₀,hδ,ah,hs,ht,Or.inr ⟨he1,ε,hε,hback⟩⟩

/- This selects the actual source which the later geometry should consume.
The original source is retained when the differential no-crossing branch
is unavailable. The retained extension assertion is then conditional on
that original branch, rather than an extra unproved condition. -/
private theorem select_finite_extension_source
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r q : ℕ) (hq : 0<q) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : FiniteExtensionWitness model X Y f r n s t x y)
    (aZ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)))
    (haZ : Detects (model.convergence (.quotient (r-1) (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X (r-1) s t 0 x)) aZ) :
    ∃ a₀ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (r-1)),
      Detects (model.convergence (.quotient (r-1) (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel model X (r-1) s t 0 x)) a₀ ∧
      a₀ ≫ ((model.quotients.tower _).triangle
        (show 0<r-1 by have := W.page_ge_two; omega)
        (show r-1<r-1+q by omega)).delta =
        aZ ≫ ((model.quotients.tower _).triangle
          (show 0<r-1 by have := W.page_ge_two; omega)
          (show r-1<r-1+q by omega)).delta ∧
      (NoCrossingOn model X ((r-1:ℕ)+q) r (s,t) →
        FiniteExtensionAtSource X Y f r n s t x y W a₀) := by
  by_cases hnc : NoCrossingOn model X ((r-1:ℕ)+q) r (s,t)
  · obtain ⟨a₀,ha₀,hδ,hext⟩ := finite_extension_source_sync X Y f r q hq n s t x y W hnc aZ haZ
    exact ⟨a₀,ha₀,hδ,fun _ => hext⟩
  · exact ⟨aZ,haZ,rfl,fun h => (hnc h).elim⟩

end
end KIP126.ProofTools.Internal.Mahowald
