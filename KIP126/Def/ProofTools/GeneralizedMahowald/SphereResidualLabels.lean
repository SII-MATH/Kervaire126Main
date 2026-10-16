module
import all KIP126.Def.ProofTools.GeneralizedMahowald.MayCorrection
import all KIP126.Def.ProofTools.GeneralizedMahowald.SphereMayCorrection

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
set_option maxHeartbeats 1000000

private theorem actual_raw_residual_flat_detects_zero
    (Y Z : ClassicalObject) (g : Y.obj model.auxiliary ⟶ Z.obj model.auxiliary)
    (rW r i : ℕ) (hi : 0 < i) (m s t : ℤ) (hm : 0 ≤ m)
    (y : Ambient model Y (s,t)) (yBar : Ambient model Z (s+m,t+m))
    (Wg : FiniteExtensionWitness model Y Z g rW m s t y yBar)
    (p : ℤ×ℤ) (xBar : Ambient model Z p)
    (hd : m=0 → HasDifferential (model.classical.obj (Z.obj model.auxiliary))
      (i+1) p (s+m,t+m) xBar yBar)
    (hyBar : yBar ∈ permanentCycles model Z (s+m,t+m))
    (D : SyntheticObject)
    (hD : D=.shift (0,(i:ℤ)+normalizedExponent model.classicalTower g) (.quotient r (.nu Y)))
    (U : SyntheticSpectrum)
    (eD : U ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj (D.obj model.nu model.auxiliary))
    (raw : (model.nu.functor.obj (Z.obj model.auxiliary))⟦(1:ℤ)⟧ ⟶ U) :
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    let t₀ := ff.preimage ((biSuspensionIso (i:ℤ)
      (model.nu.functor.obj (Z.obj model.auxiliary))).hom ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (lambdaPow i (model.nu.functor.obj (Z.obj model.auxiliary))) ≫ raw ≫ eD.hom)
    Detects (model.convergence D) (s,t,t+normalizedExponent model.classicalTower g)
      (familyPageMap model.family ((model.normalizedMap Y Z g).map≫t₀) 2
        (s,t,t+normalizedExponent model.classicalTower g)
        (regradeE2 (by simp) (infiniteSourceForExtension model Y Z g s t y))) 0 := by
  dsimp only
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
  let t₀ := ff.preimage ((biSuspensionIso (i:ℤ)
    (model.nu.functor.obj (Z.obj model.auxiliary))).hom ≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (lambdaPow i (model.nu.functor.obj (Z.obj model.auxiliary))) ≫ raw ≫ eD.hom)
  by_cases hm0 : m=0
  · subst m
    have heg : (normalizedExponent model.classicalTower g : ℤ)=0 := by
      have := Wg.length_lower
      omega
    have hD0 : D=.shift (0,(i:ℤ)) (.quotient r (.nu Y)) := by
      rw [hD,heg,add_zero]
    cases hD0
    let E : SyntheticObject := .quotient r (.nu Y)
    let epsilon : (SyntheticCategory.biShift (0,-(i:ℤ))).obj
        ((SyntheticCategory.biShift (0,(i:ℤ))).obj (E.obj model.nu model.auxiliary)) ≅
        E.obj model.nu model.auxiliary :=
      (biShiftAddIso (0,(i:ℤ)) (0,-(i:ℤ)) (0,0) (by ext <;> simp)).app _ ≪≫
        SyntheticCategory.biShift_zero.app _
    have hz := zero_length_actual_toda_residual_detects_zero Y Z g rW i hi s t y yBar Wg
      p xBar (hd rfl) hyBar E U eD epsilon raw
    have hindex : (s+0,t+0,t+0)=(s,t,t+normalizedExponent model.classicalTower g) := by
      ext <;> dsimp <;> omega
    have hzt := detects_transport hindex _ _ hz
    have regrade_comp {A : SyntheticAdamsSS.{0}} {i j k : Tridegree}
        (h : i=j) (h' : j=k) (z : A.E₂ i) :
        regradeE2 h' (regradeE2 h z) = regradeE2 (h.trans h') z := by
      subst j; subst k; rfl
    have regrade_zero {m m' w w' : ℤ} {V : SyntheticSpectrum}
        (hm : m=m') (hw : w=w') :
        homotopyRegrade hm hw (0 : BiHom m w V)=0 := by
      subst m'; subst w'; rfl
    simp only [page_regrade,regrade_comp,regrade_zero] at hzt
    exact hzt
  · have hmpos : 0<m := by omega
    have hz := positive_extension_postcompose_e2_zero Y Z g rW m s t hmpos y yBar Wg
      (D.obj model.nu model.auxiliary) t₀
    have hz' : familyPageMap model.family ((model.normalizedMap Y Z g).map≫t₀) 2
        (s,t,t+normalizedExponent model.classicalTower g)
        (regradeE2 (by simp) (infiniteSourceForExtension model Y Z g s t y)) = 0 := by
      have hzR := congrArg (regradeE2 (by simp :
        (s,(t-s)+s,t+normalizedExponent model.classicalTower g)=
          (s,t,t+normalizedExponent model.classicalTower g))) hz
      rw [page_regrade] at hzR
      simpa only [regradeE2,map_zero] using hzR
    rw [hz']
    exact ⟨0,HasInfinityRepresentative.zero _ 2 (by omega) _,0,by simp,by simp⟩


private theorem actual_extension_source_native_detects
    (Y Z : ClassicalObject) (g : Y.obj model.auxiliary ⟶ Z.obj model.auxiliary)
    (q : ℕ) (s t : ℤ) (y : Ambient model Y (s,t))
    (ag : BiHom (t-s) (t+normalizedExponent model.classicalTower g)
      (XModLambdaN ((extensionSourceObject model Y Z g).obj model.nu model.auxiliary) q))
    (hag : Detects (model.convergence (.quotient q (extensionSourceObject model Y Z g)))
      (s,(t-s)+s,t+normalizedExponent model.classicalTower g)
      (finiteSourceForExtension model Y Z g q s t y)
      (homotopyRegrade (by simp) rfl ag)) :
    Detects (model.convergence (.quotient q (extensionSourceObject model Y Z g)))
      (s,t,t+normalizedExponent model.classicalTower g)
      (familyPageMap model.family
        (XModLambdaN.incl ((extensionSourceObject model Y Z g).obj model.nu model.auxiliary) q)
        2 (s,t,t+normalizedExponent model.classicalTower g)
        (regradeE2 (by simp) (infiniteSourceForExtension model Y Z g s t y))) ag := by
  let p : Tridegree := (s,(t-s)+s,t+normalizedExponent model.classicalTower g)
  have hsource : finiteSourceForExtension model Y Z g q s t y =
      familyPageMap model.family (XModLambdaN.incl _ q) 2 p
        (infiniteSourceForExtension model Y Z g s t y) := by
    unfold finiteSourceForExtension infiniteSourceForExtension finiteNuLabel
    rw [page_regrade]
    rfl
  have hag' := (congrArg (fun z => Detects
    (model.convergence (.quotient q (extensionSourceObject model Y Z g))) p z
    (homotopyRegrade (show t-s=((t-s)+s)-s by omega) rfl ag)) hsource).mp hag
  have hindex : p=(s,t,t+normalizedExponent model.classicalTower g) := by
    simp only [p,sub_add_cancel]
  have hnative := detects_transport hindex _ _ hag'
  have regrade_comp {m m' m'' w w' w'' : ℤ} {V : SyntheticSpectrum}
      (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
      (z : BiHom m w V) :
      homotopyRegrade hm' hw' (homotopyRegrade hm hw z) =
        homotopyRegrade (hm.trans hm') (hw.trans hw') z := by
    subst m'; subst m''; subst w'; subst w''; rfl
  simp only [page_regrade,regrade_comp] at hnative
  exact hnative

end
end KIP126.ProofTools.Internal.Mahowald
