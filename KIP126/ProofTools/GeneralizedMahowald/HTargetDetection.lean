module
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionDetection
import all KIP126.ProofTools.GeneralizedMahowald.HSourceSelection
import all KIP126.ProofTools.GeneralizedMahowald.SphereLabels
import all KIP126.ProofTools.GeneralizedMahowald.HTarget
import KIP126.AdamsSynthetic
/-! Detection of the actual normalized h target in the finite Mahowald argument.
The finite extension packet supplies the chosen source and its actual target.
The suspension label bridge identifies that target, and the normalized
cofiber comparison identifies the same representative with the unshifted image.
This module handles the supplied packet branch; it does not replace finite
extension no-crossing by an unproved representative-synchronization premise. -/
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
set_option maxHeartbeats 2500000

private theorem suspension_finite_detects_adjacent
    (X : ClassicalObject) (q k : ℕ) (hkq : k<q) (s t t₀ : ℤ) (ht : t=t₀+1)
    (x : Ambient model X (s,t₀)) (sx : Ambient model (.shift 1 X) (s,t))
    (εq : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεq : XModLambdaN.incl _ q ≫ εq.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
    (hsx : (model.classicalSuspension X).DesuspendsClass s t sx (by simpa [ht] using x))
    (a : BiHom (t-s) (t-k)
      (XModLambdaN (model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary)) q))
    (ha : Detects (model.convergence (.quotient q (.nu (.shift 1 X)))) (s,t,t-k)
      (finiteTargetLabel model (.shift 1 X) q s t k sx) a) :
    Detects (model.convergence (.quotient q (.nu X))) (s,t₀,t₀-k)
      (finiteTargetLabel model X q s t₀ k x)
      (quotientUnshift X (1,1) (t₀-s,t₀-k) q εq
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (a ≫ XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q))) := by
  subst t
  exact suspension_finite_detects X q k hkq s t₀ x sx εq hεq hsx a ha

private theorem extension_target_label_reindex
    (Z Y : ClassicalObject) (f : Z.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (l s t : ℤ) (hl : (normalizedExponent model.classicalTower f : ℤ)≤l)
    (y : Ambient model Y (s+l,t+l))
    (b : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q))
    (hb : Detects (model.convergence (.quotient q (.nu Y)))
      (s+l,(t-s)+(s+l),t+normalizedExponent model.classicalTower f)
      (finiteTargetForExtension model Z Y f q l s t hl y)
      (homotopyRegrade (by dsimp; omega) rfl b)) :
    Detects (model.convergence (.quotient q (.nu Y)))
      (s+l,t+l,t+l-(l-normalizedExponent model.classicalTower f).toNat)
      (finiteTargetLabel model Y q (s+l) (t+l) (l-normalizedExponent model.classicalTower f).toNat y)
      (homotopyRegrade (by dsimp; omega) (by dsimp; rw [Int.toNat_of_nonneg (by omega)]; omega) b) := by
  have e2_comp {A : SyntheticAdamsSS} {u v w : Tridegree}
      (huv : u=v) (hvw : v=w) (z : A.E₂ u) :
      regradeE2 hvw (regradeE2 huv z)=regradeE2 (huv.trans hvw) z := by
    subst v; subst w; rfl
  have twice {A : SyntheticSpectrum} {m m' m'' w w' w'' : ℤ}
      (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
      (a : BiHom m w A) :
      homotopyRegrade hm' hw' (homotopyRegrade hm hw a) =
        homotopyRegrade (hm.trans hm') (hw.trans hw') a := by
    subst m'; subst m''; subst w'; subst w''; rfl
  have hbi := detects_transport
    (show (s+l,(t-s)+(s+l),t+normalizedExponent model.classicalTower f)=
      (s+l,t+l,t+l-(l-normalizedExponent model.classicalTower f).toNat) by
      ext <;> simp only [Int.toNat_of_nonneg (by omega : 0≤l-normalizedExponent model.classicalTower f)] <;> omega) _ _ hb
  simp only [finiteTargetForExtension,twice] at hbi
  erw [e2_comp] at hbi
  exact hbi

private theorem finite_h_target_desuspend_detects
    (X Z : ClassicalObject) (h : Z.obj model.auxiliary ⟶ (ClassicalObject.shift 1 X).obj model.auxiliary)
    (q : ℕ) (l s t e : ℤ)
    (he : e + normalizedExponent model.classicalTower h = 1)
    (xBar : Ambient model Z (s,t))
    (x : Ambient model X (s+l,t+l-1))
    (sx : Ambient model (.shift 1 X) (s+l,t+l))
    (W : FiniteExtensionWitness model Z (.shift 1 X) h (q+1) l s t xBar sx)
    (hsx : (model.classicalSuspension X).DesuspendsClass (s+l) (t+l) sx x)
    (εq : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεq : XModLambdaN.incl _ q ≫ εq.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ q))
    (b : BiHom (t-s) (t+normalizedExponent model.classicalTower h)
      (XModLambdaN (model.nu.functor.obj ((ClassicalObject.shift 1 X).obj model.auxiliary)) q))
    (hb : Detects (model.convergence (.quotient q (.nu (.shift 1 X))))
      (s+l,t+l,t+l-(l-normalizedExponent model.classicalTower h).toNat)
      (finiteTargetLabel model (.shift 1 X) q (s+l) (t+l)
        (l-normalizedExponent model.classicalTower h).toNat sx)
      (homotopyRegrade (by dsimp; omega)
        (by have := W.length_lower; dsimp; rw [Int.toNat_of_nonneg (by omega)]; omega) b)) :
    Detects (model.convergence (.quotient q (.nu X))) (s+l,t+l-1,t-e)
      (regradeE2 (by have := W.length_lower; ext <;>
        simp only [Int.toNat_of_nonneg (by omega : 0≤l-normalizedExponent model.classicalTower h)]; omega)
        (finiteTargetLabel model X q (s+l) (t+l-1)
          (l-normalizedExponent model.classicalTower h).toNat x))
      (homotopyRegrade (by dsimp; omega) rfl
        (quotientUnshift X (1,1) (t-s-1,t-e) q εq
          (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
            (b ≫ XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q)))) := by
  let k := (l-normalizedExponent model.classicalTower h).toNat
  have hk : (k:ℤ)=l-normalizedExponent model.classicalTower h := by
    dsimp only [k]
    exact Int.toNat_of_nonneg (by have := W.length_lower; omega)
  have hkq : k<q := by have := W.length_upper; have := W.length_lower; omega
  have twice {A : SyntheticSpectrum} {m m' m'' w w' w'' : ℤ}
      (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
      (a : BiHom m w A) :
      homotopyRegrade hm' hw' (homotopyRegrade hm hw a) =
        homotopyRegrade (hm.trans hm') (hw.trans hw') a := by
    subst m'; subst m''; subst w'; subst w''; rfl
  have hd := suspension_finite_detects_adjacent X q k hkq (s+l) (t+l) (t+l-1)
    (by omega) x sx εq hεq hsx _ hb
  have htgt := detects_transport (show (s+l,t+l-1,t+l-1-k)=(s+l,t+l-1,t-e) by
    ext <;> dsimp; omega) _ _ hd
  have unshift_regrade (m m' w w' : ℤ) (hm : m=m') (hw : w=w')
      (a : BiHom ((m,w)+(1,1)).1 ((m,w)+(1,1)).2
        (XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
      homotopyRegrade hm hw (quotientUnshift X (1,1) (m,w) q εq a) =
        quotientUnshift X (1,1) (m',w') q εq
          (homotopyRegrade (congrArg (fun z => z+1) hm) (congrArg (fun z => z+1) hw) a) := by
    subst m'; subst w'; rfl
  have hrep : homotopyRegrade (show (t+l-1)-(s+l)=t-s-1 by omega)
      (show t+l-1-k=t-e by omega)
      (quotientUnshift X (1,1) ((t+l-1)-(s+l),t+l-1-k) q εq
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (homotopyRegrade (show t-s=(t+l)-(s+l) by omega)
            (show t+normalizedExponent model.classicalTower h=t+l-k by omega) b ≫
              XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q))) =
      quotientUnshift X (1,1) (t-s-1,t-e) q εq
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (b ≫ XModLambdaN.map (model.nu.suspensionIso (X.obj model.auxiliary)).hom q)) := by
    rw [unshift_regrade]
    simp only [←regrade_comp,twice]
  rw [←hrep]
  simpa only [twice] using htgt


/-- The actual normalized cofiber image has the desuspended target label when
its chosen source is accompanied by the finite extension packet. -/
private theorem normalized_h_target_detects
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (q : ℕ) (l s t : ℤ)
    (xBar : Ambient model T.Z (s,t))
    (x : Ambient model T.X (s+l,t+l-1))
    (sx : Ambient model (.shift 1 T.X) (s+l,t+l))
    (W : FiniteExtensionWitness model T.Z (.shift 1 T.X) T.h (q+1) l s t xBar sx)
    (hsx : (model.classicalSuspension T.X).DesuspendsClass (s+l) (t+l) sx x)
    (aZ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (T.Z.obj model.auxiliary)) q))
    (hsource : FiniteExtensionAtSource T.Z (.shift 1 T.X) T.h (q+1) l s t xBar sx W aZ)
    (εδ : XModLambdaN ((SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).obj
          (model.nu.functor.obj (T.X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).obj
          (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) q))
    (hεδ : XModLambdaN.incl _ q≫εδ.hom =
      (SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).map
          (XModLambdaN.incl _ q)) :
    Detects (model.convergence (.quotient q (.nu T.X)))
      (s+l,t+l-1,t-((normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g))
      (regradeE2 (by have := W.length_lower; ext <;>
        simp only [Int.toNat_of_nonneg (by omega : 0≤l-normalizedExponent model.classicalTower T.h)]; omega)
        (finiteTargetLabel model T.X q (s+l) (t+l-1)
          (l-normalizedExponent model.classicalTower T.h).toNat x))
      (homotopyRegrade (by dsimp; omega) rfl
        (quotientShiftDesuspend T.X
          (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)
          q εδ (t-s) t
          (aZ≫XModLambdaN.map (HasFunctorialCofiber.cofibι (model.normalizedMap T.Y T.Z T.g).map≫
            (normalized_g_cofiber_iso T he hT).hom) q))) := by
  have hq : 0<q := by have := W.page_ge_two; omega
  obtain ⟨ah,_hsource,htarget,hunshift⟩ := hsource
  have ht := extension_target_label_reindex T.Z (.shift 1 T.X) T.h q l s t W.length_lower
    sx (ah≫finiteExtensionMap model T.Z (.shift 1 T.X) T.h q) htarget
  letI := model.exactness.shiftCommShift (1,1)
  letI := model.exactness.shiftExact (1,1)
  obtain ⟨εσ,hεσ,_⟩ := quotient_shift_exists model.quotients.coherence (1,1) q
    (model.nu.functor.obj (T.X.obj model.auxiliary))
  have hd := finite_h_target_desuspend_detects T.X T.Z T.h q l s t
    ((normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)
    he xBar x sx W hsx εσ hεσ _ ht
  have heq := normalized_h_target_representative T he hT q hq s t aZ ah hunshift
    εδ hεδ εσ hεσ
  simp only [Category.assoc] at hd
  rw [heq] at hd
  exact hd


private theorem normalized_h_target_detects_native
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g + normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (q : ℕ) (l s t : ℤ)
    (xBar : Ambient model T.Z (s,t))
    (x : Ambient model T.X (s+l,t+l-1))
    (sx : Ambient model (.shift 1 T.X) (s+l,t+l))
    (W : FiniteExtensionWitness model T.Z (.shift 1 T.X) T.h (q+1) l s t xBar sx)
    (hsx : (model.classicalSuspension T.X).DesuspendsClass (s+l) (t+l) sx x)
    (aZ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (T.Z.obj model.auxiliary)) q))
    (hsource : FiniteExtensionAtSource T.Z (.shift 1 T.X) T.h (q+1) l s t xBar sx W aZ)
    (εδ : XModLambdaN ((SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).obj
          (model.nu.functor.obj (T.X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).obj
          (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) q))
    (hεδ : XModLambdaN.incl _ q≫εδ.hom =
      (SyntheticCategory.biShift
        (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)).map
          (XModLambdaN.incl _ q)) :
    Detects (model.convergence (.quotient q (.nu T.X)))
      (s+l,t+l-1,t+l-1-(l-normalizedExponent model.classicalTower T.h).toNat)
      (finiteTargetLabel model T.X q (s+l) (t+l-1)
        (l-normalizedExponent model.classicalTower T.h).toNat x)
      (homotopyRegrade (by dsimp; omega)
        (by
          have := W.length_lower
          dsimp
          rw [Int.toNat_of_nonneg (by omega : 0≤l-normalizedExponent model.classicalTower T.h)]
          omega)
        (quotientShiftDesuspend T.X
          (1,(normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)
          q εδ (t-s) t
          (aZ≫XModLambdaN.map (HasFunctorialCofiber.cofibι (model.normalizedMap T.Y T.Z T.g).map≫
            (normalized_g_cofiber_iso T he hT).hom) q))) := by
  have hd := normalized_h_target_detects T he hT q l s t xBar x sx W hsx aZ hsource εδ hεδ
  have ht := detects_transport
    (show (s+l,t+l-1,t-((normalizedExponent model.classicalTower T.f : ℤ)+normalizedExponent model.classicalTower T.g)) =
      (s+l,t+l-1,t+l-1-(l-normalizedExponent model.classicalTower T.h).toNat) by
      have := W.length_lower
      ext <;> simp only [Int.toNat_of_nonneg (by omega : 0≤l-normalizedExponent model.classicalTower T.h)]; omega) _ _ hd
  convert ht using 1
  · have inv {A : SyntheticAdamsSS} {i j : Tridegree} (h : i=j) (y : A.E₂ i) :
        regradeE2 h.symm (regradeE2 h y) = y := by subst j; rfl
    exact (inv _ _).symm
  · have twice {A : SyntheticSpectrum} {m m' m'' w w' w'' : ℤ}
        (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
        (a : BiHom m w A) :
        homotopyRegrade hm' hw' (homotopyRegrade hm hw a) =
          homotopyRegrade (hm.trans hm') (hw.trans hw') a := by
      subst m'; subst m''; subst w'; subst w''; rfl
    rw [twice]

end
end KIP126.ProofTools.Internal.Mahowald
