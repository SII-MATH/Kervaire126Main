module

public import KIP126.Def.AdamsSynthetic.ExtensionLaws.GeneralizedMahowald.Data
public import KIP126.Literature.AdamsSynthetic.ComparisonTheorems
import all KIP126.Main.ExtensionLaws.PageExtensionStretching.Proofs
import KIP126.Def.Synthetic.QuotientTower.Proofs
import KIP126.Def.Synthetic.QuotientRestrictions.Proofs
import KIP126.Def.SpectralSequence.Basic.Category.Proofs
import KIP126.Def.ClassicalAdams.PageRepresentatives.Proofs
import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs

public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.Synthetic.Detection.Proofs
public import KIP126.Def.Comparison.ClassicalSynthetic.EInfty.Proofs
public import KIP126.Def.SpectralSequence.BoundedExtension.UnderlyingComplex.Proofs

import KIP126.Def.Synthetic.Sphere.Shift.Data
import KIP126.Def.Synthetic.Sphere.Actions.Data
import KIP126.Def.Synthetic.Context.Coherence.Proofs
import KIP126.Def.Synthetic.QuotientMap.Proofs

@[expose] public section

/-! The generalized Mahowald rule under the stated classical/synthetic
and May comparison hypotheses. The two marked geometric proof obligations
remain unproved. The existing argument retains the specified extension,
desuspension, differential and no-crossing conditions. -/
namespace KIP126.Main.ExtensionLaws

open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Classical.Adams
open KIP126.Literature.AdamsSynthetic

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : AdamsComparison H M Syn)

/-- Refine the rule's no-crossing disjunction into its two actual forms. -/
theorem MahowaldNoCrossingWitness.ofHypotheses
    {T : ClassicalCofiberTriangle D.hopfAndDetector} {n m l s t : ℤ}
    (W : MahowaldHypotheses D T n m l s t) :
    MahowaldNoCrossingWitness D T W := by
  rcases W.no_crossing with h | h
  · exact .hExtension h
  · exact .classicalDifferential h.1 h.2.1 h.2.2


open KIP126.Synthetic.SpectralSequence KIP126.Classical.Adams.PageRepresentatives
open KIP126.SpectralSequence KIP126.Synthetic.PageExtension
open private shifted_finite_source_exists from KIP126.Main.ExtensionLaws.PageExtensionStretching.Proofs

/- In the top nonzero weight of a finite quotient, two detected targets
coincide as actual homotopy classes. Thus an extension gives a strict
preimage of any specified representative with that target label. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem finite_top_extension_preimage
    (synthetic : SyntheticComparisonTheorems D) (X Y : ClassicalObject)
    (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)
    (r : ℕ) (n s t : ℤ)
    (x : E2 H (X.obj D.hopfAndDetector) s t)
    (y : E2 H (Y.obj D.hopfAndDetector) (s+n) (t+n))
    (W : FiniteExtensionWitness D X Y f r n s t x y)
    (htop : (r:ℤ)-1 ≤ n-normalizedExponent H f+1)
    (b : BiHom (t-s) (t+normalizedExponent H f)
      (XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) (r-1)))
    (hb : Detects (D.convergence (.quotient (r-1) (.nu Y)))
      (s+n,(t-s)+(s+n),t+normalizedExponent H f)
      (finiteTargetForExtension D X Y f (r-1) n s t W.length_lower y)
      (homotopyRegrade (by dsimp; omega) rfl b)) :
    ∃ a : BiHom (t-s) (t+normalizedExponent H f)
      ((SyntheticObject.quotient (r-1) (extensionSourceObject D X Y f)).obj D.nu D.hopfAndDetector),
      a ≫ finiteExtensionMap D X Y f (r-1) = b ∧
      Detects (D.convergence (.quotient (r-1) (extensionSourceObject D X Y f)))
        (s,(t-s)+s,t+normalizedExponent H f)
        (finiteSourceForExtension D X Y f (r-1) s t x)
        (homotopyRegrade (by dsimp; omega) rfl a) := by
  have finite_quotient_high_filtration_zero_int
      (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
      (a : BiHom m w (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) : a = 0 := by
    have hz (j : ℤ) (hj : s ≤ j) :
        IsZero (((D.family.nuQuotient D.nu (X.obj D.hopfAndDetector) q).sequence.ssData
          (j,m+j,w)).eInfty) := by
      have hwin : ¬ (0 ≤ (m+j)-w ∧ (m+j)-w < q) := by omega
      haveI : Subsingleton (finiteEInftyModel H (X.obj D.hopfAndDetector) q (j,m+j) w) := by
        simp only [finiteEInftyModel, hwin, ite_false]
        infer_instance
      haveI : Subsingleton (((D.family.nuQuotient D.nu (X.obj D.hopfAndDetector) q).sequence.ssData
          (j,m+j,w)).eInfty) :=
        (synthetic.eInfty.presentation.finite (X.obj D.hopfAndDetector) q hq (j,m+j) w).injective.subsingleton
      exact ModuleCat.isZero_of_subsingleton _
    apply D.homotopySeparated (.quotient q (.nu X)) m w a
    intro j
    by_cases hj : s ≤ (j:ℤ)
    · exact ((D.convergence (.quotient q (.nu X))).filtrationAtLeast_iff_of_eInfty_isZero
        s j m w hj (fun k hk _ => hz k hk) a).mp ha
    · exact towerFiltrationSubmodule_antitone (nuCoefficientUnit H.unit D.nu) _ (m,w)
        (by omega) ha
  have finite_top_detection_unique
      (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (s t w : ℤ) (hwindow : (q:ℤ) ≤ t+1-w)
      (x : (D.family.nuQuotient D.nu (X.obj D.hopfAndDetector) q).E₂ (s,t,w))
      (a b : BiHom (t-s) w (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q))
      (ha : Detects (D.convergence (.quotient q (.nu X))) (s,t,w) x a)
      (hb : Detects (D.convergence (.quotient q (.nu X))) (s,t,w) x b) : a=b := by
    apply sub_eq_zero.mp
    exact finite_quotient_high_filtration_zero_int synthetic X q hq (t-s) w (s+1)
      (by omega) (a-b)
      (detects_sub_filtration (D.convergence (.quotient q (.nu X))) (s,t,w) ha hb)
  have extension_equation_representatives
      {A B : Syn} (g : A ⟶ B)
      (ca : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family A)
      (cb : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family B)
      (p : ℤ × ℤ) (s n : ℤ)
      (x : ((D.family.obj A).sequence.ssData (s,p.1+s,p.2)).eInfty)
      (y : ((D.family.obj B).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
      (h : ExtensionEquation g ca cb p s n x y) :
      ∃ (a : (Subobject.underlying.obj
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p) : ModuleCat ℤ))
        (b : (Subobject.underlying.obj
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) B).F (s+n) p) : ModuleCat ℤ)),
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p).arrow a ≫ g =
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) B).F (s+n) p).arrow b ∧
        (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s p a =
          (extensionSourceIso (nuCoefficientUnit H.unit D.nu) g ca p s).hom x ∧
        (towerFiltration (nuCoefficientUnit H.unit D.nu) B).toAssociatedGraded (s+n) p b =
          (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g cb p (s+n)).hom y := by
    obtain ⟨hn, ⟨z,hz⟩⟩ := h
    refine ⟨z.1 (ULift.up 1), z.2 (ULift.up 1), ?_, ?_, ?_⟩
    · have he := congrArg (fun e => e.2.2 (ULift.up 1)) hz
      dsimp only [FilteredComplex.Solutions.equation] at he
      simp only [extensionComplex, underlyingComplex_d_one] at he
      change (syntheticHomotopyMap g p)
          (((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p).arrow (z.1 (ULift.up 1))) -
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) B).F (s+n) p).arrow (z.2 (ULift.up 1)) = 0 at he
      exact sub_eq_zero.mp he
    · have he := congrArg (fun e => e.1 (ULift.up 1)) hz
      dsimp only [FilteredComplex.Solutions.equation] at he
      change (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s p
        (z.1 (ULift.up 1)) = elementMap _ (ULift.up 1) at he
      simpa [elementMap] using he
    · have he := congrArg (fun e => e.2.1 (ULift.up 1)) hz
      dsimp only [FilteredComplex.Solutions.equation] at he
      change (towerFiltration (nuCoefficientUnit H.unit D.nu) B).toAssociatedGraded (s+n) p
        (z.2 (ULift.up 1)) = elementMap _ (ULift.up 1) at he
      simpa [elementMap] using he
  have source_frame_detects
      {A B : Syn} (g : A ⟶ B)
      (ca : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family A)
      (p : ℤ × ℤ) (s : ℤ)
      (x : ((D.family.obj A).sequence.ssData (s,p.1+s,p.2)).eInfty)
      (x0 : (D.family.obj A).E₂ (s,p.1+s,p.2))
      (hx : HasInfinityRepresentative _ 2 _ x0 x)
      (a : (Subobject.underlying.obj
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p) : ModuleCat ℤ))
      (ha : (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s p a =
        (extensionSourceIso (nuCoefficientUnit H.unit D.nu) g ca p s).hom x) :
      Detects ca (s,p.1+s,p.2) x0
        (homotopyRegrade (by dsimp; omega) rfl
          (((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p).arrow a)) := by
    have lift_frame (m m' w s : ℤ) (hm : m=m') {V : ModuleCat.{v} ℤ} (e : V)
        (I : V ≅ (towerFiltration (nuCoefficientUnit H.unit D.nu) A).associatedGraded s (m',w))
        (a : (Subobject.underlying.obj
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m,w)) : ModuleCat ℤ))
        (ha : (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s (m,w) a =
          (I ≪≫ eqToIso (congrArg
            (fun z => (towerFiltration (nuCoefficientUnit H.unit D.nu) A).associatedGraded s (z,w)) hm.symm)).hom e) :
        ∃ a' : (Subobject.underlying.obj
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m',w)) : ModuleCat ℤ),
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m',w)).arrow a' =
            homotopyRegrade hm rfl (((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m,w)).arrow a) ∧
          I.hom e = (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s (m',w) a' := by
      subst m'
      refine ⟨a,rfl,?_⟩
      simpa only [eqToIso_refl, Iso.trans_refl] using ha.symm
    obtain ⟨a',ha',hga⟩ := lift_frame p.1 ((p.1+s)-s) p.2 s (by omega) x
      (ca.identification (s,p.1+s,p.2)) a ha
    exact ⟨x,hx,a',ha',hga⟩
  let unit := nuCoefficientUnit H.unit D.nu
  let A := (SyntheticObject.quotient (r-1) (extensionSourceObject D X Y f)).obj D.nu D.hopfAndDetector
  let B := XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) (r-1)
  let p := (t-s,t+normalizedExponent H f)
  obtain ⟨a,b',hab,hax,hby⟩ := extension_equation_representatives
    (finiteExtensionMap D X Y f (r-1)) _ _ p s n W.source W.target W.equation
  have ha := source_frame_detects (finiteExtensionMap D X Y f (r-1))
    (D.convergence (.quotient (r-1) (extensionSourceObject D X Y f))) p s W.source
    _ W.source_rep a hax
  have hb' := source_frame_detects (𝟙 B)
    (D.convergence (.quotient (r-1) (.nu Y))) p (s+n) W.target
    _ W.target_rep b' hby
  have hr := W.page_ge_two
  have heq := finite_top_detection_unique synthetic Y (r-1) (by omega)
    (s+n) ((t-s)+(s+n)) (t+normalizedExponent H f) (by omega)
    _ _ _ hb' hb
  have heq' : ((towerFiltration unit B).F (s+n) p).arrow b' = b := by
    have hinj (u v w : ℤ) (huv : u=v) :
        Function.Injective (homotopyRegrade huv (rfl : w=w) (X:=B)) := by
      subst v
      exact Function.injective_id
    exact hinj _ _ _ _ heq
  refine ⟨((towerFiltration unit A).F s p).arrow a, hab.trans heq', ha⟩

/- Strictly related homotopy representatives give an extension equation
with the specified detected labels, by using their filtration witnesses. -/
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem extension_equation_of_detected_pair
    {A B : Syn} (g : A ⟶ B)
    (ca : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family A)
    (cb : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family B)
    (p : ℤ × ℤ) (s n : ℤ) (hn : 0 ≤ n)
    (x0 : (D.family.obj A).E₂ (s,p.1+s,p.2))
    (y0 : (D.family.obj B).E₂ (s+n,p.1+(s+n),p.2))
    (a : BiHom p.1 p.2 A) (b : BiHom p.1 p.2 B)
    (ha : Detects ca (s,p.1+s,p.2) x0 (homotopyRegrade (by dsimp; omega) rfl a))
    (hb : Detects cb (s+n,p.1+(s+n),p.2) y0 (homotopyRegrade (by dsimp; omega) rfl b))
    (hab : a ≫ g=b) :
    ∃ x y, HasInfinityRepresentative _ 2 _ x0 x ∧
      HasInfinityRepresentative _ 2 _ y0 y ∧ ExtensionEquation g ca cb p s n x y := by
  have frame_of_source_detects
      {A B : Syn} (g : A ⟶ B)
      (ca : TowerConvergence (nuCoefficientUnit H.unit D.nu) D.family A)
      (p : ℤ × ℤ) (s : ℤ)
      (x0 : (D.family.obj A).E₂ (s,p.1+s,p.2))
      (a0 : BiHom p.1 p.2 A)
      (ha0 : Detects ca (s,p.1+s,p.2) x0 (homotopyRegrade (by dsimp; omega) rfl a0)) :
      ∃ x : ((D.family.obj A).sequence.ssData (s,p.1+s,p.2)).eInfty,
        HasInfinityRepresentative _ 2 _ x0 x ∧
        ∃ a : (Subobject.underlying.obj
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p) : ModuleCat ℤ),
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p).arrow a = a0 ∧
          (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s p a =
            (extensionSourceIso (nuCoefficientUnit H.unit D.nu) g ca p s).hom x := by
    have lower_frame (m m' w s : ℤ) (hm : m=m') {V : ModuleCat.{v} ℤ} (e : V)
        (I : V ≅ (towerFiltration (nuCoefficientUnit H.unit D.nu) A).associatedGraded s (m',w))
        (a0 : BiHom m w A)
        (a' : (Subobject.underlying.obj
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m',w)) : ModuleCat ℤ))
        (ha' : ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m',w)).arrow a' = homotopyRegrade hm rfl a0)
        (hga : I.hom e = (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s (m',w) a') :
        ∃ a : (Subobject.underlying.obj
            ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m,w)) : ModuleCat ℤ),
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s (m,w)).arrow a = a0 ∧
          (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s (m,w) a =
            (I ≪≫ eqToIso (congrArg
              (fun z => (towerFiltration (nuCoefficientUnit H.unit D.nu) A).associatedGraded s (z,w)) hm.symm)).hom e := by
      subst m'
      exact ⟨a',ha',hga.symm⟩
    obtain ⟨e,he,a',ha',hga⟩ := ha0
    obtain ⟨a,ha,hg⟩ := lower_frame p.1 ((p.1+s)-s) p.2 s (by omega) e
      (ca.identification (s,p.1+s,p.2)) a0 a' ha' hga
    exact ⟨e,he,a,ha,hg⟩
  obtain ⟨x,hx,a',ha',hax⟩ := frame_of_source_detects g ca p s x0 a ha
  obtain ⟨y,hy,b',hb',hby⟩ := frame_of_source_detects (𝟙 B) cb p (s+n) y0 b hb
  have hom_ext_one {V : ModuleCat.{v} ℤ}
      (f g : ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ V)
      (h : f (ULift.up 1) = g (ULift.up 1)) : f=g := by
    apply ModuleCat.hom_ext
    have hh : f.hom.comp ULift.moduleEquiv.symm.toLinearMap =
        g.hom.comp ULift.moduleEquiv.symm.toLinearMap := LinearMap.ext_ring h
    ext z
    exact DFunLike.congr_fun hh z.down
  refine ⟨x,y,hx,hy,hn,⟨⟨elementMap a',elementMap b'⟩,?_⟩⟩
  apply Prod.ext
  · apply hom_ext_one
    change (towerFiltration (nuCoefficientUnit H.unit D.nu) A).toAssociatedGraded s p
      (elementMap a' (ULift.up 1)) = elementMap _ (ULift.up 1)
    simpa [elementMap] using hax
  · apply Prod.ext
    · apply hom_ext_one
      change (towerFiltration (nuCoefficientUnit H.unit D.nu) B).toAssociatedGraded (s+n) p
        (elementMap b' (ULift.up 1)) = elementMap _ (ULift.up 1)
      have hby' : (towerFiltration (nuCoefficientUnit H.unit D.nu) B).toAssociatedGraded (s+n) p b' =
          (extensionTargetIso (nuCoefficientUnit H.unit D.nu) g cb p (s+n)).hom y := hby
      simpa [elementMap] using hby'
    · apply hom_ext_one
      change (syntheticHomotopyMap g p)
          (((towerFiltration (nuCoefficientUnit H.unit D.nu) A).F s p).arrow (elementMap a' (ULift.up 1))) -
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) B).F (s+n) p).arrow (elementMap b' (ULift.up 1)) = 0
      have hab' : syntheticHomotopyMap g p a = (b : syntheticHomotopy B p) := hab
      simpa [elementMap, ha', hb'] using sub_eq_zero.mpr hab'

/- A fixed actual first-quotient label determines detection in lambda layer zero.
The finite lift criterion supplies the infinity representative; low-weight
vanishing supplies filtration, and the actual rho map reflects its grade. -/
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 1600000 in
private theorem first_label_detects_unshifted (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D)
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : E2 H (X.obj D.hopfAndDetector) s t)
    (a : BiHom (t-s) t (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q))
    (ha : a ≫ (D.quotientTower (D.nu.functor.obj (X.obj D.hopfAndDetector))).rho 1 q hq =
      firstLabel D X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (D.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel D X q s t 0 x)) a := by
  have finite_bottom_filtration (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D)
      (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
      (a : BiHom (t-s) t (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q)) :
      FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a := by
    have hzero : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 0 a := by
      refine ⟨a,?_⟩
      change a ≫ adamsTowerMap _ _ 0 0 _ = a
      rw [adamsTowerMap_self]
      exact Category.comp_id a
    by_cases hs : s ≤ 0
    · exact towerFiltrationSubmodule_antitone _ _ _ hs hzero
    · apply ((D.convergence (.quotient q (.nu X))).filtrationAtLeast_iff_of_eInfty_isZero
        0 s (t-s) t (by omega) (fun k _ hk => ?_) a).mp hzero
      change IsZero (((D.family.obj (XModLambdaN
        (D.nu.functor.obj (X.obj D.hopfAndDetector)) q)).sequence.ssData (k,(t-s)+k,t)).eInfty)
      letI : Subsingleton (((D.family.obj (XModLambdaN
          (D.nu.functor.obj (X.obj D.hopfAndDetector)) q)).sequence.ssData (k,(t-s)+k,t)).eInfty) :=
        KIP126.Comparison.syntheticEInfty_finite_subsingleton_of_outside
        H D.nu D.family synthetic.eInfty.presentation (X.obj D.hopfAndDetector) q hq
          (k,(t-s)+k) t (by omega)
      exact ModuleCat.isZero_of_subsingleton _

  have family_map_data (D : AdamsComparison H M Syn)  {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family f r i = (D.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
    let F := (D.family.functor.map f).toSSDataMorphism
    let PX := (D.family.functor.obj X).ssData i
    let PY := (D.family.functor.obj Y).ssData i
    let nX : WithTop ℕ := ↑(r-(D.family.functor.obj X).r₀).toNat
    let nY : WithTop ℕ := ↑(r-(D.family.functor.obj Y).r₀).toNat
    change (@eqToHom (ModuleCat ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
      (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
      @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
    have hX : nX=↑(r-2).toNat := by dsimp only [nX]; rw [D.family.firstPage X]
    have hY : nY=↑(r-2).toNat := by dsimp only [nY]; rw [D.family.firstPage Y]
    have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
        (n m n0 : WithTop ℕ) (hn : n=n0) (hm : m=n0)
        (h1 : A n0=A n) (h2 : B n=B m) (h3 : B m=B n0) :
        eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j n0 := by
      subst n
      subst m
      simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY (↑(r-2).toNat) hX hY _ _ _
  have family_page_comp (D : AdamsComparison H M Syn)  {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
    rw [family_map_data D,family_map_data D,family_map_data D,Functor.map_comp]
    exact (SSDataMorphism.pageMap_comp _ _ _ _).symm
  have family_infinity_representative_map (D : AdamsComparison H M Syn)
      {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
      (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
      (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
      HasInfinityRepresentative (D.family.obj Y) 2 i
        (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
    obtain ⟨hr,z,hz,he⟩ := hy
    change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
      (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
    let F := (D.family.functor.map f).toSSDataMorphism
    refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
    · rw [family_map_data D]
      have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
        (((D.family.obj Y).sequence.ssData i).pageπ 0)
      dsimp only [SyntheticAdamsFamily.obj] at h
      rw [←F.pageπ_pageMap] at h
      exact (congrArg (fun a => a z) h).symm.trans (by
        simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
    · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
        change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
        rw [he])

  have grade_natural (D : AdamsComparison H M Syn) (A B : SyntheticObject)
      (f : A.obj D.nu D.hopfAndDetector ⟶ B.obj D.nu D.hopfAndDetector) (i : Tridegree)
      (a : (Subobject.underlying.obj ((towerFiltration (nuCoefficientUnit H.unit D.nu)
        (A.obj D.nu D.hopfAndDetector)).F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ))
      (b : (Subobject.underlying.obj ((towerFiltration (nuCoefficientUnit H.unit D.nu)
        (B.obj D.nu D.hopfAndDetector)).F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ))
      (hab : ((towerFiltration (nuCoefficientUnit H.unit D.nu)
        (A.obj D.nu D.hopfAndDetector)).F i.1 (i.2.1-i.1,i.2.2)).arrow a ≫ f =
          ((towerFiltration (nuCoefficientUnit H.unit D.nu)
            (B.obj D.nu D.hopfAndDetector)).F i.1 (i.2.1-i.1,i.2.2)).arrow b) :
      ((D.convergence B).identification i).inv
        ((towerFiltration (nuCoefficientUnit H.unit D.nu)
          (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) b) =
      (D.family.functor.map f).eInftyMap i (((D.convergence A).identification i).inv
        ((towerFiltration (nuCoefficientUnit H.unit D.nu)
          (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a)) := by
    obtain ⟨c,hca,hce⟩ := D.comparisonCompatible.convergence_natural A B f
    have hc := c.iso_compat i
    simp only [KIP126.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,
      TowerConvergence.toSynthetic,SyntheticAdamsConvergence.toConvergence] at hc
    rw [hce] at hc
    have hb : (c.filtration_compat i.1 (i.2.1-i.1,i.2.2)).choose a = b := by
      apply (ModuleCat.mono_iff_injective
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F
          i.1 (i.2.1-i.1,i.2.2)).arrow).mp inferInstance
      have he := ConcreteCategory.congr_hom
        (c.filtration_compat i.1 (i.2.1-i.1,i.2.2)).choose_spec a
      change _ = c.aMap (i.2.1-i.1,i.2.2) _ at he
      have hm : c.aMap (i.2.1-i.1,i.2.2)
          (((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F
            i.1 (i.2.1-i.1,i.2.2)).arrow a) =
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F
            i.1 (i.2.1-i.1,i.2.2)).arrow a ≫ f := by rw [hca]; rfl
      exact he.trans (hm.trans hab)
    have hp := ConcreteCategory.congr_hom
      (show (towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded
          i.1 (i.2.1-i.1,i.2.2) ≫ Filtration.inducedAssocGradedMap c.aMap c.filtration_compat
            i.1 (i.2.1-i.1,i.2.2) =
        (c.filtration_compat i.1 (i.2.1-i.1,i.2.2)).choose ≫
          (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded
            i.1 (i.2.1-i.1,i.2.2) from cokernel.π_desc _ _ _) a
    simp only [ModuleCat.comp_apply] at hp
    have hp' := hp.trans (congrArg ((towerFiltration (nuCoefficientUnit H.unit D.nu)
      (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2)) hb)
    apply ((D.convergence B).identification i).toLinearEquiv.injective
    have he := ConcreteCategory.congr_hom hc (((D.convergence A).identification i).inv
      ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) a))
    simp only [ModuleCat.comp_apply] at he
    have hA := ((D.convergence A).identification i).toLinearEquiv.apply_symm_apply
      ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) a)
    have hB := ((D.convergence B).identification i).toLinearEquiv.apply_symm_apply
      ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) b)
    exact hB.trans (hp'.symm.trans ((congrArg
      (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 (i.2.1-i.1,i.2.2))
        hA.symm).trans he.symm))

  have detects_map (D : AdamsComparison H M Syn) (A B : SyntheticObject)
      (f : A.obj D.nu D.hopfAndDetector ⟶ B.obj D.nu D.hopfAndDetector) (i : Tridegree)
      (x : (D.family.obj (A.obj D.nu D.hopfAndDetector)).E₂ i)
      (a : BiHom (i.2.1-i.1) i.2.2 (A.obj D.nu D.hopfAndDetector))
      (ha : Detects (D.convergence A) i x a) :
      Detects (D.convergence B) i (familyPageMap D.family f 2 i x) (a ≫ f) := by
    obtain ⟨e,he,a',ha',hga⟩ := ha
    obtain ⟨c,hca,hce⟩ := D.comparisonCompatible.convergence_natural A B f
    let b := (c.filtration_compat i.1 (i.2.1-i.1,i.2.2)).choose a'
    have hb : ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F
        i.1 (i.2.1-i.1,i.2.2)).arrow b = a ≫ f := by
      have h := ConcreteCategory.congr_hom
        (c.filtration_compat i.1 (i.2.1-i.1,i.2.2)).choose_spec a'
      change _ = c.aMap (i.2.1-i.1,i.2.2) _ at h
      have hm : c.aMap (i.2.1-i.1,i.2.2)
          (((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F
            i.1 (i.2.1-i.1,i.2.2)).arrow a') = a ≫ f := by
        rw [hca]
        change _ ≫ f = _
        rw [ha']
      exact h.trans hm
    refine ⟨_,family_infinity_representative_map D f i x e he,b,hb,?_⟩
    have h := grade_natural D A B f i a' b (by rw [ha',hb])
    have haE : ((D.convergence A).identification i).inv
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded
          i.1 (i.2.1-i.1,i.2.2) a') = e := by
      rw [←hga]
      exact ((D.convergence A).identification i).toLinearEquiv.symm_apply_apply e
    rw [haE] at h
    exact (congrArg ((D.convergence B).identification i).hom h).symm.trans
      (((D.convergence B).identification i).toLinearEquiv.apply_symm_apply _)

  have detects_reflect (D : AdamsComparison H M Syn) (A B : SyntheticObject)
      (f : A.obj D.nu D.hopfAndDetector ⟶ B.obj D.nu D.hopfAndDetector) (i : Tridegree)
      (hf : Function.Injective ((D.family.functor.map f).eInftyMap i).hom)
      (x : (D.family.obj (A.obj D.nu D.hopfAndDetector)).E₂ i)
      (e : ((D.family.obj (A.obj D.nu D.hopfAndDetector)).sequence.ssData i).eInfty)
      (he : HasInfinityRepresentative _ 2 i x e)
      (a : BiHom (i.2.1-i.1) i.2.2 (A.obj D.nu D.hopfAndDetector))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) i.1 a)
      (hb : Detects (D.convergence B) i (familyPageMap D.family f 2 i x) (a ≫ f)) :
      Detects (D.convergence A) i x a := by
    have ha' : a ∈ (ModuleCat.subobjectModule _)
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F
          i.1 (i.2.1-i.1,i.2.2)) := by
      simpa only [FiltrationAtLeast,towerFiltration,OrderIso.apply_symm_apply] using ha
    obtain ⟨a',ha'⟩ := ha'
    obtain ⟨eB,heB,b,hb,hgb⟩ := hb
    have huniq := heB.unique (family_infinity_representative_map D f i x e he)
    have h := grade_natural D A B f i a' b (by rw [ha',hb])
    have hB : ((D.convergence B).identification i).inv
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded
          i.1 (i.2.1-i.1,i.2.2) b) = (D.family.functor.map f).eInftyMap i e := by
      rw [←hgb]
      exact (((D.convergence B).identification i).toLinearEquiv.symm_apply_apply eB).trans huniq
    have hA := hf (h.symm.trans hB)
    refine ⟨e,he,a',ha',?_⟩
    exact (congrArg ((D.convergence A).identification i).hom hA).symm.trans
      (((D.convergence A).identification i).toLinearEquiv.apply_symm_apply _)


  have first_label_detects (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D)
      (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
      (x : E2 H (X.obj D.hopfAndDetector) s t)
      (a : BiHom (t-s) t (XModLambdaN (nuZero D X) q))
      (ha : a ≫ (D.quotientTower (nuZero D X)).rho 1 q hq = firstLabel D X s t x) :
      Detects (D.convergence (.quotient q (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel D X q s t 0 x))
        (a ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q) := by
    let Z := D.nu.functor.obj (X.obj D.hopfAndDetector)
    let f : nuZero D X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
    have h0 : (s,t,t+0-(0:ℕ))=(s,t,t) := by simp
    let x0 : (D.family.obj (nuZero D X)).E₂ (s,t,t) :=
      (congrArg (fun i => ((D.family.obj (nuZero D X)).E₂ i : Type v)) h0).mp
        (D.nuE2 X 0 s t 0 x)
    let xq0 (n : ℕ) := familyPageMap D.family (XModLambdaN.incl (nuZero D X) n) 2 (s,t,t) x0
    let xq (n : ℕ) := familyPageMap D.family (XModLambdaN.incl Z n) 2 (s,t,t)
      (familyPageMap D.family f 2 (s,t,t) x0)
    have map_label (n : ℕ) :
        familyPageMap D.family (XModLambdaN.map f n) 2 (s,t,t) (xq0 n) = xq n := by
      dsimp only [xq0,xq]
      rw [←ModuleCat.comp_apply,family_page_comp,←XModLambdaN.incl_naturality]
      rw [←family_page_comp,ModuleCat.comp_apply]
    have rho_label :
        familyPageMap D.family ((D.quotientTower Z).rho 1 q hq) 2 (s,t,t) (xq q) = xq 1 := by
      dsimp only [xq]
      rw [←ModuleCat.comp_apply,family_page_comp,(D.quotientTower Z).rho_quotient]
    have hx : x ∈ cycles H (X.obj D.hopfAndDetector) q (s,t) :=
      (synthetic.finite_lift X q hq s t x).mpr ⟨a,ha⟩
    have transport_infinity {A : SyntheticAdamsSS.{v}} {i j : Tridegree}
        (h : i=j) (x : A.E₂ i)
        (hx : ∃ e : (A.sequence.ssData i).eInfty, HasInfinityRepresentative A 2 i x e) :
        ∃ e : (A.sequence.ssData j).eInfty,
          HasInfinityRepresentative A 2 j
            ((congrArg (fun k => (A.E₂ k : Type v)) h).mp x) e := by
      subst j
      exact hx
    have map_cast {A B : Syn} (g : A ⟶ B) {i j : Tridegree} (h : i=j)
        (x : (D.family.obj A).E₂ i) :
        (congrArg (fun k => ((D.family.obj B).E₂ k : Type v)) h).mp
          (familyPageMap D.family g 2 i x) =
        familyPageMap D.family g 2 j
          ((congrArg (fun k => ((D.family.obj A).E₂ k : Type v)) h).mp x) := by
      subst j
      rfl
    have hex : ∃ e0 : ((D.family.obj (XModLambdaN (nuZero D X) q)).sequence.ssData
        (s,t,t)).eInfty, HasInfinityRepresentative (D.family.obj (XModLambdaN (nuZero D X) q)) 2 (s,t,t) (xq0 q) e0 := by
      have hh := transport_infinity h0 (finiteNuLabel D X q 0 s t 0 x)
        (shifted_finite_source_exists D synthetic X q hq 0 s t x hx)
      have hl : (congrArg (fun k => ((D.family.obj (XModLambdaN (nuZero D X) q)).E₂ k : Type v)) h0).mp
          (finiteNuLabel D X q 0 s t 0 x) = xq0 q :=
        map_cast (XModLambdaN.incl (nuZero D X) q) h0 (D.nuE2 X 0 s t 0 x)
      exact (congrArg (fun z => ∃ e0 : ((D.family.obj (XModLambdaN (nuZero D X) q)).sequence.ssData
        (s,t,t)).eInfty, HasInfinityRepresentative (D.family.obj (XModLambdaN (nuZero D X) q)) 2 (s,t,t) z e0) hl).mp hh
    obtain ⟨e0,he0⟩ := hex
    have he := family_infinity_representative_map D (XModLambdaN.map f q) (s,t,t) _ e0 he0
    have he' : HasInfinityRepresentative (D.family.obj (XModLambdaN Z q)) 2 (s,t,t) (xq q)
        ((D.family.functor.map (XModLambdaN.map f q)).eInftyMap (s,t,t) e0) :=
      (congrArg (fun z => HasInfinityRepresentative (D.family.obj (XModLambdaN Z q)) 2 (s,t,t) z
        ((D.family.functor.map (XModLambdaN.map f q)).eInftyMap (s,t,t) e0)) (map_label q)).mp he
    have hb0 : Detects (D.convergence (.quotient 1 (.shift (0,0) (.nu X))))
        (s,t,t) (xq0 1) (firstLabel D X s t x) := by
      have transport_detects {A : SyntheticObject} {i j : Tridegree} (h : i=j)
          (x : (D.family.obj (A.obj D.nu D.hopfAndDetector)).E₂ i)
          (a : BiHom (i.2.1-i.1) i.2.2 (A.obj D.nu D.hopfAndDetector))
          (ha : Detects (D.convergence A) i x a) :
          Detects (D.convergence A) j
            ((congrArg (fun k => ((D.family.obj (A.obj D.nu D.hopfAndDetector)).E₂ k : Type v)) h).mp x)
            ((congrArg (fun k : Tridegree => BiHom (k.2.1-k.1) k.2.2 (A.obj D.nu D.hopfAndDetector)) h).mp a) := by
        subst j
        exact ha
      have h1 : (s,t,t+0)=(s,t,t) := by simp
      have h01 : (s,t,t+0-(0:ℕ))=(s,t,t+0) := by simp only [Nat.cast_zero,sub_zero]
      let x1 : (D.family.obj (nuZero D X)).E₂ (s,t,t+0) :=
        (congrArg (fun k => ((D.family.obj (nuZero D X)).E₂ k : Type v)) h01).mp
          (D.nuE2 X 0 s t 0 x)
      let a1 : BiHom (t-s) (t+0) (XModLambdaN (nuZero D X) 1) :=
        (D.firstQuotient (X.obj D.hopfAndDetector) 0 s t).symm x
      have hr : Detects (D.convergence (.quotient 1 (.shift (0,0) (.nu X)))) (s,t,t+0)
          (familyPageMap D.family (XModLambdaN.incl (nuZero D X) 1) 2 (s,t,t+0) x1) a1 :=
        D.comparisonCompatible.nu_first_quotient X 0 s t x
      have hh := transport_detects h1 _ _ hr
      have cast_comp {A B C : Type v} (hAB : A=B) (hBC : B=C) (hAC : A=C) (a : A) :
          hBC.mp (hAB.mp a) = hAC.mp a := by
        subst B
        subst C
        rfl
      have hx1 : (congrArg (fun k => ((D.family.obj (nuZero D X)).E₂ k : Type v)) h1).mp x1 = x0 := by
        exact cast_comp
          (congrArg (fun k => ((D.family.obj (nuZero D X)).E₂ k : Type v)) h01)
          (congrArg (fun k => ((D.family.obj (nuZero D X)).E₂ k : Type v)) h1)
          (congrArg (fun k => ((D.family.obj (nuZero D X)).E₂ k : Type v)) h0)
          (D.nuE2 X 0 s t 0 x)
      have hlabel : (congrArg (fun k => ((D.family.obj (XModLambdaN (nuZero D X) 1)).E₂ k : Type v)) h1).mp
          (familyPageMap D.family (XModLambdaN.incl (nuZero D X) 1) 2 (s,t,t+0) x1) = xq0 1 :=
        (map_cast _ h1 x1).trans (congrArg (familyPageMap D.family (XModLambdaN.incl (nuZero D X) 1)
          2 (s,t,t)) hx1)
      have halabel : (congrArg (fun k : Tridegree => BiHom (k.2.1-k.1) k.2.2
          (XModLambdaN (nuZero D X) 1)) h1).mp a1 = firstLabel D X s t x := by
        rfl
      exact (congrArg₂ (fun z a => Detects (D.convergence (.quotient 1 (.shift (0,0) (.nu X))))
        (s,t,t) z a) hlabel halabel).mp hh
    have hb := detects_map D (.quotient 1 (.shift (0,0) (.nu X))) (.quotient 1 (.nu X))
      (XModLambdaN.map f 1) (s,t,t) _ _ hb0
    have hb' : Detects (D.convergence (.quotient 1 (.nu X))) (s,t,t) (xq 1)
        (firstLabel D X s t x ≫ XModLambdaN.map f 1) :=
      (congrArg (fun z => Detects (D.convergence (.quotient 1 (.nu X))) (s,t,t) z
        (firstLabel D X s t x ≫ XModLambdaN.map f 1)) (map_label 1)).mp hb
    have hactual :
        (a ≫ XModLambdaN.map f q) ≫ (D.quotientTower Z).rho 1 q hq =
          firstLabel D X s t x ≫ XModLambdaN.map f 1 := by
      rw [Category.assoc,←(D.comparisonCompatible.quotient_naturality f).rho_naturality,
        ←Category.assoc,ha]
    have hinj : Function.Injective ((D.family.functor.map ((D.quotientTower Z).rho 1 q hq)).eInftyMap
        (s,t,t)).hom :=
      KIP126.Comparison.syntheticEInfty_rho_finite_injective
        H D.nu D.family synthetic.eInfty.presentation synthetic.eInfty.weightShift
        (fun Y => D.quotientTower (D.nu.functor.obj Y)) synthetic.eInfty.maps
        (X.obj D.hopfAndDetector) 1 q (by decide) hq (s,t) t (by omega)
    have hdet := detects_reflect D (.quotient q (.nu X)) (.quotient 1 (.nu X))
      ((D.quotientTower Z).rho 1 q hq) (s,t,t) hinj (xq q) _ he'
      (a ≫ XModLambdaN.map f q) (finite_bottom_filtration D synthetic X q hq s t _)
      ((congrArg₂ (fun z b => Detects (D.convergence (.quotient 1 (.nu X))) (s,t,t) z b)
        rho_label hactual).mpr hb')
    have htarget : regradeE2 (by simp) (finiteTargetLabel D X q s t 0 x) = xq q := by
      have h2 : (s,t,t-(0:ℕ))=(s,t,t) := by simp
      have h02 : (s,t,t+0-(0:ℕ))=(s,t,t-(0:ℕ)) := by simp only [add_zero]
      let x2 : (D.family.obj (nuZero D X)).E₂ (s,t,t-(0:ℕ)) :=
        (congrArg (fun k => ((D.family.obj (nuZero D X)).E₂ k : Type v)) h02).mp
          (D.nuE2 X 0 s t 0 x)
      have cast_comp {A B C : Type v} (hAB : A=B) (hBC : B=C) (hAC : A=C) (a : A) :
          hBC.mp (hAB.mp a) = hAC.mp a := by
        subst B
        subst C
        rfl
      have hx2 : (congrArg (fun k => ((D.family.obj (nuZero D X)).E₂ k : Type v)) h2).mp x2 = x0 :=
        cast_comp
          (congrArg (fun k => ((D.family.obj (nuZero D X)).E₂ k : Type v)) h02)
          (congrArg (fun k => ((D.family.obj (nuZero D X)).E₂ k : Type v)) h2)
          (congrArg (fun k => ((D.family.obj (nuZero D X)).E₂ k : Type v)) h0)
          (D.nuE2 X 0 s t 0 x)
      have regrade_cast {A : SyntheticAdamsSS.{v}} {i j : Tridegree} (h : i=j) (x : A.E₂ i) :
          regradeE2 h x = (congrArg (fun k => (A.E₂ k : Type v)) h).mp x := by
        subst j
        rfl
      rw [regrade_cast]
      exact (map_cast (XModLambdaN.incl Z q) h2 _).trans (congrArg
        (familyPageMap D.family (XModLambdaN.incl Z q) 2 (s,t,t))
        ((map_cast f h2 x2).trans (congrArg (familyPageMap D.family f 2 (s,t,t)) hx2)))
    exact (congrArg (fun z => Detects (D.convergence (.quotient q (.nu X))) (s,t,t) z
      (a ≫ XModLambdaN.map f q)) htarget).mpr hdet

  let Z := D.nu.functor.obj (X.obj D.hopfAndDetector)
  let f : nuZero D X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
  let g : Z ⟶ nuZero D X := SyntheticCategory.biShift_zero.inv.app _
  have hfg : f ≫ g = 𝟙 _ := Iso.hom_inv_id_app _ _
  have hgf : g ≫ f = 𝟙 _ := Iso.inv_hom_id_app _ _
  have hfirst : (a ≫ XModLambdaN.map g q) ≫ (D.quotientTower (nuZero D X)).rho 1 q hq =
      firstLabel D X s t x := by
    rw [Category.assoc,←(D.comparisonCompatible.quotient_naturality g).rho_naturality,
      ←Category.assoc,ha,Category.assoc,←D.quotientFunctoriality.map_comp,hfg,
      D.quotientFunctoriality.map_id,Category.comp_id]
  have h := first_label_detects D synthetic X q hq s t x (a ≫ XModLambdaN.map g q) hfirst
  have hback : (a ≫ XModLambdaN.map g q) ≫ XModLambdaN.map f q = a := by
    rw [Category.assoc,←D.quotientFunctoriality.map_comp,hgf,
      D.quotientFunctoriality.map_id,Category.comp_id]
  exact (congrArg (fun a => Detects (D.convergence (.quotient q (.nu X))) (s,t,t)
    (regradeE2 (by simp) (finiteTargetLabel D X q s t 0 x)) a) hback).mp h

/- Actual finite-quotient boundary correction, using the same selected
triangles and the finite E∞ window (MainPaper prop:6de7d130). -/
open CategoryTheory.Pretriangulated KIP126.SpectralSequence.FinitePageCalculus in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 1600000 in
private theorem actual_rho_kernel_correction
    (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject)
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q) (s t : ℤ)
    (y : cycles H (X.obj D.hopfAndDetector) ((q:ℤ)-t+(t-(q-1:ℕ))) (s,t))
    (hy : y.val ∈ boundaries H (X.obj D.hopfAndDetector) (d+q:ℕ) (s,t))
    (c : BiHom (t-s) (t-(q-1:ℕ))
      (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q))
    (hc : Detects (D.convergence (.quotient q (.nu X)))
      (s,t,t-(q-1:ℕ)) (finiteTargetLabel D X q s t (q-1) y.val) c) :
    let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
    let δ1 : XModLambdaN A (d+1) ⟶
        ((SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
      simpa only [Nat.add_sub_cancel_left] using
        ((D.quotientTower A).triangle (by omega : 0<d+1)
          (show d+1<d+1+q by omega)).delta
    ∃ a : BiHom ((t-s)+1) ((t-(q-1:ℕ))-((d+1:ℕ):ℤ)) (XModLambdaN A (d+1)),
      a ≫ (D.quotientTower A).rho 1 (d+1) (by omega) = 0 ∧
      homotopyRegrade (by omega) (by omega)
        (biSuspensionHomEquiv ((t-s)+1) ((t-(q-1:ℕ))-((d+1:ℕ):ℤ)) ((d+1:ℕ):ℤ)
          (XModLambdaN A q) (a≫δ1)) = c := by
  have shifted_finite_high_filtration_zero (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject) (r : ℕ) (hr : 0<r)
      (i n w s : ℤ) (hs : (r:ℤ) ≤ n+s-(w-i))
      (a : BiHom n w ((SyntheticCategory.biShift (0,i)).obj
        (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) r)))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) : a=0 := by
    let B : SyntheticObject := .shift (0,i) (.quotient r (.nu X))
    have hz (j : ℤ) (hj : s≤j) :
        IsZero (((D.family.obj (B.obj D.nu D.hopfAndDetector)).sequence.ssData (j,n+j,w)).eInfty) := by
      have hwin : ¬(0≤(n+j)-(w-i) ∧ (n+j)-(w-i)<r) := by omega
      haveI : Subsingleton (finiteEInftyModel H (X.obj D.hopfAndDetector) r (j,n+j) (w-i)) := by
        simp only [finiteEInftyModel,hwin,ite_false]
        infer_instance
      haveI : Subsingleton (((D.family.obj (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) r)).sequence.ssData
          (j,n+j,w-i)).eInfty) :=
        (synthetic.eInfty.presentation.finite (X.obj D.hopfAndDetector) r hr (j,n+j) (w-i)).injective.subsingleton
      have he := synthetic.eInfty.weightShift.iso
        (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) r) i (j,n+j) (w-i)
      rw [sub_add_cancel] at he
      haveI : Subsingleton (((D.family.obj (B.obj D.nu D.hopfAndDetector)).sequence.ssData
          (j,n+j,w)).eInfty) := he.injective.subsingleton
      exact ModuleCat.isZero_of_subsingleton _
    apply D.homotopySeparated B n w a
    intro j
    by_cases hj : s≤(j:ℤ)
    · exact ((D.convergence B).filtrationAtLeast_iff_of_eInfty_isZero s j n w hj
        (fun k hk _ => hz k hk) a).mp ha
    · exact towerFiltrationSubmodule_antitone (nuCoefficientUnit H.unit D.nu) _ (n,w)
        (by omega) ha

  have detected_map_zero_above_shifted_finite_top (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (A : SyntheticObject) (X : ClassicalObject)
      (r : ℕ) (hr : 0<r) (i s t w : ℤ) (htop : (r:ℤ) ≤ t+1-(w-i))
      (h : A.obj D.nu D.hopfAndDetector ⟶ (SyntheticCategory.biShift (0,i)).obj
        (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) r))
      (x : (D.family.obj (A.obj D.nu D.hopfAndDetector)).E₂ (s,t,w))
      (a : BiHom (t-s) w (A.obj D.nu D.hopfAndDetector))
      (ha : Detects (D.convergence A) (s,t,w) x a)
      (e : ((D.family.obj (A.obj D.nu D.hopfAndDetector)).sequence.ssData (s,t,w)).eInfty)
      (he : HasInfinityRepresentative (D.family.obj (A.obj D.nu D.hopfAndDetector)) 2 (s,t,w) x e)
      (hzero : (D.family.functor.map h).eInftyMap (s,t,w) e=0) : a≫h=0 := by
    let B : SyntheticObject := .shift (0,i) (.quotient r (.nu X))
    obtain ⟨e',he',a',ha',hga⟩ := ha
    have heq := he'.unique he
    subst e'
    obtain ⟨c,hca,hce⟩ := D.comparisonCompatible.convergence_natural A B h
    let b := (c.filtration_compat s (t-s,w)).choose a'
    have hb : ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F
        s (t-s,w)).arrow b = a≫h := by
      have hh := ConcreteCategory.congr_hom (c.filtration_compat s (t-s,w)).choose_spec a'
      change _ = c.aMap (t-s,w) _ at hh
      have hm : c.aMap (t-s,w)
          (((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F
            s (t-s,w)).arrow a') = a≫h := by
        rw [hca]
        change _≫h = _
        rw [ha']
      exact hh.trans hm
    have hc := c.iso_compat (s,t,w)
    simp only [KIP126.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,
      TowerConvergence.toSynthetic,SyntheticAdamsConvergence.toConvergence] at hc
    rw [hce] at hc
    have hc' := ConcreteCategory.congr_hom hc e
    simp only [ModuleCat.comp_apply] at hc'
    have hci : ((D.convergence B).identification (s,t,w)).hom
        ((D.family.functor.map h).eInftyMap (s,t,w) e) = 0 :=
      (congrArg ((D.convergence B).identification (s,t,w)).hom hzero).trans (map_zero _)
    have hgr : (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s (t-s,w))
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded
          s (t-s,w) a') = 0 :=
      (congrArg (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s (t-s,w)) hga).symm.trans
        (hc'.symm.trans hci)
    have hp := ConcreteCategory.congr_hom
      (show (towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded
          s (t-s,w) ≫ Filtration.inducedAssocGradedMap c.aMap c.filtration_compat s (t-s,w) =
        (c.filtration_compat s (t-s,w)).choose ≫
          (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded
            s (t-s,w) from cokernel.π_desc _ _ _) a'
    simp only [ModuleCat.comp_apply] at hp
    have hg : (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded
        s (t-s,w) b = 0 := hp.symm.trans hgr
    have hm := (subobject_cokernel_π_eq_zero_iff
      ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F (s+1) (t-s,w))
      ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F s (t-s,w))
      ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).mono s (t-s,w)) b).mp hg
    have hnext : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (s+1) (a≫h) := by
      change FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) (s+1)
        (a≫h : BiHom (t-s) w (B.obj D.nu D.hopfAndDetector))
      rw [←hb]
      simpa only [FiltrationAtLeast,towerFiltration,OrderIso.apply_symm_apply] using hm
    exact shifted_finite_high_filtration_zero D synthetic X r hr i (t-s) w (s+1)
      (by omega) (a≫h) hnext

  have biSuspensionIso_natural (i : ℤ) {A B : Syn} (f : A ⟶ B) :
      (SyntheticCategory.biShift (1,-i)).map f ≫ (biSuspensionIso i B).hom =
        (biSuspensionIso i A).hom ≫
          (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-i)).map f) := by
    let e : (SyntheticCategory.biShift ((0,-i)+(1,0)) : Syn ⥤ Syn) ≅
        SyntheticCategory.biShift (0,-i) ⋙ shiftFunctor Syn (1:ℤ) :=
      (SyntheticCategory.biShift_comp (0,-i) (1,0)).symm ≪≫
        Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,-i)) (SyntheticCategory.biShift_compat 1)
    have cast_natural (p p' : ℤ×ℤ) (hp : p=p')
        (E : (SyntheticCategory.biShift p : Syn ⥤ Syn) ≅
          SyntheticCategory.biShift (0,-i) ⋙ shiftFunctor Syn (1:ℤ))
        (hA : ((SyntheticCategory.biShift p).obj A ≅
          (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj A)) =
          ((SyntheticCategory.biShift p').obj A ≅
          (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj A)))
        (hB : ((SyntheticCategory.biShift p).obj B ≅
          (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj B)) =
          ((SyntheticCategory.biShift p').obj B ≅
          (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj B))) :
        (SyntheticCategory.biShift p').map f ≫ (cast hB (E.app B)).hom =
          (cast hA (E.app A)).hom ≫
            (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-i)).map f) := by
      subst p'
      exact E.hom.naturality f
    unfold biSuspensionIso
    exact cast_natural ((0,-i)+(1,0)) (1,-i) (by ext <;> simp) e _ _

  have shifted_representative_zero_iff (n w i : ℤ) (Q B : Syn)
      (L : (SyntheticCategory.biShift (0,-i)).obj Q ⟶ B)
      (c : BiHom (n-1) (w+i) Q) :
      (biSuspensionHomEquiv n w i Q).symm c ≫ (shiftFunctor Syn (1:ℤ)).map L = 0 ↔
        (SyntheticCategory.biShift (0,-i)).map c ≫ L = 0 := by
    let e0 := (susp_invariance (n-1) (w+i) 1 (-i) Q).trans
      (Iso.homCongr (Iso.refl _) (biSuspensionIso i Q))
    have h0 : e0 c ≫ (shiftFunctor Syn (1:ℤ)).map L = 0 ↔
        (SyntheticCategory.biShift (0,-i)).map c ≫ L = 0 := by
      change (𝟙 _ ≫ ((SyntheticCategory.biShift_comp (n-1,w+i) (1,-i)).inv.app S_0_0 ≫
        (SyntheticCategory.biShift (1,-i)).map c ≫ 𝟙 _) ≫ (biSuspensionIso i Q).hom) ≫
          (shiftFunctor Syn (1:ℤ)).map L = 0 ↔ _
      simp only [Category.id_comp,Category.comp_id,Category.assoc]
      rw [← Category.assoc ((SyntheticCategory.biShift (1,-i)).map c),
        biSuspensionIso_natural]
      simp only [Category.assoc]
      rw [←Functor.map_comp]
      constructor
      · intro h
        apply (shiftFunctor Syn (1:ℤ)).map_injective
        rw [Functor.map_zero]
        apply (cancel_epi (biSuspensionIso i (Smn (n-1) (w+i))).hom).mp
        apply (cancel_epi ((SyntheticCategory.biShift_comp (n-1,w+i) (1,-i)).inv.app S_0_0)).mp
        simpa only [comp_zero,Category.assoc] using h
      · intro h
        simp only [h,Functor.map_zero,comp_zero]
    have cast_equiv (n' w' : ℤ) (hn:n'=n) (hw:w'=w)
        (e' : BiHom (n-1) (w+i) Q ≃
          BiHom n' w' (((SyntheticCategory.biShift (0,-i)).obj Q)⟦(1:ℤ)⟧))
        (he' : e' c ≫ (shiftFunctor Syn (1:ℤ)).map L = 0 ↔
          (SyntheticCategory.biShift (0,-i)).map c ≫ L = 0)
        (ht : (BiHom (n-1) (w+i) Q ≃
          BiHom n' w' (((SyntheticCategory.biShift (0,-i)).obj Q)⟦(1:ℤ)⟧)) =
          (BiHom (n-1) (w+i) Q ≃
          BiHom n w (((SyntheticCategory.biShift (0,-i)).obj Q)⟦(1:ℤ)⟧))) :
        (cast ht e') c ≫ (shiftFunctor Syn (1:ℤ)).map L = 0 ↔
          (SyntheticCategory.biShift (0,-i)).map c ≫ L = 0 := by
      subst n'
      subst w'
      exact he'
    change (biSuspensionHomUnderlyingEquiv n w i Q).symm c ≫ _ = 0 ↔ _
    dsimp only [biSuspensionHomUnderlyingEquiv,Equiv.symm_symm]
    exact cast_equiv (n-1+1) (w+i+-i) (sub_add_cancel n 1)
      (add_neg_cancel_right w i) e0 h0 _

  have shifted_composite_zero_of_conjugate
      (i : ℤ) {A Q B Y : Syn} (c : A ⟶ Q) (h : Q ⟶ B)
      (L : (SyntheticCategory.biShift (0,-i)).obj Q ⟶ Y)
      (ε : (SyntheticCategory.biShift (0,-i)).obj B ≅ Y)
      (hL : (SyntheticCategory.biShift (0,-i)).map h ≫ ε.hom = L) :
      (SyntheticCategory.biShift (0,-i)).map c ≫ L = 0 ↔ c ≫ h = 0 := by
    letI := (SyntheticCategory.biShift_fullyFaithful (Syn:=Syn) (0,-i)).faithful
    rw [←hL,←Category.assoc,←Functor.map_comp]
    constructor
    · intro hz
      apply (SyntheticCategory.biShift (0,-i)).map_injective
      rw [Functor.map_zero]
      apply (cancel_mono ε.hom).mp
      simpa only [zero_comp] using hz
    · intro hz
      rw [hz,Functor.map_zero,zero_comp]

  have weight_shift_kernel_via_transpose
      (F : SyntheticAdamsFamily Syn) (S : EInftyWeightShift F) (hS : S.Natural)
      (A B Y : Syn) (k : ℤ) (p : ℤ×ℤ) (w : ℤ)
      (h : A ⟶ B) (ε : (SyntheticCategory.biShift (0,k)).obj B ≅ Y)
      (g : (SyntheticCategory.biShift (0,k)).obj A ⟶ Y)
      (hg : (SyntheticCategory.biShift (0,k)).map h ≫ ε.hom = g)
      (e : ((F.obj A).sequence.ssData (p.1,p.2,w)).eInfty) :
      ((F.functor.map g).eInftyMap (p.1,p.2,w+k))
        ((S.iso A k p w).symm e) = 0 ↔
      ((F.functor.map h).eInftyMap (p.1,p.2,w)) e = 0 := by
    let V (j : Tridegree) : Syn ⥤ ModuleCat.{v} ℤ := F.functor ⋙
      { obj := fun E => (E.ssData j).eInfty
        map := fun f => f.eInftyMap j
        map_id := fun E => SpectralSequenceMorphism.eInftyMap_id E j
        map_comp := fun f g => SpectralSequenceMorphism.eInftyMap_comp f g j }
    have hs := hS h k p w ((S.iso A k p w).symm e)
    rw [LinearEquiv.apply_symm_apply] at hs
    have hz : ((F.functor.map ((SyntheticCategory.biShift (0,k)).map h)).eInftyMap
          (p.1,p.2,w+k)) ((S.iso A k p w).symm e) = 0 ↔
        ((F.functor.map h).eInftyMap (p.1,p.2,w)) e = 0 := by
      rw [←hs]
      exact (LinearEquiv.map_eq_zero_iff _).symm
    change (V (p.1,p.2,w+k)).map g ((S.iso A k p w).symm e) = 0 ↔ _
    rw [←hg,Functor.map_comp,ModuleCat.comp_apply]
    exact (LinearEquiv.map_eq_zero_iff (((V (p.1,p.2,w+k)).mapIso ε).toLinearEquiv)).trans hz

  have weight_shift_lower_kernel_via_transpose
      (F : SyntheticAdamsFamily Syn) (S : EInftyWeightShift F) (hS : S.Natural)
      (A B Y : Syn) (i : ℕ) (p : ℤ×ℤ) (w : ℤ)
      (h : A ⟶ B) (ε : (SyntheticCategory.biShift (0,-(i:ℤ))).obj B ≅ Y)
      (g : (SyntheticCategory.biShift (0,-(i:ℤ))).obj A ⟶ Y)
      (hg : (SyntheticCategory.biShift (0,-(i:ℤ))).map h ≫ ε.hom = g)
      (e : ((F.obj A).sequence.ssData (p.1,p.2,w)).eInfty) :
      ((F.functor.map g).eInftyMap (p.1,p.2,w-i))
        ((S.lowerIso A i p w).symm e) = 0 ↔
      ((F.functor.map h).eInftyMap (p.1,p.2,w)) e = 0 := by
    have transport (A B : ℤ → ModuleCat.{v} ℤ) (T : ModuleCat.{v} ℤ)
        (f : ∀ n, A n ⟶ B n) (j j' : ℤ) (hj : j=j')
        (v : T) (a : A j' ≃ₗ[ℤ] T) :
        f j ((Eq.mpr (congrArg (fun n => A n ≃ₗ[ℤ] T) hj) a).symm v) = 0 ↔
          f j' (a.symm v) = 0 := by
      subst j'
      rfl
    have ht := transport
      (fun n => ((F.obj ((SyntheticCategory.biShift (0,-(i:ℤ))).obj A)).sequence.ssData (p.1,p.2,n)).eInfty)
      (fun n => ((F.obj Y).sequence.ssData (p.1,p.2,n)).eInfty)
      (((F.obj A).sequence.ssData (p.1,p.2,w)).eInfty)
      (fun n => (F.functor.map g).eInftyMap (p.1,p.2,n))
      (w-i) (w+(-(i:ℤ))) (sub_eq_add_neg _ _) e (S.iso A (-(i:ℤ)) p w)
    exact ht.trans (weight_shift_kernel_via_transpose F S hS A B Y (-(i:ℤ)) p w h ε g hg e)

  have finite_target_boundary_lambda_zero (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject)
      (r i : ℕ) (hi : 0 < i) (hir : i < r) (s t : ℤ)
      (y : cycles H (X.obj D.hopfAndDetector) ((r-i:ℕ)-t+(t-(r-i-1:ℕ))) (s,t))
      (hy : y.val ∈ boundaries H (X.obj D.hopfAndDetector) r (s,t))
      (b : BiHom (t-s) (t-(r-i-1:ℕ))
        (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) (r-i)))
      (hb : Detects (D.convergence (.quotient (r-i) (.nu X)))
        (s,t,t-(r-i-1:ℕ)) (finiteTargetLabel D X (r-i) s t (r-i-1) y.val) b) :
      (SyntheticCategory.biShift (0,-(i:ℤ))).map b ≫
        ((D.quotientTower (D.nu.functor.obj (X.obj D.hopfAndDetector))).triangle hi hir).lambdaMap = 0 := by
    let Q := XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) (r-i)
    let Y := XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) r
    let T := (D.quotientTower (D.nu.functor.obj (X.obj D.hopfAndDetector))).triangle hi hir
    obtain ⟨e,he,ha⟩ := hb
    have hwin : 0≤t-(t-(r-i-1:ℕ)) ∧ t-(t-(r-i-1:ℕ))<(r-i:ℕ) := by omega
    have hlabel := (synthetic.eInfty.labels.1 X (r-i) (by omega) (s,t) (r-i-1) (by omega) y e).mp he
    have hk := synthetic.eInfty.maps.lambda_finite (X.obj D.hopfAndDetector) r i hir (s,t)
      (t-(r-i-1:ℕ)) hwin e
    rw [hlabel] at hk
    have hk0 : synthetic.eInfty.weightShift.finiteLambdaMap
        (D.quotientTower (D.nu.functor.obj (X.obj D.hopfAndDetector))) r i hir (s,t)
        (t-(r-i-1:ℕ)) e = 0 := by
      apply (synthetic.eInfty.presentation.finiteWindow (X.obj D.hopfAndDetector) r (by omega)
        (s,t) ((t-(r-i-1:ℕ))-i) (by constructor <;> omega)).injective
      rw [map_zero,hk]
      exact (KIP126.Algebra.NestedQuotient.map_projection_eq_zero
        (cycles_antitone H (X.obj D.hopfAndDetector) (s,t)
          (by omega : (r:ℤ)-t+((t-(r-i-1:ℕ))-i) ≤ (r-i:ℕ)-t+(t-(r-i-1:ℕ))))
        (boundaries_monotone H (X.obj D.hopfAndDetector) (s,t)
          (by omega : 1+t-(t-(r-i-1:ℕ)) ≤ 1+t-((t-(r-i-1:ℕ))-i))) y).mpr
          (by convert hy using 1; congr 1; omega)
    let ε : (SyntheticCategory.biShift (0,-(i:ℤ))).obj
        ((SyntheticCategory.biShift (0,(i:ℤ))).obj Y) ≅ Y :=
      (SyntheticCategory.biShift_comp (0,(i:ℤ)) (0,-(i:ℤ))).app Y ≪≫
        eqToIso (congrArg (fun k => (SyntheticCategory.biShift k).obj Y)
          (show (0,(i:ℤ))+(0,-(i:ℤ))=(0,0) by ext <;> simp)) ≪≫
        SyntheticCategory.biShift_zero.app Y
    let h : Q ⟶ (SyntheticCategory.biShift (0,(i:ℤ))).obj Y :=
      (SyntheticCategory.biShift_fullyFaithful (0,-(i:ℤ))).preimage (T.lambdaMap ≫ ε.inv)
    have hh : (SyntheticCategory.biShift (0,-(i:ℤ))).map h ≫ ε.hom = T.lambdaMap := by
      rw [show (SyntheticCategory.biShift (0,-(i:ℤ))).map h = T.lambdaMap ≫ ε.inv from
        (SyntheticCategory.biShift_fullyFaithful (0,-(i:ℤ))).map_preimage _,
        Category.assoc,ε.inv_hom_id,Category.comp_id]
    have hzero : (D.family.functor.map h).eInftyMap (s,t,t-(r-i-1:ℕ)) e=0 :=
      (weight_shift_lower_kernel_via_transpose D.family synthetic.eInfty.weightShift
        synthetic.eInfty.maps.shift_natural Q _ Y i (s,t) (t-(r-i-1:ℕ)) h ε T.lambdaMap hh e).mp
        (by
          change (D.family.functor.map
            ((D.quotientTower (D.nu.functor.obj (X.obj D.hopfAndDetector))).lambdaInclusion i r hir)).eInftyMap
            (s,t,(t-(r-i-1:ℕ))-i)
            ((synthetic.eInfty.weightShift.lowerIso Q i (s,t) (t-(r-i-1:ℕ))).symm e)=0 at hk0
          simpa only [FiniteLambdaQuotientTower.lambdaInclusion,dif_neg (Nat.ne_of_gt hi),T,Y] using hk0)
    have hb0 : b≫h=0 := detected_map_zero_above_shifted_finite_top D synthetic
      (.quotient (r-i) (.nu X)) X r (by omega) i s t (t-(r-i-1:ℕ)) (by omega)
      h (finiteTargetLabel D X (r-i) s t (r-i-1) y.val) b ⟨e,he,ha⟩ e he hzero
    have hshift : (SyntheticCategory.biShift (0,-(i:ℤ))).map b≫T.lambdaMap=0 :=
      (shifted_composite_zero_of_conjugate (i:ℤ) b h T.lambdaMap ε hh).mpr hb0
    exact hshift

  have quotient_maps_difference_factors {A B : Syn} (j : ℕ)
      (a b : XModLambdaN A j ⟶ B)
      (hab : XModLambdaN.incl A j ≫ a = XModLambdaN.incl A j ≫ b) :
      ∃ z : ((SyntheticCategory.biShift (0,-(j:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶ B,
        a-b = XModLambdaN.proj A j ≫ z := by
    apply Triangle.yoneda_exact₃ (XModLambdaN.cofiberTriangle A j)
      (XModLambdaN.cofiberTriangle_distinguished A j) (a-b)
    change XModLambdaN.incl A j ≫ (a-b) = 0
    rw [Preadditive.comp_sub,hab,sub_self]

  have quotient_maps_equal_on_spheres_of_no_return {A B : Syn} (j : ℕ)
      (a b : XModLambdaN A j ⟶ B)
      (hab : XModLambdaN.incl A j ≫ a = XModLambdaN.incl A j ≫ b)
      (hzero : ∀ (m w : ℤ)
        (c : BiHom m w (((SyntheticCategory.biShift (0,-(j:ℤ))).obj A)⟦(1:ℤ)⟧))
        (z : ((SyntheticCategory.biShift (0,-(j:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶ B), c ≫ z = 0) :
      ∀ (m w : ℤ) (c : BiHom m w (XModLambdaN A j)), c ≫ a = c ≫ b := by
    obtain ⟨z,hz⟩ := quotient_maps_difference_factors j a b hab
    intro m w c
    apply sub_eq_zero.mp
    rw [←Preadditive.comp_sub,hz,←Category.assoc]
    exact hzero m w (c ≫ XModLambdaN.proj A j) z

  have negative_shift_nu_to_quotient_zero
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D) (X Y : ClassicalObject)
      (j : ℕ) (hj : 0 < j) (m w : ℤ)
      (c : BiHom m w ((SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
        (D.nu.functor.obj (X.obj D.hopfAndDetector))))
      (z : (SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
        (D.nu.functor.obj (X.obj D.hopfAndDetector)) ⟶
          XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) j) : c ≫ z = 0 := by
    let A : SyntheticObject := .shift (0,-(j:ℤ)-1) (.nu X)
    let B : SyntheticObject := .quotient j (.nu Y)
    let L : ℤ := w-m+j+1
    have hzA (k : ℤ) (hk : k < L) :
        IsZero (((D.family.obj (A.obj D.nu D.hopfAndDetector)).sequence.ssData (k,m+k,w)).eInfty) := by
      letI : Subsingleton (((D.family.obj (D.nu.functor.obj (X.obj D.hopfAndDetector))).sequence.ssData
          (k,m+k,w+j+1)).eInfty) :=
        KIP126.Comparison.syntheticEInfty_nu_subsingleton_of_outside
          H D.nu D.family synthetic.eInfty.presentation (X.obj D.hopfAndDetector) (k,m+k) (w+j+1)
            (by dsimp only [L] at hk; omega)
      have hSub : Subsingleton (((D.family.obj ((SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
          (D.nu.functor.obj (X.obj D.hopfAndDetector)))).sequence.ssData
            (k,m+k,(w+j+1)+(-(j:ℤ)-1))).eInfty) :=
        (synthetic.eInfty.weightShift.iso _ (-(j:ℤ)-1) (k,m+k) (w+j+1)).injective.subsingleton
      have he : (w+(j:ℤ)+1)+(-(j:ℤ)-1)=w := by omega
      rw [he] at hSub
      letI := hSub
      change IsZero (((D.family.obj ((SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
        (D.nu.functor.obj (X.obj D.hopfAndDetector)))).sequence.ssData (k,m+k,w)).eInfty)
      exact ModuleCat.isZero_of_subsingleton _
    have hc0 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 0 c := by
      refine ⟨c,?_⟩
      change c ≫ adamsTowerMap _ _ 0 0 _ = c
      rw [adamsTowerMap_self]
      exact Category.comp_id c
    have hcL : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) L c := by
      by_cases hL : L≤0
      · exact towerFiltrationSubmodule_antitone _ _ _ hL hc0
      · exact ((D.convergence A).filtrationAtLeast_iff_of_eInfty_isZero 0 L m w
          (by omega) (fun k _ hk => hzA k hk) c).mp hc0
    have hcz : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) L (c ≫ z) := by
      obtain ⟨a,ha⟩ := hcL
      refine ⟨a ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) z L.toNat,?_⟩
      change (a ≫ adamsTowerInduced _ z L.toNat) ≫ adamsTowerMap _ _ 0 L.toNat _ = c ≫ z
      rw [Category.assoc,adamsTowerInduced_map,←Category.assoc]
      change (towerHomotopyMap (nuCoefficientUnit H.unit D.nu) _ L.toNat (m,w) a) ≫ z = _
      rw [ha]
    have hzB (k : ℤ) (hk : L≤k) :
        IsZero (((D.family.obj (B.obj D.nu D.hopfAndDetector)).sequence.ssData (k,m+k,w)).eInfty) := by
      haveI : Subsingleton (((D.family.obj (XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) j)).sequence.ssData
          (k,m+k,w)).eInfty) :=
        KIP126.Comparison.syntheticEInfty_finite_subsingleton_of_outside
          H D.nu D.family synthetic.eInfty.presentation (Y.obj D.hopfAndDetector) j hj (k,m+k) w
            (by dsimp only [L] at hk; omega)
      change IsZero (((D.family.obj (XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) j)).sequence.ssData
        (k,m+k,w)).eInfty)
      exact ModuleCat.isZero_of_subsingleton _
    apply D.homotopySeparated B m w (c ≫ z)
    intro k
    by_cases hk : L≤(k:ℤ)
    · exact ((D.convergence B).filtrationAtLeast_iff_of_eInfty_isZero L k m w hk
        (fun t ht _ => hzB t ht) (c ≫ z)).mp hcz
    · exact towerFiltrationSubmodule_antitone _ _ _ (by omega) hcz

  have quotient_nu_maps_equal_on_spheres
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D) (X Y : ClassicalObject)
      (j : ℕ) (hj : 0 < j)
      (a b : XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) j ⟶
        XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) j)
      (hab : XModLambdaN.incl _ j ≫ a = XModLambdaN.incl _ j ≫ b) :
      ∀ (m w : ℤ) (c : BiHom m w (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) j)),
        c ≫ a = c ≫ b := by
    apply quotient_maps_equal_on_spheres_of_no_return j a b hab
    intro m w c z
    let V := D.nu.functor.obj (X.obj D.hopfAndDetector)
    let ε : ((SyntheticCategory.biShift (0,-(j:ℤ))).obj V)⟦(1:ℤ)⟧ ≅
        (SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
          (D.nu.functor.obj ((ClassicalObject.shift 1 X).obj D.hopfAndDetector)) :=
      (SyntheticCategory.biShift_compat (Syn:=Syn) 1).symm.app _ ≪≫
        (SyntheticCategory.biShift_comp (0,-(j:ℤ)) (1,0)).app V ≪≫
        eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj V)
          (show (0,-(j:ℤ))+(1,0)=(1,1)+(0,-(j:ℤ)-1) by ext <;> simp)) ≪≫
        (SyntheticCategory.biShift_comp (1,1) (0,-(j:ℤ)-1)).symm.app V ≪≫
        (SyntheticCategory.biShift (0,-(j:ℤ)-1)).mapIso (D.nu.suspensionIso _).symm
    have h := negative_shift_nu_to_quotient_zero D synthetic (.shift 1 X) Y j hj m w
      (c ≫ ε.hom) (ε.inv ≫ z)
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h

  have shift_minus_one_quotient_maps_equal_on_spheres
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D) (X Y : ClassicalObject)
      (d : ℕ)
      (a b : (SyntheticCategory.biShift (0,-1)).obj
          (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) d) ⟶
        XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) (d+1))
      (hab : (SyntheticCategory.biShift (0,-1)).map (XModLambdaN.incl _ d) ≫ a =
        (SyntheticCategory.biShift (0,-1)).map (XModLambdaN.incl _ d) ≫ b) :
      ∀ (m w : ℤ) (c : BiHom m w ((SyntheticCategory.biShift (0,-1)).obj
          (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) d))), c ≫ a = c ≫ b := by
    letI := D.shiftCommShift (0,-1)
    letI := D.shiftExact (0,-1)
    let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
    let V := D.nu.functor.obj (X.obj D.hopfAndDetector)
    let T := XModLambdaN.cofiberTriangle V d
    have hzero : (F.mapTriangle.obj T).mor₂ ≫ (a-b) = 0 := by
      change F.map (XModLambdaN.incl V d) ≫ (a-b) = 0
      rw [Preadditive.comp_sub,hab,sub_self]
    obtain ⟨z,hz⟩ := Triangle.yoneda_exact₃ (F.mapTriangle.obj T)
      (F.map_distinguished T (XModLambdaN.cofiberTriangle_distinguished V d)) (a-b) hzero
    intro m w c
    let ε : (F.obj ((SyntheticCategory.biShift (0,-(d:ℤ))).obj V))⟦(1:ℤ)⟧ ≅
        (SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ)-1)).obj
          (D.nu.functor.obj ((ClassicalObject.shift 1 X).obj D.hopfAndDetector)) :=
      (shiftFunctor Syn (1:ℤ)).mapIso ((lambdaShiftAddIso d 1 (d+1) rfl).app V) ≪≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).symm.app _ ≪≫
        (SyntheticCategory.biShift_comp (0,-((d+1:ℕ):ℤ)) (1,0)).app V ≪≫
        eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj V)
          (show (0,-((d+1:ℕ):ℤ))+(1,0)=(1,1)+(0,-((d+1:ℕ):ℤ)-1) by ext <;> simp)) ≪≫
        (SyntheticCategory.biShift_comp (1,1) (0,-((d+1:ℕ):ℤ)-1)).symm.app V ≪≫
        (SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ)-1)).mapIso (D.nu.suspensionIso _).symm
    have h := negative_shift_nu_to_quotient_zero D synthetic (.shift 1 X) Y (d+1) (by omega) m w
      ((c ≫ (F.mapTriangle.obj T).mor₃) ≫ ε.hom) (ε.inv ≫ z)
    have hcz : (c ≫ (F.mapTriangle.obj T).mor₃) ≫ z = 0 := by
      simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h
    apply sub_eq_zero.mp
    rw [←Preadditive.comp_sub,hz,←Category.assoc]
    exact hcz

  have successor_cofiber_map_exists (D : AdamsComparison H M Syn) (A : Syn) (d : ℕ) :
      let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
      letI := D.shiftCommShift (0,-1)
      ∃ c : F.obj (XModLambdaN A d) ⟶ XModLambdaN A (d+1),
        F.map (XModLambdaN.incl A d) ≫ c = lambdaPow 1 A ≫ XModLambdaN.incl A (d+1) ∧
        c ≫ XModLambdaN.proj A (d+1) =
          F.map (XModLambdaN.proj A d) ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫
            (shiftFunctor Syn (1:ℤ)).map ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app A) := by
    let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
    letI := D.shiftCommShift (0,-1)
    letI := D.shiftExact (0,-1)
    let T := XModLambdaN.cofiberTriangle A d
    let U := XModLambdaN.cofiberTriangle A (d+1)
    have hs : F.map (lambdaPow d A) ≫ lambdaPow 1 A =
        (lambdaShiftAddIso d 1 (d+1) rfl).hom.app A ≫ lambdaPow (d+1) A :=
      (lambdaPow_add_comparison D.shiftCoherence d 1 (d+1) rfl A).symm
    obtain ⟨c,hc,hd⟩ := complete_distinguished_triangle_morphism
      (F.mapTriangle.obj T) U
      (F.map_distinguished T (XModLambdaN.cofiberTriangle_distinguished A d))
      (XModLambdaN.cofiberTriangle_distinguished A (d+1))
      ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app A) (lambdaPow 1 A) hs
    refine ⟨c,hc,?_⟩
    change (F.map (XModLambdaN.proj A d) ≫ (F.commShiftIso (1:ℤ)).hom.app _) ≫
        (shiftFunctor Syn (1:ℤ)).map ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app A) =
      c ≫ XModLambdaN.proj A (d+1) at hd
    simpa only [Category.assoc] using hd.symm

  have successor_lambda_proj_evaluation (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject) (d : ℕ)
      (l : (SyntheticCategory.biShift (0,-1)).obj
        (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) d) ⟶
        XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) (d+1))
      (hl : (SyntheticCategory.biShift (0,-1)).map
        (XModLambdaN.incl (D.nu.functor.obj (X.obj D.hopfAndDetector)) d) ≫ l =
        lambdaPow 1 (D.nu.functor.obj (X.obj D.hopfAndDetector)) ≫
          XModLambdaN.incl (D.nu.functor.obj (X.obj D.hopfAndDetector)) (d+1))
      (m w : ℤ) (b : BiHom m w ((SyntheticCategory.biShift (0,-1)).obj
        (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) d))) :
      let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
      letI := D.shiftCommShift (0,-1)
      b ≫ l ≫ XModLambdaN.proj (D.nu.functor.obj (X.obj D.hopfAndDetector)) (d+1) =
        b ≫ F.map (XModLambdaN.proj (D.nu.functor.obj (X.obj D.hopfAndDetector)) d) ≫
          (F.commShiftIso (1:ℤ)).hom.app _ ≫
            (shiftFunctor Syn (1:ℤ)).map
              ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app
                (D.nu.functor.obj (X.obj D.hopfAndDetector))) := by
    letI := D.shiftCommShift (0,-1)
    obtain ⟨c,hc,hp⟩ := successor_cofiber_map_exists D
      (D.nu.functor.obj (X.obj D.hopfAndDetector)) d
    have he := shift_minus_one_quotient_maps_equal_on_spheres
      D synthetic X X d l c (hl.trans hc.symm) m w b
    rw [←Category.assoc,he,Category.assoc,hp]

  have selected_delta_evaluation_eq_cofiber
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject)
      (i j : ℕ)
      (T : LambdaRhoDeltaTriangle (D.nu.functor.obj (X.obj D.hopfAndDetector)) i j)
      (m w : ℤ)
      (a : BiHom m w (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) i)) :
      a ≫ T.delta = a ≫ XModLambdaN.proj (D.nu.functor.obj (X.obj D.hopfAndDetector)) i ≫
        (shiftFunctor Syn (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(i:ℤ))).map
            (XModLambdaN.incl (D.nu.functor.obj (X.obj D.hopfAndDetector)) (j-i))) := by
    let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
    let base := XModLambdaN.cofiberTriangle A i
    obtain ⟨c,hc,hδ⟩ := complete_distinguished_triangle_morphism
      base (Triangle.mk T.lambdaMap T.rho T.delta)
      (XModLambdaN.cofiberTriangle_distinguished A i) T.distinguished
      ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i)))
      (XModLambdaN.incl A j) T.lambda_quotient.symm
    change XModLambdaN A i ⟶ XModLambdaN A i at c
    change XModLambdaN.incl A i ≫ c = XModLambdaN.incl A j ≫ T.rho at hc
    have hc' : XModLambdaN.incl A i ≫ c = XModLambdaN.incl A i ≫ 𝟙 _ := by
      rw [hc,T.rho_quotient,Category.comp_id]
    have hac : a ≫ c = a := by
      simpa only [Category.comp_id] using
        quotient_nu_maps_equal_on_spheres D synthetic X X i T.i_pos c (𝟙 _) hc' m w a
    change XModLambdaN.proj A i ≫ (shiftFunctor Syn (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) =
      c ≫ T.delta at hδ
    calc
      a ≫ T.delta = (a ≫ c) ≫ T.delta := by rw [hac]
      _ = a ≫ XModLambdaN.proj A i ≫ (shiftFunctor Syn (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) := by
        rw [Category.assoc,←hδ]

  have shift_minus_one_preserves_sphere_evaluation {A B : Syn}
      (f g : A ⟶ B)
      (h : ∀ (m w : ℤ) (a : BiHom m w A), a ≫ f = a ≫ g)
      (m w : ℤ) (b : BiHom m w ((SyntheticCategory.biShift (0,-1)).obj A)) :
      b ≫ (SyntheticCategory.biShift (0,-1)).map f =
        b ≫ (SyntheticCategory.biShift (0,-1)).map g := by
    let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
    let e : F.obj (Smn m (w+1)) ≅ Smn m w :=
      (SyntheticCategory.biShift_comp (m,w+1) (0,-1)).app S_0_0 ≪≫
        eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj (S_0_0 : Syn))
          (show (m,w+1)+(0,-1)=(m,w) by ext <;> simp))
    let a : BiHom m (w+1) A :=
      (SyntheticCategory.biShift_fullyFaithful (0,-1)).preimage (e.hom ≫ b)
    have ha : F.map a = e.hom ≫ b :=
      (SyntheticCategory.biShift_fullyFaithful (0,-1)).map_preimage _
    apply (cancel_epi e.hom).mp
    change e.hom ≫ b ≫ F.map f = e.hom ≫ b ≫ F.map g
    rw [←Category.assoc,←ha,←Functor.map_comp,h,Functor.map_comp,ha,Category.assoc]

  have successor_delta_lambda_evaluation (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject) (d q : ℕ)
      (hd : 0<d) (hq : 0<q) (m w : ℤ) :
      let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
      let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
      letI := D.shiftCommShift (0,-1)
      let l : F.obj (XModLambdaN A d) ⟶ XModLambdaN A (d+1) := by
        simpa only [F,Nat.add_sub_cancel,Nat.cast_one] using
          ((D.quotientTower A).triangle (by omega : 0<1) (by omega : 1<d+1)).lambdaMap
      let δ0 : XModLambdaN A d ⟶
          ((SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
        simpa only [Nat.add_sub_cancel_left] using
          ((D.quotientTower A).triangle hd (show d<d+q by omega)).delta
      let δ1 : XModLambdaN A (d+1) ⟶
          ((SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
        simpa only [Nat.add_sub_cancel_left] using
          ((D.quotientTower A).triangle (by omega : 0<d+1)
            (show d+1<d+1+q by omega)).delta
      ∀ b : BiHom m w (F.obj (XModLambdaN A d)),
        b ≫ l ≫ δ1 = b ≫ F.map δ0 ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor Syn (1:ℤ)).map
            ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app (XModLambdaN A q)) := by
    dsimp only
    intro b
    let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
    let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
    let G := SyntheticCategory.biShift (Syn:=Syn) (0,-(d:ℤ))
    let J := SyntheticCategory.biShift (Syn:=Syn) (0,-((d+1:ℕ):ℤ))
    letI := D.shiftCommShift (0,-1)
    let l : F.obj (XModLambdaN A d) ⟶ XModLambdaN A (d+1) := by
      simpa only [F,Nat.add_sub_cancel,Nat.cast_one] using
        ((D.quotientTower A).triangle (by omega : 0<1) (by omega : 1<d+1)).lambdaMap
    let δ0 : XModLambdaN A d ⟶ (G.obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
      simpa only [Nat.add_sub_cancel_left] using
        ((D.quotientTower A).triangle hd (show d<d+q by omega)).delta
    let δ1 : XModLambdaN A (d+1) ⟶ (J.obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
      simpa only [Nat.add_sub_cancel_left] using
        ((D.quotientTower A).triangle (by omega : 0<d+1)
          (show d+1<d+1+q by omega)).delta
    have source_transport {S T : Syn} (Q : ℕ → Syn) (f : ∀ k, S ⟶ Q k)
        {k k' : ℕ} (h : k=k') (g : Q k ⟶ T) (v : S ⟶ T)
        (hv : f k ≫ g = v) :
        f k' ≫ Eq.mp (congrArg (fun j => Q j ⟶ T) h) g = v := by
      subst k'; exact hv
    have target_transport {S T : Syn} (Q : ℕ → Syn) (a : S ⟶ T)
        {k k' : ℕ} (h : k=k') (g : T ⟶ Q k) (v : ∀ j, S ⟶ Q j)
        (hv : a ≫ g = v k) :
        a ≫ Eq.mp (congrArg (fun j => T ⟶ Q j) h) g = v k' := by
      subst k'; exact hv
    have hl : F.map (XModLambdaN.incl A d) ≫ l =
        lambdaPow 1 A ≫ XModLambdaN.incl A (d+1) := by
      exact source_transport (fun k => F.obj (XModLambdaN A k))
        (fun k => F.map (XModLambdaN.incl A k)) (Nat.add_sub_cancel d 1)
        ((D.quotientTower A).triangle (by omega : 0<1) (by omega : 1<d+1)).lambdaMap _
        ((D.quotientTower A).triangle (by omega : 0<1) (by omega : 1<d+1)).lambda_quotient
    have hδ0 : ∀ (m' w' : ℤ) (a : BiHom m' w' (XModLambdaN A d)),
        a ≫ δ0 = a ≫ XModLambdaN.proj A d ≫
          (shiftFunctor Syn (1:ℤ)).map (G.map (XModLambdaN.incl A q)) := by
      intro m' w' a
      exact target_transport (fun k => (G.obj (XModLambdaN A k))⟦(1:ℤ)⟧) a
        (Nat.add_sub_cancel_left d q)
        ((D.quotientTower A).triangle hd (show d<d+q by omega)).delta
        (fun k => a ≫ XModLambdaN.proj A d ≫ (shiftFunctor Syn (1:ℤ)).map (G.map (XModLambdaN.incl A k)))
        (selected_delta_evaluation_eq_cofiber D synthetic X d (d+q)
          ((D.quotientTower A).triangle hd (show d<d+q by omega)) m' w' a)
    have hδ1 : (b ≫ l) ≫ δ1 = (b ≫ l) ≫ XModLambdaN.proj A (d+1) ≫
        (shiftFunctor Syn (1:ℤ)).map (J.map (XModLambdaN.incl A q)) := by
      exact target_transport (fun k => (J.obj (XModLambdaN A k))⟦(1:ℤ)⟧) (b ≫ l)
        (Nat.add_sub_cancel_left (d+1) q)
        ((D.quotientTower A).triangle (by omega : 0<d+1) (show d+1<d+1+q by omega)).delta
        (fun k => (b ≫ l) ≫ XModLambdaN.proj A (d+1) ≫
          (shiftFunctor Syn (1:ℤ)).map (J.map (XModLambdaN.incl A k)))
        (selected_delta_evaluation_eq_cofiber D synthetic X (d+1) (d+1+q)
          ((D.quotientTower A).triangle (by omega : 0<d+1)
            (show d+1<d+1+q by omega)) m w (b ≫ l))
    have hp := successor_lambda_proj_evaluation D synthetic X d l hl m w b
    have heval := shift_minus_one_preserves_sphere_evaluation δ0
      (XModLambdaN.proj A d ≫ (shiftFunctor Syn (1:ℤ)).map (G.map (XModLambdaN.incl A q)))
      hδ0 m w b
    have hκ := (lambdaShiftAddIso d 1 (d+1) rfl).hom.naturality (XModLambdaN.incl A q)
    change F.map (G.map (XModLambdaN.incl A q)) ≫
        (lambdaShiftAddIso d 1 (d+1) rfl).hom.app (XModLambdaN A q) =
      (lambdaShiftAddIso d 1 (d+1) rfl).hom.app A ≫ J.map (XModLambdaN.incl A q) at hκ
    change b ≫ l ≫ δ1 = b ≫ F.map δ0 ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫ _
    calc
      _ = (b ≫ l ≫ XModLambdaN.proj A (d+1)) ≫
          (shiftFunctor Syn (1:ℤ)).map (J.map (XModLambdaN.incl A q)) := by
        simpa only [Category.assoc] using hδ1
      _ = (b ≫ F.map (XModLambdaN.proj A d) ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor Syn (1:ℤ)).map ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app A)) ≫
          (shiftFunctor Syn (1:ℤ)).map (J.map (XModLambdaN.incl A q)) :=
        congrArg (fun z => z ≫ (shiftFunctor Syn (1:ℤ)).map
          (J.map (XModLambdaN.incl A q))) hp
      _ = b ≫ F.map δ0 ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor Syn (1:ℤ)).map
            ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app (XModLambdaN A q)) := by
        simp only [Category.assoc]
        rw [←Functor.map_comp,hκ.symm,Functor.map_comp]
        rw [←Functor.commShiftIso_hom_naturality_assoc]
        rw [←Functor.map_comp_assoc,←Category.assoc b,←heval]
        simp only [Category.assoc,F]

  have successor_shifted_delta_preimage
      [(SyntheticCategory.biShift (Syn:=Syn) (0,-1)).CommShift ℤ]
      [(SyntheticCategory.biShift (Syn:=Syn) (0,-1)).IsTriangulated]
      {A : Syn} (d r : ℕ) (T : LambdaRhoDeltaTriangle A d r)
      (n w : ℤ)
      (c : BiHom (n-1) (w+((d+1:ℕ):ℤ)) (XModLambdaN A (r-d)))
      (hc : (SyntheticCategory.biShift (0,-(d:ℤ))).map c ≫ T.lambdaMap = 0) :
      ∃ a : BiHom n w ((SyntheticCategory.biShift (0,-1)).obj (XModLambdaN A d)),
        a ≫ (SyntheticCategory.biShift (0,-1)).map T.delta ≫
          ((SyntheticCategory.biShift (0,-1)).commShiftIso (1:ℤ)).hom.app _ ≫
            (shiftFunctor Syn (1:ℤ)).map
              ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app (XModLambdaN A (r-d))) =
          (biSuspensionHomEquiv n w ((d+1:ℕ):ℤ) (XModLambdaN A (r-d))).symm c := by
    let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
    let Q := XModLambdaN A (r-d)
    let κ : SyntheticCategory.biShift (0,-(d:ℤ)) ⋙ F ≅
        SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ)) :=
      lambdaShiftAddIso (Syn:=Syn) d 1 (d+1) rfl
    let ε : F.obj (((SyntheticCategory.biShift (0,-(d:ℤ))).obj Q)⟦(1:ℤ)⟧) ≅
        ((SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ))).obj Q)⟦(1:ℤ)⟧ :=
      (F.commShiftIso (1:ℤ)).app _ ≪≫ (shiftFunctor Syn (1:ℤ)).mapIso (κ.app Q)
    let b := (biSuspensionHomEquiv n w ((d+1:ℕ):ℤ) Q).symm c
    have hc' : (SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ))).map c ≫
        κ.inv.app Q ≫ F.map T.lambdaMap = 0 := by
      rw [←Category.assoc,κ.inv.naturality c,Category.assoc]
      change κ.inv.app (Smn (n-1) (w+((d+1:ℕ):ℤ))) ≫
        F.map ((SyntheticCategory.biShift (0,-(d:ℤ))).map c) ≫ F.map T.lambdaMap = 0
      rw [←Functor.map_comp,hc,Functor.map_zero,comp_zero]
    have hb : b ≫ (shiftFunctor Syn (1:ℤ)).map (κ.inv.app Q ≫ F.map T.lambdaMap) = 0 :=
      (shifted_representative_zero_iff n w ((d+1:ℕ):ℤ) Q _
        (κ.inv.app Q ≫ F.map T.lambdaMap) c).mpr hc'
    have hb' : (b ≫ ε.inv) ≫ F.map ((shiftFunctor Syn (1:ℤ)).map T.lambdaMap) = 0 := by
      change (b ≫ (shiftFunctor Syn (1:ℤ)).map (κ.inv.app Q) ≫
        (F.commShiftIso (1:ℤ)).inv.app _) ≫ F.map ((shiftFunctor Syn (1:ℤ)).map T.lambdaMap) = 0
      rw [Category.assoc,Category.assoc,←F.commShiftIso_inv_naturality T.lambdaMap (1:ℤ)]
      rw [←Category.assoc ((shiftFunctor Syn (1:ℤ)).map (κ.inv.app Q)),←Functor.map_comp]
      rw [←Category.assoc,hb,zero_comp]
    let U := F.mapTriangle.obj (CategoryTheory.Pretriangulated.Triangle.mk T.lambdaMap T.rho T.delta)
    have hU : U ∈ distTriang Syn :=
      F.map_distinguished _ T.distinguished
    have hb'' : (b ≫ ε.inv) ≫ (F.commShiftIso (1:ℤ)).hom.app _ ≫
        (shiftFunctor Syn (1:ℤ)).map (F.map T.lambdaMap) = 0 := by
      rw [←F.commShiftIso_hom_naturality T.lambdaMap (1:ℤ),←Category.assoc,hb',zero_comp]
    have hz : ((b ≫ ε.inv) ≫ (F.commShiftIso (1:ℤ)).hom.app _) ≫ U.rotate.mor₃ = 0 := by
      change ((b ≫ ε.inv) ≫ (F.commShiftIso (1:ℤ)).hom.app _) ≫
        (-((shiftFunctor Syn (1:ℤ)).map (F.map T.lambdaMap))) = 0
      rw [Preadditive.comp_neg,Category.assoc,hb'',neg_zero]
    obtain ⟨a,ha⟩ := U.rotate.coyoneda_exact₃
      (CategoryTheory.Pretriangulated.rot_of_distTriang U hU) _ hz
    change (b ≫ ε.inv) ≫ (F.commShiftIso (1:ℤ)).hom.app _ =
      a ≫ (F.map T.delta ≫ (F.commShiftIso (1:ℤ)).hom.app _) at ha
    have ha' : a ≫ F.map T.delta = b ≫ ε.inv := by
      apply (cancel_mono ((F.commShiftIso (1:ℤ)).hom.app _)).mp
      simpa only [Category.assoc] using ha.symm
    refine ⟨a,?_⟩
    change a ≫ F.map T.delta ≫ ε.hom = b
    rw [←Category.assoc,ha',Category.assoc,ε.inv_hom_id,Category.comp_id]

  have finite_target_boundary_lambda_zero_reindex (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject)
      (r i q : ℕ) (hi : 0 < i) (hir : i < r) (hqi : r-i=q) (s t : ℤ)
      (y : cycles H (X.obj D.hopfAndDetector) ((q:ℤ)-t+(t-(q-1:ℕ))) (s,t))
      (hy : y.val ∈ boundaries H (X.obj D.hopfAndDetector) r (s,t))
      (b : BiHom (t-s) (t-(q-1:ℕ))
        (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q))
      (hb : Detects (D.convergence (.quotient q (.nu X)))
        (s,t,t-(q-1:ℕ)) (finiteTargetLabel D X q s t (q-1) y.val) b) :
      (SyntheticCategory.biShift (0,-(i:ℤ))).map b ≫
        Eq.mp (congrArg (fun j => (SyntheticCategory.biShift (0,-(i:ℤ))).obj
          (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) j) ⟶
            XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) r) hqi)
          ((D.quotientTower (D.nu.functor.obj (X.obj D.hopfAndDetector))).triangle hi hir).lambdaMap = 0 := by
    subst q
    exact finite_target_boundary_lambda_zero D synthetic X r i hi hir s t y hy b hb

  have successor_shifted_delta_preimage_reindex
      [(SyntheticCategory.biShift (Syn:=Syn) (0,-1)).CommShift ℤ]
      [(SyntheticCategory.biShift (Syn:=Syn) (0,-1)).IsTriangulated]
      {A : Syn} (d r q : ℕ) (hq : r-d=q) (T : LambdaRhoDeltaTriangle A d r)
      (n w : ℤ)
      (c : BiHom (n-1) (w+((d+1:ℕ):ℤ)) (XModLambdaN A q))
      (hc : (SyntheticCategory.biShift (0,-(d:ℤ))).map c ≫
        Eq.mp (congrArg (fun j => (SyntheticCategory.biShift (0,-(d:ℤ))).obj
          (XModLambdaN A j) ⟶ XModLambdaN A r) hq) T.lambdaMap = 0) :
      ∃ a : BiHom n w ((SyntheticCategory.biShift (0,-1)).obj (XModLambdaN A d)),
        a ≫ (SyntheticCategory.biShift (0,-1)).map
          (Eq.mp (congrArg (fun j => XModLambdaN A d ⟶
            ((SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A j))⟦(1:ℤ)⟧) hq) T.delta) ≫
          ((SyntheticCategory.biShift (0,-1)).commShiftIso (1:ℤ)).hom.app _ ≫
            (shiftFunctor Syn (1:ℤ)).map
              ((lambdaShiftAddIso d 1 (d+1) rfl).hom.app (XModLambdaN A q)) =
          (biSuspensionHomEquiv n w ((d+1:ℕ):ℤ) (XModLambdaN A q)).symm c := by
    subst q
    exact successor_shifted_delta_preimage d r T n w c hc

  dsimp only
  let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
  let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
  letI := D.shiftCommShift (0,-1)
  letI := D.shiftExact (0,-1)
  let T0 := (D.quotientTower A).triangle hd (show d<d+q by omega)
  let l : F.obj (XModLambdaN A d) ⟶ XModLambdaN A (d+1) := by
    simpa only [F,Nat.add_sub_cancel,Nat.cast_one] using
      ((D.quotientTower A).triangle (by omega : 0<1) (by omega : 1<d+1)).lambdaMap
  let δ0 : XModLambdaN A d ⟶
      ((SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
    simpa only [Nat.add_sub_cancel_left] using T0.delta
  let δ1 : XModLambdaN A (d+1) ⟶
      ((SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
    simpa only [Nat.add_sub_cancel_left] using
      ((D.quotientTower A).triangle (by omega : 0<d+1)
        (show d+1<d+1+q by omega)).delta
  let L0 : (SyntheticCategory.biShift (0,-(d:ℤ))).obj (XModLambdaN A q) ⟶
      XModLambdaN A (d+q) := by
    simpa only [Nat.add_sub_cancel_left] using T0.lambdaMap
  have hz : (SyntheticCategory.biShift (0,-(d:ℤ))).map c≫L0=0 :=
    finite_target_boundary_lambda_zero_reindex D synthetic X (d+q) d q hd (by omega)
      (Nat.add_sub_cancel_left d q) s t y hy c hc
  have regrade_zero {m m' v v' : ℤ} (hm:m=m') (hv:v=v')
      (b : BiHom m v (XModLambdaN A q)) :
      (SyntheticCategory.biShift (0,-(d:ℤ))).map (homotopyRegrade hm hv b)≫L0=0 ↔
        (SyntheticCategory.biShift (0,-(d:ℤ))).map b≫L0=0 := by
    subst m'; subst v'; rfl
  let c' : BiHom (((t-s)+1)-1) (((t-(q-1:ℕ))-((d+1:ℕ):ℤ))+((d+1:ℕ):ℤ))
      (XModLambdaN A q) := homotopyRegrade (by omega) (by omega) c
  have pre := successor_shifted_delta_preimage_reindex d (d+q) q (Nat.add_sub_cancel_left d q)
    T0 ((t-s)+1) ((t-(q-1:ℕ))-((d+1:ℕ):ℤ))
  obtain ⟨β,hβ⟩ := pre c' ((regrade_zero (by omega) (by omega) c).mpr hz)
  have heval := successor_delta_lambda_evaluation D synthetic X d q hd hq
    ((t-s)+1) ((t-(q-1:ℕ))-((d+1:ℕ):ℤ)) β
  have hδ : (β≫l)≫δ1 =
      (biSuspensionHomEquiv ((t-s)+1) ((t-(q-1:ℕ))-((d+1:ℕ):ℤ)) ((d+1:ℕ):ℤ)
        (XModLambdaN A q)).symm c' := by
    simpa only [Category.assoc] using heval.trans hβ
  refine ⟨β≫l,?_,?_⟩
  · rw [Category.assoc]
    have hl0 := (D.quotientTower A).lambda_comp_rho (by omega : 0<1) (by omega : 1<d+1)
    have source_transport (Q : ℕ → Syn) {B C : Syn} {j j' : ℕ}
        (hj : j=j') (g : Q j ⟶ B) (f : B ⟶ C) (hz : g≫f=0) :
        Eq.mp (congrArg (fun k => Q k ⟶ B) hj) g ≫ f = 0 := by
      subst j'; exact hz
    have hl : l ≫ (D.quotientTower A).rho 1 (d+1) (by omega) = 0 :=
      source_transport (fun j => F.obj (XModLambdaN A j)) (Nat.add_sub_cancel d 1) _ _ hl0
    rw [hl,comp_zero]
  · change homotopyRegrade _ _
      (biSuspensionHomEquiv ((t-s)+1) ((t-(q-1:ℕ))-((d+1:ℕ):ℤ)) ((d+1:ℕ):ℤ)
        (XModLambdaN A q) ((β≫l)≫δ1)) = c
    rw [hδ,AddEquiv.apply_symm_apply]
    have regrade_inverse {m m' v v' : ℤ} (hm:m=m') (hv:v=v')
        (b : BiHom m v (XModLambdaN A q)) :
        homotopyRegrade hm.symm hv.symm (homotopyRegrade hm hv b)=b := by
      subst m'; subst v'; rfl
    exact regrade_inverse (by omega) (by omega) c

open CategoryTheory.Pretriangulated KIP126.SpectralSequence.FinitePageCalculus in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 1600000 in
private theorem adjacent_mahowald_case
    (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject)
    (i : ℕ) (hi : 0 < i) (s t : ℤ)
    (x : E2 H (X.obj D.hopfAndDetector) s t)
    (y : E2 H (X.obj D.hopfAndDetector) (s+i+1) (t+i))
    (hd : KIP126.SpectralSequence.HasDifferential
      (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector)) (i+1)
        (s,t) (s+i+1,t+i) x y) :
    let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
    let δ : XModLambdaN A i ⟶
        ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
      simpa only [show i.succ-i=1 by omega] using
        ((D.quotientTower A).triangle hi (Nat.lt_succ_self i)).delta
    ∃ a : BiHom (t-s) t (XModLambdaN A i),
      a ≫ (D.quotientTower A).rho 1 i (by omega) =
        firstLabel D X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
      Detects (D.convergence (.quotient 1 (.nu X))) (s+i+1,t+i,t+i)
        (regradeE2 (by simp) (finiteTargetLabel D X 1 (s+i+1) (t+i) 0 y))
        (homotopyRegrade (by dsimp; omega) rfl
          (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A 1) (a ≫ δ))) := by
  have represents_zero_mem_boundary (H : Mod2EilenbergMacLane (C:=C)) (X : C) (r : ℤ) (p : ℤ×ℤ)
      (y : Ambient H X p)
      (hy : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit X) r p y 0) :
      y ∈ boundaries H X (r-1) p := by
    let E := adamsTowerInternalSpectralSequence H.unit X
    let P := E.ssData p
    let k : WithTop ℕ := ↑(r-2).toNat
    change ∃ _ : 2≤r, ∃ z : (Subobject.underlying.obj (P.Z k) : ModuleCat ℤ),
      cycleMap H X k p z = y ∧ P.pageπ k z = 0 at hy
    obtain ⟨_,z,hz,hz0⟩ := hy
    obtain ⟨b,hb⟩ := (subobject_cokernel_π_eq_zero_iff (P.B k) (P.Z k) (P.B_le_Z k) z).mp hz0
    let j := Subobject.ofLE (P.B k) (P.Z k) (P.B_le_Z k)
    have hj : j b = z := by
      apply (ModuleCat.mono_iff_injective (P.Z k).arrow).mp inferInstance
      have h := ConcreteCategory.congr_hom (Subobject.ofLE_arrow (P.B_le_Z k)) b
      exact h.trans hb
    change ∃ b, boundaryMap H X (↑(r-1-1).toNat) p b = y
    rw [show r-1-1=r-2 by omega]
    refine ⟨b,?_⟩
    have hlabel : j ≫ cycleMap H X k p = boundaryMap H X k p := by
      dsimp only [j,cycleMap,boundaryMap,P,E]
      rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
    change boundaryMap H X k p b = y
    rw [←hlabel,ModuleCat.comp_apply,hj]
    exact hz

  have differential_targets_sub_mem_boundary (H : Mod2EilenbergMacLane (C:=C)) (X : C)
      (r : ℤ) (p q : ℤ×ℤ) (x : Ambient H X p) (y z : Ambient H X q)
      (hy : HasDifferential (adamsTowerInternalSpectralSequence H.unit X) r p q x y)
      (hz : HasDifferential (adamsTowerInternalSpectralSequence H.unit X) r p q x z) :
      y-z ∈ boundaries H X (r-1) q := by
    obtain ⟨hdeg,a,b,ha,hb,hab⟩ := hy
    obtain ⟨hdeg',a',b',ha',hb',hab'⟩ := hz
    have haa := represents_unique ha ha'
    subst a'
    have hbb : b=b' := hab.symm.trans hab'
    apply represents_zero_mem_boundary H X r q (y-z)
    simpa only [hbb,sub_self] using represents_sub hb hb'

  have detects_sub {K : Syn} {unit : S_0_0 ⟶ K}
      {F : SyntheticAdamsFamily Syn} {X : Syn} (c : TowerConvergence unit F X)
      (i : Tridegree) {x y : (F.obj X).E₂ i}
      {a b : BiHom (i.2.1-i.1) i.2.2 X}
      (ha : Detects c i x a) (hb : Detects c i y b) : Detects c i (x-y) (a-b) := by
    obtain ⟨e,⟨hr,z,hz,he⟩,a',ha',hga⟩ := ha
    obtain ⟨e',⟨_,z',hz',he'⟩,b',hb',hgb⟩ := hb
    refine ⟨e-e',⟨hr,z-z',?_,?_⟩,a'-b',?_,?_⟩
    · rw [map_sub,hz,hz']
    · rw [map_sub,he,he']
    · rw [map_sub,ha',hb']
    · rw [map_sub,map_sub,hga,hgb]

  have finiteTargetLabel_sub (D : AdamsComparison H M Syn) (X : ClassicalObject)
      (q : ℕ) (s t : ℤ) (k : ℕ) (x y : E2 H (X.obj D.hopfAndDetector) s t) :
      finiteTargetLabel D X q s t k (x-y) =
        finiteTargetLabel D X q s t k x - finiteTargetLabel D X q s t k y := by
    have cast_sub (E : SyntheticAdamsSS.{v}) (s t w w' : ℤ) (h : w=w')
        (a b : E.E₂ (s,t,w)) :
        (congrArg (fun k => (E.E₂ (s,t,k) : Type v)) h).mp (a-b) =
          (congrArg (fun k => (E.E₂ (s,t,k) : Type v)) h).mp a -
            (congrArg (fun k => (E.E₂ (s,t,k) : Type v)) h).mp b := by
      subst w'; rfl
    simp only [finiteTargetLabel,targetNuLabel,map_sub]
    rw [cast_sub] <;> simp only [map_sub,add_zero]

  have adjacent_bockstein_actual_pair
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject)
      (i : ℕ) (hi : 0 < i) (s t : ℤ) (x : E2 H (X.obj D.hopfAndDetector) s t)
      (hx : x ∈ cycles H (X.obj D.hopfAndDetector) i (s,t)) :
      ∃ (aZero : BiHom (t-s) t (XModLambdaN (nuZero D X) i))
        (a : BiHom (t-s) t (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) i)),
        a = aZero ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) i ∧
        a ≫ (D.quotientTower (D.nu.functor.obj (X.obj D.hopfAndDetector))).rho 1 i hi =
          firstLabel D X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
        KIP126.SpectralSequence.HasDifferential
          (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector)) (i+1)
          (s,t) (s+i+1,t+i) x (bocksteinLabel D X i hi s t aZero) ∧
        Detects (D.convergence (.quotient 1 (.nu X))) (s+i+1,t+i,t+i)
          (regradeE2 (by simp) (finiteTargetLabel D X 1 (s+i+1) (t+i) 0
            (bocksteinLabel D X i hi s t aZero)))
          (homotopyRegrade (by dsimp; omega) rfl
            (biSuspensionHomEquiv (t-s) t (i:ℤ)
              (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) (i+1-i))
              (a ≫ ((D.quotientTower (D.nu.functor.obj (X.obj D.hopfAndDetector))).triangle hi
                (Nat.lt_succ_self i)).delta) ≫
              eqToHom (congrArg (fun n => XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) n)
                (show i+1-i=1 by omega)))) := by
    have bockstein_arrow_eq_biSuspensionIso_inv
        (D : AdamsComparison H M Syn) (X : ClassicalObject) (q : ℕ) (hq : 0 < q) :
        bocksteinArrow D X q hq =
          ((D.quotientTower (nuZero D X)).triangle hq (Nat.lt_succ_self q)).delta ≫
            (biSuspensionIso (q : ℤ) (XModLambdaN (nuZero D X) (q+1-q))).inv ≫
              eqToHom (congrArg (fun n => (SyntheticCategory.biShift (1,-(q:ℤ))).obj
                (XModLambdaN (nuZero D X) n)) (show q+1-q=1 by omega)) := by
      have hcast {A A' B : Syn} (h : A=A') (e : A ≅ B)
          (he : (A ≅ B) = (A' ≅ B)) :
          (he.mp e).inv = e.inv ≫ eqToHom h := by
        subst A'
        change e.inv = e.inv ≫ 𝟙 A
        exact (Category.comp_id _).symm
      simp only [bocksteinArrow, biSuspensionIso]
      rw [hcast (congrArg (fun p : ℤ × ℤ => (SyntheticCategory.biShift p).obj
        (XModLambdaN (nuZero D X) (q+1-q))) (by ext <;> simp))]
      simp only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Category.assoc, eqToHom_trans]


    have biSuspensionHomEquiv_eq_inverse_susp (n w q : ℤ) (Q : Syn)
        (a : BiHom n w (((SyntheticCategory.biShift (0,-q)).obj Q)⟦(1:ℤ)⟧)) :
        biSuspensionHomEquiv n w q Q a =
          (susp_invariance (n-1) (w+q) 1 (-q) Q).symm
            (homotopyRegrade (by omega) (by omega) (a ≫ (biSuspensionIso q Q).inv)) := by
      have hc (n' w' : ℤ) (hn : n' = n) (hw : w' = w)
          (e : BiHom (n-1) (w+q) Q ≃
            BiHom n' w' (((SyntheticCategory.biShift (0,-q)).obj Q)⟦(1:ℤ)⟧))
          (he : (BiHom (n-1) (w+q) Q ≃
              BiHom n' w' (((SyntheticCategory.biShift (0,-q)).obj Q)⟦(1:ℤ)⟧)) =
            (BiHom (n-1) (w+q) Q ≃
              BiHom n w (((SyntheticCategory.biShift (0,-q)).obj Q)⟦(1:ℤ)⟧))) :
          (he.mp e).symm a = e.symm (homotopyRegrade hn.symm hw.symm a) := by
        subst n'
        subst w'
        rfl
      have regrade_comp {n' w' : ℤ} (hn : n=n') (hw : w=w') {A B : Syn}
          (a : BiHom n w A) (f : A ⟶ B) :
          homotopyRegrade hn hw (a ≫ f) = homotopyRegrade hn hw a ≫ f := by
        subst n'
        subst w'
        rfl
      change biSuspensionHomUnderlyingEquiv n w q Q a = _
      simp only [biSuspensionHomUnderlyingEquiv]
      rw [hc (n-1+1) (w+q+-q) (by omega) (by omega)]
      simp only [Equiv.symm_trans_apply, Iso.homCongr_symm, Iso.homCongr_apply,
        Iso.symm_hom, Iso.symm_inv, Iso.refl_hom, Category.id_comp, regrade_comp]


    have firstLabel_bocksteinLabel_eq
        (D : AdamsComparison H M Syn) (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
        (a : BiHom (t-s) t (XModLambdaN (nuZero D X) q)) :
        firstLabel D X (s+q+1) (t+q) (bocksteinLabel D X q hq s t a) =
          homotopyRegrade (by omega) rfl
            ((susp_invariance (t-s-1) (t+q) 1 (-(q:ℤ)) _).symm
              (homotopyRegrade (by omega) (by omega) (a ≫ bocksteinArrow D X q hq))) := by
      have regrade_cast {a b c d m n : ℤ} {Q : Syn}
          (h1 : a=m) (h2 : b=n) (h3 : a=c) (h4 : b=d)
          (he : BiHom m n Q = BiHom c d Q) (x : BiHom a b Q) :
          he.mp (homotopyRegrade h1 h2 x) = homotopyRegrade h3 h4 x := by
        subst m; subst n; subst c; subst d
        rfl
      simp only [firstLabel, bocksteinLabel, AddEquiv.symm_apply_apply]
      exact regrade_cast _ _ _ _ _ _


    have firstLabel_bocksteinLabel_eq_actual_delta
        (D : AdamsComparison H M Syn) (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
        (a : BiHom (t-s) t (XModLambdaN (nuZero D X) q)) :
        firstLabel D X (s+q+1) (t+q) (bocksteinLabel D X q hq s t a) =
          homotopyRegrade (by omega) rfl
            (biSuspensionHomEquiv (t-s) t (q:ℤ) (XModLambdaN (nuZero D X) (q+1-q))
              (a ≫ ((D.quotientTower (nuZero D X)).triangle hq (Nat.lt_succ_self q)).delta) ≫
              eqToHom (congrArg (fun n => XModLambdaN (nuZero D X) n)
                (show q+1-q=1 by omega))) := by
      have regrade_comp {n w n' w' : ℤ} (hn : n=n') (hw : w=w') {A B : Syn}
          (a : BiHom n w A) (f : A ⟶ B) :
          homotopyRegrade hn hw (a ≫ f) = homotopyRegrade hn hw a ≫ f := by
        subst n'; subst w'
        rfl
      have inverse_susp_cast {A B : Syn} (h : A=B) (n w k l : ℤ)
          (b : BiHom (n+k) (w+l) ((SyntheticCategory.biShift (k,l)).obj A)) :
          (susp_invariance n w k l B).symm
            (b ≫ eqToHom (congrArg (SyntheticCategory.biShift (k,l)).obj h)) =
            (susp_invariance n w k l A).symm b ≫ eqToHom h := by
        subst B
        simp only [eqToHom_refl, Category.comp_id]
      rw [firstLabel_bocksteinLabel_eq, bockstein_arrow_eq_biSuspensionIso_inv,
        biSuspensionHomEquiv_eq_inverse_susp]
      simp only [regrade_comp, ←Category.assoc]
      rw [inverse_susp_cast (congrArg (fun n => XModLambdaN (nuZero D X) n)
        (show q+1-q=1 by omega))]
      rw [regrade_comp]


    have biSuspensionIso_natural (i : ℤ) {A B : Syn} (f : A ⟶ B) :
        (SyntheticCategory.biShift (1,-i)).map f ≫ (biSuspensionIso i B).hom =
          (biSuspensionIso i A).hom ≫
            (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-i)).map f) := by
      let e : (SyntheticCategory.biShift ((0,-i)+(1,0)) : Syn ⥤ Syn) ≅
          SyntheticCategory.biShift (0,-i) ⋙ shiftFunctor Syn (1:ℤ) :=
        (SyntheticCategory.biShift_comp (0,-i) (1,0)).symm ≪≫
          Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,-i)) (SyntheticCategory.biShift_compat 1)
      have cast_natural (p p' : ℤ×ℤ) (hp : p=p')
          (E : (SyntheticCategory.biShift p : Syn ⥤ Syn) ≅
            SyntheticCategory.biShift (0,-i) ⋙ shiftFunctor Syn (1:ℤ))
          (hA : ((SyntheticCategory.biShift p).obj A ≅
            (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj A)) =
            ((SyntheticCategory.biShift p').obj A ≅
            (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj A)))
          (hB : ((SyntheticCategory.biShift p).obj B ≅
            (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj B)) =
            ((SyntheticCategory.biShift p').obj B ≅
            (shiftFunctor Syn (1:ℤ)).obj ((SyntheticCategory.biShift (0,-i)).obj B))) :
          (SyntheticCategory.biShift p').map f ≫ (cast hB (E.app B)).hom =
            (cast hA (E.app A)).hom ≫
              (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-i)).map f) := by
        subst p'
        exact E.hom.naturality f
      unfold biSuspensionIso
      exact cast_natural ((0,-i)+(1,0)) (1,-i) (by ext <;> simp) e _ _


    have biSuspensionHomEquiv_natural (n w q : ℤ) {A B : Syn} (f : A ⟶ B)
        (a : BiHom n w (((SyntheticCategory.biShift (0,-q)).obj A)⟦(1:ℤ)⟧)) :
        biSuspensionHomEquiv n w q B
            (a ≫ (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-q)).map f)) =
          biSuspensionHomEquiv n w q A a ≫ f := by
      have susp_nat (n w k l : ℤ) (b : BiHom n w A) :
          susp_invariance n w k l A b ≫ (SyntheticCategory.biShift (k,l)).map f =
            susp_invariance n w k l B (b ≫ f) := by
        change ((SyntheticCategory.biShift_comp (n,w) (k,l)).inv.app S_0_0 ≫
          (SyntheticCategory.biShift (k,l)).map b ≫ 𝟙 _) ≫ _ =
          _ ≫ (SyntheticCategory.biShift (k,l)).map (b ≫ f) ≫ 𝟙 _
        simp only [Functor.map_comp, Category.comp_id, Category.assoc, Iso.app_inv]
      have inv_susp_nat (n w k l : ℤ)
          (b : BiHom (n+k) (w+l) ((SyntheticCategory.biShift (k,l)).obj A)) :
          (susp_invariance n w k l B).symm (b ≫ (SyntheticCategory.biShift (k,l)).map f) =
            (susp_invariance n w k l A).symm b ≫ f := by
        apply (susp_invariance n w k l B).injective
        rw [Equiv.apply_symm_apply, ←susp_nat, Equiv.apply_symm_apply]
      have hi : (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-q)).map f) ≫
          (biSuspensionIso q B).inv =
          (biSuspensionIso q A).inv ≫ (SyntheticCategory.biShift (1,-q)).map f := by
        apply (cancel_mono (biSuspensionIso q B).hom).mp
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [biSuspensionIso_natural]
        simp only [Iso.inv_hom_id_assoc]
      have regrade_comp {n w n' w' : ℤ} (hn : n=n') (hw : w=w') {A B : Syn}
          (a : BiHom n w A) (f : A ⟶ B) :
          homotopyRegrade hn hw (a ≫ f) = homotopyRegrade hn hw a ≫ f := by
        subst n'; subst w'
        rfl
      rw [biSuspensionHomEquiv_eq_inverse_susp, biSuspensionHomEquiv_eq_inverse_susp]
      simp only [Category.assoc]
      rw [hi, ←Category.assoc, regrade_comp, inv_susp_nat]
    let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
    let f : nuZero D X ⟶ A := SyntheticCategory.biShift_zero.hom.app A
    obtain ⟨aZero,haZero,hdiff⟩ := synthetic.bockstein X i hi s t x hx
    let a : BiHom (t-s) t (XModLambdaN A i) := aZero ≫ XModLambdaN.map f i
    have hfirst : a ≫ (D.quotientTower A).rho 1 i hi =
        firstLabel D X s t x ≫ XModLambdaN.map f 1 := by
      dsimp only [a]
      have hn : (D.quotientTower (nuZero D X)).rho 1 i hi ≫ XModLambdaN.map f 1 =
          XModLambdaN.map f i ≫ (D.quotientTower A).rho 1 i hi :=
        (D.comparisonCompatible.quotient_naturality f).rho_naturality hi
      rw [Category.assoc, ←hn, ←Category.assoc, haZero]
    refine ⟨aZero,a,rfl,hfirst,hdiff,?_⟩
    let y := bocksteinLabel D X i hi s t aZero
    let b : BiHom ((t+i)-(s+i+1)) (t+i) (XModLambdaN A 1) :=
      homotopyRegrade (by omega) rfl
        (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A (i+1-i))
          (a ≫ ((D.quotientTower A).triangle hi (Nat.lt_succ_self i)).delta) ≫
          eqToHom (congrArg (fun n => XModLambdaN A n) (show i+1-i=1 by omega)))
    have hb : b = firstLabel D X (s+i+1) (t+i) y ≫ XModLambdaN.map f 1 := by
      have hdelta : XModLambdaN.map f i ≫
          ((D.quotientTower A).triangle hi (Nat.lt_succ_self i)).delta =
        ((D.quotientTower (nuZero D X)).triangle hi (Nat.lt_succ_self i)).delta ≫
          (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-(i:ℤ))).map
            (XModLambdaN.map f (i+1-i))) :=
        (D.comparisonCompatible.quotient_naturality f).delta_naturality hi (Nat.lt_succ_self i)
      have map_cast (n m : ℕ) (h : n=m) :
          XModLambdaN.map f n ≫ eqToHom (congrArg (fun k => XModLambdaN A k) h) =
            eqToHom (congrArg (fun k => XModLambdaN (nuZero D X) k) h) ≫ XModLambdaN.map f m := by
        subst m
        simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      have regrade_comp {n w n' w' : ℤ} (hn : n=n') (hw : w=w') {A B : Syn}
          (a : BiHom n w A) (f : A ⟶ B) :
          homotopyRegrade hn hw (a ≫ f) = homotopyRegrade hn hw a ≫ f := by
        subst n'; subst w'
        rfl
      dsimp only [b,a,y]
      rw [firstLabel_bocksteinLabel_eq_actual_delta]
      rw [Category.assoc aZero,hdelta,←Category.assoc aZero,
        biSuspensionHomEquiv_natural]
      simp only [Category.assoc, regrade_comp]
      rw [map_cast (i+1-i) 1 (by omega)]
    change Detects (D.convergence (.quotient 1 (.nu X))) (s+i+1,t+i,t+i) _ b
    apply first_label_detects_unshifted D synthetic X 1 (by omega) (s+i+1) (t+i) y b
    change b ≫ (D.quotientTower A).rho 1 1 _ = _
    rw [(D.quotientTower A).rho_id,Category.comp_id]
    exact hb

  dsimp only
  let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
  let δ : XModLambdaN A i ⟶
      ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
    simpa only [show i.succ-i=1 by omega] using
      ((D.quotientTower A).triangle hi (Nat.lt_succ_self i)).delta
  let boundary (a : BiHom (t-s) t (XModLambdaN A i)) :
      BiHom ((t+i)-(s+i+1)) (t+i) (XModLambdaN A 1) :=
    homotopyRegrade (by omega) rfl
      (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A 1) (a ≫ δ))
  have hx : x ∈ cycles H (X.obj D.hopfAndDetector) i (s,t) := by
    obtain ⟨_,xr,yr,hxr,hyr,hdr⟩ := hd
    have h := (isCycle_iff_represents H (X.obj D.hopfAndDetector) ((i:ℤ)+1)
      (by omega) (s,t) x).mpr ⟨xr,hxr⟩
    simpa only [add_sub_cancel_right] using h.2
  obtain ⟨aZero,a0,ha0,hfirst,hd0,hdet0⟩ := adjacent_bockstein_actual_pair D synthetic X i hi s t x hx
  let y0 := bocksteinLabel D X i hi s t aZero
  have Ecast {A B U : Syn} (h : A=B) (n w q : ℤ)
      (g : U ⟶ ((SyntheticCategory.biShift (0,-q)).obj A)⟦(1:ℤ)⟧)
      (he : (U ⟶ ((SyntheticCategory.biShift (0,-q)).obj A)⟦(1:ℤ)⟧) =
        (U ⟶ ((SyntheticCategory.biShift (0,-q)).obj B)⟦(1:ℤ)⟧))
      (a : BiHom n w U) :
      biSuspensionHomEquiv n w q B (a ≫ he.mp g) =
        biSuspensionHomEquiv n w q A (a ≫ g) ≫ eqToHom h := by
    subst B
    change biSuspensionHomEquiv n w q A (a ≫ g) =
      biSuspensionHomEquiv n w q A (a ≫ g) ≫ 𝟙 A
    exact (Category.comp_id _).symm
  have hbound0 : Detects (D.convergence (.quotient 1 (.nu X))) (s+i+1,t+i,t+i)
      (regradeE2 (by simp) (finiteTargetLabel D X 1 (s+i+1) (t+i) 0 y0)) (boundary a0) := by
    dsimp only [boundary,δ]
    rw [Ecast (congrArg (fun j => XModLambdaN A j) (show i+1-i=1 by omega))]
    exact hdet0
  let b : BiHom ((t+i)-(s+i+1)) (t+i) (XModLambdaN A 1) :=
    firstLabel D X (s+i+1) (t+i) y ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1
  have hdb : Detects (D.convergence (.quotient 1 (.nu X))) (s+i+1,t+i,t+i)
      (regradeE2 (by simp) (finiteTargetLabel D X 1 (s+i+1) (t+i) 0 y)) b := by
    apply first_label_detects_unshifted D synthetic X 1 (by omega) (s+i+1) (t+i) y b
    change b ≫ (D.quotientTower A).rho 1 1 _ = _
    rw [(D.quotientTower A).rho_id,Category.comp_id]
  have hdiff : y-y0 ∈ boundaries H (X.obj D.hopfAndDetector) i (s+i+1,t+i) := by
    have h := differential_targets_sub_mem_boundary H
      (X.obj D.hopfAndDetector) ((i:ℤ)+1) (s,t) (s+i+1,t+i) x y y0 hd hd0
    simpa only [add_sub_cancel_right] using h
  by_cases hi1 : i=1
  · have heq : y=y0 := by
      have hz : y-y0=0 := by simpa only [hi1,Nat.cast_one,boundaries_one,Submodule.mem_bot] using hdiff
      exact sub_eq_zero.mp hz
    refine ⟨a0,hfirst,?_⟩
    change Detects _ (s+i+1,t+i,t+i) _ (boundary a0)
    simpa only [heq] using hbound0
  · have hi2 : 1 < i := by omega
    have hsub : Detects (D.convergence (.quotient 1 (.nu X))) (s+i+1,t+i,t+i)
        (regradeE2 (by simp) (finiteTargetLabel D X 1 (s+i+1) (t+i) 0 (y-y0)))
        (b-boundary a0) := by
      have h := detects_sub _ (s+i+1,t+i,t+i) hdb hbound0
      have regrade_sub {E : SyntheticAdamsSS.{v}} {j k : Tridegree} (hjk : j=k)
          (u v : E.E₂ j) : regradeE2 hjk (u-v) = regradeE2 hjk u - regradeE2 hjk v := by
        subst k
        rfl
      rwa [←regrade_sub,←finiteTargetLabel_sub] at h
    have hcorrection : ∃ z : BiHom (t-s) t (XModLambdaN A i),
        z ≫ (D.quotientTower A).rho 1 i (by omega) = 0 ∧ boundary z = b-boundary a0 := by
      obtain ⟨d,rfl⟩ : ∃ d : ℕ, i=d+1 := ⟨i-1,by omega⟩
      let i : ℕ := d+1
      let yd : cycles H (X.obj D.hopfAndDetector)
          ((1:ℤ)-(t+i)+((t+i)-(1-1:ℕ))) (s+i+1,t+i) :=
        ⟨y-y0,by
          rw [show (1:ℤ)-(t+i)+((t+i)-(1-1:ℕ))=1 by omega,cycles_one]
          trivial⟩
      have hyd : yd.val ∈ boundaries H (X.obj D.hopfAndDetector) (d+1:ℕ) (s+i+1,t+i) := hdiff
      let c : BiHom ((t+i)-(s+i+1)) ((t+i)-(1-1:ℕ)) (XModLambdaN A 1) :=
        homotopyRegrade rfl (by omega) (b-boundary a0)
      have hc : Detects (D.convergence (.quotient 1 (.nu X)))
          (s+i+1,t+i,(t+i)-(1-1:ℕ))
          (finiteTargetLabel D X 1 (s+i+1) (t+i) (1-1) yd.val) c := by
        have back (u v w w' : ℤ) (h : w=w')
            (x : (D.family.obj (XModLambdaN A 1)).E₂ (u,v,w))
            (a : BiHom (v-u) w' (XModLambdaN A 1))
            (ha : Detects (D.convergence (.quotient 1 (.nu X))) (u,v,w')
              (regradeE2 (by rw [h]) x) a) :
            Detects (D.convergence (.quotient 1 (.nu X))) (u,v,w) x
              (homotopyRegrade rfl h.symm a) := by
          subst w'
          simpa only [regradeE2,eqToHom_refl,ModuleCat.id_apply,homotopyRegrade] using ha
        change Detects (D.convergence (.quotient 1 (.nu X)))
          (s+i+1,t+i,(t+i)-(0:ℤ))
          (finiteTargetLabel D X 1 (s+i+1) (t+i) 0 (y-y0))
          (homotopyRegrade rfl (by dsimp; omega) (b-boundary a0))
        exact back _ _ _ _ (by omega) _ _ hsub
      have hpre := actual_rho_kernel_correction D synthetic X
        d 1 (by omega) (by omega) (s+i+1) (t+i) yd hyd c hc
      dsimp only at hpre
      have reindex (n w v : ℤ) (hn : n=t-s) (hw : w=t) (hv : v=t+i)
          (hm : n-1=(t+i)-(s+i+1)) (he : w+i=v)
          (hp : ∃ a : BiHom n w (XModLambdaN A i),
            a ≫ (D.quotientTower A).rho 1 i (by dsimp [i]; omega) = 0 ∧
            homotopyRegrade hm he
              (biSuspensionHomEquiv n w (i:ℤ) (XModLambdaN A 1) (a ≫ δ)) =
              homotopyRegrade rfl hv.symm (b-boundary a0)) :
          ∃ z : BiHom (t-s) t (XModLambdaN A i),
            z ≫ (D.quotientTower A).rho 1 i (by dsimp [i]; omega) = 0 ∧
              boundary z=b-boundary a0 := by
        subst n; subst w; subst v
        exact hp
      exact reindex (((t+i)-(s+i+1))+1) (((t+i)-(1-1:ℕ))-((d+1:ℕ):ℤ))
        ((t+i)-(1-1:ℕ)) (by omega) (by dsimp [i]; omega) (by omega)
        (by omega) (by dsimp [i]; omega) hpre
    obtain ⟨z,hzfirst,hzboundary⟩ := hcorrection
    refine ⟨a0+z,?_,?_⟩
    · rw [Preadditive.add_comp,hfirst,hzfirst,add_zero]
    · have hadd (u v : BiHom (t-s) t (XModLambdaN A i)) :
          boundary (u+v)=boundary u+boundary v := by
        have regrade_add {m w m' w' : ℤ} (hm:m=m') (hw:w=w') {Q : Syn}
            (u v : BiHom m w Q) : homotopyRegrade hm hw (u+v) =
              homotopyRegrade hm hw u + homotopyRegrade hm hw v := by
          subst m'; subst w'; rfl
        simp only [boundary,Preadditive.add_comp,map_add,regrade_add]
      have hb : boundary (a0+z)=b := by rw [hadd,hzboundary]; abel
      change Detects _ (s+i+1,t+i,t+i) _ (boundary (a0+z))
      rw [hb]
      exact hdb

open CategoryTheory.Pretriangulated KIP126.SpectralSequence.FinitePageCalculus in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 1600000 in
private theorem zero_target_actual_lift
    (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q) (s t : ℤ)
    (x : E2 H (X.obj D.hopfAndDetector) s t)
    (hd : KIP126.SpectralSequence.HasDifferential
      (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector)) (i+q)
      (s,t) (s+i+q,t+i+q-1) x 0) :
    ∃ a : BiHom (t-s) t (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) i),
      a ≫ (D.quotientTower (D.nu.functor.obj (X.obj D.hopfAndDetector))).rho 1 i hi =
        firstLabel D X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      a ≫ ((D.quotientTower (D.nu.functor.obj (X.obj D.hopfAndDetector))).triangle hi
        (show i < i+q by omega)).delta = 0 := by
  let E := adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector)
  let r : ℤ := i+q
  have hr : 2 ≤ r := by dsimp [r]; omega
  obtain ⟨hdeg,xr,yr,hxr,hyr,hdiff⟩ := hd
  have hy0 : yr=0 := represents_unique hyr (RepresentsOnPage.zero hr)
  have hz : E.d r (s,t) xr=0 := by
    apply (ModuleCat.mono_iff_injective (eqToHom (congrArg (E.Page r) hdeg))).mp inferInstance
    simpa only [ModuleCat.comp_apply,hy0,map_zero] using hdiff
  obtain ⟨_,z,hx,hzr⟩ := hxr
  let P := E.ssData (s,t)
  let n : ℕ := (r-2).toNat
  change (Subobject.underlying.obj (P.Z ↑n) : ModuleCat ℤ) at z
  change P.pageπ ↑n z=xr at hzr
  have hn : (↑n:WithTop ℕ) ≤ ↑(n+1) := by exact_mod_cast Nat.le_succ n
  let down := Subobject.ofLE (P.Z ↑(n+1)) (P.Z ↑n) (P.Z_anti hn)
  have hk : xr ∈ LinearMap.ker (E.d r (s,t)).hom := hz
  rw [←subobjectModule_kernel,E.Z_succ r (s,t) (by exact hr),subobjectModule_image] at hk
  obtain ⟨v,hv⟩ := hk
  change (Subobject.underlying.obj (P.Z ↑(n+1)) : ModuleCat ℤ) at v
  change P.pageπ ↑n (down v)=xr at hv
  have hb : (P.Z ↑n).arrow (z-down v) ∈ (ModuleCat.subobjectModule P.V) (P.B ↑n) := by
    apply (subobject_cokernel_π_eq_zero_iff (P.B ↑n) (P.Z ↑n) (P.B_le_Z _) _).mp
    change P.pageπ ↑n (z-down v)=0
    rw [map_sub,hzr,hv,sub_self]
  have hb' : (P.Z ↑n).arrow (z-down v) ∈
      (ModuleCat.subobjectModule P.V) (P.Z ↑(n+1)) :=
    (ModuleCat.subobjectModule P.V).monotone ((P.B_mono hn).trans (P.B_le_Z _)) hb
  have hv' : (P.Z ↑n).arrow (down v) ∈
      (ModuleCat.subobjectModule P.V) (P.Z ↑(n+1)) := by
    change (down ≫ (P.Z ↑n).arrow) v ∈ _
    dsimp only [down]
    rw [Subobject.ofLE_arrow]
    exact ⟨v,rfl⟩
  have hz' := ((ModuleCat.subobjectModule P.V) (P.Z ↑(n+1))).add_mem hb' hv'
  rw [map_sub,sub_add_cancel] at hz'
  obtain ⟨z',hz'⟩ := hz'
  have hxnext : x ∈ cycles H (X.obj D.hopfAndDetector) (i+q:ℕ) (s,t) := by
    have hn' : ((i+q:ℕ):ℤ)-1 = (n+1:ℕ) := by dsimp [n,r]; omega
    change ∃ v', (cycleMap H (X.obj D.hopfAndDetector) ↑(((i+q:ℕ):ℤ)-1).toNat (s,t)) v'=x
    rw [hn',Int.toNat_natCast]
    refine ⟨z',?_⟩
    have heq : (Subobject.ofLE (P.Z ↑(n+1)) (P.Z 0) (P.Z_anti bot_le)) z' =
        (Subobject.ofLE (P.Z ↑n) (P.Z 0) (P.Z_anti bot_le)) z := by
      apply (ModuleCat.mono_iff_injective (P.Z 0).arrow).mp inferInstance
      simpa only [←ModuleCat.comp_apply,Subobject.ofLE_arrow] using hz'
    change (P.pageπ 0) ((Subobject.ofLE (P.Z ↑(n+1)) (P.Z 0) (P.Z_anti bot_le)) z')=x
    rw [heq]
    exact hx
  obtain ⟨cZero,hcZero⟩ := (synthetic.finite_lift X (i+q) (by omega) s t x).mp hxnext
  let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
  let f : nuZero D X ⟶ A := SyntheticCategory.biShift_zero.hom.app A
  let c : BiHom (t-s) t (XModLambdaN A (i+q)) := cZero ≫ XModLambdaN.map f (i+q)
  refine ⟨c ≫ (D.quotientTower A).rho i (i+q) (by omega),?_,?_⟩
  · rw [Category.assoc,(D.quotientTower A).rho_comp hi (by omega)]
    dsimp only [c]
    have hnatur : (D.quotientTower (nuZero D X)).rho 1 (i+q) (by omega) ≫
          XModLambdaN.map f 1 =
        XModLambdaN.map f (i+q) ≫ (D.quotientTower A).rho 1 (i+q) (by omega) :=
      (D.comparisonCompatible.quotient_naturality f).rho_naturality (by omega)
    rw [Category.assoc,←hnatur,←Category.assoc,hcZero]
  · rw [Category.assoc,(D.quotientTower A).rho_comp_delta hi (by omega),comp_zero]

open CategoryTheory.Pretriangulated KIP126.SpectralSequence.FinitePageCalculus
  KIP126.Comparison.ClassicalSynthetic in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 6000000 in
private theorem sphere_boundary_nonadjacent
    (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D)
    (i k : ℕ) (hi : 0 < i) (hik : i < k) (s t : ℤ)
    (x : E2 H SphereSpectrum s t)
    (y : E2 H SphereSpectrum (s+k+1) (t+k))
    (hd : HasDifferential (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      (k+1) (s,t) (s+k+1,t+k) x y)
    (hy : y ∈ permanentCycles H SphereSpectrum (s+k+1,t+k))
 :
    ∃ a : BiHom (t-s) t (XModLambdaN (D.nu.functor.obj SphereSpectrum) i),
      a ≫ (D.quotientTower _).rho 1 i hi =
        firstLabel D .sphere s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      Detects (D.convergence (.quotient (k+1-i) (.nu .sphere)))
        (s+k+1,t+k,t+k-(k-i:ℕ))
        (finiteTargetLabel D .sphere (k+1-i) (s+k+1) (t+k) (k-i) y)
        (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
          (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN (D.nu.functor.obj SphereSpectrum) (k+1-i))
            (a ≫ ((D.quotientTower _).triangle hi (show i < k+1 by omega)).delta))) := by
  have family_map_data (D : AdamsComparison H M Syn)  {X Y : Syn} (f : X ⟶ Y) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family f r i = (D.family.functor.map f).toSSDataMorphism.pageMap i (↑(r-2).toNat) := by
    let F := (D.family.functor.map f).toSSDataMorphism
    let PX := (D.family.functor.obj X).ssData i
    let PY := (D.family.functor.obj Y).ssData i
    let nX : WithTop ℕ := ↑(r-(D.family.functor.obj X).r₀).toNat
    let nY : WithTop ℕ := ↑(r-(D.family.functor.obj Y).r₀).toNat
    change (@eqToHom (ModuleCat ℤ) _ (PX.page (↑(r-2).toNat)) (PX.page nX) _ ≫
      (F.pageMap i nX ≫ @eqToHom (ModuleCat ℤ) _ (PY.page nX) (PY.page nY) _) ≫
      @eqToHom (ModuleCat ℤ) _ (PY.page nY) (PY.page (↑(r-2).toNat)) _) = F.pageMap i (↑(r-2).toNat)
    have hX : nX=↑(r-2).toNat := by dsimp only [nX]; rw [D.family.firstPage X]
    have hY : nY=↑(r-2).toNat := by dsimp only [nY]; rw [D.family.firstPage Y]
    have normalize (A B : WithTop ℕ → ModuleCat.{v} ℤ) (j : ∀ n, A n ⟶ B n)
        (n m n0 : WithTop ℕ) (hn : n=n0) (hm : m=n0)
        (h1 : A n0=A n) (h2 : B n=B m) (h3 : B m=B n0) :
        eqToHom h1 ≫ (j n ≫ eqToHom h2) ≫ eqToHom h3 = j n0 := by
      subst n
      subst m
      simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    exact normalize PX.page PY.page (fun n => F.pageMap i n) nX nY (↑(r-2).toNat) hX hY _ _ _

  have family_page_comp (D : AdamsComparison H M Syn)  {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
      familyPageMap D.family f r i ≫ familyPageMap D.family g r i = familyPageMap D.family (f ≫ g) r i := by
    rw [family_map_data D,family_map_data D,family_map_data D,Functor.map_comp]
    exact (SSDataMorphism.pageMap_comp _ _ _ _).symm

  have family_infinity_representative_map (D : AdamsComparison H M Syn)
      {X Y : Syn} (f : X ⟶ Y) (i : Tridegree)
      (y : (D.family.obj X).E₂ i) (e : ((D.family.obj X).sequence.ssData i).eInfty)
      (hy : HasInfinityRepresentative (D.family.obj X) 2 i y e) :
      HasInfinityRepresentative (D.family.obj Y) 2 i
        (familyPageMap D.family f 2 i y) ((D.family.functor.map f).eInftyMap i e) := by
    obtain ⟨hr,z,hz,he⟩ := hy
    change (Subobject.ofLE (((D.family.functor.obj X).ssData i).Z ⊤)
      (((D.family.functor.obj X).ssData i).Z 0) _ ≫ ((D.family.functor.obj X).ssData i).pageπ 0) z=y at hz
    let F := (D.family.functor.map f).toSSDataMorphism
    refine ⟨hr,F.cycleMap i ⊤ z,?_,?_⟩
    · rw [family_map_data D]
      have h := F.cycleMap_ofLE_assoc i (show (0:WithTop ℕ)≤⊤ from le_top)
        (((D.family.obj Y).sequence.ssData i).pageπ 0)
      dsimp only [SyntheticAdamsFamily.obj] at h
      rw [←F.pageπ_pageMap] at h
      exact (congrArg (fun a => a z) h).symm.trans (by
        simpa only [ModuleCat.comp_apply,CategoryTheory.comp_apply] using congrArg (fun q => F.pageMap i 0 q) hz)
    · exact (congrArg (fun a => a z) (F.pageπ_pageMap i ⊤)).symm.trans (by
        change F.pageMap i ⊤ (((D.family.obj X).sequence.ssData i).pageπ ⊤ z)=_
        rw [he])

  have grade_natural (D : AdamsComparison H M Syn) (A B : SyntheticObject)
      (f : A.obj D.nu D.hopfAndDetector ⟶ B.obj D.nu D.hopfAndDetector) (i : Tridegree)
      (a : (Subobject.underlying.obj ((towerFiltration (nuCoefficientUnit H.unit D.nu)
        (A.obj D.nu D.hopfAndDetector)).F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ))
      (b : (Subobject.underlying.obj ((towerFiltration (nuCoefficientUnit H.unit D.nu)
        (B.obj D.nu D.hopfAndDetector)).F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ))
      (hab : ((towerFiltration (nuCoefficientUnit H.unit D.nu)
        (A.obj D.nu D.hopfAndDetector)).F i.1 (i.2.1-i.1,i.2.2)).arrow a ≫ f =
          ((towerFiltration (nuCoefficientUnit H.unit D.nu)
            (B.obj D.nu D.hopfAndDetector)).F i.1 (i.2.1-i.1,i.2.2)).arrow b) :
      ((D.convergence B).identification i).inv
        ((towerFiltration (nuCoefficientUnit H.unit D.nu)
          (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) b) =
      (D.family.functor.map f).eInftyMap i (((D.convergence A).identification i).inv
        ((towerFiltration (nuCoefficientUnit H.unit D.nu)
          (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2) a)) := by
    obtain ⟨c,hca,hce⟩ := D.comparisonCompatible.convergence_natural A B f
    have hc := c.iso_compat i
    simp only [KIP126.SpectralSequence.Filtration.transportGraded_self,Category.comp_id,
      TowerConvergence.toSynthetic,SyntheticAdamsConvergence.toConvergence] at hc
    rw [hce] at hc
    have hb : (c.filtration_compat i.1 (i.2.1-i.1,i.2.2)).choose a = b := by
      apply (ModuleCat.mono_iff_injective
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F
          i.1 (i.2.1-i.1,i.2.2)).arrow).mp inferInstance
      have he := ConcreteCategory.congr_hom
        (c.filtration_compat i.1 (i.2.1-i.1,i.2.2)).choose_spec a
      change _ = c.aMap (i.2.1-i.1,i.2.2) _ at he
      have hm : c.aMap (i.2.1-i.1,i.2.2)
          (((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F
            i.1 (i.2.1-i.1,i.2.2)).arrow a) =
          ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F
            i.1 (i.2.1-i.1,i.2.2)).arrow a ≫ f := by rw [hca]; rfl
      exact he.trans (hm.trans hab)
    have hp := ConcreteCategory.congr_hom
      (show (towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded
          i.1 (i.2.1-i.1,i.2.2) ≫ Filtration.inducedAssocGradedMap c.aMap c.filtration_compat
            i.1 (i.2.1-i.1,i.2.2) =
        (c.filtration_compat i.1 (i.2.1-i.1,i.2.2)).choose ≫
          (towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded
            i.1 (i.2.1-i.1,i.2.2) from cokernel.π_desc _ _ _) a
    simp only [ModuleCat.comp_apply] at hp
    have hp' := hp.trans (congrArg ((towerFiltration (nuCoefficientUnit H.unit D.nu)
      (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded i.1 (i.2.1-i.1,i.2.2)) hb)
    apply ((D.convergence B).identification i).toLinearEquiv.injective
    have he := ConcreteCategory.congr_hom hc (((D.convergence A).identification i).inv
      ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) a))
    simp only [ModuleCat.comp_apply] at he
    have hA := ((D.convergence A).identification i).toLinearEquiv.apply_symm_apply
      ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) a)
    have hB := ((D.convergence B).identification i).toLinearEquiv.apply_symm_apply
      ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) b)
    exact hB.trans (hp'.symm.trans ((congrArg
      (Filtration.inducedAssocGradedMap c.aMap c.filtration_compat i.1 (i.2.1-i.1,i.2.2))
        hA.symm).trans he.symm))

  have detects_map (D : AdamsComparison H M Syn) (A B : SyntheticObject)
      (f : A.obj D.nu D.hopfAndDetector ⟶ B.obj D.nu D.hopfAndDetector) (i : Tridegree)
      (x : (D.family.obj (A.obj D.nu D.hopfAndDetector)).E₂ i)
      (a : BiHom (i.2.1-i.1) i.2.2 (A.obj D.nu D.hopfAndDetector))
      (ha : Detects (D.convergence A) i x a) :
      Detects (D.convergence B) i (familyPageMap D.family f 2 i x) (a ≫ f) := by
    obtain ⟨e,he,a',ha',hga⟩ := ha
    obtain ⟨c,hca,hce⟩ := D.comparisonCompatible.convergence_natural A B f
    let b := (c.filtration_compat i.1 (i.2.1-i.1,i.2.2)).choose a'
    have hb : ((towerFiltration (nuCoefficientUnit H.unit D.nu) (B.obj D.nu D.hopfAndDetector)).F
        i.1 (i.2.1-i.1,i.2.2)).arrow b = a ≫ f := by
      have h := ConcreteCategory.congr_hom
        (c.filtration_compat i.1 (i.2.1-i.1,i.2.2)).choose_spec a'
      change _ = c.aMap (i.2.1-i.1,i.2.2) _ at h
      have hm : c.aMap (i.2.1-i.1,i.2.2)
          (((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).F
            i.1 (i.2.1-i.1,i.2.2)).arrow a') = a ≫ f := by
        rw [hca]
        change _ ≫ f = _
        rw [ha']
      exact h.trans hm
    refine ⟨_,family_infinity_representative_map D f i x e he,b,hb,?_⟩
    have h := grade_natural D A B f i a' b (by rw [ha',hb])
    have haE : ((D.convergence A).identification i).inv
        ((towerFiltration (nuCoefficientUnit H.unit D.nu) (A.obj D.nu D.hopfAndDetector)).toAssociatedGraded
          i.1 (i.2.1-i.1,i.2.2) a') = e := by
      rw [←hga]
      exact ((D.convergence A).identification i).toLinearEquiv.symm_apply_apply e
    rw [haE] at h
    exact (congrArg ((D.convergence B).identification i).hom h).symm.trans
      (((D.convergence B).identification i).toLinearEquiv.apply_symm_apply _)

  have sphere_first_quotient_label (D : AdamsComparison H M Syn) (s t : ℤ)
      (y : E2 H SphereSpectrum s t) :
      D.sphereFirstQuotient s t
        (firstLabel D .sphere s t y ≫ XModLambdaN.map
          ((SyntheticCategory.biShift_zero.hom.app _) ≫ D.nu.unitIso.hom) 1) = y := by
    let e := SyntheticCategory.biShift_zero.app (D.nu.functor.obj SphereSpectrum) ≪≫ D.nu.unitIso
    let Q := (D.quotientFunctoriality.functor 1).mapIso e
    let c : BiHom (t-s) t (XModLambdaN (nuZero D .sphere) 1) ≃+ E2 H SphereSpectrum s t :=
      Eq.mp (congrArg (fun z : ℤ => BiHom (t-s) z
        (XModLambdaN (nuZero D .sphere) 1) ≃+ E2 H SphereSpectrum s t)
        (Int.add_zero t)) (D.firstQuotient SphereSpectrum 0 s t)
    change c ((firstLabel D .sphere s t y ≫ Q.hom) ≫ Q.inv) = y
    rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
    have cast_symm (n m : ℤ) (h : n = m)
        (e : BiHom (t-s) n (XModLambdaN (nuZero D .sphere) 1) ≃+
          E2 H SphereSpectrum s t) (z : E2 H SphereSpectrum s t) :
        (congrArg (fun w => BiHom (t-s) w (XModLambdaN (nuZero D .sphere) 1)) h).mp
            (e.symm z) =
          ((congrArg (fun w => BiHom (t-s) w (XModLambdaN (nuZero D .sphere) 1) ≃+
            E2 H SphereSpectrum s t) h).mp e).symm z := by
      subst m
      rfl
    have hc : firstLabel D .sphere s t y = c.symm y := by
      exact cast_symm (t+0) t (Int.add_zero t) (D.firstQuotient SphereSpectrum 0 s t) y
    rw [hc,AddEquiv.apply_symm_apply]

  have sphere_finite_lambda_detects (D : AdamsComparison H M Syn)
      (q : ℕ) (_hq : 0 < q) (s t : ℤ) (k : ℕ)
      (y : E2 H SphereSpectrum s t)
      (α : BiHom (t-s) t (D.nu.functor.obj SphereSpectrum))
      (hα : α ≫ XModLambdaN.incl _ 1 =
        firstLabel D .sphere s t y ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
      Detects (D.convergence (.quotient q (.nu .sphere))) (s,t,t-k)
        (finiteTargetLabel D .sphere q s t k y)
        (lambdaMultiply k α ≫ XModLambdaN.incl _ q) := by
    have family_page_id (X : Syn) (r : ℤ) (i : Tridegree) :
        familyPageMap D.family (𝟙 X) r i = 𝟙 _ := by
      rw [family_map_data,CategoryTheory.Functor.map_id]
      exact SSDataMorphism.pageMap_id _ _ _
    let a : BiHom (t-s) t (S_0_0 : Syn) := α ≫ D.nu.unitIso.hom
    have hfirst : quotientClass 1 a =
        firstLabel D .sphere s t y ≫ XModLambdaN.map
          (SyntheticCategory.biShift_zero.hom.app _ ≫ D.nu.unitIso.hom) 1 := by
      dsimp only [quotientClass,a]
      rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc,hα,
        Category.assoc,←D.quotientFunctoriality.map_comp]
      rfl
    have hl : D.sphereFirstQuotient s t (quotientClass 1 a) = y := by
      rw [hfirst]
      exact sphere_first_quotient_label D s t y
    have hs := D.comparisonCompatible.homotopy_lambda s t k a
    rw [hl] at hs
    have hforw : familyPageMap D.family D.nu.unitIso.hom 2 (s,t,t-k)
        (targetNuLabel D .sphere s t k y) = D.sphereE2 s t k y := by
      let z : (D.family.obj (nuZero D .sphere)).E₂ (s,t,t-k) := by
        simpa [SyntheticAdamsSS.E₂] using D.nuE2 .sphere 0 s t k y
      exact (ConcreteCategory.congr_hom (family_page_comp D
        (SyntheticCategory.biShift_zero.hom.app _) D.nu.unitIso.hom 2 (s,t,t-k)) z).trans
          (D.comparisonCompatible.sphere_nu s t k y)
    have hback : familyPageMap D.family D.nu.unitIso.inv 2 (s,t,t-k)
        (D.sphereE2 s t k y) = targetNuLabel D .sphere s t k y := by
      rw [←hforw,←ModuleCat.comp_apply,family_page_comp,Iso.hom_inv_id,family_page_id]
      rfl
    have hc : lambdaMultiply k a ≫ D.nu.unitIso.inv = lambdaMultiply k α := by
      dsimp only [lambdaMultiply,a]
      simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
    have hn := detects_map D .sphere (.nu .sphere) D.nu.unitIso.inv
      (s,t,t-k) _ _ hs
    have hn' : Detects (D.convergence (.nu .sphere)) (s,t,t-k)
        (targetNuLabel D .sphere s t k y) (lambdaMultiply k α) := by
      exact (congrArg₂ (Detects (D.convergence (.nu .sphere)) (s,t,t-k)) hback hc).mp hn
    exact detects_map D (.nu .sphere) (.quotient q (.nu .sphere))
      (XModLambdaN.incl _ q) (s,t,t-k) _ _ hn'

  have finite_quotient_high_filtration_zero_int (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
      (a : BiHom m w (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q))
      (ha : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) s a) : a = 0 := by
    have hz (j : ℤ) (hj : s ≤ j) :
        IsZero (((D.family.nuQuotient D.nu (X.obj D.hopfAndDetector) q).sequence.ssData
          (j,m+j,w)).eInfty) := by
      have hwin : ¬ (0 ≤ (m+j)-w ∧ (m+j)-w < q) := by omega
      haveI : Subsingleton (finiteEInftyModel H (X.obj D.hopfAndDetector) q (j,m+j) w) := by
        simp only [finiteEInftyModel, hwin, ite_false]
        infer_instance
      haveI : Subsingleton (((D.family.nuQuotient D.nu (X.obj D.hopfAndDetector) q).sequence.ssData
          (j,m+j,w)).eInfty) :=
        (synthetic.eInfty.presentation.finite (X.obj D.hopfAndDetector) q hq (j,m+j) w).injective.subsingleton
      exact ModuleCat.isZero_of_subsingleton _
    apply D.homotopySeparated (.quotient q (.nu X)) m w a
    intro j
    by_cases hj : s ≤ (j:ℤ)
    · exact ((D.convergence (.quotient q (.nu X))).filtrationAtLeast_iff_of_eInfty_isZero
        s j m w hj (fun k hk _ => hz k hk) a).mp ha
    · exact towerFiltrationSubmodule_antitone (nuCoefficientUnit H.unit D.nu) _ (m,w)
        (by omega) ha

  have finite_top_detection_unique (D : AdamsComparison H M Syn)
      (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
      (s t w : ℤ) (hwindow : (q:ℤ) ≤ t+1-w)
      (x : (D.family.nuQuotient D.nu (X.obj D.hopfAndDetector) q).E₂ (s,t,w))
      (a b : BiHom (t-s) w (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) q))
      (ha : Detects (D.convergence (.quotient q (.nu X))) (s,t,w) x a)
      (hb : Detects (D.convergence (.quotient q (.nu X))) (s,t,w) x b) : a=b := by
    apply sub_eq_zero.mp
    exact finite_quotient_high_filtration_zero_int D synthetic X q hq (t-s) w (s+1)
      (by omega) (a-b)
      (detects_sub_filtration (D.convergence (.quotient q (.nu X))) (s,t,w) ha hb)

  have adjacent_sphere_representative_and_target_lift
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D)
      (i k : ℕ) (hi : 0 < i) (hik : i ≤ k) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (y : E2 H SphereSpectrum (s+k+1) (t+k))
      (hd : HasDifferential (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
        (k+1) (s,t) (s+k+1,t+k) x y)
      (hy : y ∈ permanentCycles H SphereSpectrum (s+k+1,t+k)) :
      let A := D.nu.functor.obj SphereSpectrum
      let δ : XModLambdaN A k ⟶
          ((SyntheticCategory.biShift (0,-(k:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
        simpa only [show k.succ-k=1 by omega] using
          ((D.quotientTower A).triangle (show 0<k by omega) (Nat.lt_succ_self k)).delta
      ∃ (a : BiHom (t-s) t (XModLambdaN A k))
          (α : BiHom ((t+k)-(s+k+1)) (t+k) A),
        a ≫ (D.quotientTower A).rho 1 k (by omega) =
          firstLabel D .sphere s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
        α ≫ XModLambdaN.incl A 1 =
          firstLabel D .sphere (s+k+1) (t+k) y ≫
            XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
        homotopyRegrade (by omega) rfl
            (biSuspensionHomEquiv (t-s) t (k:ℤ) (XModLambdaN A 1) (a ≫ δ)) =
          α ≫ XModLambdaN.incl A 1 ∧
        (a ≫ (D.quotientTower A).rho i k hik) ≫ (D.quotientTower A).rho 1 i hi =
          firstLabel D .sphere s t x ≫
            XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 := by
    dsimp only
    let A := D.nu.functor.obj SphereSpectrum
    obtain ⟨a,ha,had⟩ := adjacent_mahowald_case D synthetic .sphere k (by omega) s t x y hd
    obtain ⟨α0,hα0⟩ := (synthetic.permanent_lift .sphere (s+k+1) (t+k) y).mp hy
    let α : BiHom ((t+k)-(s+k+1)) (t+k) A :=
      α0 ≫ SyntheticCategory.biShift_zero.hom.app A
    have hα : α ≫ XModLambdaN.incl A 1 =
        firstLabel D .sphere (s+k+1) (t+k) y ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 := by
      dsimp only [α]
      rw [Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
      exact congrArg (fun z => z ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1) hα0
    have hαρ : (α ≫ XModLambdaN.incl A 1) ≫ (D.quotientTower A).rho 1 1 (by decide) =
        firstLabel D .sphere (s+k+1) (t+k) y ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 := by
      rw [(D.quotientTower A).rho_id,Category.comp_id]
      exact hα
    have hαd := first_label_detects_unshifted D synthetic .sphere 1 (by decide)
      (s+k+1) (t+k) y (α ≫ XModLambdaN.incl A 1) hαρ
    refine ⟨a,α,ha,hα,?_,?_⟩
    · exact finite_top_detection_unique D synthetic .sphere 1 (by decide)
        (s+k+1) (t+k) (t+k) (by omega) _ _ _ had hαd
    · rw [Category.assoc,(D.quotientTower A).rho_comp hi hik]
      exact ha

  have inverse_associativity (coh : BiShiftCoherence Syn)
      (a b c ab bc total : ℤ×ℤ) (hab : a+b=ab) (hbc : b+c=bc)
      (ht : ab+c=total) (ht' : a+bc=total) (X : Syn) :
      (biShiftAddIso a bc total ht').inv.app X ≫
          (biShiftAddIso b c bc hbc).inv.app ((SyntheticCategory.biShift a).obj X) =
        (biShiftAddIso ab c total ht).inv.app X ≫
          (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).inv.app X) := by
    have he : (SyntheticCategory.biShift c).mapIso ((biShiftAddIso a b ab hab).app X) ≪≫
          (biShiftAddIso ab c total ht).app X =
        (biShiftAddIso b c bc hbc).app ((SyntheticCategory.biShift a).obj X) ≪≫
          (biShiftAddIso a bc total ht').app X := by
      apply Iso.ext
      exact coh.associativity a b c ab bc total hab hbc ht ht' X
    have h := congrArg Iso.inv he
    simpa only [Iso.trans_inv,Functor.mapIso_inv,Iso.app_inv] using h.symm

  have shift_hom_associativity (coh : BiShiftCoherence Syn)
      (a b c ab bc total : ℤ×ℤ) (hab : a+b=ab) (hbc : b+c=bc)
      (ht : ab+c=total) (ht' : a+bc=total) {A : Syn}
      (α : (SyntheticCategory.biShift a).obj (S_0_0 : Syn) ⟶ A) :
      (biShiftAddIso a bc total ht').inv.app S_0_0 ≫
          (SyntheticCategory.biShift bc).map α ≫ (biShiftAddIso b c bc hbc).inv.app A =
        (biShiftAddIso ab c total ht).inv.app S_0_0 ≫
          (SyntheticCategory.biShift c).map
            ((biShiftAddIso a b ab hab).inv.app S_0_0 ≫ (SyntheticCategory.biShift b).map α) := by
    rw [(biShiftAddIso b c bc hbc).inv.naturality α]
    change _ ≫ _ ≫ (SyntheticCategory.biShift c).map ((SyntheticCategory.biShift b).map α) = _
    rw [←Category.assoc,inverse_associativity coh,Functor.map_comp,Category.assoc]

  have susp_regrade_eq (n u k l m w : ℤ) (hm : n+k=m) (hw : u+l=w)
      (A : Syn) (α : BiHom n u A) :
      homotopyRegrade hm hw (susp_invariance n u k l A α) =
        (biShiftAddIso (n,u) (k,l) (m,w) (Prod.ext hm hw)).inv.app S_0_0 ≫
          (SyntheticCategory.biShift (k,l)).map α := by
    subst m
    subst w
    simp [homotopyRegrade,susp_invariance,biShiftAddIso]

  have bi_susp_symm_eq (m w q : ℤ) (A : Syn) (α : BiHom (m-1) (w+q) A) :
      (biSuspensionHomEquiv m w q A).symm α =
        homotopyRegrade (sub_add_cancel m 1) (add_neg_cancel_right w q)
          (susp_invariance (m-1) (w+q) 1 (-q) A α) ≫ (biSuspensionIso q A).hom := by
    have hc (m' w' : ℤ) (hm : m'=m) (hw : w'=w)
        (e : BiHom (m-1) (w+q) A ≃ BiHom m' w' (((SyntheticCategory.biShift (0,-q)).obj A)⟦(1:ℤ)⟧))
        (he : (BiHom (m-1) (w+q) A ≃ BiHom m' w' (((SyntheticCategory.biShift (0,-q)).obj A)⟦(1:ℤ)⟧)) =
          (BiHom (m-1) (w+q) A ≃ BiHom m w (((SyntheticCategory.biShift (0,-q)).obj A)⟦(1:ℤ)⟧))) :
        (he.mp e) α = homotopyRegrade hm hw (e α) := by
      subst m'; subst w'; rfl
    have regrade_comp {m' w' : ℤ} (hm : m'=m) (hw : w'=w) {B C : Syn}
        (a : BiHom m' w' B) (f : B ⟶ C) :
        homotopyRegrade hm hw (a≫f) = homotopyRegrade hm hw a ≫ f := by
      subst m'; subst w'; rfl
    change (biSuspensionHomUnderlyingEquiv m w q A).symm α = _
    simp only [biSuspensionHomUnderlyingEquiv,Equiv.symm_symm]
    rw [hc (m-1+1) (w+q+-q) (by omega) (by omega)]
    simp only [Equiv.trans_apply,Iso.homCongr_apply,Iso.refl_inv,Category.id_comp,regrade_comp]

  have bi_susp_iso_hom_eq (q : ℤ) (A : Syn) :
      (biSuspensionIso q A).hom =
        (biShiftAddIso (0,-q) (1,0) (1,-q) (by ext <;> simp)).inv.app A ≫
          (SyntheticCategory.biShift_compat 1).hom.app ((SyntheticCategory.biShift (0,-q)).obj A) := by
    have hc {X X' Y : Syn} (h : X=X') (e : X ≅ Y) (he : (X ≅ Y)=(X' ≅ Y)) :
        (he.mp e).hom = eqToHom h.symm ≫ e.hom := by
      subst X'; simp
    unfold biSuspensionIso
    rw [hc (congrArg (fun p : ℤ×ℤ => (SyntheticCategory.biShift p).obj A) (by ext <;> simp))]
    simp only [biShiftAddIso,Iso.trans_hom,Iso.trans_inv,
      NatTrans.comp_app,eqToIso.inv,eqToHom_app,Category.assoc]
    rfl

  let vertical_hom (n w q : ℤ) (A : Syn) (α : BiHom n (w+q) A) :
      BiHom n w ((SyntheticCategory.biShift (0,-q)).obj A) :=
    (biShiftAddIso (n,w+q) (0,-q) (n,w) (by ext <;> simp)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (0,-q)).map α

  have bi_susp_symm_vertical (coh : BiShiftCoherence Syn)
      (m w q : ℤ) (A : Syn) (α : BiHom (m-1) (w+q) A) :
      (biSuspensionHomEquiv m w q A).symm α =
        (biShiftAddIso (m-1,w) (1,0) (m,w) (by ext <;> simp)).inv.app S_0_0 ≫
          (SyntheticCategory.biShift_compat 1).hom.app (Smn (m-1) w) ≫
            (shiftFunctor Syn (1:ℤ)).map (vertical_hom (m-1) w q A α) := by
    rw [bi_susp_symm_eq,susp_regrade_eq,bi_susp_iso_hom_eq]
    have h := shift_hom_associativity coh
      (m-1,w+q) (0,-q) (1,0) (m-1,w) (1,-q) (m,w)
      (by ext <;> simp) (by ext <;> simp) (by ext <;> simp) (by ext <;> simp) α
    have h' := congrArg (fun f => f ≫ (SyntheticCategory.biShift_compat 1).hom.app
      ((SyntheticCategory.biShift (0,-q)).obj A)) h
    calc
      _ = (biShiftAddIso (m-1,w) (1,0) (m,w) (by ext <;> simp)).inv.app S_0_0 ≫
          (SyntheticCategory.biShift (1,0)).map (vertical_hom (m-1) w q A α) ≫
            (SyntheticCategory.biShift_compat 1).hom.app ((SyntheticCategory.biShift (0,-q)).obj A) := by
        simpa only [vertical_hom,Category.assoc] using h'
      _ = _ := by
        rw [(SyntheticCategory.biShift_compat 1).hom.naturality]
        rfl

  have lambda_regrade_eq (n u : ℤ) (d : ℕ) (v : ℤ) (hv : u-(d:ℤ)=v)
      (A : Syn) (α : BiHom n u A) :
      homotopyRegrade rfl hv (lambdaMultiply d α) =
        (biShiftAddIso (n,u) (0,-(d:ℤ)) (n,v) (by ext <;> dsimp <;> omega)).inv.app S_0_0 ≫
          lambdaPow d (Smn n u) ≫ α := by
    subst v
    simp only [homotopyRegrade,lambdaMultiply,biShiftAddIso,Iso.trans_inv,NatTrans.comp_app,
      eqToIso.inv,eqToHom_app,Category.assoc]

  have vertical_hom_lambda (coh : BiShiftCoherence Syn)
      (i k : ℕ) (hik : i ≤ k) (n w : ℤ) (A : Syn) (α : BiHom n (w+k) A) :
      vertical_hom n w (k:ℤ) A α ≫ lambdaRestrictionSourceMap i k hik A =
        vertical_hom n w (i:ℤ) A
          (homotopyRegrade rfl (by omega) (lambdaMultiply (k-i) α)) := by
    dsimp only [vertical_hom,lambdaRestrictionSourceMap,lambdaShiftAddIso,KIP126.Synthetic.Context.lambdaDegree]
    rw [lambda_regrade_eq]
    have h := shift_hom_associativity coh
      (n,w+k) (0,-((k-i:ℕ):ℤ)) (0,-(i:ℤ)) (n,w+i) (0,-(k:ℤ)) (n,w)
      (by ext <;> dsimp <;> omega) (by ext <;> dsimp; omega)
      (by ext <;> dsimp <;> omega) (by ext <;> dsimp <;> omega) α
    have h' := congrArg (fun f => f ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
      (lambdaPow (k-i) A)) h
    simpa only [Smn,Category.assoc,←Functor.map_comp,lambdaPow_naturality] using h'

  have bi_susp_lambda_transition (coh : BiShiftCoherence Syn)
      (i k : ℕ) (hik : i ≤ k) (m w : ℤ) (A : Syn)
      (α : BiHom (m-1) (w+k) A) :
      biSuspensionHomEquiv m w (i:ℤ) A
        ((biSuspensionHomEquiv m w (k:ℤ) A).symm α ≫
          (shiftFunctor Syn (1:ℤ)).map (lambdaRestrictionSourceMap i k hik A)) =
        homotopyRegrade rfl (by omega) (lambdaMultiply (k-i) α) := by
    apply (biSuspensionHomEquiv m w (i:ℤ) A).symm.injective
    rw [AddEquiv.symm_apply_apply,bi_susp_symm_vertical coh,bi_susp_symm_vertical coh]
    simp only [Category.assoc]
    rw [←Functor.map_comp,vertical_hom_lambda coh]

  have bi_susp_natural (coh : BiShiftCoherence Syn)
      (m w i : ℤ) {A B : Syn} (f : A ⟶ B)
      (a : BiHom m w (((SyntheticCategory.biShift (0,-i)).obj A)⟦(1:ℤ)⟧)) :
      biSuspensionHomEquiv m w i B
        (a ≫ (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-i)).map f)) =
        biSuspensionHomEquiv m w i A a ≫ f := by
    obtain ⟨α,rfl⟩ := (biSuspensionHomEquiv m w i A).symm.surjective a
    rw [AddEquiv.apply_symm_apply]
    apply (biSuspensionHomEquiv m w i B).symm.injective
    rw [AddEquiv.symm_apply_apply,bi_susp_symm_vertical coh,bi_susp_symm_vertical coh]
    simp only [vertical_hom,Functor.map_comp,Category.assoc]

  have lambda_transition_evaluation [HasFunctorialCofiber (C := Syn)]
      (coh : BiShiftCoherence Syn) (i k : ℕ) (hik : i ≤ k) (q : ℕ)
      (m w : ℤ) (A : Syn) (α : BiHom (m-1) (w+k) A) :
      biSuspensionHomEquiv m w (i:ℤ) (XModLambdaN A q)
        ((biSuspensionHomEquiv m w (k:ℤ) A).symm α ≫
          (shiftFunctor Syn (1:ℤ)).map
            (lambdaRestrictionSourceMap i k hik A ≫
              (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A q))) =
        homotopyRegrade rfl (by omega) (lambdaMultiply (k-i) α ≫ XModLambdaN.incl A q) := by
    have regrade_comp {n n' v v' : ℤ} (hn : n=n') (hv : v=v')
        {A B : Syn} (a : BiHom n v A) (f : A ⟶ B) :
        homotopyRegrade hn hv (a≫f) = homotopyRegrade hn hv a ≫ f := by
      subst n'; subst v'; rfl
    rw [Functor.map_comp,←Category.assoc,bi_susp_natural coh,
      bi_susp_lambda_transition coh,regrade_comp]

  have quotient_maps_difference_factors {A B : Syn} (j : ℕ)
      (a b : XModLambdaN A j ⟶ B)
      (hab : XModLambdaN.incl A j ≫ a = XModLambdaN.incl A j ≫ b) :
      ∃ z : ((SyntheticCategory.biShift (0,-(j:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶ B,
        a-b = XModLambdaN.proj A j ≫ z := by
    apply Triangle.yoneda_exact₃ (XModLambdaN.cofiberTriangle A j)
      (XModLambdaN.cofiberTriangle_distinguished A j) (a-b)
    change XModLambdaN.incl A j ≫ (a-b) = 0
    rw [Preadditive.comp_sub,hab,sub_self]

  have quotient_maps_equal_on_spheres_of_no_return {A B : Syn} (j : ℕ)
      (a b : XModLambdaN A j ⟶ B)
      (hab : XModLambdaN.incl A j ≫ a = XModLambdaN.incl A j ≫ b)
      (hzero : ∀ (m w : ℤ)
        (c : BiHom m w (((SyntheticCategory.biShift (0,-(j:ℤ))).obj A)⟦(1:ℤ)⟧))
        (z : ((SyntheticCategory.biShift (0,-(j:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶ B), c ≫ z = 0) :
      ∀ (m w : ℤ) (c : BiHom m w (XModLambdaN A j)), c ≫ a = c ≫ b := by
    obtain ⟨z,hz⟩ := quotient_maps_difference_factors j a b hab
    intro m w c
    apply sub_eq_zero.mp
    rw [←Preadditive.comp_sub,hz,←Category.assoc]
    exact hzero m w (c ≫ XModLambdaN.proj A j) z

  have negative_shift_nu_to_quotient_zero
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D) (X Y : ClassicalObject)
      (j : ℕ) (hj : 0 < j) (m w : ℤ)
      (c : BiHom m w ((SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
        (D.nu.functor.obj (X.obj D.hopfAndDetector))))
      (z : (SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
        (D.nu.functor.obj (X.obj D.hopfAndDetector)) ⟶
          XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) j) : c ≫ z = 0 := by
    let A : SyntheticObject := .shift (0,-(j:ℤ)-1) (.nu X)
    let B : SyntheticObject := .quotient j (.nu Y)
    let L : ℤ := w-m+j+1
    have hzA (k : ℤ) (hk : k < L) :
        IsZero (((D.family.obj (A.obj D.nu D.hopfAndDetector)).sequence.ssData (k,m+k,w)).eInfty) := by
      letI : Subsingleton (((D.family.obj (D.nu.functor.obj (X.obj D.hopfAndDetector))).sequence.ssData
          (k,m+k,w+j+1)).eInfty) :=
        KIP126.Comparison.syntheticEInfty_nu_subsingleton_of_outside
          H D.nu D.family synthetic.eInfty.presentation (X.obj D.hopfAndDetector) (k,m+k) (w+j+1)
            (by dsimp only [L] at hk; omega)
      have hSub : Subsingleton (((D.family.obj ((SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
          (D.nu.functor.obj (X.obj D.hopfAndDetector)))).sequence.ssData
            (k,m+k,(w+j+1)+(-(j:ℤ)-1))).eInfty) :=
        (synthetic.eInfty.weightShift.iso _ (-(j:ℤ)-1) (k,m+k) (w+j+1)).injective.subsingleton
      have he : (w+(j:ℤ)+1)+(-(j:ℤ)-1)=w := by omega
      rw [he] at hSub
      letI := hSub
      change IsZero (((D.family.obj ((SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
        (D.nu.functor.obj (X.obj D.hopfAndDetector)))).sequence.ssData (k,m+k,w)).eInfty)
      exact ModuleCat.isZero_of_subsingleton _
    have hc0 : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) 0 c := by
      refine ⟨c,?_⟩
      change c ≫ adamsTowerMap _ _ 0 0 _ = c
      rw [adamsTowerMap_self]
      exact Category.comp_id c
    have hcL : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) L c := by
      by_cases hL : L≤0
      · exact towerFiltrationSubmodule_antitone _ _ _ hL hc0
      · exact ((D.convergence A).filtrationAtLeast_iff_of_eInfty_isZero 0 L m w
          (by omega) (fun k _ hk => hzA k hk) c).mp hc0
    have hcz : FiltrationAtLeast (nuCoefficientUnit H.unit D.nu) L (c ≫ z) := by
      obtain ⟨a,ha⟩ := hcL
      refine ⟨a ≫ adamsTowerInduced (nuCoefficientUnit H.unit D.nu) z L.toNat,?_⟩
      change (a ≫ adamsTowerInduced _ z L.toNat) ≫ adamsTowerMap _ _ 0 L.toNat _ = c ≫ z
      rw [Category.assoc,adamsTowerInduced_map,←Category.assoc]
      change (towerHomotopyMap (nuCoefficientUnit H.unit D.nu) _ L.toNat (m,w) a) ≫ z = _
      rw [ha]
    have hzB (k : ℤ) (hk : L≤k) :
        IsZero (((D.family.obj (B.obj D.nu D.hopfAndDetector)).sequence.ssData (k,m+k,w)).eInfty) := by
      haveI : Subsingleton (((D.family.obj (XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) j)).sequence.ssData
          (k,m+k,w)).eInfty) :=
        KIP126.Comparison.syntheticEInfty_finite_subsingleton_of_outside
          H D.nu D.family synthetic.eInfty.presentation (Y.obj D.hopfAndDetector) j hj (k,m+k) w
            (by dsimp only [L] at hk; omega)
      change IsZero (((D.family.obj (XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) j)).sequence.ssData
        (k,m+k,w)).eInfty)
      exact ModuleCat.isZero_of_subsingleton _
    apply D.homotopySeparated B m w (c ≫ z)
    intro k
    by_cases hk : L≤(k:ℤ)
    · exact ((D.convergence B).filtrationAtLeast_iff_of_eInfty_isZero L k m w hk
        (fun t ht _ => hzB t ht) (c ≫ z)).mp hcz
    · exact towerFiltrationSubmodule_antitone _ _ _ (by omega) hcz

  have quotient_nu_maps_equal_on_spheres
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D) (X Y : ClassicalObject)
      (j : ℕ) (hj : 0 < j)
      (a b : XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) j ⟶
        XModLambdaN (D.nu.functor.obj (Y.obj D.hopfAndDetector)) j)
      (hab : XModLambdaN.incl _ j ≫ a = XModLambdaN.incl _ j ≫ b) :
      ∀ (m w : ℤ) (c : BiHom m w (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) j)),
        c ≫ a = c ≫ b := by
    apply quotient_maps_equal_on_spheres_of_no_return j a b hab
    intro m w c z
    let V := D.nu.functor.obj (X.obj D.hopfAndDetector)
    let ε : ((SyntheticCategory.biShift (0,-(j:ℤ))).obj V)⟦(1:ℤ)⟧ ≅
        (SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
          (D.nu.functor.obj ((ClassicalObject.shift 1 X).obj D.hopfAndDetector)) :=
      (SyntheticCategory.biShift_compat (Syn:=Syn) 1).symm.app _ ≪≫
        (SyntheticCategory.biShift_comp (0,-(j:ℤ)) (1,0)).app V ≪≫
        eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj V)
          (show (0,-(j:ℤ))+(1,0)=(1,1)+(0,-(j:ℤ)-1) by ext <;> simp)) ≪≫
        (SyntheticCategory.biShift_comp (1,1) (0,-(j:ℤ)-1)).symm.app V ≪≫
        (SyntheticCategory.biShift (0,-(j:ℤ)-1)).mapIso (D.nu.suspensionIso _).symm
    have h := negative_shift_nu_to_quotient_zero D synthetic (.shift 1 X) Y j hj m w
      (c ≫ ε.hom) (ε.inv ≫ z)
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h

  have selected_delta_evaluation_eq_cofiber
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject)
      (i j : ℕ)
      (T : LambdaRhoDeltaTriangle (D.nu.functor.obj (X.obj D.hopfAndDetector)) i j)
      (m w : ℤ)
      (a : BiHom m w (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) i)) :
      a ≫ T.delta = a ≫ XModLambdaN.proj (D.nu.functor.obj (X.obj D.hopfAndDetector)) i ≫
        (shiftFunctor Syn (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(i:ℤ))).map
            (XModLambdaN.incl (D.nu.functor.obj (X.obj D.hopfAndDetector)) (j-i))) := by
    let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
    let base := XModLambdaN.cofiberTriangle A i
    obtain ⟨c,hc,hδ⟩ := complete_distinguished_triangle_morphism
      base (Triangle.mk T.lambdaMap T.rho T.delta)
      (XModLambdaN.cofiberTriangle_distinguished A i) T.distinguished
      ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i)))
      (XModLambdaN.incl A j) T.lambda_quotient.symm
    change XModLambdaN A i ⟶ XModLambdaN A i at c
    change XModLambdaN.incl A i ≫ c = XModLambdaN.incl A j ≫ T.rho at hc
    have hc' : XModLambdaN.incl A i ≫ c = XModLambdaN.incl A i ≫ 𝟙 _ := by
      rw [hc,T.rho_quotient,Category.comp_id]
    have hac : a ≫ c = a := by
      simpa only [Category.comp_id] using
        quotient_nu_maps_equal_on_spheres D synthetic X X i T.i_pos c (𝟙 _) hc' m w a
    change XModLambdaN.proj A i ≫ (shiftFunctor Syn (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) =
      c ≫ T.delta at hδ
    calc
      a ≫ T.delta = (a ≫ c) ≫ T.delta := by rw [hac]
      _ = a ≫ XModLambdaN.proj A i ≫ (shiftFunctor Syn (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) := by
        rw [Category.assoc,←hδ]

  have selected_delta_cross_index_of_inclusion_square
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D) (X : ClassicalObject)
      (i k j : ℕ) (hi : 0 < i) (hik : i ≤ k) (hkj : k < j)
      (v : (SyntheticCategory.biShift (0,-(k:ℤ))).obj
          (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) (j-k)) ⟶
        (SyntheticCategory.biShift (0,-(i:ℤ))).obj
          (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) (j-i)))
      (hv : (SyntheticCategory.biShift (0,-(k:ℤ))).map
          (XModLambdaN.incl (D.nu.functor.obj (X.obj D.hopfAndDetector)) (j-k)) ≫ v =
        lambdaRestrictionSourceMap i k hik (D.nu.functor.obj (X.obj D.hopfAndDetector)) ≫
          (SyntheticCategory.biShift (0,-(i:ℤ))).map
            (XModLambdaN.incl (D.nu.functor.obj (X.obj D.hopfAndDetector)) (j-i)))
      (m w : ℤ)
      (a : BiHom m w (XModLambdaN (D.nu.functor.obj (X.obj D.hopfAndDetector)) k)) :
      (a ≫ (D.quotientTower (D.nu.functor.obj (X.obj D.hopfAndDetector))).rho i k hik) ≫
          ((D.quotientTower (D.nu.functor.obj (X.obj D.hopfAndDetector))).triangle hi
            (show i < j by omega)).delta =
        (a ≫ ((D.quotientTower (D.nu.functor.obj (X.obj D.hopfAndDetector))).triangle
          (show 0 < k by omega) hkj).delta) ≫ (shiftFunctor Syn (1:ℤ)).map v := by
    let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
    rw [selected_delta_evaluation_eq_cofiber D synthetic X i j,
      selected_delta_evaluation_eq_cofiber D synthetic X k j]
    simp only [Category.assoc]
    rw [D.comparisonCompatible.quotient_restriction]
    rw [←Category.assoc (XModLambdaN.restriction D.shiftCoherence A i k hik),
      XModLambdaN.restriction_proj]
    simp only [Category.assoc]
    rw [←Functor.map_comp,←hv,Functor.map_comp]

  have canonical_finite_lambda_transition_exists {X : Syn}
      (Q : FiniteLambdaQuotientTower X) (i k q : ℕ) (hik : i < k) (hdq : k-i < q) :
      ∃ v : (SyntheticCategory.biShift (0,-(k:ℤ))).obj (XModLambdaN X (q-(k-i))) ⟶
          (SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN X q),
        (SyntheticCategory.biShift (0,-(k:ℤ))).map (XModLambdaN.incl X (q-(k-i))) ≫ v =
          lambdaRestrictionSourceMap i k hik.le X ≫
            (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl X q) ∧
        v = (lambdaShiftAddIso (k-i) i k (Nat.sub_add_cancel hik.le)).inv.app
            (XModLambdaN X (q-(k-i))) ≫
          (SyntheticCategory.biShift (0,-(i:ℤ))).map
            (Q.triangle (by omega : 0 < k-i) hdq).lambdaMap := by
    let l := (Q.triangle (by omega : 0 < k-i) hdq).lambdaMap
    have hl : (SyntheticCategory.biShift (0,-((k-i:ℕ):ℤ))).map
        (XModLambdaN.incl X (q-(k-i))) ≫ l = lambdaPow (k-i) X ≫ XModLambdaN.incl X q :=
      (Q.triangle (by omega : 0 < k-i) hdq).lambda_quotient
    refine ⟨(lambdaShiftAddIso (k-i) i k (Nat.sub_add_cancel hik.le)).inv.app
        (XModLambdaN X (q-(k-i))) ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map l,?_,rfl⟩
    rw [←Category.assoc,NatTrans.naturality,Category.assoc]
    change (lambdaShiftAddIso (k-i) i k (Nat.sub_add_cancel hik.le)).inv.app X ≫
        (SyntheticCategory.biShift (0,-(i:ℤ))).map
          ((SyntheticCategory.biShift (0,-((k-i:ℕ):ℤ))).map (XModLambdaN.incl X (q-(k-i)))) ≫
            (SyntheticCategory.biShift (0,-(i:ℤ))).map l = _
    rw [←Functor.map_comp,hl,Functor.map_comp]
    simp only [lambdaRestrictionSourceMap,KIP126.Synthetic.Context.lambdaDegree,Category.assoc]

  have sphere_cross_index_normalized
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D)
      (i k : ℕ) (hi : 0 < i) (hik : i < k) :
      ∃ v : (SyntheticCategory.biShift (0,-(k:ℤ))).obj
          (XModLambdaN (D.nu.functor.obj SphereSpectrum) 1) ⟶
        (SyntheticCategory.biShift (0,-(i:ℤ))).obj
          (XModLambdaN (D.nu.functor.obj SphereSpectrum) (k+1-i)),
        (SyntheticCategory.biShift (0,-(k:ℤ))).map (XModLambdaN.incl _ 1) ≫ v =
          lambdaRestrictionSourceMap i k hik.le _ ≫
            (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl _ (k+1-i)) ∧
        ∀ (m w : ℤ) (a : BiHom m w (XModLambdaN (D.nu.functor.obj SphereSpectrum) k)),
          (a ≫ (D.quotientTower _).rho i k hik.le) ≫
            ((D.quotientTower _).triangle hi (show i < k+1 by omega)).delta =
          (a ≫ (by simpa only [show k.succ-k=1 by omega] using
            ((D.quotientTower _).triangle (show 0 < k by omega) (Nat.lt_succ_self k)).delta)) ≫
            (shiftFunctor Syn (1:ℤ)).map v := by
    let A := D.nu.functor.obj SphereSpectrum
    let F := SyntheticCategory.biShift (Syn:=Syn) (0,-(k:ℤ))
    have hv_exists : ∃ v : F.obj (XModLambdaN A 1) ⟶
        (SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A (k+1-i)),
        F.map (XModLambdaN.incl A 1) ≫ v =
          lambdaRestrictionSourceMap i k hik.le A ≫
            (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (k+1-i)) := by
      have raw : ∃ v : F.obj (XModLambdaN A ((k+1-i)-(k-i))) ⟶
          (SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A (k+1-i)),
          F.map (XModLambdaN.incl A ((k+1-i)-(k-i))) ≫ v =
            lambdaRestrictionSourceMap i k hik.le A ≫
              (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (k+1-i)) := by
        obtain ⟨v,hv,_⟩ := canonical_finite_lambda_transition_exists
          (D.quotientTower A) i k (k+1-i) hik (by omega)
        exact ⟨v,hv⟩
      exact (congrArg (fun n => ∃ v : F.obj (XModLambdaN A n) ⟶
          (SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A (k+1-i)),
          F.map (XModLambdaN.incl A n) ≫ v =
            lambdaRestrictionSourceMap i k hik.le A ≫
              (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (k+1-i)))
        (show (k+1-i)-(k-i)=1 by omega)).mp raw
    obtain ⟨v,hv⟩ := hv_exists
    have hn : k.succ-k=1 := by omega
    let c : XModLambdaN A (k+1-k) ⟶ XModLambdaN A 1 :=
      eqToHom (congrArg (fun n => XModLambdaN A n) hn)
    have incl_cast (n n' : ℕ) (h : n=n') :
        XModLambdaN.incl A n ≫ eqToHom (congrArg (fun n => XModLambdaN A n) h) =
          XModLambdaN.incl A n' := by
      subst n'
      simp only [eqToHom_refl,Category.comp_id]
    have hvraw : F.map (XModLambdaN.incl A (k+1-k)) ≫ (F.map c ≫ v) =
        lambdaRestrictionSourceMap i k hik.le A ≫
          (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (k+1-i)) := by
      rw [←Category.assoc,←Functor.map_comp]
      dsimp only [c]
      rw [incl_cast (k+1-k) 1 hn]
      exact hv
    have cast_delta (Q : ℕ → Syn) (F G : Syn ⥤ Syn) (B : Syn)
        (n n' : ℕ) (h : n=n') (δ : B ⟶ G.obj (F.obj (Q n)))
        (ht : (B ⟶ G.obj (F.obj (Q n))) = (B ⟶ G.obj (F.obj (Q n')))) :
        δ ≫ G.map (F.map (eqToHom (congrArg Q h))) = ht.mp δ := by
      subst n'
      simp only [eqToHom_refl,CategoryTheory.Functor.map_id,Category.comp_id]
      rfl
    refine ⟨v,hv,?_⟩
    intro m w a
    have hc := selected_delta_cross_index_of_inclusion_square D synthetic .sphere
      i k (k+1) hi hik.le (Nat.lt_succ_self k) (F.map c ≫ v) hvraw m w a
    have hδ : ((D.quotientTower A).triangle (show 0 < k by omega) (Nat.lt_succ_self k)).delta ≫
          (shiftFunctor Syn (1:ℤ)).map (F.map c) =
        (by simpa only [show k.succ-k=1 by omega] using
          ((D.quotientTower A).triangle (show 0 < k by omega) (Nat.lt_succ_self k)).delta) := by
      exact cast_delta (fun n => XModLambdaN A n) F (shiftFunctor Syn (1:ℤ)) (XModLambdaN A k)
        (k+1-k) 1 hn _ _
    refine hc.trans ?_
    rw [Functor.map_comp]
    have h := congrArg (fun z => (a ≫ z) ≫ (shiftFunctor Syn (1:ℤ)).map v) hδ
    simpa only [Category.assoc,A,ClassicalObject.obj] using h

  have sphere_boundary_of_normalized_cross
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D)
      (i k : ℕ) (hi : 0 < i) (hik : i < k) (s t : ℤ)
      (x : E2 H SphereSpectrum s t)
      (y : E2 H SphereSpectrum (s+k+1) (t+k))
      (hd : HasDifferential (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
        (k+1) (s,t) (s+k+1,t+k) x y)
      (hy : y ∈ permanentCycles H SphereSpectrum (s+k+1,t+k))
      (v : (SyntheticCategory.biShift (0,-(k:ℤ))).obj
        (XModLambdaN (D.nu.functor.obj SphereSpectrum) 1) ⟶
        (SyntheticCategory.biShift (0,-(i:ℤ))).obj
          (XModLambdaN (D.nu.functor.obj SphereSpectrum) (k+1-i)))
      (hv : (SyntheticCategory.biShift (0,-(k:ℤ))).map (XModLambdaN.incl _ 1) ≫ v =
        lambdaRestrictionSourceMap i k hik.le _ ≫
          (SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl _ (k+1-i)))
      (hc : ∀ (a : BiHom (t-s) t (XModLambdaN (D.nu.functor.obj SphereSpectrum) k)),
        (a ≫ (D.quotientTower _).rho i k hik.le) ≫
          ((D.quotientTower _).triangle hi (show i < k+1 by omega)).delta =
        (a ≫ (by simpa only [show k.succ-k=1 by omega] using
          ((D.quotientTower _).triangle (show 0 < k by omega) (Nat.lt_succ_self k)).delta)) ≫
          (shiftFunctor Syn (1:ℤ)).map v) :
      ∃ a : BiHom (t-s) t (XModLambdaN (D.nu.functor.obj SphereSpectrum) i),
        a ≫ (D.quotientTower _).rho 1 i hi =
          firstLabel D .sphere s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
        Detects (D.convergence (.quotient (k+1-i) (.nu .sphere)))
          (s+k+1,t+k,t+k-(k-i:ℕ))
          (finiteTargetLabel D .sphere (k+1-i) (s+k+1) (t+k) (k-i) y)
          (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
            (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN (D.nu.functor.obj SphereSpectrum) (k+1-i))
              (a ≫ ((D.quotientTower _).triangle hi (show i < k+1 by omega)).delta))) := by
    let A := D.nu.functor.obj SphereSpectrum
    let δ : XModLambdaN A k ⟶
        ((SyntheticCategory.biShift (0,-(k:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
      simpa only [show k.succ-k=1 by omega] using
        ((D.quotientTower A).triangle (show 0 < k by omega) (Nat.lt_succ_self k)).delta
    obtain ⟨ak,α,ha,hα,hδ,hfirst⟩ := adjacent_sphere_representative_and_target_lift
      D synthetic i k hi hik.le s t x y hd hy
    let α' : BiHom ((t-s)-1) (t+k) A := homotopyRegrade (by omega) rfl α
    have regrade_comp {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
        {A B : Syn} (a : BiHom m w A) (f : A ⟶ B) :
        homotopyRegrade hm hw (a≫f) = homotopyRegrade hm hw a ≫ f := by
      subst m'; subst w'; rfl
    have regrade_compose {m m' m'' w w' w'' : ℤ}
        (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
        {B : Syn} (b : BiHom m w B) :
        homotopyRegrade hm' hw' (homotopyRegrade hm hw b) =
          homotopyRegrade (hm.trans hm') (hw.trans hw') b := by
      subst m'; subst w'; subst m''; subst w''; rfl
    have undo_regrade {n n' w : ℤ} (hn : n=n') {B C : Syn}
        (a : BiHom n w B) (b : BiHom n' w C) (f : C ⟶ B)
        (h : homotopyRegrade hn rfl a = b ≫ f) :
        a = homotopyRegrade hn.symm rfl b ≫ f := by
      subst n'
      exact h
    have hδ' : biSuspensionHomEquiv (t-s) t (k:ℤ) (XModLambdaN A 1) (ak≫δ) =
        α' ≫ XModLambdaN.incl A 1 := by
      exact undo_regrade (by omega) _ α (XModLambdaN.incl A 1) hδ
    have hδactual : ak≫δ =
        (biSuspensionHomEquiv (t-s) t (k:ℤ) A).symm α' ≫
          (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-(k:ℤ))).map
            (XModLambdaN.incl A 1)) := by
      apply (biSuspensionHomEquiv (t-s) t (k:ℤ) (XModLambdaN A 1)).injective
      rw [hδ',bi_susp_natural D.shiftCoherence,AddEquiv.apply_symm_apply]
    have heval : biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A (k+1-i))
        ((ak ≫ (D.quotientTower A).rho i k hik.le) ≫
          ((D.quotientTower A).triangle hi (show i < k+1 by omega)).delta) =
        homotopyRegrade rfl (by omega)
          (lambdaMultiply (k-i) α' ≫ XModLambdaN.incl A (k+1-i)) := by
      rw [hc,hδactual,Category.assoc,←Functor.map_comp,hv]
      exact lambda_transition_evaluation D.shiftCoherence i k hik.le (k+1-i) (t-s) t A α'
    refine ⟨ak ≫ (D.quotientTower A).rho i k hik.le,hfirst,?_⟩
    rw [heval]
    have hcal := sphere_finite_lambda_detects D (k+1-i) (by omega)
      (s+k+1) (t+k) (k-i) y α hα
    have cancel_lambda_regrade {n n' w w' : ℤ} (hn : n=n') (d : ℕ)
        (hw : w-(d:ℤ)=w') {B C : Syn} (a : BiHom n w B) (f : B ⟶ C) :
        homotopyRegrade hn.symm hw.symm
          (homotopyRegrade rfl hw
            (lambdaMultiply d (homotopyRegrade hn rfl a) ≫ f)) =
          lambdaMultiply d a ≫ f := by
      subst n'
      subst w'
      rfl
    have hlast := cancel_lambda_regrade
      (show (t+k)-(s+k+1)=(t-s)-1 by omega) (k-i)
      (show (t+k)-(k-i:ℕ)=t+i by omega) α (XModLambdaN.incl A (k+1-i))
    exact (congrArg (Detects (D.convergence (.quotient (k+1-i) (.nu .sphere)))
      (s+k+1,t+k,t+k-(k-i:ℕ))
      (finiteTargetLabel D .sphere (k+1-i) (s+k+1) (t+k) (k-i) y)) hlast).mpr hcal

  obtain ⟨v,hv,hc⟩ := sphere_cross_index_normalized D synthetic i k hi hik
  exact sphere_boundary_of_normalized_cross D synthetic i k hi hik s t x y hd hy
    v hv (hc (t-s) t)

open CategoryTheory.Pretriangulated KIP126.SpectralSequence.FinitePageCalculus
  KIP126.Comparison.ClassicalSynthetic in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 6000000 in
private theorem sphere_mahowald_case
    (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q) (s t : ℤ)
    (x : E2 H SphereSpectrum s t)
    (y : E2 H SphereSpectrum (s+i+q) (t+i+q-1))
    (hd : HasDifferential (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
      (i+q) (s,t) (s+i+q,t+i+q-1) x y)
    (hy : y ∈ permanentCycles H SphereSpectrum (s+i+q,t+i+q-1)) :
    let A := D.nu.functor.obj SphereSpectrum
    let δ : XModLambdaN A i ⟶
        ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
      simpa only [Nat.add_sub_cancel_left] using
        ((D.quotientTower A).triangle hi (show i < i+q by omega)).delta
    ∃ a : BiHom (t-s) t (XModLambdaN A i),
      a ≫ (D.quotientTower A).rho 1 i hi =
        firstLabel D .sphere s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
      Detects (D.convergence (.quotient q (.nu .sphere))) (s+i+q,t+i+q-1,t+i)
        (regradeE2 (by exact congrArg (fun w : ℤ => (s+i+q,t+i+q-1,w)) (by omega))
          (finiteTargetLabel D .sphere q (s+i+q) (t+i+q-1) (q-1) y))
        (homotopyRegrade (by dsimp; omega) rfl
          (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A q) (a≫δ))) := by
  have sphere_boundary_nonadjacent_reindexed
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D)
      (i k j q d : ℕ) (hi : 0 < i) (hik : i < k)
      (hj : j=k+1) (hq : j-i=q) (hdexp : d=k-i)
      (s t S T : ℤ) (hS : S=s+k+1) (hT : T=t+k)
      (x : E2 H SphereSpectrum s t) (y : E2 H SphereSpectrum S T)
      (hd : HasDifferential (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
        j (s,t) (S,T) x y)
      (hy : y ∈ permanentCycles H SphereSpectrum (S,T)) :
      let A := D.nu.functor.obj SphereSpectrum
      let δ : XModLambdaN A i ⟶
          ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
        simpa only [hq] using
          ((D.quotientTower A).triangle hi (show i < j by omega)).delta
      ∃ a : BiHom (t-s) t (XModLambdaN A i),
        a ≫ (D.quotientTower A).rho 1 i hi =
          firstLabel D .sphere s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
        Detects (D.convergence (.quotient q (.nu .sphere))) (S,T,t+i)
          (regradeE2 (by exact congrArg (fun w : ℤ => (S,T,w)) (by omega)) (finiteTargetLabel D .sphere q S T d y))
          (homotopyRegrade (by dsimp; omega) rfl
            (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A q) (a≫δ))) := by
    subst j
    subst q
    subst d
    subst S
    subst T
    dsimp only
    obtain ⟨a,ha,had⟩ := sphere_boundary_nonadjacent D synthetic i k hi hik s t x y hd hy
    refine ⟨a,ha,?_⟩
    have change_weight {X : SyntheticObject} (S T w w' m bweight : ℤ)
        (hw : w=w') (hm : m=T-S) (hb : bweight=w)
        (z : (D.family.obj (X.obj D.nu D.hopfAndDetector)).E₂ (S,T,w))
        (b : BiHom m bweight (X.obj D.nu D.hopfAndDetector))
        (h : Detects (D.convergence X) (S,T,w) z (homotopyRegrade hm hb b)) :
        Detects (D.convergence X) (S,T,w')
          (regradeE2 (congrArg (fun v => (S,T,v)) hw) z)
          (homotopyRegrade hm (hb.trans hw) b) := by
      subst w'
      simpa only [regradeE2,eqToHom_refl,ModuleCat.id_apply] using h
    exact change_weight (s+k+1) (t+k) (t+k-(k-i:ℕ)) (t+i) ((t-s)-1) (t+i)
      (by omega) (by omega) (by omega) _ _ had

  have sphere_boundary_adjacent_reindexed
      (D : AdamsComparison H M Syn) (synthetic : SyntheticComparisonTheorems D)
      (i : ℕ) (hi : 0 < i) (s t S T : ℤ) (hS : S=s+i+1) (hT : T=t+i)
      (x : E2 H SphereSpectrum s t) (y : E2 H SphereSpectrum S T)
      (hd : HasDifferential (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
        (i+1) (s,t) (S,T) x y) :
      let A := D.nu.functor.obj SphereSpectrum
      let δ : XModLambdaN A i ⟶
          ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
        simpa only [show i.succ-i=1 by omega] using
          ((D.quotientTower A).triangle hi (Nat.lt_succ_self i)).delta
      ∃ a : BiHom (t-s) t (XModLambdaN A i),
        a ≫ (D.quotientTower A).rho 1 i hi =
          firstLabel D .sphere s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
        Detects (D.convergence (.quotient 1 (.nu .sphere))) (S,T,t+i)
          (regradeE2 (by exact congrArg (fun w : ℤ => (S,T,w)) (by omega)) (finiteTargetLabel D .sphere 1 S T 0 y))
          (homotopyRegrade (by dsimp; omega) rfl
            (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A 1) (a≫δ))) := by
    subst S
    subst T
    exact adjacent_mahowald_case D synthetic .sphere i hi s t x y hd

  by_cases hq1 : q=1
  · subst q
    exact sphere_boundary_adjacent_reindexed D synthetic i hi s t
      (s+i+1) (t+i+1-1) (by omega) (by omega) x y hd
  · exact sphere_boundary_nonadjacent_reindexed D synthetic
      i (i+q-1) (i+q) q (q-1) hi (by omega) (by omega) (by omega) (by omega)
      s t (s+i+q) (t+i+q-1) (by omega) (by omega) x y hd hy

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private def NonAdjacentMahowaldBoundary (X : ClassicalObject) : Prop :=
  ∀ (i q : ℕ) (hi : 0 < i) (hq : 1 < q) (s t r u v : ℤ)
    (hr : r = ((i+q:ℕ):ℤ)) (hu : u=s+i+q) (hv : v=t+i+q-1)
    (x : E2 H (X.obj D.hopfAndDetector) s t) (y : E2 H (X.obj D.hopfAndDetector) u v),
    y ∉ boundaries H (X.obj D.hopfAndDetector) q (u,v) →
    KIP126.SpectralSequence.HasDifferential
      (adamsTowerInternalSpectralSequence H.unit (X.obj D.hopfAndDetector)) r
      (s,t) (u,v) x y →
    y ∈ permanentCycles H (X.obj D.hopfAndDetector) (u,v) →
    let A := D.nu.functor.obj (X.obj D.hopfAndDetector)
    let δ : XModLambdaN A i ⟶
        ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A q))⟦(1:ℤ)⟧ := by
      simpa only [Nat.add_sub_cancel_left] using
        ((D.quotientTower A).triangle hi (show i < i+q by omega)).delta
    ∃ a : BiHom (t-s) t (XModLambdaN A i),
      a ≫ (D.quotientTower A).rho 1 i hi =
        firstLabel D X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app A) 1 ∧
      Detects (D.convergence (.quotient q (.nu X))) (u,v,t+i)
        (regradeE2 (by exact congrArg (fun w : ℤ => (u,v,w)) (by omega))
          (finiteTargetLabel D X q u v (q-1) y))
        (homotopyRegrade (by dsimp; omega) rfl
          (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN A q) (a≫δ)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The nonadjacent boundary comparison in the full Theorem 6.12 proof.
The sphere case is established. MH1 is the original remaining comparison
for a nonzero target on another spectrum; it is not a background axiom. -/
private theorem nonAdjacentMahowaldBoundary (synthetic : SyntheticComparisonTheorems D)
    (X : ClassicalObject) : NonAdjacentMahowaldBoundary D X := by
  intro i q hi hq s t r u v hr hu hv x' y' hnot hdy hperm
  subst r
  subst u
  subst v
  by_cases hX : X = .sphere
  · subst X
    exact sphere_mahowald_case D synthetic i q hi (by omega) s t x' y' hdy hperm
  · -- MH1: the remaining nonzero comparison is for X other than the sphere.
    sorry

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- MainPaper Theorem 6.12. May's signed smash-boundary input supplies
Lemma 6.11's geometric step; the compatible normalized triangle and both
no-crossing alternatives remain explicit in the conclusion's predicate. -/
private theorem generalizedMahowaldAt (synthetic : SyntheticComparisonTheorems D) (may : MayBoundaryFormula Syn)
    (T : ClassicalCofiberTriangle D.hopfAndDetector) (m : ℤ)
    (nonadjacent : m ≠ (normalizedExponent H T.g : ℤ) →
      NonAdjacentMahowaldBoundary D T.Z) :
    KIP126.AdamsSynthetic.ExtensionLaws.GeneralizedMahowaldLawAt D T m := by
  intro he htriangle n l s t
  dsimp only
  intro x y xBar yBar suspendedX hn hm hl
    hx hy hxBar hyBar hsusp hh hd hcross hg
  let eg : ℤ := normalizedExponent H T.g
  let ef : ℤ := normalizedExponent H T.f
  let eh : ℤ := normalizedExponent H T.h
  let pg : ℕ := (m-eg+2).toNat
  let q : ℕ := pg-1
  let i : ℕ := (n+l+eg-1).toNat
  let Q : ℕ := (n+m+eh).toNat
  let sf : ℤ := s+l
  let tf : ℤ := t+l-1
  have hpg : 2 ≤ pg := by dsimp [pg,eg]; omega
  have hq : 0 < q := by dsimp [q]; omega
  have hqZ : (q:ℤ)=m-eg+1 := by dsimp [q,pg]; omega
  have hi : 0 < i := by dsimp [i,eg,ef,eh] at *; omega
  have hiZ : (i:ℤ)=n+l+eg-1 := by dsimp [i,eg,ef,eh] at *; omega
  have hQ : 0 < Q := by dsimp [Q,eg,ef,eh] at *; omega
  have hQZ : (Q:ℤ)=n+m+eh := by dsimp [Q,eg,ef,eh] at *; omega
  have hn0 : 0 ≤ n := by have := Nat.zero_le (normalizedExponent H T.f); omega
  have hnf : ef ≤ n := by dsimp [ef]; omega
  let Wg : FiniteExtensionWitness D T.Y T.Z T.g pg m (sf+n) (tf+n) y yBar :=
    Classical.choice hg
  let Zν := D.nu.functor.obj (T.Z.obj D.hopfAndDetector)
  let boundary (aZ : BiHom (t-s) t (XModLambdaN Zν i)) :
      BiHom ((tf+n)-(sf+n)) (tf+n+eg) (XModLambdaN Zν q) :=
    homotopyRegrade (by dsimp [tf,sf]; omega) (by dsimp [tf]; omega)
      (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN Zν q)
        (by simpa only [Nat.add_sub_cancel_left] using
          (aZ ≫ ((D.quotientTower Zν).triangle hi (show i < i + q by omega)).delta)))
  have boundary_representative :
      ∃ aZ : BiHom (t-s) t (XModLambdaN Zν i),
        Detects (D.convergence (.quotient i (.nu T.Z))) (s,t,t)
          (regradeE2 (by simp) (finiteTargetLabel D T.Z i s t 0 xBar)) aZ ∧
        Detects (D.convergence (.quotient q (.nu T.Z)))
          (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg)
          (finiteTargetForExtension D T.Y T.Z T.g q m (sf+n) (tf+n) Wg.length_lower yBar)
          (homotopyRegrade (by dsimp; omega) rfl (boundary aZ)) := by
    have hmi : eg ≤ m := by dsimp [eg]; omega
    have hxi : xBar ∈ cycles H (T.Z.obj D.hopfAndDetector) (i:ℤ) (s,t) :=
      cycles_antitone H (T.Z.obj D.hopfAndDetector) (s,t) (by omega : (i:ℤ) ≤ n+m+l-1) hxBar.2
    obtain ⟨a0Zero,ha0Zero⟩ := (synthetic.finite_lift T.Z i hi s t xBar).mp hxi
    let a0 : BiHom (t-s) t (XModLambdaN Zν i) :=
      a0Zero ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app Zν) i
    have ha0first : a0 ≫ (D.quotientTower Zν).rho 1 i hi =
        firstLabel D T.Z s t xBar ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app Zν) 1 := by
      dsimp only [a0]
      have hnat : (D.quotientTower (nuZero D T.Z)).rho 1 i hi ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app Zν) 1 =
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app Zν) i ≫
            (D.quotientTower Zν).rho 1 i hi :=
        (D.comparisonCompatible.quotient_naturality
          (SyntheticCategory.biShift_zero.hom.app Zν)).rho_naturality hi
      rw [Category.assoc,←hnat,←Category.assoc,ha0Zero]
    have target_correction :
        ∃ c : BiHom (t-s) t (XModLambdaN Zν i),
          c ≫ (D.quotientTower Zν).rho 1 i hi = 0 ∧
          Detects (D.convergence (.quotient q (.nu T.Z)))
            (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg)
            (finiteTargetForExtension D T.Y T.Z T.g q m (sf+n) (tf+n) Wg.length_lower yBar)
            (homotopyRegrade (by dsimp; omega) rfl (boundary (a0+c))) := by
      by_cases hyB : yBar ∈ boundaries H (T.Z.obj D.hopfAndDetector) (q:ℤ) (sf+n+m,tf+n+m)
      · have boundary_target_zero (r : ℤ) (p : ℤ×ℤ) (hr : 2 ≤ r)
            (hqr : (q:ℤ) ≤ r-1)
            (z : E2 H (T.Z.obj D.hopfAndDetector) p.1 p.2)
            (hz : z ∈ boundaries H (T.Z.obj D.hopfAndDetector) q p)
            (hdz : KIP126.SpectralSequence.HasDifferential
              (adamsTowerInternalSpectralSequence H.unit (T.Z.obj D.hopfAndDetector)) r
              (s,t) p xBar z) : KIP126.SpectralSequence.HasDifferential
              (adamsTowerInternalSpectralSequence H.unit (T.Z.obj D.hopfAndDetector)) r
              (s,t) p xBar 0 := by
          let E := adamsTowerInternalSpectralSequence H.unit (T.Z.obj D.hopfAndDetector)
          have hz' : z ∈ boundaries H (T.Z.obj D.hopfAndDetector) (r-1) p :=
            boundaries_monotone H (T.Z.obj D.hopfAndDetector) p hqr hz
          have hzrep : KIP126.SpectralSequence.RepresentsOnPage E r p z 0 := by
            let P := E.ssData p
            let j : WithTop ℕ := ↑(r-2).toNat
            change ∃ b, boundaryMap H (T.Z.obj D.hopfAndDetector) ↑(r-1-1).toNat p b=z at hz'
            rw [show r-1-1=r-2 by omega] at hz'
            obtain ⟨b,hb⟩ := hz'
            let incl := Subobject.ofLE (P.B j) (P.Z j) (P.B_le_Z j)
            refine ⟨hr,incl b,?_,?_⟩
            · change cycleMap H (T.Z.obj D.hopfAndDetector) j p (incl b)=z
              have hincl : incl ≫ cycleMap H (T.Z.obj D.hopfAndDetector) j p =
                  boundaryMap H (T.Z.obj D.hopfAndDetector) j p := by
                dsimp only [incl,cycleMap,boundaryMap,P,E]
                rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
              rw [←ModuleCat.comp_apply,hincl]
              exact hb
            · change (incl ≫ P.pageπ j) b=0
              simp only [incl,SSData.pageπ,cokernel.condition]
              rfl
          obtain ⟨hdeg,xr,zr,hxr,hzr,hdiff⟩ := hdz
          have hzr0 : zr=0 := KIP126.SpectralSequence.FinitePageCalculus.represents_unique hzr hzrep
          exact ⟨hdeg,xr,0,hxr,KIP126.SpectralSequence.RepresentsOnPage.zero hr,hzr0 ▸ hdiff⟩
        have hd0 : KIP126.SpectralSequence.HasDifferential
            (adamsTowerInternalSpectralSequence H.unit (T.Z.obj D.hopfAndDetector)) (i+q)
            (s,t) (s+i+q,t+i+q-1) xBar 0 := by
          have reindex (r r' : ℤ) (hr : r=r') (p p' : ℤ×ℤ) (hp : p=p')
              (h : KIP126.SpectralSequence.HasDifferential
                (adamsTowerInternalSpectralSequence H.unit (T.Z.obj D.hopfAndDetector)) r
                (s,t) p xBar 0) : KIP126.SpectralSequence.HasDifferential
                (adamsTowerInternalSpectralSequence H.unit (T.Z.obj D.hopfAndDetector)) r'
                (s,t) p' xBar 0 := by
            subst r'; subst p'; exact h
          have hd' := boundary_target_zero (n+m+l) (sf+n+m,tf+n+m)
            hd.1 (by omega) yBar hyB hd.2
          exact reindex _ _ (by omega) _ _ (by ext <;> dsimp [sf,tf] <;> omega) hd'
        have finite_top_boundary_detects_zero (s0 t0 : ℤ)
            (z : E2 H (T.Z.obj D.hopfAndDetector) s0 t0)
            (hz : z ∈ boundaries H (T.Z.obj D.hopfAndDetector) q (s0,t0)) :
            Detects (D.convergence (.quotient q (.nu T.Z))) (s0,t0,t0-(q-1:ℕ))
              (finiteTargetLabel D T.Z q s0 t0 (q-1) z) 0 := by
          let zc : cycles H (T.Z.obj D.hopfAndDetector) ((q:ℤ)-t0+(t0-(q-1:ℕ))) (s0,t0) :=
            ⟨z,by
              rw [show ((q:ℤ)-t0+(t0-(q-1:ℕ)))=1 by omega,cycles_one]
              trivial⟩
          have he : HasInfinityRepresentative _ 2 _
              (finiteTargetLabel D T.Z q s0 t0 (q-1) z) 0 := by
            apply (synthetic.eInfty.labels.1 T.Z q hq (s0,t0) (q-1) (by omega) zc 0).mpr
            rw [map_zero]
            symm
            apply (KIP126.Algebra.NestedQuotient.projection_eq_zero zc).mpr
            change z ∈ boundaries H (T.Z.obj D.hopfAndDetector) (1+t0-(t0-(q-1:ℕ))) (s0,t0)
            convert hz using 1
            congr 1
            omega
          refine ⟨0,he,0,?_,?_⟩
          · exact map_zero _
          · simp only [map_zero]
        have htarget : Detects (D.convergence (.quotient q (.nu T.Z)))
            (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg)
            (finiteTargetForExtension D T.Y T.Z T.g q m (sf+n) (tf+n) Wg.length_lower yBar) 0 := by
          have transport_zero {p p' : Tridegree} (hp : p=p')
              (z : (D.family.obj (XModLambdaN Zν q)).E₂ p)
              (hz : Detects (D.convergence (.quotient q (.nu T.Z))) p z 0) :
              Detects (D.convergence (.quotient q (.nu T.Z))) p' (regradeE2 hp z) 0 := by
            subst p'
            exact hz
          have label_transport (s0 t0 : ℤ) (z : E2 H (T.Z.obj D.hopfAndDetector) s0 t0)
              (k k' : ℕ) (hk : k=k') (p : Tridegree)
              (hp : (s0,t0,t0-k)=p) (hp' : (s0,t0,t0-k')=p) :
              regradeE2 hp (finiteTargetLabel D T.Z q s0 t0 k z) =
                regradeE2 hp' (finiteTargetLabel D T.Z q s0 t0 k' z) := by
            subst k'
            rfl
          unfold finiteTargetForExtension
          convert transport_zero
            (p := (sf+n+m,tf+n+m,(tf+n+m)-(q-1:ℕ)))
            (p' := (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg))
            (by ext <;> dsimp <;> omega) _ (finite_top_boundary_detects_zero _ _ yBar hyB) using 1
          exact label_transport _ _ yBar _ (q-1) (by dsimp [eg] at hqZ hmi; omega) _ _ _
        obtain ⟨a,hafirst,hazero⟩ := zero_target_actual_lift D synthetic T.Z i q hi hq s t xBar hd0
        refine ⟨a-a0,?_,?_⟩
        · rw [Preadditive.sub_comp,hafirst,ha0first,sub_self]
        · have hsum : a0+(a-a0)=a := by abel
          rw [hsum]
          have regrade_zero {u u' v v' : ℤ} {A : Syn} (hu : u=u') (hv : v=v') :
              homotopyRegrade hu hv (0 : BiHom u v A)=0 := by
            subst u'; subst v'; rfl
          have hboundary : boundary a=0 := by
            have hom_cast_zero {U V V' : Syn} (h : V=V') (he : (U ⟶ V)=(U ⟶ V')) :
                he.mp (0 : U ⟶ V)=0 := by
              subst V'
              rfl
            dsimp only [boundary]
            rw [hazero]
            rw [hom_cast_zero (congrArg (fun j =>
              ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN Zν j))⟦(1:ℤ)⟧)
              (Nat.add_sub_cancel_left i q))]
            rw [map_zero,regrade_zero]
          rw [hboundary,regrade_zero]
          exact htarget
      ·
        by_cases hq1 : q=1
        · have hm_eq : (normalizedExponent H T.g : ℤ)=m := by dsimp [eg] at hqZ; omega
          have adjacent_reindexed (r u v : ℤ)
              (hr : r=(i:ℤ)+1) (hu : u=s+i+1) (hv : v=t+i)
              (y' : E2 H (T.Z.obj D.hopfAndDetector) u v)
              (hdy : KIP126.SpectralSequence.HasDifferential
                (adamsTowerInternalSpectralSequence H.unit (T.Z.obj D.hopfAndDetector))
                r (s,t) (u,v) xBar y') :
              let δ : XModLambdaN Zν i ⟶
                  ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN Zν 1))⟦(1:ℤ)⟧ := by
                simpa only [show i.succ-i=1 by omega] using
                  ((D.quotientTower Zν).triangle hi (Nat.lt_succ_self i)).delta
              ∃ a : BiHom (t-s) t (XModLambdaN Zν i),
                a ≫ (D.quotientTower Zν).rho 1 i hi =
                  firstLabel D T.Z s t xBar ≫
                    XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app Zν) 1 ∧
                Detects (D.convergence (.quotient 1 (.nu T.Z))) (u,v,v)
                  (regradeE2 (by simp) (finiteTargetLabel D T.Z 1 u v 0 y'))
                  (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
                    (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN Zν 1) (a≫δ))) := by
            subst r
            subst u
            subst v
            exact adjacent_mahowald_case D synthetic T.Z i hi s t xBar y' hdy
          obtain ⟨a,ha,hda⟩ := adjacent_reindexed (n+m+l) (sf+n+m) (tf+n+m)
            (by dsimp [eg] at hiZ; omega) (by dsimp [sf]; dsimp [eg] at hiZ; omega)
            (by dsimp [tf]; dsimp [eg] at hiZ; omega) yBar hd.2
          have finite_target_detects_of_exponent_eq (D : AdamsComparison H M Syn)
              (Y Z : ClassicalObject) (g : Y.obj D.hopfAndDetector ⟶ Z.obj D.hopfAndDetector)
              (m s0 t0 : ℤ) (hm : (normalizedExponent H g : ℤ) ≤ m)
              (he : (normalizedExponent H g : ℤ) = m)
              (y : E2 H (Z.obj D.hopfAndDetector) (s0+m) (t0+m))
              (a : BiHom ((t0+m)-(s0+m)) (t0+m)
                (XModLambdaN (D.nu.functor.obj (Z.obj D.hopfAndDetector)) 1))
              (ha : Detects (D.convergence (.quotient 1 (.nu Z))) (s0+m,t0+m,t0+m)
                (regradeE2 (by simp) (finiteTargetLabel D Z 1 (s0+m) (t0+m) 0 y)) a) :
              Detects (D.convergence (.quotient 1 (.nu Z)))
                (s0+m,(t0-s0)+(s0+m),t0+normalizedExponent H g)
                (finiteTargetForExtension D Y Z g 1 m s0 t0 hm y)
                (homotopyRegrade (by dsimp; omega) (by dsimp; omega) a) := by
            have transport {i j : Tridegree} (h : i=j)
                (x : (D.family.obj (XModLambdaN (D.nu.functor.obj (Z.obj D.hopfAndDetector)) 1)).E₂ i)
                (b : BiHom (i.2.1-i.1) i.2.2
                  (XModLambdaN (D.nu.functor.obj (Z.obj D.hopfAndDetector)) 1))
                (hb : Detects (D.convergence (.quotient 1 (.nu Z))) i x b) :
                Detects (D.convergence (.quotient 1 (.nu Z))) j (regradeE2 h x)
                  (homotopyRegrade (congrArg (fun k : Tridegree => k.2.1-k.1) h)
                    (congrArg (fun k : Tridegree => k.2.2) h) b) := by
              subst j
              exact hb
            have label_transport (s t : ℤ) (z : E2 H (Z.obj D.hopfAndDetector) s t)
                (k k' : ℕ) (hk : k=k') (i j : Tridegree)
                (h : (s,t,t-k)=j) (h0 : (s,t,t-k')=i) (h1 : i=j) :
                regradeE2 h (finiteTargetLabel D Z 1 s t k z) =
                  regradeE2 h1 (regradeE2 h0 (finiteTargetLabel D Z 1 s t k' z)) := by
              subst k'
              subst i
              subst j
              rfl
            subst m
            unfold finiteTargetForExtension
            convert transport
              (i := (s0+normalizedExponent H g,t0+normalizedExponent H g,t0+normalizedExponent H g))
              (j := (s0+normalizedExponent H g,(t0-s0)+(s0+normalizedExponent H g),
                t0+normalizedExponent H g))
              (by ext <;> dsimp; omega) _ _ ha using 1
            exact label_transport _ _ y _ 0 (by simp) _ _ _ _ _
          have htarget := finite_target_detects_of_exponent_eq D T.Y T.Z T.g
            m (sf+n) (tf+n) Wg.length_lower hm_eq yBar _ hda
          refine ⟨a-a0,?_,?_⟩
          · rw [Preadditive.sub_comp,ha,ha0first,sub_self]
          · have haa : a0+(a-a0)=a := by abel
            rw [haa]
            have transport_q (j : ℕ) (hj : 0<j) (hj1 : j=1)
                (hb : Detects (D.convergence (.quotient 1 (.nu T.Z)))
                  (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg)
                  (finiteTargetForExtension D T.Y T.Z T.g 1 m (sf+n) (tf+n) Wg.length_lower yBar)
                  (homotopyRegrade
                    (show (tf+n+m)-(sf+n+m)=((tf+n)-(sf+n))+(sf+n+m)-(sf+n+m) by omega)
                    (show tf+n+m=tf+n+eg by dsimp [eg]; omega)
                    (homotopyRegrade
                      (show (t-s)-1=(tf+n+m)-(sf+n+m) by dsimp [sf,tf]; omega)
                      (show t+(i:ℤ)=tf+n+m by dsimp [tf]; dsimp [eg] at hiZ; omega)
                      (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN Zν 1)
                        (a ≫ (by simpa only [show i.succ-i=1 by omega] using
                          ((D.quotientTower Zν).triangle hi (Nat.lt_succ_self i)).delta)))))) :
                Detects (D.convergence (.quotient j (.nu T.Z)))
                  (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg)
                  (finiteTargetForExtension D T.Y T.Z T.g j m (sf+n) (tf+n) Wg.length_lower yBar)
                  (homotopyRegrade
                    (show (tf+n)-(sf+n)=((tf+n)-(sf+n))+(sf+n+m)-(sf+n+m) by omega) rfl
                    (homotopyRegrade
                      (show (t-s)-1=(tf+n)-(sf+n) by dsimp [sf,tf]; omega)
                      (show t+(i:ℤ)=tf+n+eg by dsimp [tf]; omega)
                      (biSuspensionHomEquiv (t-s) t (i:ℤ) (XModLambdaN Zν j)
                        (by simpa only [Nat.add_sub_cancel_left] using
                          (a ≫ ((D.quotientTower Zν).triangle hi (show i < i+j by omega)).delta))))) := by
              subst j
              convert hb using 1
              have regrade_comp {m w m' w' m'' w'' : ℤ} {B : Syn}
                  (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
                  (b : BiHom m w B) :
                  homotopyRegrade hm' hw' (homotopyRegrade hm hw b) =
                    homotopyRegrade (hm.trans hm') (hw.trans hw') b := by
                subst m'; subst w'; subst m''; subst w''; rfl
              simp only [regrade_comp]
              congr 2
              have cast_comp {S U A B : Syn} (h : A=B)
                  (ha : (S ⟶ A)=(S ⟶ B)) (hf : (U ⟶ A)=(U ⟶ B))
                  (a : S ⟶ U) (f : U ⟶ A) : ha.mp (a≫f)=a≫hf.mp f := by
                subst B
                rfl
              exact cast_comp (congrArg (fun k =>
                ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN Zν k))⟦(1:ℤ)⟧)
                (Nat.add_sub_cancel_left i 1)) _ _ _ _
            exact transport_q q hq hq1 htarget
        · have hqgt : 1<q := by omega
          obtain ⟨a,ha,hda⟩ := (nonadjacent (by
            intro hmzero
            dsimp [eg] at hqZ
            omega)) i q hi hqgt s t (n+m+l) (sf+n+m) (tf+n+m)
              (by omega) (by dsimp [sf]; omega) (by dsimp [tf]; omega)
              xBar yBar hyB hd.2 hyBar
          have transport {p p' : Tridegree} (hp : p=p')
              (z : (D.family.obj (XModLambdaN Zν q)).E₂ p)
              (b : BiHom (p.2.1-p.1) p.2.2 (XModLambdaN Zν q))
              (hb : Detects (D.convergence (.quotient q (.nu T.Z))) p z b) :
              Detects (D.convergence (.quotient q (.nu T.Z))) p' (regradeE2 hp z)
                (homotopyRegrade (congrArg (fun p : Tridegree => p.2.1-p.1) hp)
                  (congrArg (fun p : Tridegree => p.2.2) hp) b) := by
            subst p'
            exact hb
          have label_transport (s0 t0 : ℤ) (z : E2 H (T.Z.obj D.hopfAndDetector) s0 t0)
              (k k' : ℕ) (hk : k=k') (p p' : Tridegree)
              (hp : (s0,t0,t0-k)=p') (h0 : (s0,t0,t0-k')=p) (h1 : p=p') :
              regradeE2 hp (finiteTargetLabel D T.Z q s0 t0 k z) =
                regradeE2 h1 (regradeE2 h0 (finiteTargetLabel D T.Z q s0 t0 k' z)) := by
            subst k'
            subst p
            subst p'
            rfl
          have hdegree : (sf+n+m,tf+n+m,t+(i:ℤ)) =
              (sf+n+m,((tf+n)-(sf+n))+(sf+n+m),tf+n+eg) := by
            ext <;> dsimp only [tf] <;> omega
          have htarget := transport hdegree _ _ hda
          have hlabel : finiteTargetForExtension D T.Y T.Z T.g q m (sf+n) (tf+n) Wg.length_lower yBar =
              regradeE2 hdegree
                (regradeE2 (by exact congrArg (fun w : ℤ => (sf+n+m,tf+n+m,w)) (by omega))
                  (finiteTargetLabel D T.Z q (sf+n+m) (tf+n+m) (q-1) yBar)) := by
            unfold finiteTargetForExtension
            exact label_transport _ _ yBar _ (q-1) (by dsimp [eg] at hqZ hmi; omega) _ _ _ _ _
          rw [←hlabel] at htarget
          refine ⟨a-a0,?_,?_⟩
          · rw [Preadditive.sub_comp,ha,ha0first,sub_self]
          · have haa : a0+(a-a0)=a := by abel
            rw [haa]
            have regrade_comp {m w m' w' m'' w'' : ℤ} {B : Syn}
                (hm : m=m') (hw : w=w') (hm' : m'=m'') (hw' : w'=w'')
                (b : BiHom m w B) :
                homotopyRegrade hm' hw' (homotopyRegrade hm hw b) =
                  homotopyRegrade (hm.trans hm') (hw.trans hw') b := by
              subst m'; subst w'; subst m''; subst w''; rfl
            dsimp only [boundary]
            simp only [regrade_comp] at htarget ⊢
            convert htarget using 1
            congr 2
            have cast_comp {S U A B : Syn} (h : A=B)
                (ha : (S ⟶ A)=(S ⟶ B)) (hf : (U ⟶ A)=(U ⟶ B))
                (a : S ⟶ U) (f : U ⟶ A) : ha.mp (a≫f)=a≫hf.mp f := by
              subst B
              rfl
            exact cast_comp (congrArg (fun k =>
              ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN Zν k))⟦(1:ℤ)⟧)
              (Nat.add_sub_cancel_left i q)) _ _ _ _
    obtain ⟨c,hc,hdelta⟩ := target_correction
    have hfirst : (a0+c) ≫ (D.quotientTower Zν).rho 1 i hi =
        firstLabel D T.Z s t xBar ≫
          XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app Zν) 1 := by
      rw [Preadditive.add_comp,ha0first,hc,add_zero]
    exact ⟨a0+c,first_label_detects_unshifted D synthetic T.Z i hi s t xBar (a0+c) hfirst,hdelta⟩
  obtain ⟨aZ,haZ,hdelta⟩ := boundary_representative
  have may_boundary_lift :
      ∀ ag : BiHom ((tf+n)-(sf+n)) (tf+n+eg)
          ((SyntheticObject.quotient q (extensionSourceObject D T.Y T.Z T.g)).obj D.nu D.hopfAndDetector),
        Detects (D.convergence (.quotient q (extensionSourceObject D T.Y T.Z T.g)))
          (sf+n,((tf+n)-(sf+n))+(sf+n),tf+n+eg)
          (finiteSourceForExtension D T.Y T.Z T.g q (sf+n) (tf+n) y)
          (homotopyRegrade (by dsimp; omega) rfl ag) →
        ag ≫ finiteExtensionMap D T.Y T.Z T.g q = boundary aZ →
        (∃ c : BiHom (tf-sf) tf (XModLambdaN (nuZero D T.X) Q),
          c ≫ (D.quotientTower (nuZero D T.X)).rho 1 Q hQ = firstLabel D T.X sf tf x) ∧
        ∃ y' : E2 H (T.Y.obj D.hopfAndDetector) (sf+n) (tf+n),
          y'-y ∈ boundaries H (T.Y.obj D.hopfAndDetector) (n+m+l-(m-eg)) (sf+n,tf+n) ∧
          ∃ (af : BiHom (tf-sf) (tf+ef)
                ((SyntheticObject.quotient Q (extensionSourceObject D T.X T.Y T.f)).obj D.nu D.hopfAndDetector))
            (bf : BiHom (tf-sf) (tf+ef)
                (XModLambdaN (D.nu.functor.obj (T.Y.obj D.hopfAndDetector)) Q)),
            Detects (D.convergence (.quotient Q (extensionSourceObject D T.X T.Y T.f)))
              (sf,(tf-sf)+sf,tf+ef) (finiteSourceForExtension D T.X T.Y T.f Q sf tf x)
              (homotopyRegrade (by dsimp; omega) rfl af) ∧
            Detects (D.convergence (.quotient Q (.nu T.Y)))
              (sf+n,(tf-sf)+(sf+n),tf+ef) (finiteTargetForExtension D T.X T.Y T.f Q n sf tf hnf y')
              (homotopyRegrade (by dsimp; omega) rfl bf) ∧
            af ≫ finiteExtensionMap D T.X T.Y T.f Q = bf := by
    intro ag hag hstrict
    -- MH2, MainPaper lines 1875–1917: hcross synchronizes the h-extension
    -- with the delta representative aZ; htriangle and may.boundary then
    -- give the actual lift through lambda^Q and the strict f_Q square.
    -- hsusp identifies the ordinary suspension label with x. Transport
    -- through lambda powers must retain the finite B_(n+m+l-(m-e(g)))
    -- ambiguity in y', not merely equality in the infinity quotient.
    -- May supplies a signed homotopy relation; removing its sign requires
    -- the mod-2 label comparison, not an assertion of characteristic two
    -- for the homotopy groups. No FiniteExtension conclusion is assumed here.
    sorry
  obtain ⟨ag,hag,hagDetect⟩ := finite_top_extension_preimage D synthetic
    T.Y T.Z T.g pg m (sf+n) (tf+n) y yBar Wg (by dsimp [pg,eg]; omega)
    (boundary aZ) hdelta
  obtain ⟨⟨c,hc⟩,y',hcong,af,bf,haf,hbf,hfstrict⟩ := may_boundary_lift ag hagDetect hag
  have hxLater : IsCycle H (T.X.obj D.hopfAndDetector) (n+m+eh) (sf,tf) x := by
    refine ⟨by dsimp [ef,eg,eh] at *; omega,?_⟩
    have hc' := (synthetic.finite_lift T.X Q hQ sf tf x).mpr ⟨c,hc⟩
    simpa only [hQZ] using hc'
  have hyLater : IsCycle H (T.Y.obj D.hopfAndDetector)
      (((Q+1:ℕ):ℤ)-1-n+normalizedExponent H T.f) (sf+n,tf+n) y' := by
    have hlevel : ((Q+1:ℕ):ℤ)-1-n+normalizedExponent H T.f = m-eg+1 := by
      simp only [Nat.cast_add,Nat.cast_one,hQZ]
      dsimp [ef,eg,eh] at *
      omega
    rw [hlevel]
    refine ⟨by dsimp [eg]; omega,?_⟩
    have hby := boundaries_le_cycles H (T.Y.obj D.hopfAndDetector) (sf+n,tf+n)
      (n+m+l-(m-eg)) (m-eg+1) hcong
    have hadd := (cycles H (T.Y.obj D.hopfAndDetector) (m-eg+1) (sf+n,tf+n)).add_mem hby hy.2
    simpa only [sub_add_cancel] using hadd
  obtain ⟨xf,yf,hxf,hyf,heq⟩ := extension_equation_of_detected_pair D
    (finiteExtensionMap D T.X T.Y T.f Q) _ _ (tf-sf,tf+ef) sf n hn0 _ _ af bf haf hbf hfstrict
  refine ⟨hxLater,y',?_,⟨by dsimp [ef,eg,eh] at *; omega,hcong⟩⟩
  have hpage : (n+m+1+normalizedExponent H T.h).toNat = Q+1 := by
    dsimp [Q,eh,ef,eg] at *
    omega
  rw [hpage]
  refine ⟨{
    page_ge_two := by omega
    length_lower := hnf
    length_upper := by simp only [Nat.cast_add,Nat.cast_one,hQZ]; dsimp [ef,eg,eh] at *; omega
    source_cycle := by simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,hQZ] using hxLater
    target_cycle := hyLater
    source := xf
    target := yf
    source_rep := hxf
    target_rep := hyf
    equation := heq }⟩

/-- MainPaper Theorem 6.12 with all middle extension lengths. The nonadjacent
comparison remains a separate Section 6 obligation; the shared May lift in
`generalizedMahowaldAt` is also still unfinished. -/
theorem generalizedMahowald (synthetic : SyntheticComparisonTheorems D) (may : MayBoundaryFormula Syn)
    (T : ClassicalCofiberTriangle D.hopfAndDetector) :
    KIP126.AdamsSynthetic.ExtensionLaws.GeneralizedMahowaldLaw D T := by
  intro he htriangle n m l s t
  exact generalizedMahowaldAt D synthetic may T m
    (fun _ => nonAdjacentMahowaldBoundary D synthetic T.Z)
    he htriangle n l s t

/-- The case `m = e(g)` of Theorem 6.12. This uses the proved adjacent
boundary comparison and the shared unfinished May lift, without importing
MH1's nonadjacent comparison. All remaining instance hypotheses are kept. -/
theorem generalizedMahowald_minimal_middle
    (synthetic : SyntheticComparisonTheorems D) (may : MayBoundaryFormula Syn)
    (T : ClassicalCofiberTriangle D.hopfAndDetector) (m : ℤ)
    (hm : m = (normalizedExponent H T.g : ℤ)) :
    KIP126.AdamsSynthetic.ExtensionLaws.GeneralizedMahowaldLawAt D T m := by
  exact generalizedMahowaldAt D synthetic may T m (fun h => False.elim (h hm))

end KIP126.Main.ExtensionLaws
