module
import all KIP126.ProofTools.GeneralizedMahowald.QuotientShift
import all KIP126.ProofTools.GeneralizedMahowald.SphereLabels
import KIP126.AdamsSynthetic
/-! Consume the fixed first-quotient shift comparison at arbitrary finite
quotient length. A detected normalized source is transported to an actual
unshifted representative with the prescribed classical label. The chosen
quotient comparison and strict inverse transport are retained for later
h-extension and no-crossing synchronization. All declarations are private. -/

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
set_option maxHeartbeats 2000000

private theorem shifted_first_detection_unique (X : ClassicalObject) (e s t : ℤ)
    (x : (model.family.obj (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) 1)).E₂ (s,t,t+e))
    (a b : BiHom (t-s) (t+e) (XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) 1))
    (ha : Detects (model.convergence (.quotient 1 (.shift (0,e) (.nu X)))) (s,t,t+e) x a)
    (hb : Detects (model.convergence (.quotient 1 (.shift (0,e) (.nu X)))) (s,t,t+e) x b) : a=b := by
  have hdiff := detects_sub_filtration (model.convergence (.quotient 1 (.shift (0,e) (.nu X))))
    (s,t,t+e) ha hb
  apply sub_eq_zero.mp
  apply synthetic_homotopy_separated (.shift (0,e) (.nu X)) 1 (t-s) (t+e) (a-b)
  intro j
  by_cases hj : s+1 ≤ (j:ℤ)
  · exact (filtration_iff_of_infinity_zero
      (model.convergence (.quotient 1 (.shift (0,e) (.nu X))))
      (s+1) j (t-s) (t+e) hj
      (fun k hk _ => shifted_quotient_eInfty_zero X 1 (by decide) e k (t-s+k) (t+e)
        (by omega)) (a-b)).mp hdiff
  · exact model.syntheticTower.filtrationSubmodule_antitone _ (t-s,t+e) (by omega) hdiff

private theorem shifted_finite_source_first
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (e s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t+e) (XModLambdaN
      ((SyntheticCategory.biShift (0,e)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.shift (0,e) (.nu X)))) (s,t,t+e)
      (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x)) a) :
    a ≫ (model.quotients.tower _).rho 1 q hq = (model.firstQuotient X e s t).symm x := by
  have hrho := detects_map (.quotient q (.shift (0,e) (.nu X)))
    (.quotient 1 (.shift (0,e) (.nu X))) ((model.quotients.tower _).rho 1 q hq)
    (s,t,t+e) _ _ ha
  have hlabel : familyPageMap model.family ((model.quotients.tower
      ((SyntheticCategory.biShift (0,e)).obj (model.nu.functor.obj (X.obj model.auxiliary)))).rho 1 q hq)
      2 (s,t,t+e) (regradeE2 (by simp) (finiteNuLabel model X q e s t 0 x)) =
      regradeE2 (by simp) (finiteNuLabel model X 1 e s t 0 x) := by
    rw [←page_regrade]
    congr 1
    unfold finiteNuLabel
    have hc := congrArg (fun g => familyPageMap model.family g 2
      (s,t,t+e-(0:ℕ)))
      ((model.quotients.tower ((SyntheticCategory.biShift (0,e)).obj
        (model.nu.functor.obj (X.obj model.auxiliary)))).rho_quotient hq)
    rw [←family_page_comp] at hc
    exact ConcreteCategory.congr_hom hc ((model.comparison.nuE2 X e s t 0) x)
  have hrho' : Detects (model.convergence (.quotient 1 (.shift (0,e) (.nu X)))) (s,t,t+e)
      (regradeE2 (by simp) (finiteNuLabel model X 1 e s t 0 x))
      (a ≫ (model.quotients.tower _).rho 1 q hq) :=
    (congrArg (fun z => Detects (model.convergence (.quotient 1 (.shift (0,e) (.nu X))))
      (s,t,t+e) z (a ≫ (model.quotients.tower _).rho 1 q hq)) hlabel).mp hrho
  apply shifted_first_detection_unique X e s t _ _ _ hrho'
  have hh := model.comparisonCompatible.first_quotient X e s t x
  unfold finiteNuLabel
  rw [page_regrade]
  have regrade_cast {A : SyntheticAdamsSS} {i j : Tridegree} (h : i=j) (z : A.E₂ i) :
      regradeE2 h z = (congrArg (fun k => (A.E₂ k : Type)) h).mp z := by
    subst j
    rfl
  rw [regrade_cast]
  exact hh

private def quotientUnshift (X : ClassicalObject) (δ p : ℤ × ℤ) (q : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (a : BiHom (p+δ).1 (p+δ).2 (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    BiHom p.1 p.2 (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q) :=
  (SyntheticCategory.biShift_fullyFaithful δ).preimage
    ((SyntheticCategory.biShift_comp p δ).hom.app S_0_0 ≫ a ≫ ε.hom)

private theorem quotient_unshift_shift (X : ClassicalObject) (δ p : ℤ × ℤ) (q : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (a : BiHom p.1 p.2 (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    quotientUnshift X δ p q ε (shiftHomotopyClass δ p a ≫ ε.inv) = a := by
  apply (SyntheticCategory.biShift_fullyFaithful δ).map_injective
  simp [quotientUnshift,shiftHomotopyClass,Category.assoc]

private theorem homotopy_regrade_inverse {m m' w w' : ℤ} {A : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) :
    homotopyRegrade hm.symm hw.symm (homotopyRegrade hm hw a)=a := by
  subst m'; subst w'; rfl

private theorem positive_first_desuspend
    (X : ClassicalObject) (s t : ℤ) (x : Ambient model X (s,t))
    (ε : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (hε : XModLambdaN.incl _ 1 ≫ ε.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ 1)) :
    quotientUnshift X (0,1) (t-s,t) 1 ε
      (homotopyRegrade (by simp) rfl ((model.firstQuotient X 1 s t).symm x)) =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  have hf := firstQuotient_positive_shift X s t x ε hε
  rw [←hf,regrade_comp,homotopy_regrade_inverse,quotient_unshift_shift]
  congr 1
  have cast (m w w' : ℤ) (h : w=w') (A : SyntheticSpectrum) (a : BiHom m w A) :
      homotopyRegrade rfl h a = (congrArg (fun v => BiHom m v A) h).mp a := by
    subst w'; rfl
  exact cast _ _ _ _ _ _

private theorem quotient_unshift_restriction
    (X : ClassicalObject) (δ p : ℤ × ℤ)
    (i q : ℕ) (hi : 0 < i) (hiq : i ≤ q)
    (εᵢ : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) i ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (εq : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hεᵢ : XModLambdaN.incl _ i ≫ εᵢ.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ i))
    (hεq : XModLambdaN.incl _ q ≫ εq.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (a : BiHom (p+δ).1 (p+δ).2 (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    quotientUnshift X δ p q εq a ≫ (model.quotients.tower _).rho i q hiq =
      quotientUnshift X δ p i εᵢ (a ≫ (model.quotients.tower _).rho i q hiq) := by
  apply (SyntheticCategory.biShift_fullyFaithful δ).map_injective
  rw [Functor.map_comp]
  simp only [quotientUnshift,Functor.FullyFaithful.map_preimage,Category.assoc]
  rw [←quotient_shift_restriction_on_spheres X δ i q hi hiq εᵢ εq hεᵢ hεq]

private theorem positive_finite_source_desuspend
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (ε₁ : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1))
    (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hε₁ : XModLambdaN.incl _ 1 ≫ ε₁.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ 1))
    (hεq : XModLambdaN.incl _ q ≫ εq.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ q))
    (a : BiHom (t-s) (t+1) (XModLambdaN
      ((SyntheticCategory.biShift (0,1)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.shift (0,1) (.nu X)))) (s,t,t+1)
      (regradeE2 (by simp) (finiteNuLabel model X q 1 s t 0 x)) a) :
    let a₀ := quotientUnshift X (0,1) (t-s,t) q εq (homotopyRegrade (by simp) rfl a)
    a₀ ≫ (model.quotients.tower _).rho 1 q hq =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x)) a₀ := by
  dsimp only
  have hfirst := shifted_finite_source_first X q hq 1 s t x a ha
  have h : quotientUnshift X (0,1) (t-s,t) q εq (homotopyRegrade (by simp) rfl a) ≫
      (model.quotients.tower _).rho 1 q hq =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
    rw [quotient_unshift_restriction X (0,1) (t-s,t) 1 q (by decide) hq ε₁ εq hε₁ hεq,
      ←regrade_comp,hfirst,positive_first_desuspend X s t x ε₁ hε₁]
  exact ⟨h,first_label_detects_unshifted X q hq s t x _ h⟩

private theorem zero_finite_source_desuspend
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t+0) (XModLambdaN
      ((SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.shift (0,0) (.nu X)))) (s,t,t+0)
      (regradeE2 (by simp) (finiteNuLabel model X q 0 s t 0 x)) a) :
    let a₀ := homotopyRegrade rfl (by simp) a ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q
    a₀ ≫ (model.quotients.tower _).rho 1 q hq =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
    Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x)) a₀ := by
  dsimp only
  have hfirst := shifted_finite_source_first X q hq 0 s t x a ha
  have h : (homotopyRegrade rfl (by simp) a ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q) ≫
      (model.quotients.tower _).rho 1 q hq =
      firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
    rw [Category.assoc,←(model.quotients.natural (SyntheticCategory.biShift_zero.hom.app _)).rho_naturality,
      ←Category.assoc,←regrade_comp,hfirst]
    congr 1
    have cast (m w w' : ℤ) (h : w=w') (A : SyntheticSpectrum) (a : BiHom m w A) :
        homotopyRegrade rfl h a = (congrArg (fun v => BiHom m v A) h).mp a := by
      subst w'; rfl
    exact cast _ _ _ _ _ _
  exact ⟨h,first_label_detects_unshifted X q hq s t x _ h⟩

private theorem shift_quotient_unshift (X : ClassicalObject) (δ p : ℤ × ℤ) (q : ℕ)
    (ε : XModLambdaN ((SyntheticCategory.biShift δ).obj
        (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (a : BiHom (p+δ).1 (p+δ).2 (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (model.nu.functor.obj (X.obj model.auxiliary))) q)) :
    shiftHomotopyClass δ p (quotientUnshift X δ p q ε a) ≫ ε.inv = a := by
  simp [quotientUnshift,shiftHomotopyClass,Category.assoc]

private theorem positive_finite_source_unshifted
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t+1) (XModLambdaN
      ((SyntheticCategory.biShift (0,1)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.shift (0,1) (.nu X)))) (s,t,t+1)
      (regradeE2 (by simp) (finiteNuLabel model X q 1 s t 0 x)) a) :
    ∃ (εq : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
          (model.nu.functor.obj (X.obj model.auxiliary))) q ≅
        (SyntheticCategory.biShift (0,1)).obj
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)),
      XModLambdaN.incl _ q ≫ εq.hom =
        (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ q) ∧
      ∃ a₀ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
        a₀ ≫ (model.quotients.tower _).rho 1 q hq =
          firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
        Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
          (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x)) a₀ ∧
        homotopyRegrade (by simp) rfl (shiftHomotopyClass (0,1) (t-s,t) a₀) ≫ εq.inv = a := by
  letI := model.exactness.shiftCommShift (0,1)
  letI := model.exactness.shiftExact (0,1)
  obtain ⟨ε₁,hε₁,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) 1
    (model.nu.functor.obj (X.obj model.auxiliary))
  obtain ⟨εq,hεq,_⟩ := quotient_shift_exists model.quotients.coherence (0,1) q
    (model.nu.functor.obj (X.obj model.auxiliary))
  have h := positive_finite_source_desuspend X q hq s t x ε₁ εq hε₁ hεq a ha
  refine ⟨εq,hεq,_,h.1,h.2,?_⟩
  rw [←regrade_comp,shift_quotient_unshift,homotopy_regrade_inverse]

private theorem zero_finite_source_unshifted
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t+0) (XModLambdaN
      ((SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj (X.obj model.auxiliary))) q))
    (ha : Detects (model.convergence (.quotient q (.shift (0,0) (.nu X)))) (s,t,t+0)
      (regradeE2 (by simp) (finiteNuLabel model X q 0 s t 0 x)) a) :
    ∃ a₀ : BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
      a₀ ≫ (model.quotients.tower _).rho 1 q hq =
        firstLabel model X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      Detects (model.convergence (.quotient q (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel model X q s t 0 x)) a₀ ∧
      homotopyRegrade rfl (by simp) a₀ ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) q = a := by
  have h := zero_finite_source_desuspend X q hq s t x a ha
  refine ⟨_,h.1,h.2,?_⟩
  rw [regrade_comp,homotopy_regrade_inverse,Category.assoc,
    ←model.quotients.functoriality.map_comp,Iso.hom_inv_id_app,
    model.quotients.functoriality.map_id,Category.comp_id]

end
end KIP126.ProofTools.Internal.Mahowald
