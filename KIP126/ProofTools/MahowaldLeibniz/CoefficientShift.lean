module

import all KIP126.ProofTools.GeneralizedMahowald.FinalDivision
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelOutputLabels

/-! Actual coefficient insertion for the finite Mahowald--Leibniz window.
The same lambda transition transports homotopy classes and commutes with
actual maps.  It preserves both source and target labels, including c=0.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- Insert c lambda coefficients using the actual selected finite triangle;
at c=0 this is the identity on the same quotient. -/
private def finiteCoefficientShiftClass (A : SyntheticSpectrum)
    (N c : ℕ) (hcN : c<N) (m w : ℤ)
    (a : BiHom m w (XModLambdaN A (N-c))) :
    BiHom m (w-c) (XModLambdaN A N) := by
  by_cases hc : c=0
  · subst c
    exact homotopyRegrade rfl (by simp) a
  · exact homotopyRegrade (by simp) (by simp [sub_eq_add_neg])
      (shiftHomotopyClass (0,-(c:ℤ)) (m,w) a) ≫
      ((model.quotients.tower A).triangle (show 0<c by omega) hcN).lambdaMap

/-- Coefficient insertion commutes with the very same actual map, so an
image equation extends together with both its detecting labels. -/
private theorem finite_coefficient_shift_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (N c : ℕ) (hcN : c<N) (m w : ℤ)
    (a : BiHom m w (XModLambdaN A (N-c))) :
    finiteCoefficientShiftClass A N c hcN m w a ≫ XModLambdaN.map f N =
      finiteCoefficientShiftClass B N c hcN m w (a ≫ XModLambdaN.map f (N-c)) := by
  by_cases hc : c=0
  · subst c
    simp only [finiteCoefficientShiftClass,↓reduceDIte,regrade_comp,Nat.sub_zero]
  · simp only [finiteCoefficientShiftClass,hc,↓reduceDIte,Category.assoc]
    rw [←(model.quotients.natural f).lambda_naturality (show 0<c by omega) hcN]
    simp only [shiftHomotopyClass,Functor.map_comp,regrade_precomp,Category.assoc]

private theorem finite_coefficient_shift_neg (A : SyntheticSpectrum)
    (N c : ℕ) (hcN : c<N) (m w : ℤ)
    (a : BiHom m w (XModLambdaN A (N-c))) :
    finiteCoefficientShiftClass A N c hcN m w (-a) =
      -finiteCoefficientShiftClass A N c hcN m w a := by
  by_cases hc : c=0
  · subst c
    simp only [finiteCoefficientShiftClass,↓reduceDIte,output_regrade_neg]
  · simp only [finiteCoefficientShiftClass,hc,↓reduceDIte,shiftHomotopyClass,
      Functor.map_neg,Preadditive.comp_neg,regrade_precomp,Preadditive.neg_comp]

/-- A visible finite label remains the same classical label, and its lambda
index increases by c.  The conclusion uses the actual class above. -/
private theorem finite_coefficient_shift_detects (X : ClassicalObject)
    (N c : ℕ) (hcN : c<N) (s t w : ℤ)
    (hw : 0≤t-w ∧ t-w<(N-c:ℕ))
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-c)))
    (ha : Detects (model.convergence (.quotient (N-c) (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (N-c)).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) x)) a) :
    Detects (model.convergence (.quotient N (.nu X))) (s,t,w-c)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap 2 (s,t,w-c)
        (nuWeightLabel model X s t (w-c) (by omega) x))
      (finiteCoefficientShiftClass _ N c hcN (t-s) w a) := by
  by_cases hc : c=0
  · subst c
    have hp : (s,t,w)=(s,t,w-(0:ℕ)) := by simp
    have h := detects_transport hp _ _ ha
    simp only [Nat.sub_zero] at h
    convert h using 1
    · have transport (v v' : ℤ) (hv : v=v') (hv₁ : v≤t) (hv₂ : v'≤t)
          (h : (s,t,v)=(s,t,v')) :
          regradeE2 h
            ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap 2 (s,t,v)
              (nuWeightLabel model X s t v hv₁ x)) =
            ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap 2 (s,t,v')
              (nuWeightLabel model X s t v' hv₂ x)) := by subst v'; rfl
      exact (transport w _ (by simp) _ _ hp).symm
    · simp only [finiteCoefficientShiftClass,↓reduceDIte]
  · simpa only [finiteCoefficientShiftClass,hc,↓reduceDIte,finiteWeightedLambdaClass,SyntheticObject.obj]
      using finite_weighted_lambda_detects X N c (by omega) hcN s t w hw x a ha

/-- Simultaneous extension of a source detection, target detection, and
actual image equation.  The map and target class are fixed before insertion. -/
private theorem finite_coefficient_shift_detects_pair
    (X Y : ClassicalObject)
    (f : model.nu.functor.obj (X.obj model.auxiliary) ⟶
      model.nu.functor.obj (Y.obj model.auxiliary))
    (N c : ℕ) (hcN : c<N) (s t s' t' w : ℤ)
    (hm : t-s=t'-s')
    (hw : 0≤t-w ∧ t-w<(N-c:ℕ))
    (hw' : 0≤t'-w ∧ t'-w<(N-c:ℕ))
    (x : Ambient model X (s,t)) (y : Ambient model Y (s',t'))
    (a : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-c)))
    (b : BiHom (t'-s') w (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) (N-c)))
    (ha : Detects (model.convergence (.quotient (N-c) (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (N-c)).pageMap 2 (s,t,w)
        (nuWeightLabel model X s t w (by omega) x)) a)
    (hb : Detects (model.convergence (.quotient (N-c) (.nu Y))) (s',t',w)
      ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) (N-c)).pageMap 2 (s',t',w)
        (nuWeightLabel model Y s' t' w (by omega) y)) b)
    (hab : homotopyRegrade hm rfl (a ≫ XModLambdaN.map f (N-c))=b) :
    Detects (model.convergence (.quotient N (.nu X))) (s,t,w-c)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap 2 (s,t,w-c)
        (nuWeightLabel model X s t (w-c) (by omega) x))
      (finiteCoefficientShiftClass _ N c hcN (t-s) w a) ∧
    Detects (model.convergence (.quotient N (.nu Y))) (s',t',w-c)
      ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) N).pageMap 2 (s',t',w-c)
        (nuWeightLabel model Y s' t' (w-c) (by omega) y))
      (finiteCoefficientShiftClass _ N c hcN (t'-s') w b) ∧
    homotopyRegrade hm rfl
      (finiteCoefficientShiftClass _ N c hcN (t-s) w a ≫ XModLambdaN.map f N) =
      finiteCoefficientShiftClass _ N c hcN (t'-s') w b := by
  refine ⟨finite_coefficient_shift_detects X N c hcN s t w hw x a ha,
    finite_coefficient_shift_detects Y N c hcN s' t' w hw' y b hb,?_⟩
  rw [finite_coefficient_shift_natural]
  have regrade (m m' : ℤ) (h : m=m')
      (a : BiHom m w (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) (N-c))) :
      homotopyRegrade h rfl (finiteCoefficientShiftClass _ N c hcN m w a) =
        finiteCoefficientShiftClass _ N c hcN m' w (homotopyRegrade h rfl a) := by
    subst m'
    rfl
  rw [regrade,hab]

/-- The weighted label agrees with the intrinsic native label at each
nonnegative lambda layer. -/
private theorem finite_coefficient_weight_label (X : ClassicalObject)
    (N j : ℕ) (s t : ℤ) (x : Ambient model X (s,t)) :
    ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
      2 (s,t,t-j) (nuWeightLabel model X s t (t-j) (by omega) x)) =
      finiteTargetLabel model X N s t j x := by
  have hj : (t-(t-j)).toNat=j := by omega
  have hn : nuWeightLabel model X s t (t-j) (by omega) x =
      targetNuLabel model X s t j x := by
    unfold nuWeightLabel
    have transport (k k' : ℕ) (h : k=k') (hp : (s,t,t-k)=(s,t,t-k')) :
        regradeE2 hp (targetNuLabel model X s t k x)=targetNuLabel model X s t k' x := by
      subst k'
      rfl
    exact transport _ j hj _
  rw [hn]
  rfl

/-- Intrinsic native-label version: the input layer j becomes exactly c+j.
This includes bottom-layer inputs and target labels which are not permanent. -/
private theorem finite_coefficient_shift_layer_detects (X : ClassicalObject)
    (N c j : ℕ) (hcN : c<N) (hj : j<N-c) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) (t-j)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (N-c)))
    (ha : Detects (model.convergence (.quotient (N-c) (.nu X))) (s,t,t-j)
      (finiteTargetLabel model X (N-c) s t j x) a) :
    Detects (model.convergence (.quotient N (.nu X))) (s,t,t-(c+j))
      (finiteTargetLabel model X N s t (c+j) x)
      (homotopyRegrade rfl (show (t-j)-c=t-(c+j) by omega)
        (finiteCoefficientShiftClass _ N c hcN (t-s) (t-j) a)) := by
  have h := finite_coefficient_shift_detects X N c hcN s t (t-j) (by omega) x a
    (by rw [finite_coefficient_weight_label]; exact ha)
  have hp : (s,t,(t-j)-c)=(s,t,t-(c+j)) := by ext <;> dsimp <;> omega
  have h' := detects_transport hp _ _ h
  convert h' using 1
  · rw [←finite_coefficient_weight_label X N (c+j) s t x]
    have transport (v v' : ℤ) (hv : v=v') (hv₁ : v≤t) (hv₂ : v'≤t)
        (h : (s,t,v)=(s,t,v')) :
        regradeE2 h
          ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap 2 (s,t,v)
            (nuWeightLabel model X s t v hv₁ x)) =
          ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap 2 (s,t,v')
            (nuWeightLabel model X s t v' hv₂ x)) := by subst v'; rfl
    exact (transport _ _ (by omega) _ _ hp).symm

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
