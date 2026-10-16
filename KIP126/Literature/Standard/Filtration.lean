module

public import KIP126.Literature.Standard
public import KIP126.Literature.Standard.QuotientAlgebra

/-! Structural filtration binding retained from bbac1fc05843,
Def/Kervaire/Route/SourceLanguage.lean:1135 and
Def/Kervaire/Route/Multiplication/Comparison.lean:82–89 (MIT).
This is the original selected-object action law, with no finite upper bound. -/
namespace KIP126.Literature.Standard
open CategoryTheory KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard

public theorem action_filtration (X : SyntheticObject) (m w m' w' s s' : ℤ)
    (a : BiHom m w (S_0_0 : SyntheticSpectrum))
    (b : BiHom m' w' (X.obj model.nu model.auxiliary))
    (ha : FiltrationAtLeast model.syntheticTower s a)
    (hb : FiltrationAtLeast model.syntheticTower s' b) :
    FiltrationAtLeast model.syntheticTower (s+s') (sphereAction a b) := by
  sorry

/-- Original AlgebraBinding.finite_action: multiplication on the actual finite
quotient, with the original positive length and all weight indices. -/
public theorem finite_action (q : ℕ) (hq : 0 < q) (s t s' t' k l : ℕ)
    (x : model.classical.sphere.Page 2 (s,t))
    (y : model.classical.sphere.Page 2 (s',t'))
    (a : BiHom ((t : ℤ)-s) ((t : ℤ)-k) (S_0_0 : SyntheticSpectrum))
    (b : BiHom ((t' : ℤ)-s') ((t' : ℤ)-l) (XModLambdaN (S_0_0 : SyntheticSpectrum) q))
    (ha : Detects (model.convergence .sphere) (s,t,(t : ℤ)-k) (model.comparison.sphereE2 s t k x) a)
    (hb : Detects (model.convergence (.quotient q .sphere)) (s',t',(t' : ℤ)-l)
      ((model.family.quotientProjection (S_0_0 : SyntheticSpectrum) q).pageMap 2
        (s',t',(t' : ℤ)-l) (model.comparison.sphereE2 s' t' l y)) b) :
    Detects (model.convergence (.quotient q .sphere))
      ((s+s' : ℕ),(t+t' : ℕ),(t+t' : ℕ)-(k+l : ℕ))
      ((model.family.quotientProjection (S_0_0 : SyntheticSpectrum) q).pageMap 2
        ((s+s' : ℕ),(t+t' : ℕ),(t+t' : ℕ)-(k+l : ℕ))
        (model.comparison.sphereE2 (s+s') (t+t') (k+l)
          (by simpa only [Nat.cast_add, Prod.mk_add_mk] using
            model.sphereAlgebra.product (s,t) (s',t') x y)))
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]; omega) (sphereAction a b)) := by
  sorry

/-- The original general first-quotient multiplication comparison composed
with QuotientAlgebraBinding.sphere_action (SourceLanguage:969–971,1129–1130).
No paper-specific unit or detection conclusion is asserted. -/
public theorem first_quotient_action (s t s' t' : ℕ)
    (x : BiHom ((t : ℤ)-s) t (S_0_0 : SyntheticSpectrum))
    (y : BiHom ((t' : ℤ)-s') t' (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)) :
    KIP126.Literature.sphereFirstQuotient model ((s+s' : ℕ) : ℤ) ((t+t' : ℕ) : ℤ)
      (homotopyRegrade (by simp only [Nat.cast_add]; omega)
        (by simp only [Nat.cast_add]) (sphereAction x y)) =
      (eqToHom (congrArg (model.classical.sphere.Page 2)
        (show ((s : ℤ),(t : ℤ)) + ((s' : ℤ),(t' : ℤ)) = (((s+s' : ℕ) : ℤ),((t+t' : ℕ) : ℤ)) by
          simp only [Prod.mk_add_mk,Nat.cast_add])))
        (model.sphereAlgebra.product (s,t) (s',t')
          (KIP126.Literature.sphereFirstQuotient model s t (quotientClass 1 x))
          (KIP126.Literature.sphereFirstQuotient model s' t' y)) := by
  rw [← quotientAlgebra_sphere_action 1 (by decide) ((t : ℤ)-s) t ((t' : ℤ)-s') t' x y]
  exact quotientAlgebra_first_quotient s t s' t' (quotientClass 1 x) y

/-- Original AlgebraBinding.classical_detection (SourceLanguage:1061–1070,
1128), on the actual homotopy product and the same classical sphere E₂. -/
public theorem classical_product_detection (s t s' t' : ℕ)
    (x : model.classical.sphere.Page 2 (s,t))
    (y : model.classical.sphere.Page 2 (s',t'))
    (a : HomotopyGroup (C := Spectrum) ((t : ℤ)-s) SphereSpectrum)
    (b : HomotopyGroup (C := Spectrum) ((t' : ℤ)-s') SphereSpectrum)
    (ha : ClassicalDetects (model.classicalConvergence .sphere) (s,t) x a)
    (hb : ClassicalDetects (model.classicalConvergence .sphere) (s',t') y b) :
    ClassicalDetects (model.classicalConvergence .sphere) ((s+s' : ℕ),(t+t' : ℕ))
      ((eqToHom (congrArg (model.classical.sphere.Page 2)
        (show ((s : ℤ),(t : ℤ)) + ((s' : ℤ),(t' : ℤ)) = (((s+s' : ℕ) : ℤ),((t+t' : ℕ) : ℤ)) by
          simp only [Prod.mk_add_mk,Nat.cast_add])))
        (model.sphereAlgebra.product (s,t) (s',t') x y))
      (eqToHom (congrArg (fun n : ℤ => Sphere (C := Spectrum) n)
        (by simp only [Nat.cast_add]; omega : ((t+t' : ℕ) : ℤ)-(s+s') =
          ((t : ℤ)-s)+((t' : ℤ)-s'))) ≫ classicalSphereProduct a b) := by
  sorry

end KIP126.Literature.Standard
