module

public import KIP126.Def.AdamsSynthetic.Quotients
public import KIP126.Def.AdamsSynthetic.Recovery
public import KIP126.Def.AdamsSynthetic.Sphere
public import KIP126.Def.AdamsSynthetic.Comparisons
public import KIP126.Def.AdamsSynthetic.Detection

@[expose] section

set_option backward.isDefEq.respectTransparency false

/-! The sphere's actual homotopy operations and their specified comparisons.
Every compatibility concerns the same ν, quotient functor, E₂ algebra and
canonical convergence. These are input conditions, not produced instances. -/

namespace KIP126.Synthetic.Context
open CategoryTheory KIP126.StableHomotopy
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The composition product through the given bigraded suspension. -/
public def sphereProduct {m n k l : ℤ}
    (x : BiHom m n (S_0_0 : Syn)) (y : BiHom k l (S_0_0 : Syn)) :
    BiHom (m + k) (n + l) (S_0_0 : Syn) :=
  (SyntheticCategory.biShift_comp (m, n) (k, l)).inv.app S_0_0 ≫
    (SyntheticCategory.biShift (k, l)).map x ≫ y

public def sphereAction {m n k l : ℤ} {X : Syn}
    (x : BiHom m n (S_0_0 : Syn)) (y : BiHom k l X) : BiHom (m + k) (n + l) X :=
  (SyntheticCategory.biShift_comp (m, n) (k, l)).inv.app S_0_0 ≫
    (SyntheticCategory.biShift (k, l)).map x ≫ y

public def lambdaMultiply {m w : ℤ} {X : Syn} (k : ℕ)
    (x : BiHom m w X) : BiHom m (w - k) X :=
  eqToHom (by congr 1; simp) ≫
    (SyntheticCategory.biShift_comp (m, w) (0, -(k : ℤ))).inv.app S_0_0 ≫
      lambdaPow k (Smn m w) ≫ x

public def homotopyRegrade {m m' w w' : ℤ} {X : Syn} (hm : m = m') (hw : w = w')
    (x : BiHom m w X) : BiHom m' w' X := by
  subst m'
  subst w'
  exact x

public def biHomTargetIso (m n : ℤ) {X Y : Syn} (e : X ≅ Y) :
    BiHom m n X ≃+ BiHom m n Y where
  toFun x := x ≫ e.hom
  invFun y := y ≫ e.inv
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp [Preadditive.add_comp]

public def quotientClass [HasFunctorialCofiber (C := Syn)] {m n : ℤ} {X : Syn} (r : ℕ)
    (x : BiHom m n X) : BiHom m n (XModLambdaN X r) :=
  x ≫ XModLambdaN.incl X r
end
end KIP126.Synthetic.Context

namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

public abbrev FirstQuotientComparison (A : ClassicalAdamsFamily C)
    (N : NuFunctorData C Syn) (aux : AuxiliaryData C) :=
  ∀ (X : ClassicalObject) (a s t : ℤ),
    BiHom (t-s) (t+a)
      (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj
        (N.functor.obj (X.obj aux))) 1) ≃ₗ[ℤ] (A.obj (X.obj aux)).Page 2 (s,t)

/-- The sphere specialization is transported from the ν-sphere comparison
using the unit iso and this same actual quotient functor. It is not another choice. -/
public def sphereFirstQuotient {A : ClassicalAdamsFamily C}
    (N : NuFunctorData C Syn) {aux : AuxiliaryData C}
    (Q : LambdaQuotientFunctoriality (Syn := Syn))
    (comparison : FirstQuotientComparison A N aux) (s t : ℤ) :
    BiHom (t-s) t (XModLambdaN (S_0_0 : Syn) 1) ≃ₗ[ℤ] A.sphere.Page 2 (s,t) := by
  let e : (SyntheticCategory.biShift (0,0)).obj (N.functor.obj SphereSpectrum) ≅
      (S_0_0 : Syn) := SyntheticCategory.biShift_zero.app _ ≪≫ N.unitIso
  let q := (Q.functor 1).mapIso e
  let c : BiHom (t-s) t
      (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
        (N.functor.obj SphereSpectrum)) 1) ≃ₗ[ℤ] A.sphere.Page 2 (s,t) := by
    exact Eq.mp (congrArg (fun z : ℤ =>
      BiHom (t-s) z (XModLambdaN ((SyntheticCategory.biShift (0,0)).obj
        (N.functor.obj SphereSpectrum)) 1) ≃ₗ[ℤ] A.sphere.Page 2 (s,t))
      (Int.add_zero t)) (comparison .sphere 0 s t)
  exact (biHomTargetIso (t-s) t q.symm).toIntLinearEquiv.trans c

/-- First-quotient and λ detection on the sphere, with the derived comparison. -/
public structure SphereDetectionCompatible
    {A : ClassicalAdamsFamily C} {F : SyntheticAdamsFamily Syn}
    {N : NuFunctorData C Syn} {aux : AuxiliaryData C}
    (K : E2Comparison A F N aux)
    (Q : LambdaQuotientFunctoriality (Syn := Syn))
    (first : FirstQuotientComparison A N aux)
    {H : Syn} {unit : S_0_0 ⟶ H} {T : SyntheticTowerPresentation unit F}
    (cSphere : SyntheticTowerConvergence T (S_0_0 : Syn))
    (cQuotient : SyntheticTowerConvergence T (XModLambdaN (S_0_0 : Syn) 1)) : Prop where
  first_quotient : ∀ (s t : ℤ) (x : A.sphere.Page 2 (s,t)),
    Detects cQuotient (s,t,t)
      (F.pageMap (XModLambdaN.incl S_0_0 1) 2 (s,t,t)
        (by simpa only [SyntheticAdamsFamily.sphere, SyntheticAdamsSS.Page,
          Nat.cast_zero, sub_zero] using K.sphereE2 s t 0 x))
      ((sphereFirstQuotient N Q first s t).symm x)
  homotopy_lambda : ∀ (s t : ℤ) (k : ℕ) (x : BiHom (t-s) t (S_0_0 : Syn)),
    Detects cSphere (s,t,t-k)
      (K.sphereE2 s t k (sphereFirstQuotient N Q first s t (quotientClass 1 x)))
      (lambdaMultiply k x)

/-- Detection respects the given E₂ product and actual composition product.
The natural-number ranges and possible zero leading terms match the fixed source. -/
public def MultiplicationCompatible
    {A : ClassicalAdamsFamily C} {F : SyntheticAdamsFamily Syn}
    {N : NuFunctorData C Syn} {aux : AuxiliaryData C}
    (K : E2Comparison A F N aux) (P : SphereE2Algebra A)
    {H : Syn} {unit : S_0_0 ⟶ H} {T : SyntheticTowerPresentation unit F}
    (cSphere : SyntheticTowerConvergence T (S_0_0 : Syn)) : Prop :=
  ∀ (s t s' t' k l : ℕ)
    (x : A.sphere.Page 2 (s,t)) (y : A.sphere.Page 2 (s',t'))
    (α : BiHom ((t : ℤ)-s) ((t : ℤ)-k) (S_0_0 : Syn))
    (β : BiHom ((t' : ℤ)-s') ((t' : ℤ)-l) (S_0_0 : Syn)),
    Detects cSphere (s,t,(t : ℤ)-k) (K.sphereE2 s t k x) α →
    Detects cSphere (s',t',(t' : ℤ)-l) (K.sphereE2 s' t' l y) β →
    Detects cSphere ((s : ℤ)+s', (t : ℤ)+t', (t : ℤ)+t'-(k+l : ℕ))
      (K.sphereE2 ((s : ℤ)+s') ((t : ℤ)+t') (k+l)
        (P.product (s,t) (s',t') x y))
      (homotopyRegrade (by dsimp; omega)
        (by dsimp; omega) (sphereProduct α β))

/-- The sign uses topological degrees; no extra weight sign is inserted. -/
public def SphereProductCommutative : Prop :=
  ∀ (m n k l : ℤ) (x : BiHom m n (S_0_0 : Syn)) (y : BiHom k l (S_0_0 : Syn)),
    sphereProduct x y = ((-1 : ℤ) ^ (m*k).natAbs) •
      homotopyRegrade (add_comm k m) (add_comm l n) (sphereProduct y x)

end
end KIP126.AdamsSynthetic
