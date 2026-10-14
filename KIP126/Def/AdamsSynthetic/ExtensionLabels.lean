module

public import KIP126.Def.AdamsSynthetic.System

@[expose] section

/-! Actual normalized maps used throughout the Section 7 route.
No NormalizedPageFamily with a globally bounded infinite ESS is required. -/
namespace KIP126.Kervaire.Route
open KIP126.Classical.Adams KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  (D : Model C Syn)
  (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)

public def extensionSourceObject : SyntheticObject :=
  .shift (0, (normalizedExponent D.classicalTower f : ℤ)) (.nu X)
public def finiteExtensionMap (q : ℕ) := XModLambdaN.map (D.normalizedMap X Y f).map q

/-- Labels for any actual shifted ν object in a finite λ quotient. -/
public def finiteNuLabel (X : ClassicalObject) (q : ℕ) (a s t : ℤ) (k : ℕ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)) :
    (D.family.obj ((SyntheticObject.quotient q (.shift (0, a) (.nu X))).obj
      D.nu D.auxiliary)).E₂ (s, t, t + a - k) :=
  D.family.pageMap (XModLambdaN.incl _ q) 2 (s, t, t + a - k)
    (D.comparison.nuE2 X a s t k x)

/-- The unshifted target label uses the specified zero-shift isomorphism. -/
public def targetNuLabel (Y : ClassicalObject) (s t : ℤ) (k : ℕ)
    (y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s,t)) :
    (D.family.obj (D.nu.functor.obj (Y.obj D.auxiliary))).E₂ (s, t, t - k) :=
  D.family.pageMap (SyntheticCategory.biShift_zero.hom.app _) 2 (s, t, t - k)
    (by simpa [SyntheticAdamsSS.E₂] using D.comparison.nuE2 Y 0 s t k y)

public def finiteTargetLabel (Y : ClassicalObject) (q : ℕ) (s t : ℤ) (k : ℕ)
    (y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s,t)) :
    (D.family.obj ((SyntheticObject.quotient q (.nu Y)).obj D.nu D.auxiliary)).E₂
      (s, t, t - k) :=
  D.family.pageMap (XModLambdaN.incl _ q) 2 (s, t, t - k)
    (targetNuLabel D Y s t k y)

/-- Only transports a proved degree equality. -/
public def regradeE2 {A : SyntheticAdamsSS.{v}} {i j : Tridegree} (h : i = j)
    (x : A.E₂ i) : A.E₂ j := (eqToHom (congrArg A.E₂ h)) x

public def finiteSourceForExtension (q : ℕ) (s t : ℤ) (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)) :
    (D.family.obj ((SyntheticObject.quotient q (extensionSourceObject D X Y f)).obj
      D.nu D.auxiliary)).E₂ (s, (t - s) + s, t + normalizedExponent D.classicalTower f) :=
  regradeE2 (by simp)
    (finiteNuLabel D X q (normalizedExponent D.classicalTower f) s t 0 x)

public def finiteTargetForExtension (q : ℕ) (n s t : ℤ)
    (hn : (normalizedExponent D.classicalTower f : ℤ) ≤ n)
    (y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s+n,t+n)) :
    (D.family.obj ((SyntheticObject.quotient q (.nu Y)).obj D.nu D.auxiliary)).E₂
      (s + n, (t - s) + (s + n), t + normalizedExponent D.classicalTower f) :=
  regradeE2 (by
    ext <;> simp only [Int.toNat_of_nonneg (sub_nonneg.mpr hn)] <;> omega)
    (finiteTargetLabel D Y q (s + n) (t + n) (n - normalizedExponent D.classicalTower f).toNat y)

public def infiniteSourceForExtension (s t : ℤ) (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)) :
    (D.family.obj ((extensionSourceObject D X Y f).obj D.nu D.auxiliary)).E₂
      (s, (t - s) + s, t + normalizedExponent D.classicalTower f) :=
  regradeE2 (by simp) (D.comparison.nuE2 X (normalizedExponent D.classicalTower f) s t 0 x)

public def infiniteTargetForExtension (n s t : ℤ)
    (hn : (normalizedExponent D.classicalTower f : ℤ) ≤ n)
    (y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s+n,t+n)) :
    (D.family.obj (D.nu.functor.obj (Y.obj D.auxiliary))).E₂
      (s + n, (t - s) + (s + n), t + normalizedExponent D.classicalTower f) :=
  regradeE2 (by
    ext <;> simp only [Int.toNat_of_nonneg (sub_nonneg.mpr hn)] <;> omega)
    (targetNuLabel D Y (s + n) (t + n) (n - normalizedExponent D.classicalTower f).toNat y)
end
end KIP126.Kervaire.Route
