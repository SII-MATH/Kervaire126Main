module

public import KIP126.Def.AdamsSynthetic.Comparison.Coherent.Data
public import KIP126.Def.Synthetic.ExtensionRelation.Predicates
public import KIP126.Def.Synthetic.Detection.Predicates

@[expose] public section

/-! Normalized maps and their finite λ quotients for the Section 7 extensions.
All classes are transported by the specified classical/synthetic comparisons. -/
namespace KIP126.AdamsSynthetic
open KIP126.Classical.Adams
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)
  (X Y : ClassicalObject) (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)

def extensionSourceObject : SyntheticObject :=
  .shift (0, (normalizedExponent H f : ℤ)) (.nu X)
def finiteExtensionMap (q : ℕ) := XModLambdaN.map (D.normalizedMap X Y f).map q

/-- Labels for any actual shifted ν object in a finite λ quotient. -/
def finiteNuLabel (X : ClassicalObject) (q : ℕ) (a s t : ℤ) (k : ℕ)
    (x : E2 H (X.obj D.hopfAndDetector) s t) :
    (D.family.obj ((SyntheticObject.quotient q (.shift (0, a) (.nu X))).obj
      D.nu D.hopfAndDetector)).E₂ (s, t, t + a - k) :=
  familyPageMap D.family (XModLambdaN.incl _ q) 2 (s, t, t + a - k)
    (D.nuE2 X a s t k x)

/-- The unshifted target label uses the specified zero-shift isomorphism. -/
def targetNuLabel (Y : ClassicalObject) (s t : ℤ) (k : ℕ)
    (y : E2 H (Y.obj D.hopfAndDetector) s t) :
    (D.family.obj (D.nu.functor.obj (Y.obj D.hopfAndDetector))).E₂ (s, t, t - k) :=
  familyPageMap D.family (SyntheticCategory.biShift_zero.hom.app _) 2 (s, t, t - k)
    (by simpa [SyntheticAdamsSS.E₂] using D.nuE2 Y 0 s t k y)

def finiteTargetLabel (Y : ClassicalObject) (q : ℕ) (s t : ℤ) (k : ℕ)
    (y : E2 H (Y.obj D.hopfAndDetector) s t) :
    (D.family.obj ((SyntheticObject.quotient q (.nu Y)).obj D.nu D.hopfAndDetector)).E₂
      (s, t, t - k) :=
  familyPageMap D.family (XModLambdaN.incl _ q) 2 (s, t, t - k)
    (targetNuLabel D Y s t k y)

/-- Only transports a proved degree equality. -/
def regradeE2 {A : SyntheticAdamsSS.{v}} {i j : Tridegree} (h : i = j)
    (x : A.E₂ i) : A.E₂ j := (eqToHom (congrArg A.E₂ h)) x

def finiteSourceForExtension (q : ℕ) (s t : ℤ) (x : E2 H (X.obj D.hopfAndDetector) s t) :
    (D.family.obj ((SyntheticObject.quotient q (extensionSourceObject D X Y f)).obj
      D.nu D.hopfAndDetector)).E₂ (s, (t - s) + s, t + normalizedExponent H f) :=
  regradeE2 (by simp)
    (finiteNuLabel D X q (normalizedExponent H f) s t 0 x)

def finiteTargetForExtension (q : ℕ) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n)
    (y : E2 H (Y.obj D.hopfAndDetector) (s + n) (t + n)) :
    (D.family.obj ((SyntheticObject.quotient q (.nu Y)).obj D.nu D.hopfAndDetector)).E₂
      (s + n, (t - s) + (s + n), t + normalizedExponent H f) :=
  regradeE2 (by
    ext <;> simp only [Int.toNat_of_nonneg (sub_nonneg.mpr hn)] <;> omega)
    (finiteTargetLabel D Y q (s + n) (t + n) (n - normalizedExponent H f).toNat y)

def infiniteSourceForExtension (s t : ℤ) (x : E2 H (X.obj D.hopfAndDetector) s t) :
    (D.family.obj ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).E₂
      (s, (t - s) + s, t + normalizedExponent H f) :=
  regradeE2 (by simp) (D.nuE2 X (normalizedExponent H f) s t 0 x)

def infiniteTargetForExtension (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n)
    (y : E2 H (Y.obj D.hopfAndDetector) (s + n) (t + n)) :
    (D.family.obj (D.nu.functor.obj (Y.obj D.hopfAndDetector))).E₂
      (s + n, (t - s) + (s + n), t + normalizedExponent H f) :=
  regradeE2 (by
    ext <;> simp only [Int.toNat_of_nonneg (sub_nonneg.mpr hn)] <;> omega)
    (targetNuLabel D Y (s + n) (t + n) (n - normalizedExponent H f).toNat y)
end
end KIP126.AdamsSynthetic
