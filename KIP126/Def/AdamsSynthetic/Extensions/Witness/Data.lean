module

public import KIP126.Def.AdamsSynthetic.Extensions.Data
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Predicates

@[expose] public section

/-! Representatives of finite and infinite extensions in the specified Adams
comparison. Each witness retains the quotient objects, detected classes and
extension equation for the same normalized map. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H} (D : AdamsComparison H M Syn)
  (X Y : ClassicalObject) (f : X.obj D.hopfAndDetector ⟶ Y.obj D.hopfAndDetector)

structure FiniteExtensionWitness (r : ℕ) (n s t : ℤ)
    (x : E2 H (X.obj D.hopfAndDetector) s t)
    (y : E2 H (Y.obj D.hopfAndDetector) (s + n) (t + n)) where
  page_ge_two : 2 ≤ r
  length_lower : (normalizedExponent H f : ℤ) ≤ n
  length_upper : n ≤ (r : ℤ) - 2 + normalizedExponent H f
  source_cycle : PageRepresentatives.IsCycle H (X.obj D.hopfAndDetector) ((r : ℤ) - 1) (s, t) x
  target_cycle : PageRepresentatives.IsCycle H (Y.obj D.hopfAndDetector)
    ((r : ℤ) - 1 - n + normalizedExponent H f) (s + n, t + n) y
  source : ((D.family.obj ((SyntheticObject.quotient (r - 1)
    (extensionSourceObject D X Y f)).obj D.nu D.hopfAndDetector)).sequence.ssData
      (s, (t - s) + s, t + normalizedExponent H f)).eInfty
  target : ((D.family.obj ((SyntheticObject.quotient (r - 1) (.nu Y)).obj
    D.nu D.hopfAndDetector)).sequence.ssData
      (s + n, (t - s) + (s + n), t + normalizedExponent H f)).eInfty
  source_rep : HasInfinityRepresentative _ 2 _
    (finiteSourceForExtension D X Y f (r - 1) s t x) source
  target_rep : HasInfinityRepresentative _ 2 _
    (finiteTargetForExtension D X Y f (r - 1) n s t length_lower y) target
  equation : ExtensionEquation (finiteExtensionMap D X Y f (r - 1))
    (D.convergence (.quotient (r - 1) (extensionSourceObject D X Y f)))
    (D.convergence (.quotient (r - 1) (.nu Y)))
    (t - s, t + normalizedExponent H f) s n source target

structure InfiniteExtensionWitness (n s t : ℤ)
    (x : E2 H (X.obj D.hopfAndDetector) s t)
    (y : E2 H (Y.obj D.hopfAndDetector) (s + n) (t + n)) where
  length_lower : (normalizedExponent H f : ℤ) ≤ n
  source_cycle : PageRepresentatives.IsPermanent H (X.obj D.hopfAndDetector) (s, t) x
  target_cycle : PageRepresentatives.IsPermanent H (Y.obj D.hopfAndDetector) (s + n, t + n) y
  source : ((D.family.obj ((extensionSourceObject D X Y f).obj D.nu D.hopfAndDetector)).sequence.ssData
    (s, (t - s) + s, t + normalizedExponent H f)).eInfty
  target : ((D.family.obj (D.nu.functor.obj (Y.obj D.hopfAndDetector))).sequence.ssData
    (s + n, (t - s) + (s + n), t + normalizedExponent H f)).eInfty
  source_rep : HasInfinityRepresentative _ 2 _ (infiniteSourceForExtension D X Y f s t x) source
  target_rep : HasInfinityRepresentative _ 2 _
    (infiniteTargetForExtension D X Y f n s t length_lower y) target
  equation : ExtensionEquation (D.normalizedMap X Y f).map
    (D.convergence (extensionSourceObject D X Y f)) (D.convergence (.nu Y))
    (t - s, t + normalizedExponent H f) s n source target

end KIP126.AdamsSynthetic
