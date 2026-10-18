module

public import KIP126.AdamsSynthetic.ExtensionLabels

@[expose] section

/-! Page extensions in the shared model, with no separate ESS, filtration,
source/target operators, or arbitrary quotient comparisons as parameters. -/
namespace KIP126.Kervaire.Route
open CategoryTheory KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  (D : Model C Syn)
  (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)

public structure FiniteExtensionWitness (r : ℕ) (n s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s+n,t+n)) where
  page_ge_two : 2 ≤ r
  length_lower : (normalizedExponent D.classicalTower f : ℤ) ≤ n
  length_upper : n ≤ (r : ℤ) - 2 + normalizedExponent D.classicalTower f
  source_cycle : ReachesPage (D.classical.obj (X.obj D.auxiliary)) r (s, t) x
  target_cycle : ReachesPage (D.classical.obj (Y.obj D.auxiliary))
    ((r : ℤ) - n + normalizedExponent D.classicalTower f) (s + n, t + n) y
  source : ((D.family.obj ((SyntheticObject.quotient (r - 1)
    (extensionSourceObject D X Y f)).obj D.nu D.auxiliary)).sequence.ssData
      (s, (t - s) + s, t + normalizedExponent D.classicalTower f)).eInfty
  target : ((D.family.obj ((SyntheticObject.quotient (r - 1) (.nu Y)).obj
    D.nu D.auxiliary)).sequence.ssData
      (s + n, (t - s) + (s + n), t + normalizedExponent D.classicalTower f)).eInfty
  source_rep : HasInfinityRepresentative _ 2 _
    (finiteSourceForExtension D X Y f (r - 1) s t x) source
  target_rep : HasInfinityRepresentative _ 2 _
    (finiteTargetForExtension D X Y f (r - 1) n s t length_lower y) target
  equation : TowerExtensionEquation
    (D.convergentMap (.quotient (r - 1) (extensionSourceObject D X Y f))
      (.quotient (r - 1) (.nu Y)) (finiteExtensionMap D X Y f (r - 1)))
    (t - s, t + normalizedExponent D.classicalTower f) s n source target

public structure InfiniteExtensionWitness (n s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s+n,t+n)) where
  length_lower : (normalizedExponent D.classicalTower f : ℤ) ≤ n
  source_cycle : IsPermanentCycle (D.classical.obj (X.obj D.auxiliary)) (s, t) x
  target_cycle : IsPermanentCycle (D.classical.obj (Y.obj D.auxiliary)) (s + n, t + n) y
  source : ((D.family.obj ((extensionSourceObject D X Y f).obj D.nu D.auxiliary)).sequence.ssData
    (s, (t - s) + s, t + normalizedExponent D.classicalTower f)).eInfty
  target : ((D.family.obj (D.nu.functor.obj (Y.obj D.auxiliary))).sequence.ssData
    (s + n, (t - s) + (s + n), t + normalizedExponent D.classicalTower f)).eInfty
  source_rep : HasInfinityRepresentative _ 2 _ (infiniteSourceForExtension D X Y f s t x) source
  target_rep : HasInfinityRepresentative _ 2 _
    (infiniteTargetForExtension D X Y f n s t length_lower y) target
  equation : TowerExtensionEquation
    (D.convergentMap (extensionSourceObject D X Y f) (.nu Y) (D.normalizedMap X Y f).map)
    (t - s, t + normalizedExponent D.classicalTower f) s n source target

end KIP126.Kervaire.Route
