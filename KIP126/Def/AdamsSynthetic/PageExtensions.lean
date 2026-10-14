module

public import KIP126.Def.AdamsSynthetic.ExtensionWitnesses

@[expose] section

/-! Page extensions in the shared model, with no separate ESS, filtration,
source/target operators, or arbitrary quotient comparisons as parameters. -/
namespace KIP126.Kervaire.Route
open CategoryTheory KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  (D : Model C Syn)
  (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)


public def FiniteExtension (r : ℕ) (n s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s+n,t+n)) : Prop :=
  Nonempty (FiniteExtensionWitness D X Y f r n s t x y)

public def FiniteExtensionWitness.Essential {r : ℕ} {n s t : ℤ} {x y}
    (W : FiniteExtensionWitness D X Y f r n s t x y) : Prop :=
  TowerEssentialExtension
    (D.convergentMap (.quotient (r - 1) (extensionSourceObject D X Y f))
      (.quotient (r - 1) (.nu Y)) (finiteExtensionMap D X Y f (r - 1)))
    (t - s, t + normalizedExponent D.classicalTower f) s n W.source W.target


public def InfiniteExtension (n s t : ℤ)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
    (y : (D.classical.obj (Y.obj D.auxiliary)).Page 2 (s+n,t+n)) : Prop :=
  Nonempty (InfiniteExtensionWitness D X Y f n s t x y)

public def InfiniteExtensionWitness.Essential {n s t : ℤ} {x y}
    (W : InfiniteExtensionWitness D X Y f n s t x y) : Prop :=
  TowerEssentialExtension
    (D.convergentMap (extensionSourceObject D X Y f) (.nu Y) (D.normalizedMap X Y f).map)
    (t - s, t + normalizedExponent D.classicalTower f) s n W.source W.target

/-- The finite target page stays in the valid page-two range. -/
public theorem FiniteExtensionWitness.target_page_ge_two {r : ℕ} {n s t : ℤ} {x y}
    (W : FiniteExtensionWitness D X Y f r n s t x y) :
    2 ≤ (r : ℤ) - n + normalizedExponent D.classicalTower f := by
  have h := W.length_upper
  omega

public theorem FiniteExtensionWitness.length_nonnegative {r : ℕ} {n s t : ℤ} {x y}
    (W : FiniteExtensionWitness D X Y f r n s t x y) : 0 ≤ n := by
  have h := W.length_lower
  omega

public theorem InfiniteExtensionWitness.length_nonnegative {n s t : ℤ} {x y}
    (W : InfiniteExtensionWitness D X Y f n s t x y) : 0 ≤ n := by
  have h := W.length_lower
  omega
end KIP126.Kervaire.Route
