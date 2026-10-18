module

public import KIP126.ProofTools.Operations
import all KIP126.ProofTools.GeneralizedLeibniz.LevelDivision

/-! Conditional division by a positive power of lambda in the actual finite
quotient square. Essential extensions in the smaller quotient whose target
is killed by the actual lambda map are excluded below the requested target
filtration. The crossing range includes the initial source filtration.

The result retains the given actual source and its image. The smaller source
is produced by division; neither its label nor a unique target lift is assumed. -/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Core.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section

/-- The extra no-crossing condition for division by `lambda^i` in quotient
`q`: every essential smaller-quotient extension with `s+i ≤ u ≤ v < N`
has target surviving the actual lambda map on E∞. All classes are at the
fixed stem/weight `(t-s, t+e(f))`, including the same-source row `u=s+i`. -/
public def FiniteLambdaKernelNoCrossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (s t N : ℤ) : Prop :=
  ∀ u v : ℤ, s+i ≤ u → u ≤ v → v < N → ∀ source target,
    TowerEssentialExtension
      (model.convergentMap
        (.shift (0,-(i:ℤ)) (.quotient (q-i) (extensionSourceObject model X Y f)))
        (.shift (0,-(i:ℤ)) (.quotient (q-i) (.nu Y)))
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (finiteExtensionMap model X Y f (q-i))))
      (t-s,t+normalizedExponent model.classicalTower f) u (v-u) source target →
      (model.family.functor.map
        ((model.quotients.tower (model.nu.functor.obj (Y.obj model.auxiliary))).triangle
          hi hiq).lambdaMap).eInftyMap
        (u+(v-u),(t-s)+(u+(v-u)),t+normalizedExponent model.classicalTower f) target ≠ 0

/-- Divide an actual finite-quotient source by `lambda^i`, retaining the
source equation and its image equation and reflecting target filtration.
The additional condition is imposed only below `N`; no target at grade `N`
is prescribed in advance and no uniqueness of its lambda preimage is claimed. -/
public theorem finiteLambdaDivision
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (s t N : ℤ) (hsN : s+i ≤ N)
    (hcross : FiniteLambdaKernelNoCrossing X Y f q i hi hiq s t N)
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) q))
    (ha : FiltrationAtLeast model.syntheticTower (s+i) a)
    (hfa : FiltrationAtLeast model.syntheticTower N (a ≫ finiteExtensionMap model X Y f q)) :
    ∃ b : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
        ((SyntheticCategory.biShift (0,-(i:ℤ))).obj
          (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) (q-i))),
      b ≫ ((model.quotients.tower _).triangle hi hiq).lambdaMap = a ∧
      FiltrationAtLeast model.syntheticTower (s+i) b ∧
      (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
        (finiteExtensionMap model X Y f (q-i))) ≫
          ((model.quotients.tower _).triangle hi hiq).lambdaMap =
        a ≫ finiteExtensionMap model X Y f q ∧
      FiltrationAtLeast model.syntheticTower N
        (b ≫ (SyntheticCategory.biShift (0,-(i:ℤ))).map
          (finiteExtensionMap model X Y f (q-i))) :=
  KIP126.ProofTools.Internal.Leibniz.normalized_finite_division_of_kernel_no_crossing
    X Y f q i hi hiq s t N hsN hcross a ha hfa

end
end KIP126.ProofTools.Standard
