module

public import KIP126.Def.Synthetic.ExtensionSS.Proofs
public import KIP126.Def.Synthetic.NormalizedMap.Data
public import KIP126.Def.Synthetic.PageExtension.Lambda.Data
public import KIP126.Def.ClassicalAdams.PageRepresentatives.Data

@[expose] public section

/-!
# A fixed comparison family for normalized page extensions

These are explicit comparison inputs, not a construction of synthetic
rigidity. Every ESS, quotient, λ map and convergence target is attached to
the same actual objects. Comparison isomorphisms are fixed for the entire
family, never selected anew for an individual extension relation.

Both finite and untruncated clauses currently use degreewise bounded
convergence. The untruncated clause does not construct an ESS for arbitrary
unbounded Adams filtrations; that extension needs a separate convergence
argument using the unbounded ESS infrastructure.
-/

namespace KIP126.Synthetic.PageExtension
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams

universe u v u' v'
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The positive-shift source of the paper's normalized map. -/
def normalizedSource (H : Mod2EilenbergMacLane (C := C))
    (N : NuFunctorData C Syn) {X Y : C} (f : X ⟶ Y) : Syn :=
  (SyntheticCategory.biShift (0, (normalizedExponent H f : ℤ))).obj (N.functor.obj X)

/-- Fixed actual ESS and top-weight comparisons for all finite quotients and
the untruncated normalized map. This record does not assert the later
Leibniz, restriction, or comparison-coherence theorems. -/
structure NormalizedPageFamily (H : Mod2EilenbergMacLane (C := C))
    (N : NuFunctorData C Syn) (F : SyntheticAdamsFamily Syn)
    {X Y : C} (f : X ⟶ Y) where
  normalized : NormalizedSyntheticMap H N f
  sourceTower : FiniteLambdaQuotientTower (normalizedSource H N f)
  targetTower : FiniteLambdaQuotientTower (N.functor.obj Y)
  towerMap : FiniteLambdaQuotientTower.Hom sourceTower targetTower normalized.map
  finite : ∀ (q : ℕ), 0 < q →
    SyntheticExtensionData F (XModLambdaN.map normalized.map q)
  infinite : SyntheticExtensionData F normalized.map
  finiteSource : ∀ (q : ℕ) (_hq : 0 < q) (s t : ℤ),
    PageRepresentatives.cycles H X q (s, t) ≃ₗ[ℤ]
      ((F.obj (XModLambdaN (normalizedSource H N f) q)).sequence.ssData
        (s, t, t + normalizedExponent H f)).eInfty
  finiteTarget : ∀ (q k : ℕ) (_hkq : k < q) (s t : ℤ),
    PageRepresentatives.cycles H Y (q - k : ℕ) (s, t) ≃ₗ[ℤ]
      ((F.obj ((SyntheticCategory.biShift (0, -(k : ℤ))).obj
        (XModLambdaN (N.functor.obj Y) (q - k)))).sequence.ssData
          (s, t, t - k)).eInfty
  infiniteSource : ∀ (s t : ℤ),
    PageRepresentatives.permanentCycles H X (s, t) ≃ₗ[ℤ]
      ((F.obj (normalizedSource H N f)).sequence.ssData
        (s, t, t + normalizedExponent H f)).eInfty
  infiniteTarget : ∀ (k : ℕ) (s t : ℤ),
    PageRepresentatives.permanentCycles H Y (s, t) ≃ₗ[ℤ]
      ((F.obj ((SyntheticCategory.biShift (0, -(k : ℤ))).obj
        (N.functor.obj Y))).sequence.ssData (s, t, t - k)).eInfty

namespace NormalizedPageFamily
variable {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

/-- The exponent is computed from the actual extension length. -/
def lambdaExponent (_P : NormalizedPageFamily H N F f) (n : ℤ) : ℕ :=
  (n - normalizedExponent H f).toNat

def degree (_P : NormalizedPageFamily H N F f) (s t : ℤ) : ℤ × ℤ :=
  (t - s, t + normalizedExponent H f)

/-- Source transport through the fixed top-weight comparison and actual ESS
E₀ identification. -/
def finiteSourceMap (P : NormalizedPageFamily H N F f)
    (q : ℕ) (hq : 0 < q) (s t : ℤ) :
    PageRepresentatives.cycles H X q (s, t) →ₗ[ℤ]
      (((P.finite q hq).ess (P.degree s t)).ssData (s, 1)).V := by
  let D := P.finite q hq
  have hi : (s, t, t + (normalizedExponent H f : ℤ)) =
      (s, (P.degree s t).1 + s, (P.degree s t).2) := by
    simp [degree]
  exact (D.sourceIso s (P.degree s t)).inv.hom.comp
    ((eqToHom (congrArg (fun i =>
      ((F.obj (XModLambdaN (normalizedSource H N f) q)).sequence.ssData i).eInfty)
      hi)).hom.comp (P.finiteSource q hq s t).toLinearMap)

/-- The target is scaled by the actual λ map from the smaller quotient.
In particular λ changes weight, and is not an endomorphism of one ambient. -/
def finiteTargetMap (P : NormalizedPageFamily H N F f)
    (q : ℕ) (hq : 0 < q) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n) (hkq : P.lambdaExponent n < q) :
    PageRepresentatives.cycles H Y (q - P.lambdaExponent n : ℕ) (s + n, t + n) →ₗ[ℤ]
      (((P.finite q hq).ess (P.degree s t)).ssData
        ((s, 1) + ((P.finite q hq).ess (P.degree s t)).diffDeg n)).V := by
  let D := P.finite q hq
  let k := P.lambdaExponent n
  let i : Tridegree := (s + n, t + n, t + n - k)
  have hk : (k : ℤ) = n - normalizedExponent H f :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hn)
  have hi : i = (s + n, (P.degree s t).1 + (s + n), (P.degree s t).2) := by
    dsimp [i, degree]
    ext <;> simp <;> omega
  exact (eqToHom (congrArg (fun p => ((D.ess (P.degree s t)).ssData p).V)
    (D.target_index (P.degree s t) n s).symm)).hom.comp
    ((D.targetIso (s + n) (P.degree s t)).inv.hom.comp
      ((eqToHom (congrArg (fun j =>
        ((F.obj (XModLambdaN (N.functor.obj Y) q)).sequence.ssData j).eInfty) hi)).hom.comp
        (((F.functor.map (P.targetTower.lambdaInclusion k q hkq)).eInftyMap i).hom.comp
          (P.finiteTarget q k hkq (s + n) (t + n)).toLinearMap)))

def infiniteSourceMap (P : NormalizedPageFamily H N F f) (s t : ℤ) :
    PageRepresentatives.permanentCycles H X (s, t) →ₗ[ℤ]
      ((P.infinite.ess (P.degree s t)).ssData (s, 1)).V := by
  have hi : (s, t, t + (normalizedExponent H f : ℤ)) =
      (s, (P.degree s t).1 + s, (P.degree s t).2) := by simp [degree]
  exact (P.infinite.sourceIso s (P.degree s t)).inv.hom.comp
    ((eqToHom (congrArg (fun i =>
      ((F.obj (normalizedSource H N f)).sequence.ssData i).eInfty) hi)).hom.comp
      (P.infiniteSource s t).toLinearMap)

def infiniteTargetMap (P : NormalizedPageFamily H N F f) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n) :
    PageRepresentatives.permanentCycles H Y (s + n, t + n) →ₗ[ℤ]
      ((P.infinite.ess (P.degree s t)).ssData
        ((s, 1) + (P.infinite.ess (P.degree s t)).diffDeg n)).V := by
  let k := P.lambdaExponent n
  let i : Tridegree := (s + n, t + n, t + n - k)
  have hk : (k : ℤ) = n - normalizedExponent H f :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hn)
  have hi : i = (s + n, (P.degree s t).1 + (s + n), (P.degree s t).2) := by
    dsimp [i, degree]
    ext <;> simp <;> omega
  exact (eqToHom (congrArg (fun p => (P.infinite.ess (P.degree s t)).ssData p |>.V)
    (P.infinite.target_index (P.degree s t) n s).symm)).hom.comp
    ((P.infinite.targetIso (s + n) (P.degree s t)).inv.hom.comp
      ((eqToHom (congrArg (fun j => ((F.obj (N.functor.obj Y)).sequence.ssData j).eInfty)
        hi)).hom.comp
        (((F.functor.map (lambdaPow k (N.functor.obj Y))).eInftyMap i).hom.comp
          (P.infiniteTarget k (s + n) (t + n)).toLinearMap)))

end NormalizedPageFamily
end
end KIP126.Synthetic.PageExtension
