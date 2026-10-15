module

public import KIP126.Def.Synthetic.PageExtension.Predicates
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section

/-!
# Classical ambiguity of normalized page extensions

MainPaper Remark `def:fErextess` identifies ambiguity with ordinary Adams
boundaries B_(1+n-e), plus shorter extension images. The latter are defined
here from actual extension witnesses for the same fixed family P. These
definitions do not assert compatibility of P's comparison isomorphisms.
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
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}
  {P : NormalizedPageFamily H N F f}

/-- Reindex the actual E₂ target to the degree of a shorter extension.
Both displayed bidegrees are equal; this introduces no comparison choice. -/
def shorterTargetTransport (H : Mod2EilenbergMacLane (C := C)) (Y : C)
    (n s t : ℤ) (a : ℕ) :
    PageRepresentatives.Ambient H Y (s + n, t + n) →ₗ[ℤ]
      PageRepresentatives.Ambient H Y
        (s + a + (n - a), t + a + (n - a)) :=
  (eqToHom (congrArg (PageRepresentatives.Ambient H Y)
    (show (s + n, t + n) = (s + a + (n - a), t + a + (n - a)) by
      ext <;> omega))).hom

namespace FiniteExtensionWitness
variable {r : ℕ} {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
  {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
  (W : FiniteExtensionWitness P r n s t x y)

/-- The paper's actual target cycle space Z_(r-1-n+e). -/
abbrev TargetCycles (_W : FiniteExtensionWitness P r n s t x y) : Type v :=
  PageRepresentatives.cycles H Y (r - 1 - P.lambdaExponent n : ℕ) (s + n, t + n)

/-- Actual subtype inclusion, with the canonical integer module structure
used by the fixed family comparisons. -/
def targetInclusion : W.TargetCycles →ₗ[ℤ]
    PageRepresentatives.Ambient H Y (s + n, t + n) where
  toFun z := z.val
  map_add' _ _ := rfl
  map_smul' a z := map_intCast_smul
    (PageRepresentatives.cycles H Y (r - 1 - P.lambdaExponent n : ℕ)
      (s + n, t + n)).subtype.toAddMonoidHom ℤ ℤ a z

/-- The actual λ-scaled target comparison used by this witness. -/
def scaledTargetMap :=
  P.finiteTargetMap (r - 1) (Nat.sub_pos_of_lt W.page_ge_two) n s t
    W.exponent_le_length W.exponent_lt_quotient

/-- Ordinary Adams ambiguity restricted to the actual target cycles. -/
def ordinaryBoundaries : Submodule ℤ W.TargetCycles :=
  (PageRepresentatives.boundaries H Y (1 + n - normalizedExponent H f)
    (s + n, t + n)).comap W.targetInclusion

/-- Span of genuine shorter page-extension targets in the same final degree.
The candidate uses page r-a, source (s+a,t+a), length n-a; consequently its
target cycle level is again r-1-n+e. Neither essentiality nor nonzero targets
are imposed when forming the image span. -/
def shorterImages : Submodule ℤ W.TargetCycles :=
  Submodule.span ℤ { z | ∃ a : ℕ, 0 < a ∧ a ≤ r - 2 ∧
    (normalizedExponent H f : ℤ) ≤ n - a ∧
    ∃ x' : PageRepresentatives.Ambient H X (s + a, t + a),
      FinitePageExtension P (r - a) (n - a) (s + a) (t + a) x'
        (shorterTargetTransport H Y n s t a z.val) }

/-- The actual ESS boundary submodule, at the same differential target and
raw page index as the witness's complete target coset. -/
def essBoundaries :=
  let E := (P.finite (r - 1) (Nat.sub_pos_of_lt W.page_ge_two)).ess (P.degree s t)
  LinearMap.range ((E.ssData ((s, 1) + E.diffDeg n)).B
    (↑(n - E.r₀).toNat : WithTop ℕ)).arrow.hom

end FiniteExtensionWitness

namespace InfiniteExtensionWitness
variable {n s t : ℤ} {x : PageRepresentatives.Ambient H X (s, t)}
  {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
  (W : InfiniteExtensionWitness P n s t x y)

/-- The untruncated target consists of permanent actual E₂ representatives. -/
abbrev TargetCycles (_W : InfiniteExtensionWitness P n s t x y) : Type v :=
  PageRepresentatives.permanentCycles H Y (s + n, t + n)

def targetInclusion : W.TargetCycles →ₗ[ℤ]
    PageRepresentatives.Ambient H Y (s + n, t + n) where
  toFun z := z.val
  map_add' _ _ := rfl
  map_smul' a z := map_intCast_smul
    (PageRepresentatives.permanentCycles H Y (s + n, t + n)).subtype.toAddMonoidHom
      ℤ ℤ a z

def scaledTargetMap := P.infiniteTargetMap n s t W.exponent_le_length

def ordinaryBoundaries : Submodule ℤ W.TargetCycles :=
  (PageRepresentatives.boundaries H Y (1 + n - normalizedExponent H f)
    (s + n, t + n)).comap W.targetInclusion

/-- Shorter untruncated extensions for this same P, with permanent source
and target representatives and the same final target degree. -/
def shorterImages : Submodule ℤ W.TargetCycles :=
  Submodule.span ℤ { z | ∃ a : ℕ, 0 < a ∧
    (normalizedExponent H f : ℤ) ≤ n - a ∧
    ∃ x' : PageRepresentatives.Ambient H X (s + a, t + a),
      InfinitePageExtension P (n - a) (s + a) (t + a) x'
        (shorterTargetTransport H Y n s t a z.val) }

def essBoundaries (_W : InfiniteExtensionWitness P n s t x y) :=
  let E := P.infinite.ess (P.degree s t)
  LinearMap.range ((E.ssData ((s, 1) + E.diffDeg n)).B
    (↑(n - E.r₀).toNat : WithTop ℕ)).arrow.hom

end InfiniteExtensionWitness
end
end KIP126.Synthetic.PageExtension
