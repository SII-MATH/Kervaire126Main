module

public import KIP126.Def.Synthetic.QuotientMap.Data

@[expose] public section

/-!
# Coherent restrictions on the specified finite λ quotients

Every object is the existing `XModLambdaN X n`. Besides the historical
triangle and composition fields, compatibility with the actual quotient
inclusions binds both `rho` and `lambdaMap` to the specified λ powers.

These are explicit witness types, not constructions of their inhabitants.
No completeness or unrestricted inverse-limit claim is included.

## Laws still needed by a construction from the minimal context

The following equations describe missing coherence; they are not hypotheses
silently added to `SyntheticCategory`, nor theorems proved in this file.
Write `S a = biShift a`, `κ a b = (biShift_comp a b).hom`, and
`e = biShift_zero.hom`. After transporting degree indices along associativity,
zero, and commutativity in `ℤ × ℤ`, the relevant component equations are:

* `(S c).map ((κ a b).app X) ≫ (κ (a+b) c).app X =
    (κ b c).app ((S a).obj X) ≫ (κ a (b+c)).app X` (reassociation).
* `(κ a 0).app X = e.app ((S a).obj X)` and
  `(κ 0 a).app X = (S a).map (e.app X)` (unit laws).
* For `l = (0,-1)`,
  `lam.app ((S a).obj X) = (κ a l).app X ≫
    (biShift_comp l a).inv.app X ≫ (S a).map (lam.app X)`
  (λ commutes with the specified suspension comparisons).

In particular, a construction must justify the following multiplication law
for the *existing* recursive powers, with `p n = (0,-(n : ℤ))` and the
degree equality `p (i+j) = p i + p j` inserted on the right:

`lambdaPow (i+j) X = (biShift_comp (p i) (p j)).inv.app X ≫
  (S (p j)).map (lambdaPow i X) ≫ lambdaPow j X`.

Transporting the cofiber of a power through `S (p i)` also requires a chosen
`CommShift ℤ` structure and preservation of distinguished triangles for that
functor. These are not fields of the current minimal synthetic context.

For the specified cofiber maps, the missing functoriality equations are
`cofibMap f f (𝟙 _) (𝟙 _) _ = 𝟙 (cofib f)` and, for two composable
commuting squares `(α,β)` and `(α',β')`,
`cofibMap f g α β _ ≫ cofibMap g h α' β' _ =
  cofibMap f h (α ≫ α') (β ≫ β') _`.
Only the inclusion and boundary squares are currently supplied by
`HasFunctorialCofiber`; consequently this slice does not claim that
`XModLambdaN.map` is a functor or that tower morphisms form a category.

The records below accept the resulting finite tower and its displayed
compatibilities explicitly. They do not construct a homotopy inverse limit,
a completion map, or the E-nilpotent-completeness hypothesis required for
the BHS completion comparison.
-/

namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- A finite λ–ρ–δ triangle on the actual quotients, including its
compatibility with multiplication by the existing `lambdaPow i X`. -/
structure LambdaRhoDeltaTriangle (X : Syn) (i j : ℕ) where
  i_pos : 0 < i
  i_lt_j : i < j
  lambdaMap :
    (SyntheticCategory.biShift (0, -(i : ℤ))).obj (XModLambdaN X (j - i)) ⟶
      XModLambdaN X j
  rho : XModLambdaN X j ⟶ XModLambdaN X i
  delta : XModLambdaN X i ⟶
    ((SyntheticCategory.biShift (0, -(i : ℤ))).obj
      (XModLambdaN X (j - i)))⟦(1 : ℤ)⟧
  distinguished : Triangle.mk lambdaMap rho delta ∈ distTriang Syn
  lambda_quotient :
    (SyntheticCategory.biShift (0, -(i : ℤ))).map (XModLambdaN.incl X (j - i)) ≫
        lambdaMap = lambdaPow i X ≫ XModLambdaN.incl X j
  rho_quotient : XModLambdaN.incl X j ≫ rho = XModLambdaN.incl X i

/-- Restriction maps between the existing finite λ quotients with exact
identity, composition, quotient, and triangle compatibility laws. -/
structure FiniteLambdaQuotientTower (X : Syn) where
  rho : ∀ (i j : ℕ), i ≤ j → (XModLambdaN X j ⟶ XModLambdaN X i)
  rho_id : ∀ i, rho i i le_rfl = 𝟙 (XModLambdaN X i)
  rho_comp : ∀ {k i j : ℕ} (hki : k ≤ i) (hij : i ≤ j),
    rho i j hij ≫ rho k i hki = rho k j (hki.trans hij)
  rho_quotient : ∀ {i j : ℕ} (hij : i ≤ j),
    XModLambdaN.incl X j ≫ rho i j hij = XModLambdaN.incl X i
  triangle : ∀ {i j : ℕ}, 0 < i → i < j → LambdaRhoDeltaTriangle X i j
  triangle_rho : ∀ {i j : ℕ} (hi : 0 < i) (hij : i < j),
    (triangle hi hij).rho = rho i j hij.le

end KIP126.Synthetic.Context
