module

public import KIP126.AdamsSynthetic.Coherence

set_option backward.isDefEq.respectTransparency false

@[expose] section

/-! Maps and finite triangles on the actual chosen λ-power cofibers.
Functoriality of the chosen cofiber maps is explicit input. Restriction and
triangle data do not assert completeness, boundedness, or convergence. -/

namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

public noncomputable def XModLambdaN.incl (X : Syn) (n : ℕ) : X ⟶ XModLambdaN X n :=
  HasFunctorialCofiber.cofibι (lambdaPow n X)

public noncomputable def XModLambdaN.proj (X : Syn) (n : ℕ) :
    XModLambdaN X n ⟶ ((SyntheticCategory.biShift (0, -(n : ℤ))).obj X)⟦(1 : ℤ)⟧ :=
  HasFunctorialCofiber.cofibδ (lambdaPow n X)

/-- The map supplied by the same chosen cofiber construction. No identity
or composition law for this choice is asserted by the minimal cofiber class. -/
public noncomputable def XModLambdaN.map {X Y : Syn} (f : X ⟶ Y) (n : ℕ) :
    XModLambdaN X n ⟶ XModLambdaN Y n :=
  HasFunctorialCofiber.cofibMap (lambdaPow n X) (lambdaPow n Y)
    ((SyntheticCategory.biShift (0, -(n : ℤ))).map f) f (lambdaPow_naturality n f)

/-- This is the actual λⁿ cofiber triangle. The definition makes no
inverse-limit or completeness assertion. -/
public noncomputable def XModLambdaN.cofiberTriangle (X : Syn) (n : ℕ) : Triangle Syn :=
  Triangle.mk (lambdaPow n X) (XModLambdaN.incl X n) (XModLambdaN.proj X n)

end KIP126.Synthetic.Context

namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

public theorem XModLambdaN.incl_naturality {X Y : Syn} (f : X ⟶ Y) (n : ℕ) :
    f ≫ XModLambdaN.incl Y n = XModLambdaN.incl X n ≫ XModLambdaN.map f n :=
  HasFunctorialCofiber.cofibMap_ι (lambdaPow n X) (lambdaPow n Y)
    ((SyntheticCategory.biShift (0, -(n : ℤ))).map f) f (lambdaPow_naturality n f)

public theorem XModLambdaN.proj_naturality {X Y : Syn} (f : X ⟶ Y) (n : ℕ) :
    XModLambdaN.map f n ≫ XModLambdaN.proj Y n =
      XModLambdaN.proj X n ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(n : ℤ))).map f) :=
  HasFunctorialCofiber.cofibMap_δ (lambdaPow n X) (lambdaPow n Y)
    ((SyntheticCategory.biShift (0, -(n : ℤ))).map f) f (lambdaPow_naturality n f)

public theorem XModLambdaN.cofiberTriangle_distinguished (X : Syn) (n : ℕ) :
    XModLambdaN.cofiberTriangle X n ∈ distTriang Syn :=
  HasFunctorialCofiber.cofib_distinguished (lambdaPow n X)

public theorem XModLambdaN.lambdaPow_comp_incl (X : Syn) (n : ℕ) :
    lambdaPow n X ≫ XModLambdaN.incl X n = 0 :=
  comp_distTriang_mor_zero₁₂ _ (XModLambdaN.cofiberTriangle_distinguished X n)

public theorem XModLambdaN.incl_comp_proj (X : Syn) (n : ℕ) :
    XModLambdaN.incl X n ≫ XModLambdaN.proj X n = 0 :=
  comp_distTriang_mor_zero₂₃ _ (XModLambdaN.cofiberTriangle_distinguished X n)

end KIP126.Synthetic.Context

namespace KIP126.Synthetic.Context
open CategoryTheory KIP126.StableHomotopy
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
public structure LambdaQuotientFunctoriality : Prop where
  map_id : ∀ (X : Syn) (n : ℕ), XModLambdaN.map (𝟙 X) n = 𝟙 _
  map_comp : ∀ {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ),
    XModLambdaN.map (f ≫ g) n = XModLambdaN.map f n ≫ XModLambdaN.map g n

end KIP126.Synthetic.Context

namespace KIP126.Synthetic.Context

open CategoryTheory KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The chosen cofiber map of the proved λ-power factorization square.
Both its source and target are the existing `XModLambdaN` objects. This
construction alone does not assert identity or composition laws for the
choice of `HasFunctorialCofiber.cofibMap`. -/
public noncomputable def XModLambdaN.restriction (coh : BiShiftCoherence Syn)
    (X : Syn) (i j : ℕ) (hij : i ≤ j) : XModLambdaN X j ⟶ XModLambdaN X i :=
  HasFunctorialCofiber.cofibMap (lambdaPow j X) (lambdaPow i X)
    (lambdaRestrictionSourceMap i j hij X) (𝟙 X)
    (by simpa only [lambdaDegree, Category.comp_id] using
      lambdaRestrictionSourceMap_commutes coh i j hij X)

end KIP126.Synthetic.Context

namespace KIP126.Synthetic.Context

open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- A finite λ–ρ–δ triangle on the actual quotients, including its
compatibility with multiplication by the existing `lambdaPow i X`. -/
public structure LambdaRhoDeltaTriangle (X : Syn) (i j : ℕ) where
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
public structure FiniteLambdaQuotientTower (X : Syn) where
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

namespace KIP126.Synthetic.Context

open CategoryTheory KIP126.StableHomotopy

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {X Y : Syn}

/-- All components are the actual `XModLambdaN.map f n`; this record supplies
their compatibility with the specified restrictions and λ–ρ–δ triangles. -/
public structure FiniteLambdaQuotientTower.Hom (TX : FiniteLambdaQuotientTower X)
    (TY : FiniteLambdaQuotientTower Y) (f : X ⟶ Y) : Prop where
  rho_naturality : ∀ {i j : ℕ} (hij : i ≤ j),
    TX.rho i j hij ≫ XModLambdaN.map f i =
      XModLambdaN.map f j ≫ TY.rho i j hij
  lambda_naturality : ∀ {i j : ℕ} (hi : 0 < i) (hij : i < j),
    (SyntheticCategory.biShift (0, -(i : ℤ))).map
          (XModLambdaN.map f (j - i)) ≫
        (TY.triangle hi hij).lambdaMap =
      (TX.triangle hi hij).lambdaMap ≫ XModLambdaN.map f j
  delta_naturality : ∀ {i j : ℕ} (hi : 0 < i) (hij : i < j),
    XModLambdaN.map f i ≫ (TY.triangle hi hij).delta =
      (TX.triangle hi hij).delta ≫
        (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -(i : ℤ))).map
            (XModLambdaN.map f (j - i)))

end KIP126.Synthetic.Context

namespace KIP126.Synthetic.Context
open CategoryTheory KIP126.StableHomotopy
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The quotient functor uses exactly the selected cofiber maps. -/
public noncomputable def LambdaQuotientFunctoriality.functor
    (Q : LambdaQuotientFunctoriality (Syn := Syn)) (n : ℕ) : Syn ⥤ Syn where
  obj X := XModLambdaN X n
  map f := XModLambdaN.map f n
  map_id X := Q.map_id X n
  map_comp f g := Q.map_comp f g n

/-- Restrictions commute with the actual inclusion, by the cofiber square. -/
public theorem XModLambdaN.restriction_incl (coh : BiShiftCoherence Syn)
    (X : Syn) (i j : ℕ) (hij : i ≤ j) :
    XModLambdaN.incl X j ≫ XModLambdaN.restriction coh X i j hij =
      XModLambdaN.incl X i := by
  have h := HasFunctorialCofiber.cofibMap_ι (lambdaPow j X) (lambdaPow i X)
    (lambdaRestrictionSourceMap i j hij X) (𝟙 X)
    (by simpa only [lambdaDegree, Category.comp_id] using
      lambdaRestrictionSourceMap_commutes coh i j hij X)
  simpa only [Category.id_comp, XModLambdaN.incl, XModLambdaN.restriction, XModLambdaN] using h.symm

/-- The selected finite quotient system and its structural coherences.
The restriction agreement rules out an unrelated family of identically named maps. -/
public structure LambdaQuotientSystem (Syn : Type u) [SyntheticCategory.{u,v} Syn]
    [HasFunctorialCofiber (C := Syn)] where
  coherence : BiShiftCoherence Syn
  functoriality : LambdaQuotientFunctoriality (Syn := Syn)
  tower : ∀ X : Syn, FiniteLambdaQuotientTower X
  restriction : ∀ (X : Syn) (i j : ℕ) (hij : i ≤ j),
    (tower X).rho i j hij = XModLambdaN.restriction coherence X i j hij
  natural : ∀ {X Y : Syn} (f : X ⟶ Y), FiniteLambdaQuotientTower.Hom (tower X) (tower Y) f
end KIP126.Synthetic.Context
