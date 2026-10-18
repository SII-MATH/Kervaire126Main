module

public import KIP126.AdamsSynthetic.Normalized
public import KIP126.AdamsSynthetic.Detection

@[expose] section

/-! Explicit filtration obligations on the same coefficient tower. The
factorization comparison and separation are supplied proofs, not new global
facts. Finite filtration is derived from separation. The boundedness statement
uses finite, rationally acyclic, two-local objects and still contains zero. -/

namespace KIP126.AdamsSynthetic
open CategoryTheory CategoryTheory.Limits MonoidalCategory Pretriangulated
open KIP126.StableHomotopy KIP126.Classical.Adams
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]

/-- The finite sphere/shift/cofiber closure, independently of the smaller
configuration selected by the main proof. -/
public inductive IsFiniteSpectrum : C → Prop where
  | sphere : IsFiniteSpectrum SphereSpectrum
  | shift {X : C} (n : ℤ) : IsFiniteSpectrum X → IsFiniteSpectrum (X⟦n⟧)
  | cofiber {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧} :
      Triangle.mk f g h ∈ distTriang C →
      IsFiniteSpectrum X → IsFiniteSpectrum Y → IsFiniteSpectrum Z

/-- Homology uses this coefficient object and the actual tensor product. -/
public abbrev ModTwoHomology (H : ModTwoCoefficients C) (n : ℤ) (X : C) :=
  HomotopyGroup n (H.object ⊗ X)

public def modTwoHomologyMap (H : ModTwoCoefficients C) {X Y : C}
    (f : X ⟶ Y) (n : ℤ) : ModTwoHomology H n X →+ ModTwoHomology H n Y :=
  inducedMap (H.object ◁ f) n

public def ZeroOnModTwoHomology (H : ModTwoCoefficients C)
    {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ n, ∀ x : ModTwoHomology H n X, modTwoHomologyMap H f n x = 0

/-- Positive-length factorizations through maps zero on the same HF₂ homology. -/
public inductive AdamsMapFactorization (H : ModTwoCoefficients C) :
    {X Y : C} → ℕ → (X ⟶ Y) → Prop where
  | single {X Y : C} (f : X ⟶ Y) :
      ZeroOnModTwoHomology H f → AdamsMapFactorization H 1 f
  | prepend {X Y Z : C} {n : ℕ} (f : X ⟶ Y) (g : Y ⟶ Z) :
      ZeroOnModTwoHomology H f → AdamsMapFactorization H n g →
      AdamsMapFactorization H (n + 1) (f ≫ g)

/-- The old lower-bound responsibility, without its redundant value wrapper. -/
public def FactorizationFiltration (H : ModTwoCoefficients C)
    {X Y : C} (f : X ⟶ Y) (s : ℤ) : Prop :=
  ∀ n : ℕ, 0 < n → (n : ℤ) ≤ s → AdamsMapFactorization H n f

variable {H : ModTwoCoefficients C} {A : ClassicalAdamsFamily C}

/-- Integer filtration is the actual target-tower factorization; negative
indices are stage zero, as in the tower itself. -/
public def MapAdamsFiltration (P : ClassicalTowerPresentation H.unit A)
    {X Y : C} (f : X ⟶ Y) (s : ℤ) : Prop :=
  MapFiltrationAtLeast P f s.toNat

public def ExactMapAdamsFiltration (P : ClassicalTowerPresentation H.unit A)
    {X Y : C} (f : X ⟶ Y) (s : ℤ) : Prop :=
  MapAdamsFiltration P f s ∧ ¬ MapAdamsFiltration P f (s + 1)

/-- The comparison is an explicit obligation for the chosen coefficient tower. -/
public structure FactorizationFiltrationComparison
    (P : ClassicalTowerPresentation H.unit A) : Prop where
  agrees : ∀ {X Y : C} (f : X ⟶ Y) (s : ℤ),
    FactorizationFiltration H f s ↔ MapAdamsFiltration P f s

public theorem mapAdamsFiltration_zero (P : ClassicalTowerPresentation H.unit A)
    {X Y : C} (f : X ⟶ Y) : MapAdamsFiltration P f 0 := by
  refine ⟨f ≫ (P.tower Y).zeroIso.inv, ?_⟩
  change (f ≫ (P.tower Y).zeroIso.inv) ≫ (P.tower Y).projection 0 = f
  rw [AbstractAdamsTower.projection, AbstractAdamsTower.map_self]
  change (f ≫ (P.tower Y).zeroIso.inv) ≫
    (𝟙 _ ≫ (P.tower Y).zeroIso.hom) = f
  rw [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

public theorem mapAdamsFiltration_mono (P : ClassicalTowerPresentation H.unit A)
    {X Y : C} (f : X ⟶ Y) {s t : ℤ} (hst : s ≤ t)
    (ht : MapAdamsFiltration P f t) : MapAdamsFiltration P f s := by
  obtain ⟨a, ha⟩ := ht
  refine ⟨a ≫ (P.tower Y).mapAt (show (s.toNat : ℤ) ≤ t.toNat by omega), ?_⟩
  rw [Category.assoc, AbstractAdamsTower.projection_compat]
  exact ha

/-- Odd torsion includes zero. It must not be replaced by mere nonzeroness. -/
public def IsOddTorsionMap {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ n : ℕ, Odd n ∧ 0 < n ∧ n • f = 0

/-- Original foundational proof responsibility, retained as an explicit
proof parameter. It is not an automatically supplied literature fact. -/
public def FiniteMapSeparation (P : ClassicalTowerPresentation H.unit A) : Prop :=
  ∀ {X Y : C}, IsFiniteSpectrum X → IsFiniteSpectrum Y →
    ∀ f : X ⟶ Y, (∀ s : ℤ, MapAdamsFiltration P f s) → IsOddTorsionMap f

public theorem separated_factorization (P : ClassicalTowerPresentation H.unit A)
    (comparison : FactorizationFiltrationComparison P) (separation : FiniteMapSeparation P)
    {X Y : C} (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y)
    (hf : ∀ s : ℤ, FactorizationFiltration H f s) : IsOddTorsionMap f :=
  separation hX hY f (fun s => (comparison.agrees f s).mp (hf s))

/-- Finite exact filtration is derived, with the finite-spectrum and
non-odd-torsion conditions that the old unqualified statement omitted. -/
public theorem finite_filtration_of_not_odd (P : ClassicalTowerPresentation H.unit A)
    (separation : FiniteMapSeparation P) {X Y : C}
    (hX : IsFiniteSpectrum X) (hY : IsFiniteSpectrum Y) (f : X ⟶ Y)
    (hf : ¬ IsOddTorsionMap f) : ∃ s : ℤ, ExactMapAdamsFiltration P f s := by
  classical
  have failure : ∃ n : ℕ, ¬ MapAdamsFiltration P f (n : ℤ) := by
    by_contra h
    push Not at h
    apply hf
    apply separation hX hY f
    intro s
    exact h s.toNat
  let n := Nat.find failure
  have hn : ¬ MapAdamsFiltration P f (n : ℤ) := Nat.find_spec failure
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    exact hn (by simpa [hn0] using mapAdamsFiltration_zero P f)
  refine ⟨((n - 1 : ℕ) : ℤ), ?_, ?_⟩
  · by_contra hprev
    have hle := Nat.find_min' failure hprev
    change n ≤ n - 1 at hle
    omega
  · have heq : ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by omega
    simpa only [heq] using hn

/-- Rational acyclicity expressed intrinsically by torsion of actual
homotopy groups; no unspecified `True` hypothesis is used. -/
public def RationallyAcyclic (X : C) : Prop :=
  ∀ n : ℤ, ∀ x : HomotopyGroup n X, ∃ k : ℕ, 0 < k ∧ k • x = 0

/-- Odd multiplication is invertible on the actual homotopy groups. This
excludes the odd torsion that otherwise survives every mod-two filtration. -/
public def HomotopyTwoLocal (X : C) : Prop :=
  ∀ n : ℤ, ∀ k : ℕ, Odd k →
    Function.Bijective (fun x : HomotopyGroup n X => k • x)

/-- A corrected boundedness input. A producer must justify this assertion
on finite, rationally acyclic, two-local spectra in its chosen system. -/
public structure AdamsBoundednessInput (P : ClassicalTowerPresentation H.unit A) : Prop where
  bounded : ∀ X : C, IsFiniteSpectrum X → RationallyAcyclic X → HomotopyTwoLocal X →
    ∀ i : ℤ, ∃ N : ℤ, ∀ s : ℤ, N < s → (P.tower X).filtrationSubmodule s i = ⊥

public theorem AdamsBoundednessInput.excludes_nonzero
    {P : ClassicalTowerPresentation H.unit A} (B : AdamsBoundednessInput P)
    (X : C) (hX : IsFiniteSpectrum X) (hr : RationallyAcyclic X) (hl : HomotopyTwoLocal X)
    (i : ℤ) : ∃ N : ℤ, ∀ s : ℤ, N < s → ∀ x : HomotopyGroup i X,
      x ≠ 0 → x ∉ (P.tower X).filtrationSubmodule s i := by
  obtain ⟨N,hN⟩ := B.bounded X hX hr hl i
  refine ⟨N, fun s hs x hx hmem => ?_⟩
  rw [hN s hs] at hmem
  exact hx hmem

public theorem filtration_contains_zero (P : ClassicalTowerPresentation H.unit A)
    (X : C) (s i : ℤ) : (0 : HomotopyGroup i X) ∈ (P.tower X).filtrationSubmodule s i :=
  Submodule.zero_mem _

end
end KIP126.AdamsSynthetic
