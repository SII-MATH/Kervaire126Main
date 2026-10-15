module

public import KIP126.Def.Synthetic.Sphere.Homotopy.Predicates
public import KIP126.Def.Synthetic.Context.Coherence.Proofs
public import Mathlib.CategoryTheory.Triangulated.Yoneda

@[expose] public section

namespace KIP126.Synthetic.Context
open CategoryTheory CategoryTheory.Pretriangulated KIP126.StableHomotopy
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The quotient predicate is equivalent to actual factorization through λʳ,
by exactness of its specified distinguished cofiber triangle. -/
theorem vanishesModLambda_iff_factors {m n : ℤ} {X : Syn} (r : ℕ)
    (x : BiHom m n X) :
    VanishesModLambda r x ↔
      ∃ y : Smn m n ⟶ (SyntheticCategory.biShift (0, -(r : ℤ))).obj X,
        y ≫ lambdaPow r X = x := by
  let T := XModLambdaN.cofiberTriangle X r
  have hT : T ∈ distTriang Syn := HasFunctorialCofiber.cofib_distinguished _
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := T.coyoneda_exact₂ hT x hx
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    change (y ≫ lambdaPow r X) ≫ XModLambdaN.incl X r = 0
    have hz : lambdaPow r X ≫ XModLambdaN.incl X r = 0 :=
      comp_distTriang_mor_zero₁₂ T hT
    rw [Category.assoc, hz, Limits.comp_zero]

set_option backward.isDefEq.respectTransparency false in
omit [HasFunctorialCofiber (C := Syn)] in
/-- Injectivity of the one-step λ action throughout the lower weight range
gives injectivity of every finite λ power. -/
theorem lambda_powers_injective_of_lower_weights
    (coh : BiShiftCoherence Syn) (m wt : ℤ) (X : Syn)
    (h : ∀ wt' : ℤ, wt' ≤ wt → LambdaInjectiveAt m wt' X) :
    LambdaPowersInjectiveAt m wt X := by
  have one (k : ℕ) : Function.Injective (fun a :
      (SyntheticCategory.biShift (0,-(k : ℤ))).obj (Smn (Syn := Syn) m wt) ⟶ X =>
      SyntheticCategory.lam.app _ ≫ a) := by
    let e : Smn (Syn := Syn) m (wt-k) ≅
        (SyntheticCategory.biShift (0,-(k : ℤ))).obj (Smn m wt) :=
      eqToIso (by dsimp only [Smn]; congr 1; simp [sub_eq_add_neg]) ≪≫
        ((SyntheticCategory.biShift_comp (m,wt) (0,-(k : ℤ))).app S_0_0).symm
    intro a b hab
    apply (cancel_epi e.hom).mp
    apply h (wt-k) (by omega)
    dsimp only [lambdaAction]
    have hc : SyntheticCategory.lam.app (Smn (Syn := Syn) m (wt-k)) ≫ (e.hom ≫ a) =
        SyntheticCategory.lam.app (Smn (Syn := Syn) m (wt-k)) ≫ (e.hom ≫ b) := by
      have hn := SyntheticCategory.lam.naturality e.hom
      dsimp only [Functor.id_map] at hn
      rw [← Category.assoc, ← Category.assoc, ← hn]
      simpa only [Category.assoc] using
        congrArg (fun z => (SyntheticCategory.biShift (0,-1)).map e.hom ≫ z) hab
    exact congrArg (fun z => _ ≫ _ ≫ z) hc
  have powers (k : ℕ) : Function.Injective (fun a : BiHom m wt X =>
      lambdaPow k (Smn m wt) ≫ a) := by
    induction k with
    | zero =>
      intro a b hab
      exact (cancel_epi (SyntheticCategory.biShift_zero.hom.app (Smn m wt))).mp hab
    | succ k ih =>
      intro a b hab
      apply ih
      apply one k
      rw [lambdaPow_add coh k 1 (k+1) rfl, lambdaPow_one coh] at hab
      have hc := (cancel_epi ((lambdaShiftAddIso k 1 (k+1) rfl).inv.app (Smn (Syn := Syn) m wt))).mp
        (by simpa only [Category.assoc] using hab)
      have hn := SyntheticCategory.lam.naturality (lambdaPow k (Smn (Syn := Syn) m wt))
      dsimp only [Functor.id_map] at hn
      change (SyntheticCategory.biShift (0,-1)).map (lambdaPow k (Smn m wt)) ≫
        (SyntheticCategory.lam.app (Smn m wt) ≫ a) =
        (SyntheticCategory.biShift (0,-1)).map (lambdaPow k (Smn m wt)) ≫
        (SyntheticCategory.lam.app (Smn m wt) ≫ b) at hc
      rw [← Category.assoc, ← Category.assoc] at hc
      rw [hn] at hc
      simpa only [Category.assoc] using hc
  intro k a b hab
  apply powers k
  dsimp only [lambdaMultiply] at hab
  have hc := (cancel_epi (eqToHom (by congr 1; simp))).mp hab
  exact (cancel_epi ((SyntheticCategory.biShift_comp (m,wt) (0,-(k : ℤ))).inv.app S_0_0)).mp
    (by simpa only [Category.assoc] using hc)

end KIP126.Synthetic.Context
