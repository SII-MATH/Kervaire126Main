module

public import KIP126.Def.Synthetic.Context.Coherence.Predicates
public import KIP126.Def.Synthetic.Context.LambdaPowers.Proofs

@[expose] public section

/-! Multiplication laws for the existing recursive λ powers. -/

namespace KIP126.Synthetic.Context

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The associativity condition specialized to the existing λ suspensions. -/
theorem BiShiftCoherence.lambdaShift_associativity (coh : BiShiftCoherence Syn)
    (i j k ij jk total : ℕ) (hij : i + j = ij) (hjk : j + k = jk)
    (htotal : ij + k = total) (htotal' : i + jk = total) (X : Syn) :
    (SyntheticCategory.biShift (lambdaDegree k)).map
          ((lambdaShiftAddIso i j ij hij).hom.app X) ≫
        (lambdaShiftAddIso ij k total htotal).hom.app X =
      (lambdaShiftAddIso j k jk hjk).hom.app
          ((SyntheticCategory.biShift (lambdaDegree i)).obj X) ≫
        (lambdaShiftAddIso i jk total htotal').hom.app X := by
  exact coh.associativity (lambdaDegree i) (lambdaDegree j) (lambdaDegree k)
    (lambdaDegree ij) (lambdaDegree jk) (lambdaDegree total) _ _ _ _ X

theorem BiShiftCoherence.lambdaShift_zero_left (coh : BiShiftCoherence Syn)
    (n : ℕ) (X : Syn) :
    (lambdaShiftAddIso 0 n n (Nat.zero_add n)).hom.app X =
      (SyntheticCategory.biShift (lambdaDegree n)).map (lambdaPow 0 X) := by
  exact coh.left_unit (lambdaDegree n) X

private theorem comp_transport {a b : ℤ × ℤ} (h : a = b) (X Y : Syn)
    (f : (SyntheticCategory.biShift a).obj X ⟶ Y) :
    eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj X) h) ≫
      (h ▸ f) = f := by
  subst b
  simp

/-- The defining successor equation, expressed through the same addition iso. -/
theorem lambdaPow_succ_comparison (n : ℕ) (X : Syn) :
    (lambdaShiftAddIso 1 n (n + 1) (by omega)).hom.app X ≫ lambdaPow (n + 1) X =
      (SyntheticCategory.biShift (lambdaDegree n)).map (SyntheticCategory.lam.app X) ≫
        lambdaPow n X := by
  simp only [lambdaShiftAddIso, biShiftAddIso, lambdaDegree,
    Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, lambdaPow]
  rw [Category.assoc, comp_transport]
  exact Iso.hom_inv_id_app_assoc
    (SyntheticCategory.biShift_comp (0, -1) (0, -(n : ℤ))) X _

theorem lambdaPow_succ_comparison_of_eq (n k : ℕ) (h : 1 + n = k) (X : Syn) :
    (lambdaShiftAddIso 1 n k h).hom.app X ≫ lambdaPow k X =
      (SyntheticCategory.biShift (lambdaDegree n)).map (SyntheticCategory.lam.app X) ≫
        lambdaPow n X := by
  have hk : k = n + 1 := by omega
  cases hk
  exact lambdaPow_succ_comparison n X

/-- The chosen unit coherence identifies the first existing power with λ. -/
theorem lambdaPow_one (coh : BiShiftCoherence Syn) (X : Syn) :
    lambdaPow 1 X = SyntheticCategory.lam.app X := by
  apply (cancel_epi (SyntheticCategory.biShift_zero.hom.app
    ((SyntheticCategory.biShift (0, -1)).obj X))).mp
  calc
    _ = (lambdaShiftAddIso 1 0 1 rfl).hom.app X ≫ lambdaPow 1 X := by
      rw [show (lambdaShiftAddIso 1 0 1 rfl).hom.app X =
          SyntheticCategory.biShift_zero.hom.app
            ((SyntheticCategory.biShift (0, -1)).obj X) from
        coh.right_unit (0, -1) X]
    _ = (SyntheticCategory.biShift (lambdaDegree 0)).map
          (SyntheticCategory.lam.app X) ≫ lambdaPow 0 X :=
      lambdaPow_succ_comparison_of_eq 0 1 rfl X
    _ = _ := SyntheticCategory.biShift_zero.hom.naturality (SyntheticCategory.lam.app X)

/-- Arbitrary power decomposition, proved for the original recursive powers.
The final degree equality records all indexing transports explicitly. -/
theorem lambdaPow_add_comparison (coh : BiShiftCoherence Syn)
    (i j k : ℕ) (h : i + j = k) (X : Syn) :
    (lambdaShiftAddIso i j k h).hom.app X ≫ lambdaPow k X =
      (SyntheticCategory.biShift (lambdaDegree j)).map (lambdaPow i X) ≫
        lambdaPow j X := by
  induction i generalizing k with
  | zero =>
    have hk : k = j := by omega
    cases hk
    rw [coh.lambdaShift_zero_left]
  | succ i ih =>
    apply (cancel_epi ((SyntheticCategory.biShift (lambdaDegree j)).map
      ((lambdaShiftAddIso 1 i (i + 1) (by omega)).hom.app X))).mp
    calc
      _ = (lambdaShiftAddIso i j (i + j) rfl).hom.app
            ((SyntheticCategory.biShift (lambdaDegree 1)).obj X) ≫
          ((lambdaShiftAddIso 1 (i + j) k (by omega)).hom.app X ≫
            lambdaPow k X) := by
        rw [← Category.assoc,
          coh.lambdaShift_associativity 1 i j (i + 1) (i + j) k
            (by omega) rfl h (by omega) X]
        simp only [Category.assoc]
      _ = (lambdaShiftAddIso i j (i + j) rfl).hom.app
            ((SyntheticCategory.biShift (lambdaDegree 1)).obj X) ≫
          ((SyntheticCategory.biShift (lambdaDegree (i + j))).map
            (SyntheticCategory.lam.app X) ≫ lambdaPow (i + j) X) := by
        rw [lambdaPow_succ_comparison_of_eq]
      _ = (SyntheticCategory.biShift (lambdaDegree j)).map
            ((SyntheticCategory.biShift (lambdaDegree i)).map
              (SyntheticCategory.lam.app X)) ≫
          ((lambdaShiftAddIso i j (i + j) rfl).hom.app X ≫
            lambdaPow (i + j) X) := by
        rw [← Category.assoc, ← NatTrans.naturality]
        simp only [Functor.comp_map, Functor.id_obj, Category.assoc]
      _ = (SyntheticCategory.biShift (lambdaDegree j)).map
            ((SyntheticCategory.biShift (lambdaDegree i)).map
              (SyntheticCategory.lam.app X)) ≫
          ((SyntheticCategory.biShift (lambdaDegree j)).map (lambdaPow i X) ≫
            lambdaPow j X) := by rw [ih (i + j) rfl]
      _ = _ := by
        rw [← Category.assoc, ← Functor.map_comp, ← lambdaPow_succ_comparison,
          Functor.map_comp, Category.assoc]

/-- The same decomposition with the comparison moved to the source. -/
theorem lambdaPow_add (coh : BiShiftCoherence Syn)
    (i j k : ℕ) (h : i + j = k) (X : Syn) :
    lambdaPow k X = (lambdaShiftAddIso i j k h).inv.app X ≫
      (SyntheticCategory.biShift (lambdaDegree j)).map (lambdaPow i X) ≫
        lambdaPow j X := by
  rw [← lambdaPow_add_comparison coh i j k h X]
  simp

/-- The precise commuting square used to form actual quotient restrictions. -/
theorem lambdaRestrictionSourceMap_commutes (coh : BiShiftCoherence Syn)
    (i j : ℕ) (hij : i ≤ j) (X : Syn) :
    lambdaRestrictionSourceMap i j hij X ≫ lambdaPow i X = lambdaPow j X := by
  simpa only [lambdaRestrictionSourceMap, Category.assoc] using
    (lambdaPow_add coh (j - i) i j (Nat.sub_add_cancel hij) X).symm

/-- The source map of the restriction square is natural before any cofiber
choice is made. -/
theorem lambdaRestrictionSourceMap_naturality (i j : ℕ) (hij : i ≤ j)
    {X Y : Syn} (f : X ⟶ Y) :
    (SyntheticCategory.biShift (lambdaDegree j)).map f ≫
        lambdaRestrictionSourceMap i j hij Y =
      lambdaRestrictionSourceMap i j hij X ≫
        (SyntheticCategory.biShift (lambdaDegree i)).map f := by
  dsimp only [lambdaRestrictionSourceMap]
  rw [← Category.assoc, NatTrans.naturality, Category.assoc]
  dsimp only [Functor.comp_map, lambdaDegree]
  rw [← Functor.map_comp, lambdaPow_naturality, Functor.map_comp, Category.assoc]

end KIP126.Synthetic.Context
