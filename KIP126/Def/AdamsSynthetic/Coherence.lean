module

public import KIP126.Def.AdamsSynthetic.Context

@[expose] section

/-! Coherence and derived power laws of the same given synthetic shifts and λ.
Adapted from the fixed review source; no replacement shifts or powers are selected. -/

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The same recursive λ powers, constructed as natural transformations.
Their components are proved equal to the existing `lambdaPow` separately. -/
public noncomputable def lambdaPowNatTrans : (n : ℕ) →
    SyntheticCategory.biShift (0, -(n : ℤ)) ⟶ 𝟭 Syn
  | 0 => SyntheticCategory.biShift_zero.hom
  | n + 1 => by
      have step : SyntheticCategory.biShift ((0 : ℤ), -1) ⋙
          SyntheticCategory.biShift ((0 : ℤ), -(n : ℤ)) ⟶ 𝟭 Syn :=
        Functor.whiskerRight SyntheticCategory.lam
            (SyntheticCategory.biShift ((0 : ℤ), -(n : ℤ))) ≫
          lambdaPowNatTrans n
      have result : SyntheticCategory.biShift ((0, -1) + (0, -(n : ℤ))) ⟶ 𝟭 Syn :=
        (SyntheticCategory.biShift_comp (0, -1) (0, -(n : ℤ))).inv ≫ step
      have heq : ((0 : ℤ), (-1 : ℤ)) + ((0 : ℤ), -(n : ℤ)) =
          ((0 : ℤ), -(↑(n + 1) : ℤ)) := by simp
      exact heq ▸ result

end KIP126.Synthetic.Context

namespace KIP126.Synthetic.Context

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

theorem transported_app {a b : ℤ × ℤ} (hab : a = b)
    (α : SyntheticCategory.biShift a ⟶ 𝟭 Syn) (X : Syn) :
    (hab ▸ α).app X = (hab ▸ α.app X) := by
  subst b
  rfl

/-- This natural-transformation presentation does not choose a different λ power. -/
@[simp] public theorem lambdaPowNatTrans_app (n : ℕ) (X : Syn) :
    (lambdaPowNatTrans n).app X = lambdaPow n X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [lambdaPowNatTrans, lambdaPow, transported_app, NatTrans.comp_app,
      Functor.whiskerRight_app, ih]

/-- Every existing λ-power is natural in the synthetic object. -/
public theorem lambdaPow_naturality (n : ℕ) {X Y : Syn} (f : X ⟶ Y) :
    (SyntheticCategory.biShift (0, -(n : ℤ))).map f ≫ lambdaPow n Y =
      lambdaPow n X ≫ f := by
  have h := (lambdaPowNatTrans n).naturality f
  dsimp only [Functor.id_obj, Functor.id_map] at h
  simpa only [lambdaPowNatTrans_app] using h

end KIP126.Synthetic.Context

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The specified addition comparison, transported to a named total degree. -/
public noncomputable def biShiftAddIso (a b c : ℤ × ℤ) (h : a + b = c) :
    SyntheticCategory.biShift a ⋙ SyntheticCategory.biShift b ≅
      (SyntheticCategory.biShift c : Syn ⥤ Syn) :=
  SyntheticCategory.biShift_comp a b ≪≫
    eqToIso (congrArg SyntheticCategory.biShift h)

/-- The degree of the already defined `lambdaPow n`. -/
public def lambdaDegree (n : ℕ) : ℤ × ℤ := (0, -(n : ℤ))

/-- The existing addition comparison on the λ axis, with no new choices. -/
public noncomputable def lambdaShiftAddIso (i j k : ℕ) (h : i + j = k) :
    SyntheticCategory.biShift (lambdaDegree i) ⋙
        SyntheticCategory.biShift (lambdaDegree j) ≅
      (SyntheticCategory.biShift (lambdaDegree k) : Syn ⥤ Syn) :=
  biShiftAddIso (lambdaDegree i) (lambdaDegree j) (lambdaDegree k)
    (by subst k; ext <;> simp [lambdaDegree, Nat.cast_add, add_comm])

/-- The source map for restriction from the `j`th to the `i`th λ quotient.
It uses multiplication by the existing `lambdaPow (j-i)`, through the
specified addition comparison. Its commuting square is proved separately. -/
public noncomputable def lambdaRestrictionSourceMap (i j : ℕ) (hij : i ≤ j) (X : Syn) :
    (SyntheticCategory.biShift (lambdaDegree j)).obj X ⟶
      (SyntheticCategory.biShift (lambdaDegree i)).obj X :=
  (lambdaShiftAddIso (j - i) i j (Nat.sub_add_cancel hij)).inv.app X ≫
    (SyntheticCategory.biShift (lambdaDegree i)).map (lambdaPow (j - i) X)

end KIP126.Synthetic.Context

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

variable (Syn : Type u) [SyntheticCategory.{u, v} Syn]

/-- Associativity, units, and centrality of λ for the existing suspension
comparisons. The named intermediate and final degrees only make every
transport explicit; their equalities determine them uniquely. -/
public structure BiShiftCoherence : Prop where
  associativity : ∀ (a b c ab bc total : ℤ × ℤ)
      (hab : a + b = ab) (hbc : b + c = bc)
      (habc : ab + c = total) (habc' : a + bc = total) (X : Syn),
    (SyntheticCategory.biShift c).map ((biShiftAddIso a b ab hab).hom.app X) ≫
        (biShiftAddIso ab c total habc).hom.app X =
      (biShiftAddIso b c bc hbc).hom.app ((SyntheticCategory.biShift a).obj X) ≫
        (biShiftAddIso a bc total habc').hom.app X
  left_unit : ∀ (a : ℤ × ℤ) (X : Syn),
    (biShiftAddIso 0 a a (zero_add a)).hom.app X =
      (SyntheticCategory.biShift a).map (SyntheticCategory.biShift_zero.hom.app X)
  right_unit : ∀ (a : ℤ × ℤ) (X : Syn),
    (biShiftAddIso a 0 a (add_zero a)).hom.app X =
      SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift a).obj X)
  lambda_comm : ∀ (a : ℤ × ℤ) (X : Syn),
    SyntheticCategory.lam.app ((SyntheticCategory.biShift a).obj X) =
      (biShiftAddIso a (0, -1) (a + (0, -1)) rfl).hom.app X ≫
        (biShiftAddIso (0, -1) a (a + (0, -1)) (add_comm _ _)).inv.app X ≫
        (SyntheticCategory.biShift a).map (SyntheticCategory.lam.app X)

end KIP126.Synthetic.Context

namespace KIP126.Synthetic.Context

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

theorem lambdaDegree_add (i j : ℕ) :
    lambdaDegree (i + j) = lambdaDegree i + lambdaDegree j := by
  ext <;> simp [lambdaDegree, Nat.cast_add, add_comm]

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

theorem comp_transport {a b : ℤ × ℤ} (h : a = b) (X Y : Syn)
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
public theorem lambdaPow_one (coh : BiShiftCoherence Syn) (X : Syn) :
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
public theorem lambdaPow_add_comparison (coh : BiShiftCoherence Syn)
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
public theorem lambdaPow_add (coh : BiShiftCoherence Syn)
    (i j k : ℕ) (h : i + j = k) (X : Syn) :
    lambdaPow k X = (lambdaShiftAddIso i j k h).inv.app X ≫
      (SyntheticCategory.biShift (lambdaDegree j)).map (lambdaPow i X) ≫
        lambdaPow j X := by
  rw [← lambdaPow_add_comparison coh i j k h X]
  simp

/-- The precise commuting square used to form actual quotient restrictions. -/
public theorem lambdaRestrictionSourceMap_commutes (coh : BiShiftCoherence Syn)
    (i j : ℕ) (hij : i ≤ j) (X : Syn) :
    lambdaRestrictionSourceMap i j hij X ≫ lambdaPow i X = lambdaPow j X := by
  simpa only [lambdaRestrictionSourceMap, Category.assoc] using
    (lambdaPow_add coh (j - i) i j (Nat.sub_add_cancel hij) X).symm

/-- The restriction square at an equal index has the identity source map.
An identity law for the resulting cofiber map is a separate requirement on
the chosen cofiber construction. -/
public theorem lambdaRestrictionSourceMap_self (coh : BiShiftCoherence Syn)
    (i : ℕ) (X : Syn) :
    lambdaRestrictionSourceMap i i le_rfl X =
      𝟙 ((SyntheticCategory.biShift (lambdaDegree i)).obj X) := by
  have hzero (n : ℕ) (hn : n = 0) (hni : n + i = i) :
      (lambdaShiftAddIso n i i hni).inv.app X ≫
          (SyntheticCategory.biShift (lambdaDegree i)).map (lambdaPow n X) =
        𝟙 ((SyntheticCategory.biShift (lambdaDegree i)).obj X) := by
    cases hn
    rw [← coh.lambdaShift_zero_left i X]
    exact Iso.inv_hom_id_app _ X
  exact hzero (i - i) (Nat.sub_self i) (Nat.sub_add_cancel le_rfl)

/-- The source map of the restriction square is natural before any cofiber
choice is made. -/
public theorem lambdaRestrictionSourceMap_naturality (i j : ℕ) (hij : i ≤ j)
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
