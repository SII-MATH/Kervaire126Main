module

public import KIP126.Def.Synthetic.Context.Coherence.Proofs

@[expose] public section

/-! Composition for the actual source maps of λ-power quotient restrictions.
Only the stated suspension coherence and the already proved power law enter.
-/

namespace KIP126.Synthetic.Context

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

private theorem restriction_comparison_comp (coh : BiShiftCoherence Syn)
    (a b c ab bc total : ℕ) (hab : a + b = ab) (hbc : b + c = bc)
    (htotal : ab + c = total) (htotal' : a + bc = total) (X : Syn) :
    ((lambdaShiftAddIso a bc total htotal').inv.app X ≫
        (SyntheticCategory.biShift (lambdaDegree bc)).map (lambdaPow a X)) ≫
      ((lambdaShiftAddIso b c bc hbc).inv.app X ≫
        (SyntheticCategory.biShift (lambdaDegree c)).map (lambdaPow b X)) =
    (lambdaShiftAddIso ab c total htotal).inv.app X ≫
      (SyntheticCategory.biShift (lambdaDegree c)).map (lambdaPow ab X) := by
  apply (cancel_epi ((lambdaShiftAddIso ab c total htotal).hom.app X)).mp
  apply (cancel_epi ((SyntheticCategory.biShift (lambdaDegree c)).map
    ((lambdaShiftAddIso a b ab hab).hom.app X))).mp
  have hnat := (lambdaShiftAddIso b c bc hbc).hom.naturality (lambdaPow a X)
  dsimp only [Functor.comp_map] at hnat
  calc
    _ = (lambdaShiftAddIso b c bc hbc).hom.app
          ((SyntheticCategory.biShift (lambdaDegree a)).obj X) ≫
        ((SyntheticCategory.biShift (lambdaDegree bc)).map (lambdaPow a X) ≫
          ((lambdaShiftAddIso b c bc hbc).inv.app X ≫
            (SyntheticCategory.biShift (lambdaDegree c)).map (lambdaPow b X))) := by
      rw [← Category.assoc,
        coh.lambdaShift_associativity a b c ab bc total hab hbc htotal htotal' X]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    _ = (SyntheticCategory.biShift (lambdaDegree c)).map
        ((SyntheticCategory.biShift (lambdaDegree b)).map (lambdaPow a X) ≫
          lambdaPow b X) := by
      dsimp only [lambdaDegree] at hnat ⊢
      rw [← Category.assoc, ← hnat]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
    _ = _ := by
      rw [← lambdaPow_add_comparison coh a b ab hab X]
      simp only [Functor.map_comp, Iso.hom_inv_id_app_assoc]

/-- Restricting from `k` to `j`, then to `i`, uses the same source map as
restricting directly from `k` to `i`. -/
theorem lambdaRestrictionSourceMap_comp (coh : BiShiftCoherence Syn)
    (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (X : Syn) :
    lambdaRestrictionSourceMap j k hjk X ≫ lambdaRestrictionSourceMap i j hij X =
      lambdaRestrictionSourceMap i k (hij.trans hjk) X := by
  exact restriction_comparison_comp coh (k - j) (j - i) i (k - i) j k
    (by omega) (Nat.sub_add_cancel hij) (Nat.sub_add_cancel (hij.trans hjk))
    (Nat.sub_add_cancel hjk) X

end KIP126.Synthetic.Context
