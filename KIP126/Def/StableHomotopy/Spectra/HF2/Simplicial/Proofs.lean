module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Simplicial.Data
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

@[expose] public section

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

set_option backward.isDefEq.respectTransparency false

/-- Every degree of the specified single coefficient complex is finite. -/
theorem hf2ChainComplex_finite (n r : ℕ) : Finite ((hf2ChainComplex n).X r) := by
  by_cases hr : r = n
  · subst r
    change Finite (((HomologicalComplex.single (ModuleCat (ZMod 2))
      (ComplexShape.down ℕ) n).obj (ModuleCat.of (ZMod 2) (ZMod 2))).X n)
    rw [HomologicalComplex.single_obj_X_self]
    exact inferInstanceAs (Finite (ZMod 2))
  · letI : Subsingleton ((hf2ChainComplex n).X r) := ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) n
        (ModuleCat.of (ZMod 2) (ZMod 2)) r hr)
    exact Finite.of_subsingleton

/-- Every actual simplicial degree of this Dold--Kan object is finite.
The finite sum over simplex surjections gives the explicit finiteness proof. -/
theorem hf2SimplicialModule_finite (n r : ℕ) :
    Finite ((hf2SimplicialModule n).obj (op ⦋r⦌)) := by
  let f (A : SimplicialObject.Splitting.IndexSet (op ⦋r⦌)) :=
    (hf2ChainComplex n).X A.1.unop.len
  letI : ∀ A, Finite (f A) := fun A => hf2ChainComplex_finite n A.1.unop.len
  let e : (hf2SimplicialModule n).obj (op ⦋r⦌) ≅
      ModuleCat.of (ZMod 2) (∀ A, f A) :=
    (biproduct.isoCoproduct f).symm ≪≫ ModuleCat.biproductIsoPi f
  exact Finite.of_injective e.toLinearEquiv e.toLinearEquiv.injective

/-- Forgetting the linear structure retains the finite actual simplex sets. -/
theorem hf2SimplicialSet_finite (n r : ℕ) :
    Finite ((hf2SimplicialSet n).obj (op ⦋r⦌)) :=
  hf2SimplicialModule_finite n r

/-- Below the generating degree the actual simplicial module is zero:
every Dold--Kan summand comes from a strictly lower chain degree. -/
theorem hf2SimplicialModule_isZero_below (n r : ℕ) (hr : r < n) :
    IsZero ((hf2SimplicialModule n).obj (op ⦋r⦌)) := by
  change IsZero (∐ fun A : SimplicialObject.Splitting.IndexSet (op ⦋r⦌) =>
    (hf2ChainComplex n).X A.1.unop.len)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Sigma.hom_ext
  intro A
  have hlen := SimplexCategory.len_le_of_epi A.e
  have hz : IsZero ((hf2ChainComplex n).X A.1.unop.len) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) n
      (ModuleCat.of (ZMod 2) (ZMod 2)) A.1.unop.len (by
        have : A.1.unop.len ≤ r := hlen
        omega)
  exact hz.eq_of_src _ _

/-- The underlying simplicial set has only its zero simplex in each degree
below `n`; the assertion concerns the fixed Dold--Kan simplices. -/
theorem hf2SimplicialSet_subsingleton_below (n r : ℕ) (hr : r < n) :
    Subsingleton ((hf2SimplicialSet n).obj (op ⦋r⦌)) :=
  ModuleCat.subsingleton_of_isZero (hf2SimplicialModule_isZero_below n r hr)

/-- The normalized complex has zero homology away from the prescribed
degree. This is an algebraic calculation, not yet a topological π comparison. -/
theorem hf2NormalizedHomology_isZero (n r : ℕ) (hr : r ≠ n) :
    IsZero (((AlgebraicTopology.normalizedMooreComplex (ModuleCat (ZMod 2))).obj
      (hf2SimplicialModule n)).homology r) := by
  exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) n
    (ModuleCat.of (ZMod 2) (ZMod 2)) r hr).of_iso
      (HomologicalComplex.homologyMapIso (hf2NormalizedComplexIso n) r)

/-- The vanishing result also identifies the actual underlying homology
type as a singleton, suitable for a later cubical homotopy comparison. -/
theorem hf2NormalizedHomology_subsingleton (n r : ℕ) (hr : r ≠ n) :
    Subsingleton (((AlgebraicTopology.normalizedMooreComplex (ModuleCat (ZMod 2))).obj
      (hf2SimplicialModule n)).homology r) :=
  ModuleCat.subsingleton_of_isZero (hf2NormalizedHomology_isZero n r hr)

end KIP126.StableHomotopy.Spectra
