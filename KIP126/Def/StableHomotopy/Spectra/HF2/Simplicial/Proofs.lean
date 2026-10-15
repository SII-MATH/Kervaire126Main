module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Simplicial.Data
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

@[expose] public section

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

set_option backward.isDefEq.respectTransparency false

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

end KIP126.StableHomotopy.Spectra
