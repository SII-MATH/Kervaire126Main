module

public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Proofs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

@[expose] public section

namespace KIP126.StableHomotopy.Spectra
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

namespace HF2Bond
open AlgebraicTopology

/-- The loop object vanishes below the degree of its coefficient. -/
theorem loopModule_isZero_below (n r : ℕ) (hr : r < n) :
    IsZero ((loopModule n).obj (op ⦋r⦌)) := by
  haveI : Mono (loopInclusion n) := inferInstanceAs
    (Mono (kernel.ι (decalageProjection (hf2SimplicialModule (n + 1)))))
  exact IsZero.of_mono ((loopInclusion n).app (op ⦋r⦌))
    (hf2SimplicialModule_isZero_below (n + 1) (r + 1) (by omega))

/-- The coefficient map into degree `n+1` of the actual Dold--Kan object,
obtained from the proved normalization isomorphism and its actual inclusion. -/
noncomputable def coefficientSimplex (n : ℕ) :
    ModuleCat.of (ZMod 2) (ZMod 2) ⟶ (hf2SimplicialModule (n + 1)).obj (op ⦋n+1⦌) :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) (n + 1)
      (ModuleCat.of (ZMod 2) (ZMod 2))).inv ≫
    (hf2NormalizedComplexIso (n + 1)).inv.f (n + 1) ≫
      (NormalizedMooreComplex.objX (hf2SimplicialModule (n + 1)) (n + 1)).arrow

/-- The generating coefficient is in the kernel of the zeroth face. -/
noncomputable def coefficientLoop (n : ℕ) :
    ModuleCat.of (ZMod 2) (ZMod 2) ⟶ (loopModule n).obj (op ⦋n⦌) :=
  kernel.lift ((decalageProjection (hf2SimplicialModule (n + 1))).app (op ⦋n⦌))
    (coefficientSimplex n) ((hf2SimplicialModule_isZero_below (n + 1) n
      (Nat.lt_succ_self n)).eq_of_tgt _ _) ≫
    (PreservesKernel.iso ((evaluation _ _).obj (op ⦋n⦌))
      (decalageProjection (hf2SimplicialModule (n + 1)))).inv

/-- The generating coefficient has vanishing higher faces in the loop object. -/
theorem coefficientLoop_normalized (n : ℕ) :
    (NormalizedMooreComplex.objX (loopModule n) n).Factors (coefficientLoop n) := by
  cases n with
  | zero => exact Subobject.top_factors _
  | succ n =>
    apply (Subobject.finset_inf_factors _).mpr
    intro i hi
    apply kernelSubobject_factors
    exact (loopModule_isZero_below (n + 1) n (Nat.lt_succ_self n)).eq_of_tgt _ _

/-- The coefficient in degree `n` of the actual normalized loop complex. -/
noncomputable def coefficientNormalizedLoop (n : ℕ) :
    ModuleCat.of (ZMod 2) (ZMod 2) ⟶
      ((normalizedMooreComplex (ModuleCat (ZMod 2))).obj (loopModule n)).X n :=
  Subobject.factorThru (NormalizedMooreComplex.objX (loopModule n) n)
    (coefficientLoop n) (coefficientLoop_normalized n)

/-- A chain map from the actual coefficient complex to the normalized loop
object, preserving the specified coefficient rather than choosing a zero map. -/
noncomputable def coefficientLoopChainMap (n : ℕ) :
    hf2ChainComplex n ⟶ (normalizedMooreComplex (ModuleCat (ZMod 2))).obj (loopModule n) :=
  HomologicalComplex.mkHomFromSingle (coefficientNormalizedLoop n) (by
    intro k hk
    have hkn : k < n := by change k + 1 = n at hk; omega
    have hz : IsZero (((normalizedMooreComplex (ModuleCat (ZMod 2))).obj
        (loopModule n)).X k) :=
      IsZero.of_mono (NormalizedMooreComplex.objX (loopModule n) k).arrow
        (loopModule_isZero_below n k hkn)
    exact hz.eq_of_tgt _ _)

/-- The actual simplicial coefficient-to-loop map, by the proved Dold--Kan
correspondence applied to the displayed chain map. -/
noncomputable def coefficientToLoop (n : ℕ) : hf2SimplicialModule n ⟶ loopModule n :=
  CategoryTheory.Abelian.DoldKan.Γ.map (coefficientLoopChainMap n) ≫
    (CategoryTheory.Abelian.DoldKan.equivalence.unitIso.app (loopModule n)).inv

noncomputable def coefficientToLoopSet (n : ℕ) : hf2SimplicialSet n ⟶ loopSet n :=
  Functor.whiskerRight (coefficientToLoop n) (forget (ModuleCat (ZMod 2)))

/-- Continuous structure maps between the fixed geometric coefficient spaces. -/
noncomputable def bond (n : ℕ) : C(hf2RealizationLevel n × I, hf2RealizationLevel (n + 1)) :=
  (loopBond n).comp
    (((SSet.toTop.map (coefficientToLoopSet n)).hom.comp ContinuousMap.fst).prodMk
      ContinuousMap.snd)

theorem bond_zero (n : ℕ) (x : hf2RealizationLevel n) :
    bond n (x, 0) = (hf2RealizationLevel (n + 1)).point :=
  loopBond_zero n _

theorem bond_one (n : ℕ) (x : hf2RealizationLevel n) :
    bond n (x, 1) = (hf2RealizationLevel (n + 1)).point :=
  loopBond_one n _

theorem coefficientToLoopSet_point (n : ℕ) :
    SSet.toTop.map (coefficientToLoopSet n) (hf2RealizationLevel n).point =
      (loopRealizationLevel n).point := by
  change SSet.toTop.map (coefficientToLoopSet n)
    (realizeSimplex (hf2SimplicialSet n) (0 : (hf2SimplicialModule n).obj (op ⦋0⦌))
      default) = _
  rw [realizeSimplex_map]
  have h : (coefficientToLoopSet n).app (op ⦋0⦌)
      (0 : (hf2SimplicialModule n).obj (op ⦋0⦌)) =
        (0 : (loopModule n).obj (op ⦋0⦌)) :=
    ((coefficientToLoop n).app (op ⦋0⦌)).hom.map_zero
  rw [h]
  exact realizeSimplex_zero _ _ _

theorem bond_point (n : ℕ) (t : I) :
    bond n ((hf2RealizationLevel n).point, t) = (hf2RealizationLevel (n + 1)).point := by
  change loopBond n (SSet.toTop.map (coefficientToLoopSet n) (hf2RealizationLevel n).point, t) = _
  rw [coefficientToLoopSet_point]
  exact loopBond_point n t

end HF2Bond

/-- The actual prespectrum on the Dold--Kan geometric coefficient spaces.
Identification of its cubical stable homotopy is a further theorem. -/
noncomputable def hf2RealizationPrespectrum : Prespectrum.{0} where
  level := hf2RealizationLevel
  bond := HF2Bond.bond
  bond_point := HF2Bond.bond_point
  bond_zero := HF2Bond.bond_zero
  bond_one := HF2Bond.bond_one

end KIP126.StableHomotopy.Spectra
