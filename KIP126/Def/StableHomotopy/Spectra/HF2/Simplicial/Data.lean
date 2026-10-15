module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

/-- The actual F₂-module chain complex concentrated in degree `n`. -/
noncomputable def hf2ChainComplex (n : ℕ) : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  (HomologicalComplex.single _ (ComplexShape.down ℕ) n).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))

/-- Dold--Kan denormalization of F₂ concentrated in degree `n`. -/
noncomputable def hf2SimplicialModule (n : ℕ) : SimplicialObject (ModuleCat.{0} (ZMod 2)) :=
  CategoryTheory.Abelian.DoldKan.Γ.obj (hf2ChainComplex n)

/-- The actual underlying simplicial set of the denormalized module. -/
noncomputable def hf2SimplicialSet (n : ℕ) : SSet.{0} :=
  hf2SimplicialModule n ⋙ forget (ModuleCat (ZMod 2))

/-- The geometric realization, based at the zero vertex. The comparison
of its cubical homotopy groups with normalized homology is a further theorem. -/
noncomputable def hf2RealizationLevel (n : ℕ) : BasedSpace.{0} where
  space := SSet.toTop.obj (hf2SimplicialSet n)
  point := TopCat.toSSetObj₀Equiv
    ((sSetTopAdj.unit.app (hf2SimplicialSet n)).app (op ⦋0⦌)
      (0 : (hf2SimplicialModule n).obj (op ⦋0⦌)))

/-- Normalization recovers the specified chain complex by the counit of
the proved Dold--Kan equivalence. -/
noncomputable def hf2NormalizedComplexIso (n : ℕ) :
    (AlgebraicTopology.normalizedMooreComplex (ModuleCat (ZMod 2))).obj
      (hf2SimplicialModule n) ≅ hf2ChainComplex n :=
  CategoryTheory.Abelian.DoldKan.equivalence.counitIso.app (hf2ChainComplex n)

end KIP126.StableHomotopy.Spectra
