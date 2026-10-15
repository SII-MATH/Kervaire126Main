module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Data
public import KIP126.Def.StableHomotopy.Context.Proofs
public import Mathlib.LinearAlgebra.Finsupp.Pi

@[expose] public section

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)

/-- The sphere's coefficient homology, using the actual tensor unitor. -/
def sphereHomologyCoefficientF2Equiv (n : ℤ) :
    letI := mod2HF2HomotopyModule H R n
    mod2HomologyF2 H R n SphereSpectrum ≃ₗ[ZMod 2] HomotopyGroup n H.HF2 :=
  letI := mod2HomologyModule H R n SphereSpectrum
  letI := mod2HF2HomotopyModule H R n
  let e : Mod2Homology H n SphereSpectrum ≃+ HomotopyGroup n H.HF2 :=
    ((homotopyGroupFunctor n).mapIso (ρ_ H.HF2)).addCommGroupIsoToAddEquiv
  { e with map_smul' := ZMod.map_smul e }

/-- Length-zero coordinates follow from the Eilenberg--Mac Lane property,
not from Milnor coordinates on a page. -/
def sphereHomologyEmptyWordEquiv (n : ℤ) :
    mod2HomologyF2 H R n SphereSpectrum ≃ₗ[ZMod 2] (MilnorWord 0 n →₀ ZMod 2) := by
  letI := mod2HF2HomotopyModule H R n
  refine (sphereHomologyCoefficientF2Equiv H R n).trans
    (show HomotopyGroup n H.HF2 ≃ₗ[ZMod 2] (MilnorWord 0 n →₀ ZMod 2) from ?_)
  by_cases hn : n = 0
  · subst n
    exact (mod2Pi0LinearEquiv H R).trans
      (Finsupp.uniqueLinearEquiv (ZMod 2) (ZMod 2)
        (⟨Fin.elim0, by simp [wordDegree], fun i => Fin.elim0 i⟩ : MilnorWord 0 0)).symm
  · letI := H.homotopy_vanishes n hn
    letI : IsEmpty (MilnorWord 0 n) := ⟨fun d => hn (milnorWord_zero_degree d)⟩
    exact LinearEquiv.ofSubsingleton _ _

end

end KIP126.Classical.Adams
