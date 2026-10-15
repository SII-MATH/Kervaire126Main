module

public import KIP126.Def.Algebra.SimplicialModule.Principal.Realization.Fibration.Proofs
public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.Fibration
public import KIP126.Def.StableHomotopy.Spectra.HF2.Bond.CubicalComparison

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.HF2Bond
open CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false

/-- The actual endpoint projection of the fixed coefficient path object has
relative cubical homotopy lifting. Its simplex lifts are the specified zeroth
degeneracies; the realization theorem supplies genuine continuous lifts. -/
theorem hf2PathProjection_hasCubicalLifting (n : ℕ) :
    KIP126.Topology.HomotopyLifting.HasCubicalLifting (hf2PathProjection n) :=
  KIP126.Algebra.SimplicialModule.degreewise_surjective_realization_hasCubicalLifting
    (decalageProjection (hf2SimplicialModule (n+1)))
    (fun r => decalageProjection_app_surjective (hf2SimplicialModule (n+1))
      (op (SimplexCategory.mk r)))

/-- The adjoint of the specified continuous structure map induces actual
bijections on cubical homotopy in every nonnegative dimension. -/
theorem bondAdjointHomotopyMap_bijective (n r : ℕ) :
    Function.Bijective (bondAdjointHomotopyMap n r) :=
  bondAdjointHomotopyMap_bijective_of_lifting n r (hf2PathProjection_hasCubicalLifting n)

/-- The actual fixed coefficient prespectrum structure map gives
π_r(K_n) ≃ π_(r+1)(K_(n+1)), with its specified first-coordinate convention. -/
theorem bondHomotopyMap_bijective (n r : ℕ) :
    Function.Bijective (bondHomotopyMap n r) :=
  bondHomotopyMap_bijective_of_lifting n r (hf2PathProjection_hasCubicalLifting n)

end KIP126.StableHomotopy.Spectra.HF2Bond
