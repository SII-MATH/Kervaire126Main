module

public import KIP126.Def.StableHomotopy.Spectra.Generators

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum
open CategoryTheory Topology
open scoped unitInterval

/-- The actual cubical generator of the iterated reduced suspension sphere. -/
def sphereCube : ∀ n, GenLoop (Fin n) (sphereLevel n) (sphereLevel n).point
  | 0 => ⟨ContinuousMap.const _ (show sphereLevel 0 from (1 : Fin 2)), by
      intro t ht
      obtain ⟨i, _⟩ := ht
      exact Fin.elim0 i⟩
  | n + 1 => stabilizeLoop sphere n n (sphereCube n)

end KIP126.StableHomotopy.Spectra.Prespectrum
